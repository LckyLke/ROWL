//! A convenience interface over the verified pipeline: read a Functional
//! Syntax, N-Triples or Turtle document, or the import closure of one from a
//! catalog of documents, once and ask questions about it by IRI.
//!
//! Every answer comes from the verified kernel functions: the document reader,
//! the mapping into the raw OWL model (for N-Triples and Turtle, the reverse
//! OWL RDF mapping of `rdf_mapping`), the prepared queries of `data_ontology`, the
//! classification of `classification` and, for EL ontologies, the saturation of
//! `saturation`. `None` means the question or the
//! document is outside the reasoner's supported fragment, or a limit was
//! reached. An import closure is read and assembled by the verified
//! `import_closure::source_closure`. This module only collects names and lays
//! out answers; it adds no reasoning of its own. `dl_violation` reports, in
//! words, the verdict of the verified OWL 2 DL check `dl_validity::check_ontology`.
use rowl_kernel::classification::classify;
use rowl_kernel::data_ontology::{
    prepare, prepared_class_satisfiable, prepared_consistent, prepared_instance_of,
    prepared_subsumed, Prepared,
};
use rowl_kernel::dl_validity::{check_ontology, DlCheck};
use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::{DocumentError, DocumentLimits};
use rowl_kernel::import_catalog::{Format, Source, SourceError};
use rowl_kernel::import_closure::{source_closure, ClosureError, Origin};
use rowl_kernel::model::{
    AnnotatedAxiom, AnonymousIndividual, Axiom, Class, ClassExpression, Entity, Individual, Iri,
    NamedIndividual, RawOntology,
};
use rowl_kernel::ntriples::{read, ReadError, ReadResult};
use rowl_kernel::rdf_mapping::map_graph;
use rowl_kernel::roles::Role;
use rowl_kernel::saturation;
use rowl_kernel::source_reasoning::source_ontology;
use rowl_kernel::turtle;
use rowl_kernel::typing::EntityKind;
use std::collections::BTreeSet;
use std::sync::OnceLock;

/// The stack the verified kernel runs on. Its readers, mapping and queries
/// recurse over the length of their input, so a large document needs far more
/// than a thread's default stack; the memory is only committed as it is used.
const KERNEL_STACK: usize = 1 << 30;

/// Run `work` on a thread with [`KERNEL_STACK`] bytes of stack and return its
/// result, resuming a panic of `work` on the calling thread.
fn on_kernel_stack<T: Send>(work: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .stack_size(KERNEL_STACK)
            .spawn_scoped(scope, work)
            .expect("a thread with the kernel's stack");
        match handle.join() {
            Ok(value) => value,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    })
}

/// Generous limits for documents of everyday size.
pub fn default_limits() -> DocumentLimits {
    DocumentLimits {
        tokens: 50_000_000,
        prefixes: 10_000,
        prefix_value: 8_192,
        imports: 10_000,
        iri: 8_192,
        axioms: 5_000_000,
        annotations: AnnotationLimits {
            depth: 32,
            count: 100_000,
            iri: 8_192,
            lexical: 1_000_000,
        },
        classes: ClassLimits {
            depth: 128,
            count: 100_000,
            iri: 8_192,
        },
    }
}

/// Why a document could not be loaded.
pub enum LoadError {
    /// The verified Functional Syntax reader rejected the document.
    Document(DocumentError),
    /// The verified N-Triples reader rejected the document.
    Triples(ReadError),
    /// The verified Turtle reader rejected the document.
    Turtle(turtle::ReadError),
    /// The graph is not the RDF mapping of an ontology that the verified
    /// reverse mapping reads: an undeclared entity, an incomplete expression,
    /// an annotated axiom or a triple left over.
    Graph,
    /// The read document does not map into the raw OWL model.
    Unsupported,
    /// A document of a catalog could not be read; the inner error says why.
    InDocument {
        document: String,
        error: Box<LoadError>,
    },
    /// A document of the import closure imports an IRI that is the ontology
    /// IRI or version IRI of no document of the catalog. Nothing is fetched.
    MissingImport { document: String, iri: String },
    /// A document of the import closure imports an IRI that several documents
    /// of the catalog have as their ontology IRI or version IRI; the first two
    /// are named.
    AmbiguousImport {
        document: String,
        iri: String,
        first: String,
        second: String,
    },
    /// The import closure could not be assembled, for the reason given.
    Closure(String),
}

/// The syntax of a document of a catalog.
pub enum Syntax {
    /// OWL 2 Functional-Style Syntax.
    Functional,
    /// N-Triples, read as the OWL ontology its graph encodes.
    NTriples,
    /// Turtle, read as the OWL ontology its graph encodes; relative IRIs
    /// resolve against this base IRI until the document declares its own.
    Turtle(Vec<u8>),
}

/// A document of a catalog for [`Reasoner::from_documents`]: a name used in
/// messages, such as its path, its syntax and its bytes.
pub struct Document {
    pub name: String,
    pub syntax: Syntax,
    pub bytes: Vec<u8>,
}

/// The documents of an import closure and where its axioms come from.
struct Provenance {
    /// The names of the catalog's documents.
    names: Vec<String>,
    /// The catalog positions of the documents of the closure.
    documents: Vec<usize>,
    /// The document and position of every axiom.
    origins: Vec<Origin>,
}

/// A document read once. Its queries are prepared once, when the first
/// question that needs them is asked, so a classification that saturation
/// answers never prepares them; its OWL 2 DL verdict is likewise computed when
/// first asked for.
pub struct Reasoner {
    ontology: RawOntology,
    provenance: Option<Provenance>,
    prepared: OnceLock<Option<Prepared>>,
    violation: OnceLock<Option<String>>,
}

fn class_expression(iri: &str) -> ClassExpression {
    ClassExpression::Class(Class {
        iri: Iri {
            spelling: iri.as_bytes().to_vec(),
        },
    })
}

fn collect_classes(expression: &ClassExpression, out: &mut BTreeSet<Vec<u8>>) {
    match expression {
        ClassExpression::Class(class) => {
            out.insert(class.iri.spelling.clone());
        }
        ClassExpression::ObjectIntersectionOf(members)
        | ClassExpression::ObjectUnionOf(members) => {
            collect_classes(&members.first, out);
            collect_classes(&members.second, out);
            for member in &members.rest {
                collect_classes(member, out);
            }
        }
        ClassExpression::ObjectComplementOf(operand) => collect_classes(operand, out),
        ClassExpression::ObjectSomeValuesFrom(_, filler)
        | ClassExpression::ObjectAllValuesFrom(_, filler) => collect_classes(filler, out),
        ClassExpression::ObjectMinCardinality(_, _, Some(filler))
        | ClassExpression::ObjectMaxCardinality(_, _, Some(filler))
        | ClassExpression::ObjectExactCardinality(_, _, Some(filler)) => {
            collect_classes(filler, out)
        }
        _ => {}
    }
}

fn axiom_classes(axiom: &Axiom, out: &mut BTreeSet<Vec<u8>>) {
    match axiom {
        Axiom::Declaration(Entity::Class(class)) => {
            out.insert(class.iri.spelling.clone());
        }
        Axiom::SubClassOf(sub, sup) => {
            collect_classes(sub, out);
            collect_classes(sup, out);
        }
        Axiom::EquivalentClasses(members) | Axiom::DisjointClasses(members) => {
            collect_classes(&members.first, out);
            collect_classes(&members.second, out);
            for member in &members.rest {
                collect_classes(member, out);
            }
        }
        Axiom::DisjointUnion(class, members) => {
            out.insert(class.iri.spelling.clone());
            collect_classes(&members.first, out);
            collect_classes(&members.second, out);
            for member in &members.rest {
                collect_classes(member, out);
            }
        }
        Axiom::ObjectPropertyDomain(_, class)
        | Axiom::ObjectPropertyRange(_, class)
        | Axiom::DataPropertyDomain(_, class)
        | Axiom::ClassAssertion(class, _) => collect_classes(class, out),
        _ => {}
    }
}

/// The words for an entity kind.
fn kind_name(kind: &EntityKind) -> &'static str {
    match kind {
        EntityKind::Class => "class",
        EntityKind::Datatype => "datatype",
        EntityKind::ObjectProperty => "object property",
        EntityKind::DataProperty => "data property",
        EntityKind::AnnotationProperty => "annotation property",
        EntityKind::NamedIndividual => "named individual",
    }
}

fn iri_text(iri: &Iri) -> String {
    String::from_utf8_lossy(&iri.spelling).into_owned()
}

fn role_text(role: &Role<'_>) -> String {
    if role.inverse {
        format!("ObjectInverseOf({})", iri_text(role.iri))
    } else {
        iri_text(role.iri)
    }
}

fn anonymous_text(individual: &AnonymousIndividual) -> String {
    format!("_:{}", String::from_utf8_lossy(&individual.label))
}

/// The Functional Syntax keyword of an axiom.
fn axiom_name(axiom: &Axiom) -> &'static str {
    match axiom {
        Axiom::Declaration(_) => "Declaration",
        Axiom::SubClassOf(..) => "SubClassOf",
        Axiom::EquivalentClasses(_) => "EquivalentClasses",
        Axiom::DisjointClasses(_) => "DisjointClasses",
        Axiom::DisjointUnion(..) => "DisjointUnion",
        Axiom::SubObjectPropertyOf(..) => "SubObjectPropertyOf",
        Axiom::EquivalentObjectProperties(_) => "EquivalentObjectProperties",
        Axiom::DisjointObjectProperties(_) => "DisjointObjectProperties",
        Axiom::InverseObjectProperties(..) => "InverseObjectProperties",
        Axiom::ObjectPropertyDomain(..) => "ObjectPropertyDomain",
        Axiom::ObjectPropertyRange(..) => "ObjectPropertyRange",
        Axiom::FunctionalObjectProperty(_) => "FunctionalObjectProperty",
        Axiom::InverseFunctionalObjectProperty(_) => "InverseFunctionalObjectProperty",
        Axiom::ReflexiveObjectProperty(_) => "ReflexiveObjectProperty",
        Axiom::IrreflexiveObjectProperty(_) => "IrreflexiveObjectProperty",
        Axiom::SymmetricObjectProperty(_) => "SymmetricObjectProperty",
        Axiom::AsymmetricObjectProperty(_) => "AsymmetricObjectProperty",
        Axiom::TransitiveObjectProperty(_) => "TransitiveObjectProperty",
        Axiom::SubDataPropertyOf(..) => "SubDataPropertyOf",
        Axiom::EquivalentDataProperties(_) => "EquivalentDataProperties",
        Axiom::DisjointDataProperties(_) => "DisjointDataProperties",
        Axiom::DataPropertyDomain(..) => "DataPropertyDomain",
        Axiom::DataPropertyRange(..) => "DataPropertyRange",
        Axiom::FunctionalDataProperty(_) => "FunctionalDataProperty",
        Axiom::DatatypeDefinition(..) => "DatatypeDefinition",
        Axiom::HasKey(..) => "HasKey",
        Axiom::SameIndividual(_) => "SameIndividual",
        Axiom::DifferentIndividuals(_) => "DifferentIndividuals",
        Axiom::ClassAssertion(..) => "ClassAssertion",
        Axiom::ObjectPropertyAssertion(..) => "ObjectPropertyAssertion",
        Axiom::NegativeObjectPropertyAssertion(..) => "NegativeObjectPropertyAssertion",
        Axiom::DataPropertyAssertion(..) => "DataPropertyAssertion",
        Axiom::NegativeDataPropertyAssertion(..) => "NegativeDataPropertyAssertion",
        Axiom::AnnotationAssertion(..) => "AnnotationAssertion",
        Axiom::SubAnnotationPropertyOf(..) => "SubAnnotationPropertyOf",
        Axiom::AnnotationPropertyDomain(..) => "AnnotationPropertyDomain",
        Axiom::AnnotationPropertyRange(..) => "AnnotationPropertyRange",
    }
}

/// An axiom by its kind and its position, from 1, in the document's axioms or,
/// for an import closure, in the axioms of the document it comes from.
fn axiom_text(
    ontology: &RawOntology,
    provenance: Option<&Provenance>,
    item: &AnnotatedAxiom,
) -> String {
    let index = ontology
        .axioms
        .iter()
        .position(|candidate| std::ptr::eq(candidate, item));
    let origin = provenance.and_then(|provenance| {
        let origin = provenance.origins.get(index?)?;
        Some((provenance.names.get(origin.document)?, origin.position))
    });
    match (index, origin) {
        (_, Some((name, position))) => format!(
            "the {} axiom at position {} of {}",
            axiom_name(&item.axiom),
            position + 1,
            name
        ),
        (Some(index), None) => format!(
            "the {} axiom at position {}",
            axiom_name(&item.axiom),
            index + 1
        ),
        (None, None) => format!("a {} axiom", axiom_name(&item.axiom)),
    }
}

/// Why the verified assembly found no import closure, as a load error.
fn closure_error(error: ClosureError, names: &[String]) -> LoadError {
    let name = |document: usize| {
        names
            .get(document)
            .cloned()
            .unwrap_or_else(|| format!("document {document}"))
    };
    match error {
        ClosureError::Unread(unread) => LoadError::InDocument {
            document: name(unread.document),
            error: Box::new(match unread.error {
                SourceError::Functional(error) => LoadError::Document(error),
                SourceError::Unmapped => LoadError::Unsupported,
                SourceError::Triples(error) => LoadError::Triples(error),
                SourceError::Turtle(error) => LoadError::Turtle(error),
                SourceError::Graph => LoadError::Graph,
            }),
        },
        ClosureError::MissingImport { document, iri } => LoadError::MissingImport {
            document: name(document),
            iri: iri_text(&iri),
        },
        ClosureError::AmbiguousImport {
            document,
            iri,
            first,
            second,
        } => LoadError::AmbiguousImport {
            document: name(document),
            iri: iri_text(&iri),
            first: name(first),
            second: name(second),
        },
        ClosureError::NoRoot => {
            LoadError::Closure("the root is not a document of the catalog".into())
        }
        ClosureError::TooManyDocuments => {
            LoadError::Closure("the catalog has more documents than 32-bit keys".into())
        }
        ClosureError::Unresolved => {
            LoadError::Closure("the import closure was not resolved".into())
        }
        ClosureError::OutOfScope { document } => LoadError::Closure(format!(
            "{} has an anonymous individual outside its own scope",
            name(document)
        )),
        ClosureError::TooLarge => {
            LoadError::Closure("the import closure has more axioms than a vector holds".into())
        }
    }
}

/// The verified check's first violation in words, or `None` for `Valid`.
fn describe_violation(
    ontology: &RawOntology,
    provenance: Option<&Provenance>,
    check: &DlCheck<'_>,
) -> Option<String> {
    let axiom = |item: &AnnotatedAxiom| axiom_text(ontology, provenance, item);
    Some(match check {
        DlCheck::Valid => return None,
        DlCheck::EmptyKey(item) => format!(
            "{} has neither an object nor a data property (keys, §9.5)",
            axiom(item)
        ),
        DlCheck::Arity(item) => format!(
            "{} has fewer than two different members where two are required, or repeats a member \
             that must be different (structural arity)",
            axiom(item)
        ),
        DlCheck::ReservedOntologyIri(iri) => format!(
            "the ontology IRI {} is in the reserved vocabulary (§3.1)",
            iri_text(iri)
        ),
        DlCheck::ReservedVersionIri(iri) => format!(
            "the version IRI {} is in the reserved vocabulary (§3.1)",
            iri_text(iri)
        ),
        DlCheck::ReservedEntity { iri, kind } => format!(
            "{} is in the reserved vocabulary and cannot be used as a {} (§5.1–5.6)",
            iri_text(iri),
            kind_name(kind)
        ),
        DlCheck::ConflictingDeclarations { iri, kind, other } => format!(
            "{} is declared as a {} but is also a {} (typing constraints, §5.8.1)",
            iri_text(iri),
            kind_name(kind),
            kind_name(other)
        ),
        DlCheck::MissingDeclaration { iri, kind } => format!(
            "{} is used as a {} but not declared as one (typing constraints, §5.8.1)",
            iri_text(iri),
            kind_name(kind)
        ),
        DlCheck::TopDataProperty(item) => format!(
            "{} uses owl:topDataProperty other than as the superproperty of SubDataPropertyOf (§11.2)",
            axiom(item)
        ),
        DlCheck::MissingDatatypeDefinition(iri) => format!(
            "the datatype {} is neither built in nor defined by a DatatypeDefinition axiom (§11.2)",
            iri_text(iri)
        ),
        DlCheck::PredefinedDatatypeRedefined(item) => {
            format!("{} redefines a built-in datatype (§11.2)", axiom(item))
        }
        DlCheck::MultipleDatatypeDefinitions { first, second } => format!(
            "{} and {} define one datatype differently (§11.2)",
            axiom(first),
            axiom(second)
        ),
        DlCheck::DatatypeCycle { smaller, larger } => format!(
            "the datatype definitions are cyclic: {} is defined using {}, which depends on it (§11.2)",
            iri_text(larger),
            iri_text(smaller)
        ),
        DlCheck::DefinedDatatypeInOntologyAnnotation(_) => {
            "an ontology annotation has a literal of a defined datatype (§9.4)".to_string()
        }
        DlCheck::DefinedDatatypePosition(item) => format!(
            "{} uses a defined datatype in a literal or a datatype restriction (§9.4)",
            axiom(item)
        ),
        DlCheck::NonSimpleRole(role) => format!(
            "{} is not simple but is used where a simple object property is required: in a \
             cardinality or self restriction, or a functional, inverse-functional, irreflexive, \
             asymmetric or disjointness axiom (§11.2)",
            role_text(role)
        ),
        DlCheck::IrregularHierarchy { sub, sup } => format!(
            "the property chains require {} below {}, but {} is a subproperty of {}, so the \
             property hierarchy is not regular (§11.2)",
            role_text(sub),
            role_text(sup),
            role_text(sup),
            role_text(sub)
        ),
        DlCheck::AnonymousPosition(item) => format!(
            "{} uses an anonymous individual where OWL 2 DL forbids one (§11.2)",
            axiom(item)
        ),
        DlCheck::AnonymousSelfLoop(individual) => format!(
            "an object property assertion connects the anonymous individual {} with itself (§11.2)",
            anonymous_text(individual)
        ),
        DlCheck::AnonymousCycle { left, right } => format!(
            "the object property assertions between anonymous individuals form a cycle through {} \
             and {} (§11.2)",
            anonymous_text(left),
            anonymous_text(right)
        ),
        DlCheck::AnonymousMultipleAssertions { first, second } => format!(
            "{} and {} connect the same two anonymous individuals (§11.2)",
            axiom(first),
            axiom(second)
        ),
        DlCheck::AnonymousNoBoundaryRoot(individual) => format!(
            "no anonymous individual connected to {} has at most one assertion with a named \
             individual (§11.2)",
            anonymous_text(individual)
        ),
    })
}

impl Reasoner {
    /// Read a Functional Syntax document from its bytes.
    pub fn from_functional(bytes: &[u8], limits: &DocumentLimits) -> Result<Reasoner, LoadError> {
        on_kernel_stack(|| {
            let scope = b"document".to_vec();
            let ontology = match source_ontology(&bytes.to_vec(), limits, &scope) {
                Ok(Some(ontology)) => ontology,
                Ok(None) => return Err(LoadError::Unsupported),
                Err(error) => return Err(LoadError::Document(error)),
            };
            Ok(Reasoner::new(ontology))
        })
    }
    /// Read an N-Triples document from its bytes and the OWL ontology its
    /// graph encodes by the verified reverse RDF mapping.
    pub fn from_ntriples(bytes: &[u8]) -> Result<Reasoner, LoadError> {
        on_kernel_stack(|| {
            let scope = b"document".to_vec();
            let graph = match read(&bytes.to_vec(), &scope) {
                ReadResult::Graph(graph) => graph,
                ReadResult::Error(error) => return Err(LoadError::Triples(error)),
            };
            match map_graph(&graph) {
                Some(mapped) => Ok(Reasoner::new(mapped.ontology)),
                None => Err(LoadError::Graph),
            }
        })
    }
    /// Read a Turtle document from its bytes and the OWL ontology its graph
    /// encodes by the verified reverse RDF mapping. The document has no base
    /// IRI of its own, so a relative IRI needs an `@base` or `BASE` directive
    /// before it; [`Reasoner::from_turtle_with_base`] supplies one.
    pub fn from_turtle(bytes: &[u8]) -> Result<Reasoner, LoadError> {
        Reasoner::from_turtle_with_base(bytes, b"")
    }
    /// Read a Turtle document whose relative IRIs resolve against `base`
    /// until the document declares a base of its own.
    pub fn from_turtle_with_base(bytes: &[u8], base: &[u8]) -> Result<Reasoner, LoadError> {
        on_kernel_stack(|| {
            let scope = b"document".to_vec();
            let graph = match turtle::read(&bytes.to_vec(), &scope, &base.to_vec()) {
                turtle::ReadResult::Graph(graph) => graph,
                turtle::ReadResult::Error(error) => return Err(LoadError::Turtle(error)),
            };
            match map_graph(&graph) {
                Some(mapped) => Ok(Reasoner::new(mapped.ontology)),
                None => Err(LoadError::Graph),
            }
        })
    }
    /// Read the import closure of the document at position `root` of a
    /// catalog of documents (OWL 2 Structural Specification §3.4) and reason
    /// over its axiom closure. The verified `import_closure::source_closure`
    /// reads every document with its verified reader, each with its anonymous
    /// individuals kept apart from the other documents' (§5.6.2), follows the
    /// import IRIs, each of which must be the ontology IRI or version IRI of
    /// exactly one document of the catalog, and gathers the axioms of the
    /// documents it reaches, cycles included. Nothing is fetched.
    pub fn from_documents(
        documents: Vec<Document>,
        root: usize,
        limits: &DocumentLimits,
    ) -> Result<Reasoner, LoadError> {
        let mut names = Vec::new();
        let mut sources = Vec::new();
        for document in documents {
            names.push(document.name);
            sources.push(Source {
                format: match document.syntax {
                    Syntax::Functional => Format::Functional,
                    Syntax::NTriples => Format::NTriples,
                    Syntax::Turtle(base) => Format::Turtle(base),
                },
                bytes: document.bytes,
            });
        }
        match on_kernel_stack(|| source_closure(&sources, root, limits)) {
            Ok(closure) => Ok(Reasoner {
                ontology: closure.ontology,
                provenance: Some(Provenance {
                    names,
                    documents: closure.documents,
                    origins: closure.origins,
                }),
                prepared: OnceLock::new(),
                violation: OnceLock::new(),
            }),
            Err(error) => Err(closure_error(error, &names)),
        }
    }
    fn new(ontology: RawOntology) -> Reasoner {
        Reasoner {
            ontology,
            provenance: None,
            prepared: OnceLock::new(),
            violation: OnceLock::new(),
        }
    }
    /// The names of the documents of the import closure, in catalog order;
    /// empty for a document read on its own.
    pub fn documents(&self) -> Vec<String> {
        match &self.provenance {
            Some(provenance) => provenance
                .documents
                .iter()
                .filter_map(|&document| provenance.names.get(document).cloned())
                .collect(),
            None => Vec::new(),
        }
    }
    /// The prepared queries, prepared on first use; `None` when the axioms are
    /// outside the fragment the queries prepare.
    fn queries(&self) -> Option<&Prepared> {
        self.prepared
            .get_or_init(|| on_kernel_stack(|| prepare(&self.ontology.axioms)))
            .as_ref()
    }
    /// The raw OWL ontology that was read.
    pub fn ontology(&self) -> &RawOntology {
        &self.ontology
    }
    /// Whether the axioms have a model; an EL ontology is answered by
    /// saturation without preparing the queries.
    pub fn consistent(&self) -> Option<bool> {
        if let Some(answer) = on_kernel_stack(|| saturation::consistent(&self.ontology.axioms)) {
            return Some(answer);
        }
        let prepared = self.queries()?;
        on_kernel_stack(|| prepared_consistent(prepared))
    }
    /// Whether some model of the axioms has an instance of `class`.
    pub fn satisfiable(&self, class: &ClassExpression) -> Option<bool> {
        let prepared = self.queries()?;
        on_kernel_stack(|| prepared_class_satisfiable(prepared, class))
    }
    /// Whether every instance of `sub` is an instance of `sup` in every model.
    pub fn subsumed(&self, sub: &ClassExpression, sup: &ClassExpression) -> Option<bool> {
        let prepared = self.queries()?;
        on_kernel_stack(|| prepared_subsumed(prepared, sub, sup))
    }
    /// Whether the named individual is an instance of `class` in every model.
    pub fn instance_of(&self, individual: &str, class: &ClassExpression) -> Option<bool> {
        let individual = NamedIndividual {
            iri: Iri {
                spelling: individual.as_bytes().to_vec(),
            },
        };
        let prepared = self.queries()?;
        on_kernel_stack(|| prepared_instance_of(prepared, &individual, class))
    }
    /// The first OWL 2 DL restriction the document's axioms violate, in words,
    /// or `None` when they satisfy all of them. It is computed on demand by
    /// the verified `dl_validity::check_ontology`, whose verdict is proved
    /// exact for the structural, reserved-vocabulary, typing and global
    /// restrictions of the 2012 Structural Specification; the lexical forms of
    /// literals and facet values are not checked. For an import closure the
    /// check covers its whole axiom closure, so imported declarations count,
    /// and the ontology annotations of all its documents; of the ontology and
    /// version IRIs only the root's are checked. A document read on its own is
    /// checked without the ontologies it imports. Loading never rejects a
    /// document for these restrictions; the check runs on the first call and
    /// its verdict is kept.
    pub fn dl_violation(&self) -> Option<String> {
        let ontology = &self.ontology;
        let provenance = self.provenance.as_ref();
        self.violation
            .get_or_init(|| {
                on_kernel_stack(|| {
                    describe_violation(ontology, provenance, &check_ontology(ontology))
                })
            })
            .clone()
    }
    /// The named classes the document declares or uses, without `owl:Thing` and
    /// `owl:Nothing`, sorted by IRI.
    pub fn classes(&self) -> Vec<String> {
        let mut found = BTreeSet::new();
        for item in &self.ontology.axioms {
            axiom_classes(&item.axiom, &mut found);
        }
        found
            .into_iter()
            .filter(|iri| {
                iri.as_slice() != b"http://www.w3.org/2002/07/owl#Thing"
                    && iri.as_slice() != b"http://www.w3.org/2002/07/owl#Nothing"
            })
            .filter_map(|iri| String::from_utf8(iri).ok())
            .collect()
    }
    /// The named individuals the document asserts something about, sorted by IRI.
    pub fn individuals(&self) -> Vec<String> {
        fn add(individual: &Individual, found: &mut BTreeSet<Vec<u8>>) {
            if let Individual::Named(named) = individual {
                found.insert(named.iri.spelling.clone());
            }
        }
        let mut found = BTreeSet::new();
        for item in &self.ontology.axioms {
            match &item.axiom {
                Axiom::Declaration(Entity::NamedIndividual(named)) => {
                    found.insert(named.iri.spelling.clone());
                }
                Axiom::ClassAssertion(_, individual) => add(individual, &mut found),
                Axiom::ObjectPropertyAssertion(_, source, target)
                | Axiom::NegativeObjectPropertyAssertion(_, source, target) => {
                    add(source, &mut found);
                    add(target, &mut found);
                }
                Axiom::DataPropertyAssertion(_, source, _)
                | Axiom::NegativeDataPropertyAssertion(_, source, _) => add(source, &mut found),
                Axiom::SameIndividual(members) | Axiom::DifferentIndividuals(members) => {
                    add(&members.first, &mut found);
                    add(&members.second, &mut found);
                    for member in &members.rest {
                        add(member, &mut found);
                    }
                }
                _ => {}
            }
        }
        found
            .into_iter()
            .filter_map(|iri| String::from_utf8(iri).ok())
            .collect()
    }
    /// For each named class, its named superclasses (itself excluded) and
    /// whether it is satisfiable; `None` if some question has no answer. An EL
    /// ontology is classified by the verified saturation in one pass; otherwise
    /// the verified classification settles the questions that told subclass
    /// axioms and earlier answers already decide and asks the prepared queries
    /// only for the rest. An unsatisfiable class lists no superclasses.
    pub fn classify(&self) -> Option<Vec<Classified>> {
        let names = self.classes();
        let classes: Vec<Class> = names
            .iter()
            .map(|iri| Class {
                iri: Iri {
                    spelling: iri.as_bytes().to_vec(),
                },
            })
            .collect();
        if let Some(taxonomy) =
            on_kernel_stack(|| saturation::taxonomy(&self.ontology.axioms, &classes))
        {
            let mut out = Vec::new();
            for (index, class) in names.iter().enumerate() {
                let satisfiable = *taxonomy.satisfiable.get(index)?;
                let mut supers = Vec::new();
                if satisfiable {
                    let mut positions = taxonomy.supers.get(index)?.clone();
                    positions.sort_unstable();
                    for other in positions {
                        if other != index {
                            supers.push(names.get(other)?.clone());
                        }
                    }
                }
                out.push(Classified {
                    class: class.clone(),
                    satisfiable,
                    superclasses: supers,
                });
            }
            return Some(out);
        }
        let prepared = self.queries()?;
        let result = on_kernel_stack(|| classify(prepared, &self.ontology.axioms, &classes))?;
        let mut out = Vec::new();
        for (index, class) in names.iter().enumerate() {
            let satisfiable = *result.satisfiable.get(index)?;
            let row = result.subsumed.get(index)?;
            let mut supers = Vec::new();
            if satisfiable {
                for (other, sup) in names.iter().enumerate() {
                    if other != index && *row.get(other)? {
                        supers.push(sup.clone());
                    }
                }
            }
            out.push(Classified {
                class: class.clone(),
                satisfiable,
                superclasses: supers,
            });
        }
        Some(out)
    }
}

/// One named class of a classification.
pub struct Classified {
    pub class: String,
    pub satisfiable: bool,
    pub superclasses: Vec<String>,
}

/// The class expression of a named class IRI.
pub fn named(iri: &str) -> ClassExpression {
    class_expression(iri)
}
