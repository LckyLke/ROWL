//! A convenience interface over the verified pipeline: read a Functional
//! Syntax, N-Triples, Turtle or RDF/XML document, or the import closure of one
//! from a catalog of documents, once and ask questions about it by IRI.
//!
//! Every answer comes from the verified kernel functions: the document reader,
//! the mapping into the raw OWL model (for N-Triples, Turtle and RDF/XML, the
//! reverse OWL RDF mapping of `rdf_mapping`), the prepared queries of `data_ontology`, the
//! classification of `classification` and, for EL ontologies, the saturation of
//! `saturation`. `None` means the question or the
//! document is outside the reasoner's supported fragment, or a limit was
//! reached. An import closure is read and assembled by the verified
//! `import_closure::source_closure`. This module only collects names and lays
//! out answers; it adds no reasoning of its own. `dl_violation` reports, in
//! words, the verdict of the verified OWL 2 DL check `dl_validity::check_ontology`.
use rowl_kernel::classification::classify;
use rowl_kernel::components::{
    closure_parts, consistent_by_parts, plain_question, tbox_closure, Parts,
};
use rowl_kernel::data_ontology::{
    prepare, prepared_class_satisfiable, prepared_consistent, prepared_instance_of,
    prepared_subsumed, Prepared,
};
use rowl_kernel::dl_validity::{check_ontology, DlCheck};
use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::{DocumentError, DocumentLimits};
use rowl_kernel::import_catalog::{read_source, Format, Source, SourceError};
use rowl_kernel::import_closure::{source_closure, ClosureError, Origin};
use rowl_kernel::model::{
    AnnotatedAxiom, AnonymousIndividual, AtLeastTwo, Axiom, Class, ClassExpression, Entity,
    Individual, Iri, NamedIndividual, RawOntology,
};
use rowl_kernel::ntriples::{read, ReadError, ReadResult};
use rowl_kernel::rdf_mapping::map_graph;
use rowl_kernel::rdfxml;
use rowl_kernel::roles::Role;
use rowl_kernel::saturation;
use rowl_kernel::source_reasoning::source_ontology;
use rowl_kernel::turtle;
use rowl_kernel::typing::EntityKind;
use rowl_kernel::xml::XmlError;
use std::collections::{BTreeSet, HashMap};
use std::sync::OnceLock;

/// The stack the verified kernel runs on. Its readers, mapping and queries
/// recurse over the length of their input (the XML reader once per sibling
/// element, about 1.6 KB each), so a large document needs far more than a
/// thread's default stack; the memory is only committed as it is used.
#[cfg(target_pointer_width = "64")]
const KERNEL_STACK: usize = 4 << 30;
#[cfg(not(target_pointer_width = "64"))]
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
    /// The verified XML reader rejected an RDF/XML document.
    Xml(XmlError),
    /// The element tree of an RDF/XML document has no RDF/XML graph.
    RdfXml(rdfxml::ErrorKind),
    /// An RDF/XML document is too long for the reader's limits.
    TooLong,
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
    /// RDF/XML, read as the OWL ontology its graph encodes; relative IRIs
    /// resolve against this base IRI until `xml:base` gives another.
    RdfXml(Vec<u8>),
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
    consistency: OnceLock<Option<bool>>,
    /// The axioms other than assertions and their prepared queries, which
    /// answer class questions when the closure is consistent.
    tbox: OnceLock<Option<(Vec<AnnotatedAxiom>, Prepared)>>,
    /// The parts of the closure for instance questions, computed by the first
    /// instance question of a consistent closure.
    split: OnceLock<Option<Split>>,
}

/// The parts of a closure for instance questions (`components::closure_parts`):
/// the component of each named individual that an assertion names, and the
/// prepared queries of each part and of the axioms other than assertions,
/// prepared on first use.
struct Split {
    parts: Parts,
    component_of: HashMap<Vec<u8>, usize>,
    prepared: Vec<OnceLock<Option<Prepared>>>,
    tbox: OnceLock<Option<Prepared>>,
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

/// The words for why the verified XML reader rejected a document.
pub fn xml_error_words(error: &XmlError) -> String {
    use rowl_kernel::xml::ErrorKind;
    let what = match error.kind {
        ErrorKind::MalformedUtf8 => "the bytes are not UTF-8",
        ErrorKind::NonXmlCharacter => "a character that XML does not allow",
        ErrorKind::UnsupportedEncoding => "an encoding other than UTF-8",
        ErrorKind::UnexpectedEnd => "the text ends inside a construct",
        ErrorKind::Syntax => "the text does not match the XML grammar",
        ErrorKind::InvalidName => "a missing or invalid name",
        ErrorKind::MismatchedEndTag => "an end tag that does not match its start tag",
        ErrorKind::DuplicateAttribute => "an attribute given twice",
        ErrorKind::UndeclaredPrefix => "a namespace prefix without a declaration",
        ErrorKind::ReservedNamespace => "a reserved namespace prefix or name",
        ErrorKind::InvalidCharacterReference => {
            "a character reference to a character XML does not allow"
        }
        ErrorKind::UndeclaredEntity => "a reference to an undeclared, external or unparsed entity",
        ErrorKind::RecursiveEntity => "an entity that refers to itself",
        ErrorKind::EntityBoundary => "an entity whose content does not end inside it",
        ErrorKind::UnsupportedDeclaration => "a DTD declaration other than an internal entity",
        ErrorKind::ResourceLimit => "the entity expansion budget or a length limit",
    };
    format!("XML error at byte {}: {what}", error.offset)
}

/// The words for why the verified Functional Syntax reader rejected a
/// document: what the reader found and, when it names one, the byte where.
pub fn document_error_words(error: &DocumentError) -> String {
    let (what, offset) = document_error_parts(error);
    match offset {
        Some(offset) => format!("Functional Syntax error at byte {offset}: {what}"),
        None => format!("Functional Syntax error: {what}"),
    }
}

/// What a reader found, and the byte where, when it names one.
type Found = (&'static str, Option<usize>);

fn document_error_parts(error: &DocumentError) -> Found {
    use rowl_kernel::functional_document::{DocumentExpected, TableError};
    match error {
        DocumentError::Prefix(error) => prefix_error_parts(error),
        DocumentError::Table(kind) => (
            match kind {
                TableError::InvalidName => "a prefix declaration with an invalid prefix name",
                TableError::ReservedName => {
                    "a declaration that binds one of the standard prefix names rdf:, rdfs:, xsd: \
                     and owl: to a namespace other than its own"
                }
                TableError::InvalidNamespace => {
                    "a prefix declaration whose namespace is not an absolute IRI"
                }
                TableError::Duplicate => "a prefix name declared twice",
            },
            None,
        ),
        DocumentError::Header(error) => header_error_parts(error),
        DocumentError::Annotation(error) => annotation_error_parts(error),
        DocumentError::Declaration(error) => declaration_error_parts(error),
        DocumentError::AnnotationAxiom(error) => annotation_axiom_error_parts(error),
        DocumentError::ClassAxiom(error) => class_axiom_error_parts(error),
        DocumentError::PropertyAxiom(error) => property_axiom_error_parts(error),
        DocumentError::DataAxiom(error) => data_axiom_error_parts(error),
        DocumentError::Assertion(error) => assertion_error_parts(error),
        DocumentError::AxiomLimit { offset } => {
            ("more axioms than the reader's limit", Some(*offset))
        }
        DocumentError::Expected { expected, offset } => (
            match expected {
                DocumentExpected::Axiom => {
                    "an axiom or the closing parenthesis of the ontology was expected \
                     (rules and other constructs outside OWL 2 are not read)"
                }
                DocumentExpected::Close => "the closing parenthesis of the ontology was expected",
                DocumentExpected::End => "text after the closing parenthesis of the ontology",
            },
            Some(*offset),
        ),
    }
}

fn prefix_error_parts(error: &rowl_kernel::functional_prefixes::PrefixReadError) -> Found {
    use rowl_kernel::functional_prefixes::{PrefixReadError, PrefixSyntaxError};
    match error {
        PrefixReadError::Syntax(PrefixSyntaxError::Expected { offset, .. }) => (
            "a malformed prefix declaration or ontology opening",
            Some(*offset),
        ),
        PrefixReadError::Syntax(PrefixSyntaxError::Name(error)) => name_error_parts(error),
        PrefixReadError::Syntax(PrefixSyntaxError::DeclarationLimit { offset }) => (
            "more prefix declarations than the reader's limit",
            Some(*offset),
        ),
        PrefixReadError::InvalidText(error) => text_error_parts(error),
        PrefixReadError::NoToken { offset } => {
            ("text that is no Functional Syntax token", Some(*offset))
        }
        PrefixReadError::MissingSeparator { offset } => (
            "two tokens without white space or a parenthesis between them",
            Some(*offset),
        ),
        PrefixReadError::TokenLimit { offset } => {
            ("more tokens than the reader's limit", Some(*offset))
        }
        PrefixReadError::InvalidSpan { offset } => ("a malformed token", Some(*offset)),
    }
}

fn text_error_parts(error: &rowl_kernel::unicode::TextError) -> Found {
    use rowl_kernel::unicode::TextError;
    match error {
        TextError::InvalidPosition { offset } => ("a position inside a character", Some(*offset)),
        TextError::InvalidUtf8 { offset } => ("bytes that are not UTF-8", Some(*offset)),
        TextError::NonXmlCharacter { offset, .. } => {
            ("a character that the syntax does not allow", Some(*offset))
        }
    }
}

fn name_error_parts(error: &rowl_kernel::functional_names::NameError) -> Found {
    use rowl_kernel::functional_names::NameError;
    match error {
        NameError::InvalidSpan { offset } | NameError::InvalidToken { offset } => {
            ("a malformed name or IRI", Some(*offset))
        }
        NameError::ResourceLimit { offset } => {
            ("a name longer than the reader's limit", Some(*offset))
        }
    }
}

fn iri_error_parts(error: &rowl_kernel::functional_iris::SourceIriError) -> Found {
    use rowl_kernel::functional_iris::SourceIriError;
    match error {
        SourceIriError::Name(error) => name_error_parts(error),
        SourceIriError::InvalidParts { offset } => ("a malformed IRI", Some(*offset)),
        SourceIriError::UndeclaredPrefix { offset } => {
            ("a prefix name without a Prefix declaration", Some(*offset))
        }
        SourceIriError::ResourceLimit { offset } => {
            ("an IRI longer than the reader's limit", Some(*offset))
        }
        SourceIriError::InvalidExpandedIri { offset } => (
            "an abbreviated IRI that does not expand to an absolute IRI",
            Some(*offset),
        ),
    }
}

fn literal_error_parts(error: &rowl_kernel::functional_literals::SourceLiteralError) -> Found {
    use rowl_kernel::functional_literals::SourceLiteralError;
    match error {
        SourceLiteralError::Expected { offset, .. }
        | SourceLiteralError::InvalidSpan { offset } => ("a malformed literal", Some(*offset)),
        SourceLiteralError::Quoted(error) => ("a malformed quoted string", Some(error.offset)),
        SourceLiteralError::Language(error) => {
            let (_, offset) = name_error_parts(error);
            ("a malformed language tag", offset)
        }
        SourceLiteralError::Datatype(error) => iri_error_parts(error),
        SourceLiteralError::LexicalLimit { offset } => {
            ("a literal longer than the reader's limit", Some(*offset))
        }
        SourceLiteralError::DatatypeLimit { offset } => (
            "a datatype IRI longer than the reader's limit",
            Some(*offset),
        ),
    }
}

fn individual_error_parts(error: &rowl_kernel::functional_individuals::IndividualError) -> Found {
    use rowl_kernel::functional_individuals::IndividualError;
    match error {
        IndividualError::Expected { offset } => ("an individual was expected", Some(*offset)),
        IndividualError::Iri(error) => iri_error_parts(error),
        IndividualError::Anonymous(error) => name_error_parts(error),
        IndividualError::CountLimit { offset } => {
            ("more individuals than the reader's limit", Some(*offset))
        }
    }
}

fn range_error_parts(error: &rowl_kernel::functional_ranges::RangeError) -> Found {
    use rowl_kernel::functional_ranges::RangeError;
    match error {
        RangeError::Expected { offset, .. } => ("a malformed data range", Some(*offset)),
        RangeError::Iri(error) => iri_error_parts(error),
        RangeError::Literal(error) => literal_error_parts(error),
        RangeError::DepthLimit { offset } => (
            "a data range nested deeper than the reader's limit",
            Some(*offset),
        ),
        RangeError::CountLimit { offset } => {
            ("more members than the reader's limit", Some(*offset))
        }
    }
}

fn class_error_parts(error: &rowl_kernel::functional_classes::ClassError) -> Found {
    use rowl_kernel::functional_classes::ClassError;
    match error {
        ClassError::Expected { offset, .. } => ("a malformed class expression", Some(*offset)),
        ClassError::Iri(error) => iri_error_parts(error),
        ClassError::Individual(error) => individual_error_parts(error),
        ClassError::Range(error) => range_error_parts(error),
        ClassError::Literal(error) => literal_error_parts(error),
        ClassError::DepthLimit { offset } => (
            "a class expression nested deeper than the reader's limit",
            Some(*offset),
        ),
        ClassError::CountLimit { offset } => (
            "more members, or a larger number, than the reader's limit",
            Some(*offset),
        ),
    }
}

fn annotation_error_parts(error: &rowl_kernel::functional_annotations::AnnotationError) -> Found {
    use rowl_kernel::functional_annotations::AnnotationError;
    match error {
        AnnotationError::Expected { offset, .. } => ("a malformed annotation", Some(*offset)),
        AnnotationError::Property(error) | AnnotationError::Iri(error) => iri_error_parts(error),
        AnnotationError::Anonymous(error) => name_error_parts(error),
        AnnotationError::Literal(error) => literal_error_parts(error),
        AnnotationError::DepthLimit { offset } => (
            "annotations nested deeper than the reader's limit",
            Some(*offset),
        ),
        AnnotationError::CountLimit { offset } => {
            ("more annotations than the reader's limit", Some(*offset))
        }
    }
}

fn header_error_parts(error: &rowl_kernel::functional_header::HeaderError) -> Found {
    use rowl_kernel::functional_header::HeaderError;
    match error {
        HeaderError::Expected { offset, .. } => ("a malformed ontology header", Some(*offset)),
        HeaderError::Iri(error) => iri_error_parts(error),
        HeaderError::ImportLimit { offset } => {
            ("more imports than the reader's limit", Some(*offset))
        }
    }
}

fn declaration_error_parts(
    error: &rowl_kernel::functional_declarations::DeclarationError,
) -> Found {
    use rowl_kernel::functional_declarations::DeclarationError;
    match error {
        DeclarationError::Expected { offset, .. } => ("a malformed declaration", Some(*offset)),
        DeclarationError::Annotation(error) => annotation_error_parts(error),
        DeclarationError::Iri(error) => iri_error_parts(error),
    }
}

fn annotation_axiom_error_parts(
    error: &rowl_kernel::functional_annotation_axioms::AnnotationAxiomError,
) -> Found {
    use rowl_kernel::functional_annotation_axioms::AnnotationAxiomError;
    match error {
        AnnotationAxiomError::Expected { offset, .. } => {
            ("a malformed annotation axiom", Some(*offset))
        }
        AnnotationAxiomError::Annotation(error) | AnnotationAxiomError::Value(error) => {
            annotation_error_parts(error)
        }
        AnnotationAxiomError::Iri(error) => iri_error_parts(error),
        AnnotationAxiomError::Anonymous(error) => name_error_parts(error),
    }
}

fn class_axiom_error_parts(error: &rowl_kernel::functional_class_axioms::ClassAxiomError) -> Found {
    use rowl_kernel::functional_class_axioms::ClassAxiomError;
    match error {
        ClassAxiomError::Expected { offset, .. } => ("a malformed class axiom", Some(*offset)),
        ClassAxiomError::Annotation(error) => annotation_error_parts(error),
        ClassAxiomError::Class(error) => class_error_parts(error),
        ClassAxiomError::Iri(error) => iri_error_parts(error),
    }
}

fn property_axiom_error_parts(
    error: &rowl_kernel::functional_property_axioms::PropertyAxiomError,
) -> Found {
    use rowl_kernel::functional_property_axioms::PropertyAxiomError;
    match error {
        PropertyAxiomError::Expected { offset, .. } => {
            ("a malformed object property axiom", Some(*offset))
        }
        PropertyAxiomError::CountLimit { offset } => {
            ("more properties than the reader's limit", Some(*offset))
        }
        PropertyAxiomError::Annotation(error) => annotation_error_parts(error),
        PropertyAxiomError::Class(error) => class_error_parts(error),
    }
}

fn data_axiom_error_parts(error: &rowl_kernel::functional_data_axioms::DataAxiomError) -> Found {
    use rowl_kernel::functional_data_axioms::DataAxiomError;
    match error {
        DataAxiomError::Expected { offset, .. } => {
            ("a malformed data property axiom", Some(*offset))
        }
        DataAxiomError::CountLimit { offset } => {
            ("more properties than the reader's limit", Some(*offset))
        }
        DataAxiomError::Iri(error) => iri_error_parts(error),
        DataAxiomError::Annotation(error) => annotation_error_parts(error),
        DataAxiomError::Class(error) => class_error_parts(error),
        DataAxiomError::Range(error) => range_error_parts(error),
    }
}

fn assertion_error_parts(error: &rowl_kernel::functional_assertions::AssertionError) -> Found {
    use rowl_kernel::functional_assertions::AssertionError;
    match error {
        AssertionError::Expected { offset, .. } => ("a malformed assertion", Some(*offset)),
        AssertionError::Annotation(error) => annotation_error_parts(error),
        AssertionError::Class(error) => class_error_parts(error),
        AssertionError::Individual(error) => individual_error_parts(error),
        AssertionError::Literal(error) => literal_error_parts(error),
    }
}

/// The words for why an XML document has no RDF/XML graph.
pub fn rdfxml_error_words(kind: rdfxml::ErrorKind) -> &'static str {
    use rdfxml::ErrorKind;
    match kind {
        ErrorKind::InvalidName => {
            "an element without namespace, or a name not allowed where it occurs"
        }
        ErrorKind::UnqualifiedAttribute => "an attribute without namespace",
        ErrorKind::DuplicateAttribute => "two attributes that denote the same IRI",
        ErrorKind::InvalidAttributes => "attributes that no RDF/XML production allows together",
        ErrorKind::InvalidContent => "content that no RDF/XML production allows",
        ErrorKind::InvalidId => "an rdf:ID or rdf:nodeID value that is not an NCName",
        ErrorKind::DuplicateId => "an rdf:ID value given twice with the same base IRI",
        ErrorKind::InvalidCharacter => "a code point that is not a Unicode scalar value",
        ErrorKind::InvalidIri => {
            "a value that is not an IRI reference, or a relative IRI without a base"
        }
        ErrorKind::InvalidLanguageTag => "an ill-formed language tag",
        ErrorKind::InvalidDatatype => "rdf:datatype naming rdf:langString",
        ErrorKind::UnsupportedParseType => {
            "rdf:parseType=\"Literal\" (XML literals are not supported)"
        }
        ErrorKind::UnsupportedDatatype => {
            "rdf:datatype on an empty property element with property attributes"
        }
        ErrorKind::ResourceLimit => "a term or the number of triples beyond the reader's limits",
    }
}

/// Why the verified reader of one document rejected it, as a load error.
fn source_error(error: SourceError) -> LoadError {
    match error {
        SourceError::Functional(error) => LoadError::Document(error),
        SourceError::Unmapped => LoadError::Unsupported,
        SourceError::Triples(error) => LoadError::Triples(error),
        SourceError::Turtle(error) => LoadError::Turtle(error),
        SourceError::Xml(error) => LoadError::Xml(error),
        SourceError::RdfXml(kind) => LoadError::RdfXml(kind),
        SourceError::TooLong => LoadError::TooLong,
        SourceError::Graph => LoadError::Graph,
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
            error: Box::new(source_error(unread.error)),
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
    /// Read an RDF/XML document from its bytes and the OWL ontology its graph
    /// encodes by the verified reverse RDF mapping. The document has no base
    /// IRI of its own, so a relative IRI needs an `xml:base` in force;
    /// [`Reasoner::from_rdfxml_with_base`] supplies one.
    pub fn from_rdfxml(bytes: &[u8]) -> Result<Reasoner, LoadError> {
        Reasoner::from_rdfxml_with_base(bytes, b"")
    }
    /// Read an RDF/XML document whose relative IRIs resolve against `base`
    /// until `xml:base` gives another, by the verified catalog reader
    /// `import_catalog::read_source` with `import_catalog::rdfxml_limits`.
    pub fn from_rdfxml_with_base(bytes: &[u8], base: &[u8]) -> Result<Reasoner, LoadError> {
        on_kernel_stack(|| {
            let source = Source {
                format: Format::RdfXml(base.to_vec()),
                bytes: bytes.to_vec(),
            };
            match read_source(&source, &default_limits(), &b"document".to_vec()) {
                Ok(ontology) => Ok(Reasoner::new(ontology)),
                Err(error) => Err(source_error(error)),
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
                    Syntax::RdfXml(base) => Format::RdfXml(base),
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
                consistency: OnceLock::new(),
                tbox: OnceLock::new(),
                split: OnceLock::new(),
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
            consistency: OnceLock::new(),
            tbox: OnceLock::new(),
            split: OnceLock::new(),
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
    /// saturation without preparing the queries, and a closure that falls
    /// apart along its assertions part by part (`consistent_by_parts`). The
    /// answer is computed on the first call and kept.
    pub fn consistent(&self) -> Option<bool> {
        *self.consistency.get_or_init(|| {
            if let Some(answer) = on_kernel_stack(|| saturation::consistent(&self.ontology.axioms))
            {
                return Some(answer);
            }
            if let Some(answer) = on_kernel_stack(|| consistent_by_parts(&self.ontology.axioms)) {
                return Some(answer);
            }
            let prepared = self.queries()?;
            on_kernel_stack(|| prepared_consistent(prepared))
        })
    }
    /// The axioms other than assertions and their prepared queries, when the
    /// closure is consistent and of the kind that `components::tbox_closure`
    /// splits: they answer satisfiability and subsumption questions as the
    /// closure does (`part_satisfiable_correct`, `part_subsumed_correct`).
    fn tbox_queries(&self) -> Option<&(Vec<AnnotatedAxiom>, Prepared)> {
        if self.consistent() != Some(true) {
            return None;
        }
        self.tbox
            .get_or_init(|| {
                on_kernel_stack(|| {
                    let part = tbox_closure(&self.ontology.axioms)?;
                    let prepared = prepare(&part)?;
                    Some((part, prepared))
                })
            })
            .as_ref()
    }
    /// Whether some model of the axioms has an instance of `class`. For a
    /// consistent closure the question goes to its axioms other than
    /// assertions when they answer it.
    pub fn satisfiable(&self, class: &ClassExpression) -> Option<bool> {
        if let Some((_, tbox)) = self.tbox_queries() {
            if on_kernel_stack(|| plain_question(class)) {
                if let Some(answer) = on_kernel_stack(|| prepared_class_satisfiable(tbox, class)) {
                    return Some(answer);
                }
            }
        }
        let prepared = self.queries()?;
        on_kernel_stack(|| prepared_class_satisfiable(prepared, class))
    }
    /// Whether every instance of `sub` is an instance of `sup` in every model.
    /// For a consistent closure the question goes to its axioms other than
    /// assertions when they answer it.
    pub fn subsumed(&self, sub: &ClassExpression, sup: &ClassExpression) -> Option<bool> {
        if let Some((_, tbox)) = self.tbox_queries() {
            if on_kernel_stack(|| plain_question(sub) && plain_question(sup)) {
                if let Some(answer) = on_kernel_stack(|| prepared_subsumed(tbox, sub, sup)) {
                    return Some(answer);
                }
            }
        }
        let prepared = self.queries()?;
        on_kernel_stack(|| prepared_subsumed(prepared, sub, sup))
    }
    /// Whether the named individual is an instance of `class` in every model.
    /// When the axioms have a model, the question is first asked of the part
    /// of the closure for the individual (`components::closure_parts`): the
    /// axioms other than assertions and the component of assertions connected
    /// to the individual, which has the same answer (`parts_instance_correct`),
    /// so that independent records are answered one at a time. The parts are
    /// found once, and each is prepared when first asked.
    pub fn instance_of(&self, individual: &str, class: &ClassExpression) -> Option<bool> {
        let individual = NamedIndividual {
            iri: Iri {
                spelling: individual.as_bytes().to_vec(),
            },
        };
        if self.consistent() == Some(true) {
            if let Some(answer) = self.part_instance_of(&individual, class) {
                return Some(answer);
            }
        }
        let prepared = self.queries()?;
        on_kernel_stack(|| prepared_instance_of(prepared, &individual, class))
    }
    /// The parts of the closure for instance questions, found on first use;
    /// `None` when the closure does not fall apart into them.
    fn split(&self) -> Option<&Split> {
        self.split
            .get_or_init(|| {
                let parts = on_kernel_stack(|| closure_parts(&self.ontology.axioms))?;
                let mut component_of = HashMap::new();
                for (index, component) in parts.components.iter().enumerate() {
                    for member in &component.members {
                        if let Individual::Named(named) = member {
                            component_of.insert(named.iri.spelling.clone(), index);
                        }
                    }
                }
                let prepared = parts.components.iter().map(|_| OnceLock::new()).collect();
                Some(Split {
                    parts,
                    component_of,
                    prepared,
                    tbox: OnceLock::new(),
                })
            })
            .as_ref()
    }
    /// The answer of the part of the closure for the individual: the part of
    /// its component, or the axioms other than assertions when no assertion
    /// names it. A part that holds half of the closure or more is not split
    /// off; the whole closure answers instead.
    fn part_instance_of(
        &self,
        individual: &NamedIndividual,
        class: &ClassExpression,
    ) -> Option<bool> {
        if !on_kernel_stack(|| plain_question(class)) {
            return None;
        }
        let split = self.split()?;
        let (part, prepared) = match split.component_of.get(&individual.iri.spelling) {
            Some(&index) => (&split.parts.components[index].part, &split.prepared[index]),
            None => (&split.parts.tbox, &split.tbox),
        };
        if 2 * part.len() >= self.ontology.axioms.len() {
            return None;
        }
        let prepared = prepared
            .get_or_init(|| on_kernel_stack(|| prepare(part)))
            .as_ref()?;
        on_kernel_stack(|| prepared_instance_of(prepared, individual, class))
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
    /// The named individuals the document declares, asserts something about or
    /// names in a class expression (`ObjectOneOf`, `ObjectHasValue`), sorted
    /// by IRI.
    pub fn individuals(&self) -> Vec<String> {
        fn add(individual: &Individual, found: &mut BTreeSet<Vec<u8>>) {
            if let Individual::Named(named) = individual {
                found.insert(named.iri.spelling.clone());
            }
        }
        fn class(expression: &ClassExpression, found: &mut BTreeSet<Vec<u8>>) {
            match expression {
                ClassExpression::ObjectIntersectionOf(members)
                | ClassExpression::ObjectUnionOf(members) => {
                    class(&members.first, found);
                    class(&members.second, found);
                    for member in &members.rest {
                        class(member, found);
                    }
                }
                ClassExpression::ObjectComplementOf(inner) => class(inner, found),
                ClassExpression::ObjectOneOf(individuals) => {
                    add(&individuals.first, found);
                    for individual in &individuals.rest {
                        add(individual, found);
                    }
                }
                ClassExpression::ObjectSomeValuesFrom(_, filler)
                | ClassExpression::ObjectAllValuesFrom(_, filler) => class(filler, found),
                ClassExpression::ObjectHasValue(_, individual) => add(individual, found),
                ClassExpression::ObjectMinCardinality(_, _, Some(filler))
                | ClassExpression::ObjectMaxCardinality(_, _, Some(filler))
                | ClassExpression::ObjectExactCardinality(_, _, Some(filler)) => {
                    class(filler, found)
                }
                _ => {}
            }
        }
        fn classes(members: &AtLeastTwo<ClassExpression>, found: &mut BTreeSet<Vec<u8>>) {
            class(&members.first, found);
            class(&members.second, found);
            for member in &members.rest {
                class(member, found);
            }
        }
        let mut found = BTreeSet::new();
        for item in &self.ontology.axioms {
            match &item.axiom {
                Axiom::Declaration(Entity::NamedIndividual(named)) => {
                    found.insert(named.iri.spelling.clone());
                }
                Axiom::SubClassOf(sub, sup) => {
                    class(sub, &mut found);
                    class(sup, &mut found);
                }
                Axiom::EquivalentClasses(members)
                | Axiom::DisjointClasses(members)
                | Axiom::DisjointUnion(_, members) => classes(members, &mut found),
                Axiom::ObjectPropertyDomain(_, expression)
                | Axiom::ObjectPropertyRange(_, expression)
                | Axiom::DataPropertyDomain(_, expression)
                | Axiom::HasKey(expression, _, _) => class(expression, &mut found),
                Axiom::ClassAssertion(expression, individual) => {
                    class(expression, &mut found);
                    add(individual, &mut found);
                }
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
        let result = match self.tbox_queries() {
            Some((part, tbox)) => on_kernel_stack(|| classify(tbox, part, &classes))?,
            None => {
                let prepared = self.queries()?;
                on_kernel_stack(|| classify(prepared, &self.ontology.axioms, &classes))?
            }
        };
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
