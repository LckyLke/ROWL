//! A convenience interface over the verified pipeline: read a Functional Syntax
//! document once and ask questions about it by IRI.
//!
//! Every answer comes from the verified kernel functions: the document reader,
//! the mapping into the raw OWL model and the prepared queries of
//! `data_ontology`. `None` means the question or the document is outside the
//! reasoner's supported fragment, or a limit was reached. This module only
//! collects names and loops over questions; it adds no reasoning of its own.
use rowl_kernel::data_ontology::{
    prepare, prepared_class_satisfiable, prepared_consistent, prepared_instance_of,
    prepared_subsumed, Prepared,
};
use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::{DocumentError, DocumentLimits};
use rowl_kernel::model::{
    Axiom, Class, ClassExpression, Entity, Individual, Iri, NamedIndividual, RawOntology,
};
use rowl_kernel::source_reasoning::source_ontology;
use std::collections::BTreeSet;

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
    /// The verified reader rejected the document.
    Document(DocumentError),
    /// The document maps into the model, but its axioms are outside the
    /// fragment the queries prepare.
    Unsupported,
}

/// A document read and prepared once.
pub struct Reasoner {
    ontology: RawOntology,
    prepared: Prepared,
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

impl Reasoner {
    /// Read a Functional Syntax document from its bytes and prepare it once.
    pub fn from_functional(bytes: &[u8], limits: &DocumentLimits) -> Result<Reasoner, LoadError> {
        let scope = b"document".to_vec();
        let ontology = match source_ontology(&bytes.to_vec(), limits, &scope) {
            Ok(Some(ontology)) => ontology,
            Ok(None) => return Err(LoadError::Unsupported),
            Err(error) => return Err(LoadError::Document(error)),
        };
        match prepare(&ontology.axioms) {
            Some(prepared) => Ok(Reasoner { ontology, prepared }),
            None => Err(LoadError::Unsupported),
        }
    }
    /// The raw OWL ontology that was read.
    pub fn ontology(&self) -> &RawOntology {
        &self.ontology
    }
    /// Whether the axioms have a model.
    pub fn consistent(&self) -> Option<bool> {
        prepared_consistent(&self.prepared)
    }
    /// Whether some model of the axioms has an instance of `class`.
    pub fn satisfiable(&self, class: &ClassExpression) -> Option<bool> {
        prepared_class_satisfiable(&self.prepared, class)
    }
    /// Whether every instance of `sub` is an instance of `sup` in every model.
    pub fn subsumed(&self, sub: &ClassExpression, sup: &ClassExpression) -> Option<bool> {
        prepared_subsumed(&self.prepared, sub, sup)
    }
    /// Whether the named individual is an instance of `class` in every model.
    pub fn instance_of(&self, individual: &str, class: &ClassExpression) -> Option<bool> {
        prepared_instance_of(
            &self.prepared,
            &NamedIndividual {
                iri: Iri {
                    spelling: individual.as_bytes().to_vec(),
                },
            },
            class,
        )
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
    /// whether it is satisfiable; `None` if some question has no answer.
    pub fn classify(&self) -> Option<Vec<Classified>> {
        let classes = self.classes();
        let expressions: Vec<ClassExpression> =
            classes.iter().map(|iri| class_expression(iri)).collect();
        let mut out = Vec::new();
        for (index, sub) in expressions.iter().enumerate() {
            let satisfiable = self.satisfiable(sub)?;
            let mut supers = Vec::new();
            if satisfiable {
                for (other, sup) in expressions.iter().enumerate() {
                    if other != index && self.subsumed(sub, sup)? {
                        supers.push(classes[other].clone());
                    }
                }
            }
            out.push(Classified {
                class: classes[index].clone(),
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
