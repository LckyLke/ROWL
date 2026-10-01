//! Semantics-preserving first preprocessing stages over the full raw AST.
//!
//! These operations do not certify OWL 2 DL validity or infer new facts.
//! Keep the source ontology, declarations, vocabulary and provenance: prepare
//! logical constraints only after the frontend/validation boundary is complete.

use crate::model::{
    AnnotatedAxiom, Annotation, AtLeastTwo, Axiom, ClassExpression, ObjectPropertyExpression,
};

/// A universal constraint applies to every object, including unnamed objects.
/// `Retained` means this preprocessing stage leaves that axiom intact.
pub enum PreparedAxiom {
    UniversalClass(Box<ClassExpression>),
    Retained(Box<Axiom>),
}

pub struct PreparedAnnotatedAxiom {
    pub annotations: Vec<Annotation>,
    pub logical: PreparedAxiom,
}

/// P^- (a,b) and not P^- (a,b) become P(b,a) and not P(b,a).
/// Orientation changes neither individual identity nor equality assumptions.
pub fn canonicalize_assertion(axiom: Axiom) -> Axiom {
    match axiom {
        Axiom::ObjectPropertyAssertion(ObjectPropertyExpression::Inverse(p), a, b) => {
            Axiom::ObjectPropertyAssertion(ObjectPropertyExpression::Property(p), b, a)
        }
        Axiom::NegativeObjectPropertyAssertion(ObjectPropertyExpression::Inverse(p), a, b) => {
            Axiom::NegativeObjectPropertyAssertion(ObjectPropertyExpression::Property(p), b, a)
        }
        other => other,
    }
}

/// C ⊑ D is the universal constraint ¬C ∪ D. No fresh name/witness is added.
pub fn lower_subclass(axiom: Axiom) -> PreparedAxiom {
    match axiom {
        Axiom::SubClassOf(sub, sup) => PreparedAxiom::UniversalClass(Box::new(
            ClassExpression::ObjectUnionOf(Box::new(AtLeastTwo {
                first: ClassExpression::ObjectComplementOf(Box::new(sub)),
                second: sup,
                rest: Vec::new(),
            })),
        )),
        other => PreparedAxiom::Retained(Box::new(other)),
    }
}

/// Compose the checked stages, preserving annotation metadata verbatim.
pub fn prepare_axiom(axiom: AnnotatedAxiom) -> PreparedAnnotatedAxiom {
    PreparedAnnotatedAxiom {
        annotations: axiom.annotations,
        logical: lower_subclass(canonicalize_assertion(axiom.axiom)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Class, Individual, Iri, NamedIndividual, ObjectProperty};

    fn individual(name: &str) -> Individual {
        Individual::Named(NamedIndividual {
            iri: Iri {
                spelling: name.as_bytes().to_vec(),
            },
        })
    }

    fn inverse() -> ObjectPropertyExpression {
        ObjectPropertyExpression::Inverse(ObjectProperty {
            iri: Iri {
                spelling: b"urn:hasPart".to_vec(),
            },
        })
    }

    fn name(individual: Individual) -> Vec<u8> {
        let Individual::Named(n) = individual else {
            panic!("expected named")
        };
        n.iri.spelling
    }

    #[test]
    fn positive_and_negative_inverse_assertions_swap_only_endpoints() {
        for negative in [false, true] {
            let a = if negative {
                Axiom::NegativeObjectPropertyAssertion(
                    inverse(),
                    individual("urn:part"),
                    individual("urn:pump"),
                )
            } else {
                Axiom::ObjectPropertyAssertion(
                    inverse(),
                    individual("urn:part"),
                    individual("urn:pump"),
                )
            };
            let result = canonicalize_assertion(canonicalize_assertion(a));
            let (p, a, b) = match result {
                Axiom::ObjectPropertyAssertion(p, a, b) if !negative => (p, a, b),
                Axiom::NegativeObjectPropertyAssertion(p, a, b) if negative => (p, a, b),
                _ => panic!("assertion kind changed"),
            };
            let ObjectPropertyExpression::Property(p) = p else {
                panic!("expected forward")
            };
            assert_eq!(p.iri.spelling, b"urn:hasPart");
            assert_eq!(name(a), b"urn:pump");
            assert_eq!(name(b), b"urn:part");
        }
    }

    #[test]
    fn subclass_lowering_is_a_universal_constraint_and_keeps_metadata() {
        let class = |name: &str| {
            ClassExpression::Class(Class {
                iri: Iri {
                    spelling: name.as_bytes().to_vec(),
                },
            })
        };
        let prepared = prepare_axiom(AnnotatedAxiom {
            annotations: vec![],
            axiom: Axiom::SubClassOf(class("urn:Machine"), class("urn:Asset")),
        });
        assert!(prepared.annotations.is_empty());
        let PreparedAxiom::UniversalClass(constraint) = prepared.logical else {
            panic!("expected universal constraint")
        };
        let ClassExpression::ObjectUnionOf(terms) = *constraint else {
            panic!("expected universal disjunction")
        };
        assert!(matches!(
            terms.first,
            ClassExpression::ObjectComplementOf(_)
        ));
        assert!(matches!(terms.second, ClassExpression::Class(_)));
        assert!(terms.rest.is_empty());
    }
}
