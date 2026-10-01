use rowl_kernel::batch::{prepare_all, AxiomOrigin, PreparedAxioms, SourceAxioms};
use rowl_kernel::model::*;
use rowl_kernel::prepare::PreparedAxiom;

fn iri(name: &str) -> Iri {
    Iri {
        spelling: name.as_bytes().to_vec(),
    }
}
fn class(name: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(name) })
}
fn individual(name: &str) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(name) })
}
fn annotation(value: &str) -> Annotation {
    Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri("urn:note"),
        },
        value: AnnotationValue::Literal(Literal {
            lexical: value.as_bytes().to_vec(),
            datatype: Datatype {
                iri: iri("http://www.w3.org/2001/XMLSchema#string"),
            },
        }),
    }
}
fn item(document: u32, ordinal: u32, note: &str, axiom: Axiom, next: SourceAxioms) -> SourceAxioms {
    SourceAxioms::Cons {
        origin: AxiomOrigin { document, ordinal },
        axiom: Box::new(AnnotatedAxiom {
            annotations: vec![annotation(note)],
            axiom,
        }),
        next: Box::new(next),
    }
}

#[test]
fn mixed_batch_keeps_order_provenance_annotations_and_retained_axioms() {
    let source = item(
        1,
        7,
        "rule",
        Axiom::SubClassOf(class("urn:Machine"), class("urn:Asset")),
        item(
            2,
            3,
            "negative",
            Axiom::NegativeObjectPropertyAssertion(
                ObjectPropertyExpression::Inverse(ObjectProperty {
                    iri: iri("urn:hasPart"),
                }),
                individual("urn:motor"),
                individual("urn:pump"),
            ),
            item(
                1,
                7,
                "declaration",
                Axiom::Declaration(Entity::Class(Class {
                    iri: iri("urn:Asset"),
                })),
                SourceAxioms::Empty,
            ),
        ),
    );
    let mut prepared = prepare_all(source);
    for (document, ordinal, note, kind) in [
        (1, 7, "rule", 0),
        (2, 3, "negative", 1),
        (1, 7, "declaration", 2),
    ] {
        let PreparedAxioms::Cons {
            origin,
            axiom,
            next,
        } = prepared
        else {
            panic!("dropped occurrence")
        };
        assert_eq!((origin.document, origin.ordinal), (document, ordinal));
        assert_eq!(axiom.annotations.len(), 1);
        let AnnotationValue::Literal(literal) = &axiom.annotations[0].value else {
            panic!("annotation changed")
        };
        assert_eq!(literal.lexical, note.as_bytes());
        match (kind, axiom.logical) {
            (0, PreparedAxiom::UniversalClass(_)) => (),
            (1, PreparedAxiom::Retained(a)) => {
                let Axiom::NegativeObjectPropertyAssertion(
                    ObjectPropertyExpression::Property(p),
                    Individual::Named(subject),
                    Individual::Named(object),
                ) = *a
                else {
                    panic!("orientation/kind changed")
                };
                assert_eq!(p.iri.spelling, b"urn:hasPart");
                assert_eq!(subject.iri.spelling, b"urn:pump");
                assert_eq!(object.iri.spelling, b"urn:motor");
            }
            (2, PreparedAxiom::Retained(a)) => assert!(matches!(*a, Axiom::Declaration(_))),
            _ => panic!("occurrences reordered"),
        }
        prepared = *next;
    }
    assert!(matches!(prepared, PreparedAxioms::Empty));
}

#[test]
fn empty_batch_is_empty() {
    assert!(matches!(
        prepare_all(SourceAxioms::Empty),
        PreparedAxioms::Empty
    ));
}
