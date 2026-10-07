use rowl_kernel::anonymous_scopes::{scoped_annotated, scoped_class, scoped_ontology};
use rowl_kernel::model::{
    AnnotatedAxiom, Annotation, AnnotationProperty, AnnotationSubject, AnnotationValue,
    AnonymousIndividual, AtLeastTwo, Axiom, Class, ClassExpression, Individual, Iri, NonEmpty,
    ObjectProperty, ObjectPropertyExpression, OntologyIdentity, RawOntology,
};

fn iri(text: &str) -> Iri {
    Iri {
        spelling: text.as_bytes().to_vec(),
    }
}

fn anonymous(scope: &[u8], label: &str) -> AnonymousIndividual {
    AnonymousIndividual {
        scope: scope.to_vec(),
        label: label.as_bytes().to_vec(),
    }
}

fn class(name: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(name) })
}

/// `∃p.(A ⊓ {a})` with the individual `a` nested two levels down.
fn nested(individual: Individual) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Property(ObjectProperty { iri: iri("p") }),
        Box::new(ClassExpression::ObjectIntersectionOf(Box::new(
            AtLeastTwo {
                first: class("A"),
                second: ClassExpression::ObjectOneOf(NonEmpty {
                    first: Individual::Named(rowl_kernel::model::NamedIndividual { iri: iri("n") }),
                    rest: vec![individual],
                }),
                rest: vec![],
            },
        ))),
    )
}

fn comment(value: AnnotationValue, annotations: Vec<Annotation>) -> Annotation {
    Annotation {
        annotations,
        property: AnnotationProperty {
            iri: iri("comment"),
        },
        value,
    }
}

#[test]
fn nested_individuals_are_checked() {
    let here = b"here".to_vec();
    assert!(scoped_class(
        &here,
        &nested(Individual::Anonymous(anonymous(b"here", "x")))
    ));
    assert!(!scoped_class(
        &here,
        &nested(Individual::Anonymous(anonymous(b"there", "x")))
    ));
}

#[test]
fn annotations_and_annotation_assertions_are_checked() {
    let here = b"here".to_vec();
    let foreign = comment(AnnotationValue::Anonymous(anonymous(b"there", "y")), vec![]);
    let axiom = AnnotatedAxiom {
        annotations: vec![comment(AnnotationValue::Iri(iri("v")), vec![foreign])],
        axiom: Axiom::Declaration(rowl_kernel::model::Entity::Class(Class { iri: iri("A") })),
    };
    assert!(!scoped_annotated(&here, &axiom));
    let assertion = AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::AnnotationAssertion(
            AnnotationProperty {
                iri: iri("comment"),
            },
            AnnotationSubject::Anonymous(anonymous(b"here", "z")),
            AnnotationValue::Anonymous(anonymous(b"there", "z")),
        ),
    };
    assert!(!scoped_annotated(&here, &assertion));
    let ontology = RawOntology {
        identity: OntologyIdentity::Anonymous,
        imports: vec![],
        annotations: vec![comment(
            AnnotationValue::Anonymous(anonymous(b"here", "o")),
            vec![],
        )],
        axioms: vec![AnnotatedAxiom {
            annotations: vec![],
            axiom: Axiom::ClassAssertion(
                nested(Individual::Anonymous(anonymous(b"here", "x"))),
                Individual::Anonymous(anonymous(b"here", "x")),
            ),
        }],
    };
    assert!(scoped_ontology(&here, &ontology));
    assert!(!scoped_ontology(&b"there".to_vec(), &ontology));
}
