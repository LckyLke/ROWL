use rowl_kernel::anonymous::{axiom_positions_allowed, check_positions, class_positions_allowed};
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;

fn iri() -> Iri {
    Iri {
        spelling: b"urn:test".to_vec(),
    }
}
fn property() -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri() })
}
fn named() -> Individual {
    Individual::Named(NamedIndividual { iri: iri() })
}
fn anon() -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: b"doc".to_vec(),
        label: b"motor".to_vec(),
    })
}
fn class() -> ClassExpression {
    ClassExpression::Class(Class { iri: iri() })
}
fn bad() -> ClassExpression {
    ClassExpression::ObjectHasValue(property(), anon())
}
fn literal() -> Literal {
    Literal {
        lexical: "value".as_bytes().to_vec(),
        datatype: Datatype { iri: iri() },
    }
}
fn annotation() -> Annotation {
    Annotation {
        annotations: vec![],
        property: AnnotationProperty { iri: iri() },
        value: AnnotationValue::Anonymous(AnonymousIndividual {
            scope: b"doc".to_vec(),
            label: b"note".to_vec(),
        }),
    }
}
fn item(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![annotation()],
        axiom,
    }
}

#[test]
fn forbidden_individuals_in_nominals_and_values() {
    assert!(!class_positions_allowed(&bad()));
    assert!(!class_positions_allowed(&ClassExpression::ObjectOneOf(
        NonEmpty {
            first: named(),
            rest: vec![named(), anon()]
        }
    )));
    assert!(!class_positions_allowed(&ClassExpression::ObjectOneOf(
        NonEmpty {
            first: anon(),
            rest: vec![]
        }
    )));
    assert!(class_positions_allowed(&ClassExpression::ObjectHasValue(
        property(),
        named()
    )));
    assert!(class_positions_allowed(&ClassExpression::ObjectOneOf(
        NonEmpty {
            first: named(),
            rest: vec![named()]
        }
    )));
}

#[test]
fn recursive_class_fillers_and_all_unordered_members_are_checked() {
    let expressions = [
        ClassExpression::ObjectComplementOf(Box::new(bad())),
        ClassExpression::ObjectSomeValuesFrom(property(), Box::new(bad())),
        ClassExpression::ObjectAllValuesFrom(property(), Box::new(bad())),
        ClassExpression::ObjectMinCardinality(Natural::Zero, property(), Some(Box::new(bad()))),
        ClassExpression::ObjectMaxCardinality(Natural::Zero, property(), Some(Box::new(bad()))),
        ClassExpression::ObjectExactCardinality(Natural::Zero, property(), Some(Box::new(bad()))),
        ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
            first: class(),
            second: class(),
            rest: vec![class(), bad()],
        })),
        ClassExpression::ObjectUnionOf(Box::new(AtLeastTwo {
            first: class(),
            second: bad(),
            rest: vec![],
        })),
        ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
            first: bad(),
            second: class(),
            rest: vec![],
        })),
    ];
    for expression in expressions {
        assert!(!class_positions_allowed(&expression));
    }
    for expression in [
        ClassExpression::ObjectMinCardinality(Natural::Zero, property(), None),
        ClassExpression::ObjectMaxCardinality(Natural::Zero, property(), None),
        ClassExpression::ObjectExactCardinality(Natural::Zero, property(), None),
    ] {
        assert!(class_positions_allowed(&expression));
    }
}

#[test]
fn axioms_with_nested_classes_cannot_bypass_the_restriction() {
    let xs = || AtLeastTwo {
        first: class(),
        second: class(),
        rest: vec![bad()],
    };
    let axioms = [
        Axiom::SubClassOf(class(), bad()),
        Axiom::SubClassOf(bad(), class()),
        Axiom::EquivalentClasses(xs()),
        Axiom::DisjointClasses(xs()),
        Axiom::DisjointUnion(Class { iri: iri() }, xs()),
        Axiom::ObjectPropertyDomain(property(), bad()),
        Axiom::ObjectPropertyRange(property(), bad()),
        Axiom::DataPropertyDomain(DataProperty { iri: iri() }, bad()),
        Axiom::ClassAssertion(bad(), anon()),
        Axiom::HasKey(bad(), vec![property()], vec![]),
    ];
    for axiom in axioms {
        assert!(!axiom_positions_allowed(&axiom));
    }
}

#[test]
fn equality_difference_and_negative_assertion_positions_require_named_individuals() {
    for values in [
        AtLeastTwo {
            first: anon(),
            second: named(),
            rest: vec![],
        },
        AtLeastTwo {
            first: named(),
            second: anon(),
            rest: vec![],
        },
        AtLeastTwo {
            first: named(),
            second: named(),
            rest: vec![anon()],
        },
    ] {
        assert!(!axiom_positions_allowed(&Axiom::SameIndividual(values)));
    }
    assert!(!axiom_positions_allowed(&Axiom::DifferentIndividuals(
        AtLeastTwo {
            first: named(),
            second: named(),
            rest: vec![anon()]
        }
    )));
    assert!(!axiom_positions_allowed(
        &Axiom::NegativeObjectPropertyAssertion(property(), anon(), named())
    ));
    assert!(!axiom_positions_allowed(
        &Axiom::NegativeObjectPropertyAssertion(property(), named(), anon())
    ));
    assert!(!axiom_positions_allowed(
        &Axiom::NegativeDataPropertyAssertion(DataProperty { iri: iri() }, anon(), literal())
    ));
    assert!(axiom_positions_allowed(
        &Axiom::NegativeObjectPropertyAssertion(property(), named(), named())
    ));
}

#[test]
fn positive_assertions_and_anonymous_annotations_are_allowed_by_positions() {
    let axioms = vec![
        item(Axiom::ObjectPropertyAssertion(property(), anon(), anon())),
        item(Axiom::ClassAssertion(class(), anon())),
        item(Axiom::DataPropertyAssertion(
            DataProperty { iri: iri() },
            anon(),
            literal(),
        )),
        item(Axiom::AnnotationAssertion(
            AnnotationProperty { iri: iri() },
            AnnotationSubject::Anonymous(AnonymousIndividual {
                scope: b"doc".to_vec(),
                label: b"note".to_vec(),
            }),
            AnnotationValue::Anonymous(AnonymousIndividual {
                scope: b"doc".to_vec(),
                label: b"note2".to_vec(),
            }),
        )),
    ];
    assert!(check_positions(&axioms).is_none());
    // A positive anonymous self-edge passes positions. It still needs the
    // separate forest check before any complete DL validity claim.
}

#[test]
fn whole_closure_returns_the_first_offending_borrow_and_keeps_annotations() {
    assert!(check_positions(&vec![]).is_none());
    let axioms = vec![
        item(Axiom::ClassAssertion(class(), anon())),
        item(Axiom::ClassAssertion(bad(), named())),
        item(Axiom::NegativeObjectPropertyAssertion(
            property(),
            anon(),
            named(),
        )),
    ];
    let failure = check_positions(&axioms).expect("forbidden nested position");
    assert!(std::ptr::eq(failure, &axioms[1]));
    assert_eq!(failure.annotations.len(), 1);
}

#[test]
fn forbidden_axiom_types_check_anonymous_values_in_all_nested_annotations() {
    use rowl_kernel::anonymous::{annotated_axiom_positions_allowed, annotation_has_no_anonymous};
    let bodies = [
        Axiom::SameIndividual(AtLeastTwo {
            first: named(),
            second: named(),
            rest: vec![],
        }),
        Axiom::DifferentIndividuals(AtLeastTwo {
            first: named(),
            second: named(),
            rest: vec![],
        }),
        Axiom::NegativeObjectPropertyAssertion(property(), named(), named()),
        Axiom::NegativeDataPropertyAssertion(DataProperty { iri: iri() }, named(), literal()),
    ];
    for body in bodies {
        assert!(axiom_positions_allowed(&body));
        let nested = Annotation {
            annotations: vec![Annotation {
                annotations: vec![annotation()],
                property: AnnotationProperty { iri: iri() },
                value: AnnotationValue::Literal(literal()),
            }],
            property: AnnotationProperty { iri: iri() },
            value: AnnotationValue::Iri(iri()),
        };
        assert!(!annotation_has_no_anonymous(&nested));
        let axioms = vec![AnnotatedAxiom {
            annotations: vec![nested],
            axiom: body,
        }];
        assert!(!annotated_axiom_positions_allowed(&axioms[0]));
        assert!(std::ptr::eq(check_positions(&axioms).unwrap(), &axioms[0]));
    }
    let ordinary = AnnotatedAxiom {
        annotations: vec![annotation()],
        axiom: Axiom::ClassAssertion(class(), named()),
    };
    assert!(annotated_axiom_positions_allowed(&ordinary));
    let valid = AnnotatedAxiom {
        annotations: vec![Annotation {
            annotations: vec![],
            property: AnnotationProperty { iri: iri() },
            value: AnnotationValue::Literal(literal()),
        }],
        axiom: Axiom::NegativeObjectPropertyAssertion(property(), named(), named()),
    };
    assert!(annotated_axiom_positions_allowed(&valid));
}
