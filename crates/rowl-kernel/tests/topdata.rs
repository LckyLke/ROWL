use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
use rowl_kernel::topdata::{axiom_allowed, check_axioms};

const TOP: &str = "http://www.w3.org/2002/07/owl#topDataProperty";
fn iri(value: &str) -> Iri {
    Iri {
        spelling: value.as_bytes().to_vec(),
    }
}
fn data(value: &str) -> DataProperty {
    DataProperty { iri: iri(value) }
}
fn top() -> DataProperty {
    data(TOP)
}
fn class() -> ClassExpression {
    ClassExpression::Class(Class {
        iri: iri("urn:Machine"),
    })
}
fn individual() -> Individual {
    Individual::Named(NamedIndividual {
        iri: iri("urn:Machine-7"),
    })
}
fn literal() -> Literal {
    Literal {
        lexical: "fault".as_bytes().to_vec(),
        datatype: Datatype {
            iri: iri("http://www.w3.org/2001/XMLSchema#string"),
        },
    }
}
fn range() -> DataRange {
    DataRange::Datatype(Datatype {
        iri: iri("http://www.w3.org/2001/XMLSchema#string"),
    })
}
fn item(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![Annotation {
            annotations: vec![],
            property: AnnotationProperty {
                iri: iri("urn:reference"),
            },
            value: AnnotationValue::Iri(iri(TOP)),
        }],
        axiom,
    }
}

#[test]
fn only_superproperty_use_is_allowed_and_identity_is_exact() {
    assert!(axiom_allowed(&item(Axiom::SubDataPropertyOf(
        data("urn:fault"),
        top()
    ))));
    assert!(axiom_allowed(&item(Axiom::SubDataPropertyOf(
        data("urn:fault"),
        data("urn:record")
    ))));
    assert!(!axiom_allowed(&item(Axiom::SubDataPropertyOf(
        top(),
        data("urn:record")
    ))));
    assert!(!axiom_allowed(&item(Axiom::SubDataPropertyOf(
        top(),
        top()
    ))));
    assert!(!axiom_allowed(&item(Axiom::Declaration(
        Entity::DataProperty(top())
    ))));
    assert!(axiom_allowed(&item(Axiom::FunctionalDataProperty(data(
        "http://www.w3.org/2002/07/owl#topDataPropertyExtra"
    )))));
    assert!(axiom_allowed(&item(Axiom::FunctionalDataProperty(data(
        "http://www.w3.org/2002/07/owl#TopDataProperty"
    )))));
    // An annotation reference has the same bytes but is not a data property.
    assert!(axiom_allowed(&item(Axiom::ClassAssertion(
        class(),
        individual()
    ))));
}

#[test]
fn nested_restrictions_keys_and_assertions_cannot_hide_top() {
    for expression in [
        ClassExpression::DataSomeValuesFrom(top(), range()),
        ClassExpression::DataAllValuesFrom(top(), range()),
        ClassExpression::DataHasValue(top(), literal()),
        ClassExpression::DataMinCardinality(Natural::Zero, top(), None),
        ClassExpression::DataMaxCardinality(Natural::Zero, top(), Some(range())),
        ClassExpression::DataExactCardinality(Natural::Zero, top(), None),
    ] {
        let nested = ClassExpression::ObjectUnionOf(Box::new(AtLeastTwo {
            first: class(),
            second: class(),
            rest: vec![ClassExpression::ObjectComplementOf(Box::new(expression))],
        }));
        assert!(!axiom_allowed(&item(Axiom::SubClassOf(class(), nested))));
    }
    for axiom in [
        Axiom::HasKey(class(), vec![], vec![data("urn:serial"), top()]),
        Axiom::DataPropertyDomain(top(), class()),
        Axiom::DataPropertyRange(top(), range()),
        Axiom::FunctionalDataProperty(top()),
        Axiom::DataPropertyAssertion(top(), individual(), literal()),
        Axiom::NegativeDataPropertyAssertion(top(), individual(), literal()),
        Axiom::EquivalentDataProperties(AtLeastTwo {
            first: data("urn:serial"),
            second: data("urn:other"),
            rest: vec![top()],
        }),
        Axiom::DisjointDataProperties(AtLeastTwo {
            first: data("urn:serial"),
            second: top(),
            rest: vec![],
        }),
    ] {
        assert!(!axiom_allowed(&item(axiom)));
    }
}

#[test]
fn complete_closure_scan_returns_the_original_first_violation() {
    let axioms = vec![
        item(Axiom::SubDataPropertyOf(data("urn:fault"), top())),
        item(Axiom::FunctionalDataProperty(top())),
        item(Axiom::DataPropertyRange(top(), range())),
    ];
    assert!(std::ptr::eq(check_axioms(&axioms).unwrap(), &axioms[1]));
    assert!(check_axioms(&vec![]).is_none());
    assert!(check_axioms(&vec![item(Axiom::SubDataPropertyOf(
        data("urn:fault"),
        top()
    ))])
    .is_none());
}
