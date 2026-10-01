use rowl_kernel::arity::*;
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
use std::collections::BTreeSet;
fn iri(x: &[u8]) -> Iri {
    Iri {
        spelling: x.to_vec(),
    }
}
fn c(x: &[u8]) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(x) })
}
fn r(x: &[u8]) -> DataRange {
    DataRange::Datatype(Datatype { iri: iri(x) })
}
fn two<T>(a: T, b: T, rest: Vec<T>) -> AtLeastTwo<T> {
    AtLeastTwo {
        first: a,
        second: b,
        rest,
    }
}
fn op(k: usize) -> ObjectPropertyExpression {
    let p = ObjectProperty {
        iri: iri(if k == 2 || k == 3 {
            b"urn:q"
        } else if k == 4 {
            b"urn:r"
        } else {
            b"urn:p"
        }),
    };
    if k == 1 || k == 3 {
        ObjectPropertyExpression::Inverse(p)
    } else {
        ObjectPropertyExpression::Property(p)
    }
}
fn dp(k: usize) -> DataProperty {
    DataProperty {
        iri: iri(if k == 0 {
            b"urn:p"
        } else if k == 1 {
            b"urn:q"
        } else if k == 2 {
            b"urn:r"
        } else if k == 3 {
            b"urn:s"
        } else {
            b"urn:t"
        }),
    }
}
fn i(k: usize) -> Individual {
    match k {
        0 => Individual::Named(NamedIndividual { iri: iri(b"urn:x") }),
        3 => Individual::Named(NamedIndividual { iri: iri(b"urn:y") }),
        _ => Individual::Anonymous(AnonymousIndividual {
            scope: if k == 1 {
                b"doc1".to_vec()
            } else if k == 2 {
                b"doc2".to_vec()
            } else {
                b"doc3".to_vec()
            },
            label: b"x".to_vec(),
        }),
    }
}
fn ax(body: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom: body,
    }
}
fn bad_class() -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(two(c(b"urn:A"), c(b"urn:A"), vec![])))
}
fn bad_range() -> DataRange {
    DataRange::Union(Box::new(two(r(b"urn:dt"), r(b"urn:dt"), vec![])))
}
fn intersection(a: &[u8], b: &[u8]) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(two(c(a), c(b), vec![])))
}
#[test]
fn ordinary_associations_count_distinct_members_while_retaining_raw_repetitions() {
    assert!(!has_two_classes(&two(c(b"urn:A"), c(b"urn:A"), vec![])));
    assert!(has_two_classes(&two(
        c(b"urn:A"),
        c(b"urn:A"),
        vec![c(b"urn:B"), c(b"urn:A")]
    )));
    assert!(!has_two_ranges(&two(
        r(b"urn:d"),
        r(b"urn:d"),
        vec![r(b"urn:d")]
    )));
    assert!(has_two_ranges(&two(
        r(b"urn:d"),
        r(b"urn:d"),
        vec![r(b"urn:e")]
    )));
    assert!(!has_two_classes(&two(
        intersection(b"urn:A", b"urn:B"),
        intersection(b"urn:B", b"urn:A"),
        vec![]
    )));
    assert!(class_allowed(&ClassExpression::ObjectUnionOf(Box::new(
        two(c(b"urn:A"), c(b"urn:A"), vec![c(b"urn:B")])
    ))));
    assert!(!class_allowed(&bad_class()));
    assert!(!range_allowed(&bad_range()));
}
#[test]
fn structural_duplicates_include_nested_set_reordering_and_default_qualifiers() {
    assert!(!unique_classes(&two(
        intersection(b"urn:A", b"urn:B"),
        intersection(b"urn:B", b"urn:A"),
        vec![]
    )));
    let default = || ClassExpression::ObjectMinCardinality(Natural::Zero, op(0), None);
    let explicit = || {
        ClassExpression::ObjectMinCardinality(
            Natural::Zero,
            op(0),
            Some(Box::new(c(b"http://www.w3.org/2002/07/owl#Thing"))),
        )
    };
    assert!(!has_two_classes(&two(default(), explicit(), vec![])));
    assert!(!unique_classes(&two(
        default(),
        c(b"urn:A"),
        vec![explicit()]
    )));
    assert!(unique_classes(&two(
        c(b"urn:A"),
        ClassExpression::ObjectComplementOf(Box::new(ClassExpression::ObjectComplementOf(
            Box::new(c(b"urn:A"))
        ))),
        vec![]
    )));
}
#[test]
fn all_five_disjointness_and_difference_forms_reject_duplicate_occurrences() {
    let bad = vec![
        ax(Axiom::DisjointClasses(two(
            c(b"urn:A"),
            c(b"urn:B"),
            vec![c(b"urn:A")],
        ))),
        ax(Axiom::DisjointUnion(
            Class {
                iri: iri(b"urn:Sum"),
            },
            two(c(b"urn:A"), c(b"urn:B"), vec![c(b"urn:A")]),
        )),
        ax(Axiom::DisjointObjectProperties(two(
            op(0),
            op(1),
            vec![op(0)],
        ))),
        ax(Axiom::DisjointDataProperties(two(
            dp(0),
            dp(1),
            vec![dp(0)],
        ))),
        ax(Axiom::DifferentIndividuals(two(i(0), i(1), vec![i(0)]))),
    ];
    for x in &bad {
        assert!(!axiom_allowed(x));
    }
    let good = vec![
        ax(Axiom::DisjointClasses(two(
            c(b"urn:A"),
            c(b"urn:B"),
            vec![c(b"urn:C")],
        ))),
        // The defined class is outside the disjoint member association.
        ax(Axiom::DisjointUnion(
            Class { iri: iri(b"urn:A") },
            two(c(b"urn:A"), c(b"urn:B"), vec![]),
        )),
        ax(Axiom::DisjointObjectProperties(two(
            op(0),
            op(1),
            vec![op(2)],
        ))),
        ax(Axiom::DisjointDataProperties(two(
            dp(0),
            dp(1),
            vec![dp(2)],
        ))),
        ax(Axiom::DifferentIndividuals(two(i(0), i(1), vec![i(2)]))),
    ];
    for x in &good {
        assert!(axiom_allowed(x));
    }
}
#[test]
fn equivalence_and_sameness_allow_repetitions_only_with_two_distinct_members() {
    let good = vec![
        ax(Axiom::EquivalentClasses(two(
            c(b"urn:A"),
            c(b"urn:A"),
            vec![c(b"urn:B")],
        ))),
        ax(Axiom::EquivalentObjectProperties(two(
            op(0),
            op(0),
            vec![op(1)],
        ))),
        ax(Axiom::EquivalentDataProperties(two(
            dp(0),
            dp(0),
            vec![dp(1)],
        ))),
        ax(Axiom::SameIndividual(two(i(0), i(0), vec![i(1)]))),
    ];
    let bad = vec![
        ax(Axiom::EquivalentClasses(two(
            c(b"urn:A"),
            c(b"urn:A"),
            vec![],
        ))),
        ax(Axiom::EquivalentObjectProperties(two(op(0), op(0), vec![]))),
        ax(Axiom::EquivalentDataProperties(two(dp(0), dp(0), vec![]))),
        ax(Axiom::SameIndividual(two(i(0), i(0), vec![]))),
    ];
    for x in &good {
        assert!(axiom_allowed(x));
    }
    for x in &bad {
        assert!(!axiom_allowed(x));
    }
}
#[test]
fn all_nested_class_and_data_fillers_are_checked() {
    let bad = vec![
        bad_class(),
        ClassExpression::ObjectUnionOf(Box::new(two(c(b"urn:A"), c(b"urn:B"), vec![bad_class()]))),
        ClassExpression::ObjectComplementOf(Box::new(bad_class())),
        ClassExpression::ObjectSomeValuesFrom(op(0), Box::new(bad_class())),
        ClassExpression::ObjectAllValuesFrom(op(0), Box::new(bad_class())),
        ClassExpression::ObjectMinCardinality(Natural::Zero, op(0), Some(Box::new(bad_class()))),
        ClassExpression::ObjectMaxCardinality(Natural::Zero, op(0), Some(Box::new(bad_class()))),
        ClassExpression::ObjectExactCardinality(Natural::Zero, op(0), Some(Box::new(bad_class()))),
        ClassExpression::DataSomeValuesFrom(dp(0), bad_range()),
        ClassExpression::DataAllValuesFrom(dp(0), bad_range()),
        ClassExpression::DataMinCardinality(Natural::Zero, dp(0), Some(bad_range())),
        ClassExpression::DataMaxCardinality(Natural::Zero, dp(0), Some(bad_range())),
        ClassExpression::DataExactCardinality(Natural::Zero, dp(0), Some(bad_range())),
    ];
    for x in &bad {
        assert!(!class_allowed(x));
    }
    let literal = || Literal {
        lexical: b"unchecked lexical bytes".to_vec(),
        datatype: Datatype {
            iri: iri(b"urn:unchecked"),
        },
    };
    let good = vec![
        c(b"urn:A"),
        ClassExpression::ObjectOneOf(NonEmpty {
            first: i(0),
            rest: vec![i(0)],
        }),
        ClassExpression::ObjectHasValue(op(0), i(0)),
        ClassExpression::ObjectHasSelf(op(0)),
        ClassExpression::DataHasValue(dp(0), literal()),
        ClassExpression::ObjectMinCardinality(Natural::Zero, op(0), None),
        ClassExpression::DataMaxCardinality(Natural::Zero, dp(0), None),
    ];
    for x in &good {
        assert!(class_allowed(x));
    }
    assert!(!range_allowed(&DataRange::Complement(
        Box::new(bad_range())
    )));
    assert!(!range_allowed(&DataRange::Intersection(Box::new(two(
        r(b"urn:A"),
        r(b"urn:B"),
        vec![bad_range()]
    )))));
    assert!(range_allowed(&r(b"urn:unchecked")));
    assert!(range_allowed(&DataRange::OneOf(NonEmpty {
        first: literal(),
        rest: vec![]
    })));
    assert!(range_allowed(&DataRange::Restriction(
        Datatype { iri: iri(b"urn:d") },
        NonEmpty {
            first: FacetRestriction {
                facet: iri(b"urn:facet"),
                value: literal()
            },
            rest: vec![]
        }
    )));
}
#[test]
fn nested_axiom_positions_keys_and_ordered_chains_have_their_exact_rules() {
    let bad = vec![
        ax(Axiom::SubClassOf(c(b"urn:A"), bad_class())),
        ax(Axiom::ObjectPropertyDomain(op(0), bad_class())),
        ax(Axiom::ObjectPropertyRange(op(0), bad_class())),
        ax(Axiom::DataPropertyDomain(dp(0), bad_class())),
        ax(Axiom::DataPropertyRange(dp(0), bad_range())),
        ax(Axiom::DatatypeDefinition(
            Datatype { iri: iri(b"urn:d") },
            bad_range(),
        )),
        ax(Axiom::ClassAssertion(bad_class(), i(0))),
        ax(Axiom::HasKey(bad_class(), vec![op(0)], vec![])),
        ax(Axiom::HasKey(c(b"urn:A"), vec![], vec![])),
    ];
    for x in &bad {
        assert!(!axiom_allowed(x));
    }
    assert!(axiom_allowed(&ax(Axiom::HasKey(
        c(b"urn:A"),
        vec![op(0), op(0)],
        vec![]
    ))));
    assert!(axiom_allowed(&ax(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(two(op(0), op(0), vec![])),
        op(0)
    ))));
    assert!(axiom_allowed(&ax(Axiom::InverseObjectProperties(
        op(0),
        op(0)
    ))));
}
#[test]
fn original_first_annotated_failure_and_scoped_individual_identity_are_preserved() {
    let mut failure = ax(Axiom::DisjointClasses(two(
        c(b"urn:A"),
        c(b"urn:A"),
        vec![],
    )));
    failure.annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"urn:note"),
        },
        value: AnnotationValue::Iri(iri(b"urn:source")),
    });
    let values = vec![
        ax(Axiom::SameIndividual(two(i(0), i(1), vec![]))),
        failure,
        ax(Axiom::SubClassOf(c(b"urn:A"), bad_class())),
    ];
    let found = check_arities(&values).unwrap();
    assert!(std::ptr::eq(found, &values[1]));
    assert_eq!(found.annotations.len(), 1);
    assert!(unique_individuals(&two(i(1), i(2), vec![])));
    assert!(!unique_individuals(&two(i(1), i(1), vec![])));
    assert!(check_arities(&vec![]).is_none());
}
#[test]
fn atomic_association_counts_and_pairwise_checks_match_independent_set_oracles() {
    for size in [2_u32, 3, 4, 5] {
        for code in 0usize..3usize.pow(size) {
            let mut remaining = code;
            let mut tags = vec![];
            for _ in 0..size {
                tags.push(remaining % 3);
                remaining /= 3;
            }
            let count = tags.iter().copied().collect::<BTreeSet<_>>().len();
            let ps = two(
                op(tags[0]),
                op(tags[1]),
                tags[2..].iter().map(|k| op(*k)).collect(),
            );
            let ds = two(
                dp(tags[0]),
                dp(tags[1]),
                tags[2..].iter().map(|k| dp(*k)).collect(),
            );
            let is = two(
                i(tags[0]),
                i(tags[1]),
                tags[2..].iter().map(|k| i(*k)).collect(),
            );
            assert_eq!(has_two_properties(&ps), count >= 2);
            assert_eq!(has_two_data_properties(&ds), count >= 2);
            assert_eq!(has_two_individuals(&is), count >= 2);
            assert_eq!(unique_properties(&ps), count == tags.len());
            assert_eq!(unique_data_properties(&ds), count == tags.len());
            assert_eq!(unique_individuals(&is), count == tags.len());
        }
    }
    assert!(unique_properties(&two(
        op(0),
        op(1),
        vec![op(2), op(3), op(4)]
    )));
    assert!(unique_data_properties(&two(
        dp(0),
        dp(1),
        vec![dp(2), dp(3), dp(4)]
    )));
    assert!(unique_individuals(&two(i(0), i(1), vec![i(2), i(3), i(4)])));
    assert!(unique_classes(&two(
        c(b"urn:A"),
        c(b"urn:B"),
        vec![c(b"urn:C"), c(b"urn:D"), c(b"urn:E")]
    )));
    assert!(!same_data_property(&dp(0), &dp(1)));
    assert!(same_data_property(&dp(2), &dp(2)));
}
