use rowl_kernel::axiom_equality::*;
use rowl_kernel::model::*;
use std::collections::BTreeSet;
#[path = "support/axiom_fixtures.rs"]
mod axiom_fixtures;
use axiom_fixtures::*;

#[test]
fn all_37_constructors_cross_checked_with_distinct_and_reordered_fixtures() {
    let samples: Vec<_> = (0..37)
        .flat_map(|tag| (0..3).map(move |v| (tag, v, annotated(tag, v))))
        .collect();
    for (t, v, a) in &samples {
        for (u, w, b) in &samples {
            // Expected equivalence classes are specified by fixture identity, not
            // by calling a component comparator or inspecting implementation output.
            let expected = t == u && (*v == 2) == (*w == 2);
            assert_eq!(
                same_body(&a.axiom, &b.axiom),
                expected,
                "body {t}/{v} vs {u}/{w}"
            );
            assert_eq!(same_axiom(a, b), expected, "axiom {t}/{v} vs {u}/{w}");
        }
    }
}
#[test]
fn unordered_sets_and_ordered_chains_have_independent_collection_oracles() {
    let sequences: Vec<Vec<usize>> = (2..=5)
        .flat_map(|length| {
            (0..3usize.pow(length)).map(move |mut code| {
                (0..length)
                    .map(|_| {
                        let n = code % 3;
                        code /= 3;
                        n
                    })
                    .collect()
            })
        })
        .collect();
    for xs in &sequences {
        let set: BTreeSet<_> = xs.iter().copied().collect();
        let mut ys = xs.clone();
        ys.reverse();
        ys.push(xs[0]);
        let association = |items: &[usize]| {
            two(
                op(items[0]),
                op(items[1]),
                items[2..].iter().map(|n| op(*n)).collect(),
            )
        };
        let data_association = |items: &[usize]| {
            two(
                dp(items[0]),
                dp(items[1]),
                items[2..].iter().map(|n| dp(*n)).collect(),
            )
        };
        let individual_association = |items: &[usize]| {
            two(
                named(items[0]),
                named(items[1]),
                items[2..].iter().map(|n| named(*n)).collect(),
            )
        };
        assert_eq!(
            same_properties_association(&association(xs), &association(&ys)),
            set == ys.iter().copied().collect()
        );
        assert_eq!(
            same_data_properties_association(&data_association(xs), &data_association(&ys)),
            set == ys.iter().copied().collect()
        );
        assert_eq!(
            same_individuals_association(&individual_association(xs), &individual_association(&ys)),
            set == ys.iter().copied().collect()
        );
        assert_eq!(same_chain(&association(xs), &association(&ys)), *xs == ys);
        ys.pop();
        assert_eq!(same_chain(&association(xs), &association(&ys)), *xs == ys);
        ys[0] = 3;
        assert!(!same_properties_association(
            &association(xs),
            &association(&ys)
        ));
        assert!(!same_data_properties_association(
            &data_association(xs),
            &data_association(&ys)
        ));
        assert!(!same_individuals_association(
            &individual_association(xs),
            &individual_association(&ys)
        ));
    }
    assert!(same_properties_set(&vec![], &vec![]));
    assert!(same_data_properties_set(&vec![], &vec![]));
    assert!(!same_properties_set(&vec![], &vec![op(0)]));
    assert!(!same_data_properties_set(&vec![], &vec![dp(0)]));
}
#[test]
fn fixed_association_positions_constructor_kinds_and_inverse_orientation_remain_significant() {
    assert!(!same_body(
        &Axiom::InverseObjectProperties(op(0), op(1)),
        &Axiom::InverseObjectProperties(op(1), op(0))
    ));
    assert!(!same_body(
        &Axiom::SubClassOf(atom(0), atom(1)),
        &Axiom::SubClassOf(atom(1), atom(0))
    ));
    assert!(!same_body(
        &Axiom::SubDataPropertyOf(dp(0), dp(1)),
        &Axiom::SubDataPropertyOf(dp(1), dp(0))
    ));
    assert!(!same_body(
        &Axiom::ObjectPropertyAssertion(op(0), named(0), named(1)),
        &Axiom::ObjectPropertyAssertion(op(0), named(1), named(0))
    ));
    assert!(!same_sub_property(
        &SubObjectPropertyExpression::Single(op(0)),
        &SubObjectPropertyExpression::Chain(two(op(0), op(0), vec![]))
    ));
    let entities = [
        Entity::Class(Class { iri: iri(0) }),
        Entity::Datatype(Datatype { iri: iri(0) }),
        Entity::ObjectProperty(ObjectProperty { iri: iri(0) }),
        Entity::DataProperty(dp(0)),
        Entity::AnnotationProperty(ap(0)),
        Entity::NamedIndividual(NamedIndividual { iri: iri(0) }),
    ];
    for (i, a) in entities.iter().enumerate() {
        for (j, b) in entities.iter().enumerate() {
            assert_eq!(same_entity(a, b), i == j);
        }
    }
}
#[test]
fn nested_metadata_scoped_blanks_and_literal_spelling_are_preserved() {
    let mut a = annotated(29, 0);
    let mut b = annotated(29, 1);
    assert!(same_axiom(&a, &b));
    b.annotations.clear();
    assert!(!same_axiom(&a, &b));
    a.annotations = vec![annotation(0, true)];
    b.annotations = vec![annotation(0, false), annotation(9, false)];
    assert!(!same_axiom(&a, &b));
    let blank = |scope| AnonymousIndividual {
        scope: vec![scope],
        label: b"x".to_vec(),
    };
    assert!(same_subject(
        &AnnotationSubject::Anonymous(blank(0)),
        &AnnotationSubject::Anonymous(blank(0))
    ));
    assert!(!same_subject(
        &AnnotationSubject::Anonymous(blank(0)),
        &AnnotationSubject::Anonymous(blank(1))
    ));
    assert!(!same_subject(
        &AnnotationSubject::Iri(iri(0)),
        &AnnotationSubject::Anonymous(blank(0))
    ));
    let assertion = |text: &[u8]| {
        Axiom::DataPropertyAssertion(
            dp(0),
            named(0),
            Literal {
                lexical: text.to_vec(),
                datatype: Datatype { iri: iri(40) },
            },
        )
    };
    assert!(!same_body(&assertion(b"01"), &assertion(b"1")));
}
#[test]
fn key_associations_are_separate_sets_and_disjoint_input_still_requires_arity_validation() {
    let a = Axiom::HasKey(atom(0), vec![op(0), op(1), op(0)], vec![dp(0), dp(1)]);
    let b = Axiom::HasKey(atom(0), vec![op(1), op(0)], vec![dp(1), dp(0), dp(1)]);
    assert!(same_body(&a, &b));
    assert!(!same_body(
        &a,
        &Axiom::HasKey(atom(0), vec![op(0)], vec![dp(0), dp(1)])
    ));
    let a = AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::DisjointClasses(two(atom(0), atom(1), vec![atom(0)])),
    };
    let b = AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::DisjointClasses(two(atom(1), atom(0), vec![])),
    };
    assert!(same_axiom(&a, &b));
    assert!(!rowl_kernel::arity::axiom_allowed(&a));
    assert!(rowl_kernel::arity::axiom_allowed(&b));
}
#[test]
fn complete_comparison_agrees_with_existing_restriction_comparators() {
    for v in 0..3 {
        for w in 0..3 {
            let a = annotated(29, v);
            let b = annotated(29, w);
            assert_eq!(
                same_axiom(&a, &b),
                rowl_kernel::assertion_equality::same_object_assertion(&a, &b)
            );
            let a = annotated(24, v);
            let b = annotated(24, w);
            assert_eq!(
                same_axiom(&a, &b),
                rowl_kernel::range_equality::same_definition(&a, &b)
            );
        }
    }
}

#[test]
fn all_five_duplicate_sensitive_axiom_families_require_original_arity_checks() {
    // Variant 1 reorders and repeats members. Structural set comparison accepts
    // each pair; OWL occurrence disjointness/difference requires rejecting the
    // repeated original input before any future canonicalization.
    for tag in [3, 4, 7, 20, 27] {
        let original = annotated(tag, 1);
        let distinct = annotated(tag, 0);
        assert!(same_axiom(&original, &distinct), "constructor {tag}");
        assert!(same_axiom(&distinct, &original), "constructor {tag}");
        assert!(!rowl_kernel::arity::axiom_allowed(&original));
        assert!(rowl_kernel::arity::axiom_allowed(&distinct));
    }
}
