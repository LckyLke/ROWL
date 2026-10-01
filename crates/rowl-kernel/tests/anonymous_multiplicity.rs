use rowl_kernel::anonymous_graph::{check_forest, ForestCheck};
use rowl_kernel::anonymous_multiplicity::{check_multiplicity, same_pair, MultiplicityCheck};
use rowl_kernel::model::*;
fn iri(name: &[u8]) -> Iri {
    Iri {
        spelling: name.to_vec(),
    }
}
fn individual(scope: &[u8], label: &[u8]) -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: scope.to_vec(),
        label: label.to_vec(),
    })
}
fn annotation(text: &[u8]) -> Annotation {
    Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"urn:note"),
        },
        value: AnnotationValue::Literal(Literal {
            lexical: text.to_vec(),
            datatype: Datatype {
                iri: iri(b"urn:string"),
            },
        }),
    }
}
fn assertion(
    property: &[u8],
    inverse: bool,
    a: Individual,
    b: Individual,
    annotations: Vec<Annotation>,
) -> AnnotatedAxiom {
    let property = ObjectProperty { iri: iri(property) };
    AnnotatedAxiom {
        annotations,
        axiom: Axiom::ObjectPropertyAssertion(
            if inverse {
                ObjectPropertyExpression::Inverse(property)
            } else {
                ObjectPropertyExpression::Property(property)
            },
            a,
            b,
        ),
    }
}
fn edge(a: &[u8], b: &[u8], notes: Vec<Annotation>) -> AnnotatedAxiom {
    assertion(
        b"urn:p",
        false,
        individual(b"doc", a),
        individual(b"doc", b),
        notes,
    )
}
#[test]
fn equivalent_occurrences_are_a_single_structural_axiom_member() {
    let axioms = vec![
        edge(b"a", b"b", vec![annotation(b"x"), annotation(b"y")]),
        edge(
            b"a",
            b"b",
            vec![annotation(b"y"), annotation(b"x"), annotation(b"x")],
        ),
    ];
    assert!(matches!(
        check_multiplicity(&axioms),
        MultiplicityCheck::Allowed
    ));
    assert!(matches!(
        check_multiplicity(&vec![]),
        MultiplicityCheck::Allowed
    ));
}
#[test]
fn different_properties_inverse_forms_and_orientations_are_distinct_assertions() {
    for second in [
        assertion(
            b"urn:q",
            false,
            individual(b"doc", b"a"),
            individual(b"doc", b"b"),
            vec![],
        ),
        assertion(
            b"urn:p",
            true,
            individual(b"doc", b"a"),
            individual(b"doc", b"b"),
            vec![],
        ),
        edge(b"b", b"a", vec![]),
    ] {
        let axioms = vec![edge(b"a", b"b", vec![]), second];
        assert!(same_pair(&axioms[0], &axioms[1]));
        assert!(matches!(check_forest(&axioms), ForestCheck::Forest));
        assert!(matches!(
            check_multiplicity(&axioms),
            MultiplicityCheck::MultipleAssertions { .. }
        ));
    }
}
#[test]
fn logically_equivalent_inverse_assertions_remain_distinct_structural_axioms() {
    let axioms = vec![
        edge(b"a", b"b", vec![]),
        assertion(
            b"urn:p",
            true,
            individual(b"doc", b"b"),
            individual(b"doc", b"a"),
            vec![],
        ),
    ];
    assert!(same_pair(&axioms[0], &axioms[1]));
    assert!(matches!(
        check_multiplicity(&axioms),
        MultiplicityCheck::MultipleAssertions { .. }
    ));
    // Validation must precede inverse-assertion lowering; logical equivalence
    // is weaker than the required structural axiom-set comparison.
}

#[test]
fn different_annotations_count_as_distinct_axioms_and_report_original_borrows() {
    let axioms = vec![
        edge(b"unused", b"other", vec![]),
        edge(b"a", b"b", vec![annotation(b"reviewed")]),
        edge(b"a", b"b", vec![annotation(b"draft")]),
    ];
    let MultiplicityCheck::MultipleAssertions { first, second } = check_multiplicity(&axioms)
    else {
        panic!("distinct annotations")
    };
    assert!(std::ptr::eq(first, &axioms[1]));
    assert!(std::ptr::eq(second, &axioms[2]));
    assert_eq!(first.annotations.len(), 1);
    assert_eq!(second.annotations.len(), 1);
}
#[test]
fn assertion_sets_preserve_lexical_literal_identity() {
    let axioms = vec![
        edge(b"a", b"b", vec![annotation(b"01")]),
        edge(b"a", b"b", vec![annotation(b"1")]),
    ];
    assert!(matches!(
        check_multiplicity(&axioms),
        MultiplicityCheck::MultipleAssertions { .. }
    ));
}
#[test]
fn scopes_and_named_endpoints_do_not_create_false_anonymous_pairs() {
    let axioms = vec![
        edge(b"a", b"b", vec![]),
        assertion(
            b"urn:q",
            false,
            individual(b"other", b"a"),
            individual(b"other", b"b"),
            vec![],
        ),
        assertion(
            b"urn:q",
            false,
            individual(b"doc", b"a"),
            Individual::Named(NamedIndividual { iri: iri(b"b") }),
            vec![],
        ),
    ];
    assert!(!same_pair(&axioms[0], &axioms[1]));
    assert!(!same_pair(&axioms[0], &axioms[2]));
    assert!(matches!(
        check_multiplicity(&axioms),
        MultiplicityCheck::Allowed
    ));
}
#[test]
fn self_pairs_and_forests_are_independent_restrictions() {
    let axioms = vec![edge(b"a", b"a", vec![]), edge(b"a", b"a", vec![])];
    assert!(matches!(
        check_multiplicity(&axioms),
        MultiplicityCheck::Allowed
    ));
    assert!(matches!(check_forest(&axioms), ForestCheck::SelfLoop(_)));
    let triangle = vec![
        edge(b"a", b"b", vec![]),
        edge(b"b", b"c", vec![]),
        edge(b"c", b"a", vec![]),
    ];
    assert!(matches!(
        check_multiplicity(&triangle),
        MultiplicityCheck::Allowed
    ));
    assert!(matches!(check_forest(&triangle), ForestCheck::Cycle { .. }));
}
