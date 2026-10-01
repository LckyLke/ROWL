use rowl_kernel::anonymous_restrictions::{check_anonymous, AnonymousCheck};
use rowl_kernel::model::*;
fn iri(text: &[u8]) -> Iri {
    Iri {
        spelling: text.to_vec(),
    }
}
fn anon(label: &[u8]) -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: b"doc".to_vec(),
        label: label.to_vec(),
    })
}
fn named(text: &[u8]) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(text) })
}
fn assertion(property: &[u8], a: Individual, b: Individual) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::ObjectPropertyAssertion(
            ObjectPropertyExpression::Property(ObjectProperty { iri: iri(property) }),
            a,
            b,
        ),
    }
}
fn edge(a: &[u8], b: &[u8]) -> AnnotatedAxiom {
    assertion(b"urn:p", anon(a), anon(b))
}
fn attachment(a: &[u8], b: &[u8]) -> AnnotatedAxiom {
    assertion(b"urn:p", anon(a), named(b))
}
#[test]
fn accepts_valid_tree_and_equivalent_assertion_copies() {
    assert!(matches!(check_anonymous(&vec![]), AnonymousCheck::Allowed));
    let axioms = vec![
        edge(b"a", b"b"),
        edge(b"a", b"b"),
        attachment(b"a", b"urn:pump"),
        attachment(b"a", b"urn:motor"),
    ];
    assert!(matches!(check_anonymous(&axioms), AnonymousCheck::Allowed)); // b supplies the root
}
#[test]
fn forbidden_positions_precede_graph_failures() {
    let axioms = vec![
        edge(b"a", b"a"),
        AnnotatedAxiom {
            annotations: vec![],
            axiom: Axiom::NegativeObjectPropertyAssertion(
                ObjectPropertyExpression::Property(ObjectProperty { iri: iri(b"urn:p") }),
                anon(b"x"),
                named(b"urn:pump"),
            ),
        },
    ];
    let AnonymousCheck::ForbiddenPosition(item) = check_anonymous(&axioms) else {
        panic!("expected position error")
    };
    assert!(std::ptr::eq(item, &axioms[1]));
}
#[test]
fn self_loops_and_cycles_precede_multiplicity_and_boundary() {
    assert!(matches!(
        check_anonymous(&vec![edge(b"a", b"a"), edge(b"a", b"a")]),
        AnonymousCheck::SelfLoop(_)
    ));
    let axioms = vec![
        edge(b"a", b"b"),
        edge(b"b", b"c"),
        edge(b"c", b"a"),
        assertion(b"urn:q", anon(b"a"), anon(b"b")),
        attachment(b"a", b"urn:pump"),
        attachment(b"a", b"urn:motor"),
    ];
    assert!(matches!(
        check_anonymous(&axioms),
        AnonymousCheck::Cycle { .. }
    ));
}
#[test]
fn multiplicity_precedes_named_boundary_failures() {
    let axioms = vec![
        edge(b"a", b"b"),
        assertion(b"urn:q", anon(b"a"), anon(b"b")),
        attachment(b"a", b"urn:pump"),
        attachment(b"a", b"urn:motor"),
        attachment(b"b", b"urn:pump"),
        attachment(b"b", b"urn:motor"),
    ];
    let AnonymousCheck::MultipleAssertions { first, second } = check_anonymous(&axioms) else {
        panic!("expected multiplicity")
    };
    assert!(std::ptr::eq(first, &axioms[0]));
    assert!(std::ptr::eq(second, &axioms[1]));
}
#[test]
fn named_boundary_checks_the_whole_component() {
    let axioms = vec![
        edge(b"a", b"b"),
        attachment(b"a", b"urn:pump"),
        attachment(b"a", b"urn:motor"),
        attachment(b"b", b"urn:pump"),
        attachment(b"b", b"urn:motor"),
    ];
    assert!(matches!(
        check_anonymous(&axioms),
        AnonymousCheck::NoBoundaryRoot(_)
    ));
}
