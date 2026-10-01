use rowl_kernel::anonymous_boundary::{
    at_most_one, check_boundary, first_candidate, second_candidate, touches_named, BoundaryCheck,
};
use rowl_kernel::anonymous_graph::{check_forest, ForestCheck};
use rowl_kernel::model::*;
fn iri(text: &[u8]) -> Iri {
    Iri {
        spelling: text.to_vec(),
    }
}
fn anon(scope: &[u8], label: &[u8]) -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: scope.to_vec(),
        label: label.to_vec(),
    })
}
fn named(text: &[u8]) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(text) })
}
fn note(text: &[u8]) -> Annotation {
    Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"urn:note"),
        },
        value: AnnotationValue::Iri(iri(text)),
    }
}
fn assertion(
    property: &[u8],
    source: Individual,
    target: Individual,
    annotations: Vec<Annotation>,
) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations,
        axiom: Axiom::ObjectPropertyAssertion(
            ObjectPropertyExpression::Property(ObjectProperty { iri: iri(property) }),
            source,
            target,
        ),
    }
}
fn edge(a: &[u8], b: &[u8]) -> AnnotatedAxiom {
    assertion(b"urn:p", anon(b"doc", a), anon(b"doc", b), vec![])
}
fn attachment(a: &[u8], b: &[u8]) -> AnnotatedAxiom {
    assertion(b"urn:p", anon(b"doc", a), named(b), vec![])
}
fn allowed(axioms: &Vec<AnnotatedAxiom>) -> bool {
    matches!(check_boundary(axioms), BoundaryCheck::Allowed)
}
#[test]
fn empty_and_other_isolated_occurrences_qualify() {
    assert!(allowed(&vec![]));
    let axioms = vec![AnnotatedAxiom {
        annotations: vec![Annotation {
            annotations: vec![],
            property: AnnotationProperty {
                iri: iri(b"urn:note"),
            },
            value: AnnotationValue::Anonymous(AnonymousIndividual {
                scope: b"doc".to_vec(),
                label: b"annotation".to_vec(),
            }),
        }],
        axiom: Axiom::ClassAssertion(
            ClassExpression::Class(Class {
                iri: iri(b"urn:Part"),
            }),
            anon(b"doc", b"part"),
        ),
    }];
    assert!(allowed(&axioms));
    assert!(first_candidate(&axioms[0]).is_none());
    assert!(second_candidate(&axioms[0]).is_none());
}
#[test]
fn one_named_assertion_and_structural_copies_count_once() {
    let axioms = vec![
        assertion(
            b"urn:p",
            anon(b"doc", b"a"),
            named(b"urn:pump"),
            vec![note(b"x"), note(b"y")],
        ),
        assertion(
            b"urn:p",
            anon(b"doc", b"a"),
            named(b"urn:pump"),
            vec![note(b"y"), note(b"x"), note(b"x")],
        ),
    ];
    assert!(allowed(&axioms));
    let a = first_candidate(&axioms[0]).unwrap();
    assert!(touches_named(&axioms[0], a));
    assert!(at_most_one(&axioms, a));
}
#[test]
fn two_named_attachments_make_an_isolated_vertex_fail() {
    let axioms = vec![
        attachment(b"a", b"urn:pump"),
        attachment(b"a", b"urn:motor"),
    ];
    assert!(matches!(check_forest(&axioms), ForestCheck::Forest));
    let BoundaryCheck::NoRoot(root) = check_boundary(&axioms) else {
        panic!("expected no root")
    };
    assert!(std::ptr::eq(root, first_candidate(&axioms[0]).unwrap()));
    assert!(!at_most_one(&axioms, root));
}
#[test]
fn any_vertex_in_the_tree_can_supply_the_root() {
    for reversed in [false, true] {
        let link = if reversed {
            edge(b"b", b"a")
        } else {
            edge(b"a", b"b")
        };
        let axioms = vec![
            attachment(b"a", b"urn:pump"),
            attachment(b"a", b"urn:motor"),
            link,
        ];
        assert!(allowed(&axioms)); // b has zero named incidences
    }
}
#[test]
fn every_component_needs_its_own_root_and_scopes_remain_separate() {
    let axioms = vec![
        edge(b"a", b"b"),
        attachment(b"c", b"urn:pump"),
        attachment(b"c", b"urn:motor"),
    ];
    assert!(!allowed(&axioms));
    let axioms = vec![
        attachment(b"a", b"urn:pump"),
        attachment(b"a", b"urn:motor"),
        assertion(b"urn:p", anon(b"other", b"a"), anon(b"other", b"b"), vec![]),
    ];
    assert!(!allowed(&axioms)); // other-document a cannot rescue doc/a
}
#[test]
fn metadata_property_and_orientation_can_each_create_a_second_attachment() {
    let seconds = [
        assertion(b"urn:q", anon(b"doc", b"a"), named(b"urn:pump"), vec![]),
        assertion(b"urn:p", named(b"urn:pump"), anon(b"doc", b"a"), vec![]),
        assertion(
            b"urn:p",
            anon(b"doc", b"a"),
            named(b"urn:pump"),
            vec![note(b"new")],
        ),
    ];
    for second in seconds {
        assert!(!allowed(&vec![attachment(b"a", b"urn:pump"), second]));
    }
}
#[test]
fn graph_validity_is_a_separate_condition() {
    let axioms = vec![edge(b"a", b"b"), edge(b"b", b"c"), edge(b"c", b"a")];
    assert!(allowed(&axioms));
    assert!(matches!(check_forest(&axioms), ForestCheck::Cycle { .. }));
}
#[test]
fn exhaustive_small_graphs_match_an_independent_component_oracle() {
    let labels: [&[u8]; 3] = [b"a", b"b", b"c"];
    let pairs = [(0, 1), (0, 2), (1, 2)];
    for graph_bits in 0usize..8 {
        for config in 0usize..27 {
            let counts = [config % 3, (config / 3) % 3, config / 9];
            let mut axioms = vec![];
            let mut reach = [[false; 3]; 3];
            for (i, row) in reach.iter_mut().enumerate() {
                row[i] = true;
            }
            for (bit, (a, b)) in pairs.iter().copied().enumerate() {
                if graph_bits & (1 << bit) != 0 {
                    axioms.push(edge(labels[a], labels[b]));
                    reach[a][b] = true;
                    reach[b][a] = true;
                }
            }
            for (i, count) in counts.iter().copied().enumerate() {
                if count > 0 {
                    axioms.push(attachment(labels[i], b"urn:n1"));
                }
                if count > 1 {
                    axioms.push(attachment(labels[i], b"urn:n2"));
                }
            }
            for k in 0..3 {
                for i in 0..3 {
                    for j in 0..3 {
                        reach[i][j] |= reach[i][k] && reach[k][j];
                    }
                }
            }
            let expected = (0..3).all(|i| (0..3).any(|j| reach[i][j] && counts[j] <= 1));
            assert_eq!(
                allowed(&axioms),
                expected,
                "graph={graph_bits} attachments={counts:?}"
            );
        }
    }
}
