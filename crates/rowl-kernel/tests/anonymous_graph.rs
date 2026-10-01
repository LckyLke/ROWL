use rowl_kernel::anonymous_graph::{
    check_edges, check_forest, collect_edges, connected, same_individual, AnonymousEdges,
    ForestCheck,
};
use rowl_kernel::model::*;

fn node(scope: &[u8], label: &[u8]) -> AnonymousIndividual {
    AnonymousIndividual {
        scope: scope.to_vec(),
        label: label.to_vec(),
    }
}
fn edges<'a>(nodes: &'a [AnonymousIndividual], pairs: &[(usize, usize)]) -> AnonymousEdges<'a> {
    pairs
        .iter()
        .rev()
        .fold(AnonymousEdges::Empty, |next, &(a, b)| {
            AnonymousEdges::Edge {
                left: &nodes[a],
                right: &nodes[b],
                next: Box::new(next),
            }
        })
}
fn item(body: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom: body,
    }
}
fn property(name: &[u8], inverse: bool) -> ObjectPropertyExpression {
    let p = ObjectProperty {
        iri: Iri {
            spelling: name.to_vec(),
        },
    };
    if inverse {
        ObjectPropertyExpression::Inverse(p)
    } else {
        ObjectPropertyExpression::Property(p)
    }
}
fn anonymous(label: &[u8]) -> Individual {
    Individual::Anonymous(node(b"doc", label))
}
fn positive(a: &[u8], b: &[u8], inverse: bool) -> AnnotatedAxiom {
    item(Axiom::ObjectPropertyAssertion(
        property(b"urn:hasPart", inverse),
        anonymous(a),
        anonymous(b),
    ))
}
fn edge_count(graph: &AnonymousEdges<'_>) -> usize {
    match graph {
        AnonymousEdges::Empty => 0,
        AnonymousEdges::Edge { next, .. } => 1 + edge_count(next),
    }
}

#[test]
fn structural_identity_uses_both_exact_byte_fields() {
    let x = node(b"first", b"x");
    assert!(same_individual(&x, &node(b"first", b"x")));
    assert!(!same_individual(&x, &node(b"second", b"x")));
    assert!(!same_individual(&x, &node(b"first", b"y")));
    assert!(!same_individual(&node(b"ab", b"c"), &node(b"a", b"bc")));
    // Raw identity accepts arbitrary bytes; lexical validity is a later gate.
    assert!(same_individual(&node(&[0xff], b""), &node(&[0xff], b"")));
    assert!(!same_individual(&node(b"", b""), &node(b"", &[0])));
}

#[test]
fn connectivity_is_undirected_reflexive_and_restores_edges() {
    let nodes = [
        node(b"doc", b"a"),
        node(b"doc", b"b"),
        node(b"doc", b"c"),
        node(b"other", b"a"),
    ];
    let graph = edges(&nodes, &[(0, 1), (2, 1), (1, 0), (2, 2)]);
    let (found, graph) = connected(graph, &nodes[0], &nodes[2]);
    assert!(found);
    let (found, graph) = connected(graph, &nodes[2], &nodes[0]);
    assert!(found);
    let (found, graph) = connected(graph, &nodes[0], &nodes[3]);
    assert!(!found);
    let (found, graph) = connected(graph, &nodes[3], &nodes[3]);
    assert!(found);
    assert_eq!(edge_count(&graph), 4);
    let AnonymousEdges::Edge { left, right, .. } = graph else {
        panic!("edges retained")
    };
    assert!(std::ptr::eq(left, &nodes[0]));
    assert!(std::ptr::eq(right, &nodes[1]));
}

#[test]
fn forests_cycles_and_self_loops_have_distinct_outcomes() {
    let nodes = [
        node(b"doc", b"a"),
        node(b"doc", b"b"),
        node(b"doc", b"c"),
        node(b"doc", b"d"),
    ];
    assert!(matches!(
        check_edges(edges(&nodes, &[])),
        ForestCheck::Forest
    ));
    assert!(matches!(
        check_edges(edges(&nodes, &[(0, 1), (1, 2)])),
        ForestCheck::Forest
    ));
    assert!(matches!(
        check_edges(edges(&nodes, &[(0, 1), (2, 3)])),
        ForestCheck::Forest
    ));
    let ForestCheck::Cycle { left, right } = check_edges(edges(&nodes, &[(0, 1), (1, 2), (2, 0)]))
    else {
        panic!("triangle")
    };
    assert!(std::ptr::eq(left, &nodes[0]));
    assert!(std::ptr::eq(right, &nodes[1]));
    let ForestCheck::SelfLoop(value) = check_edges(edges(&nodes, &[(2, 2)])) else {
        panic!("self loop")
    };
    assert!(std::ptr::eq(value, &nodes[2]));
}

#[test]
fn repeated_endpoint_pairs_are_one_graph_edge() {
    let axioms = vec![
        positive(b"a", b"b", false),
        positive(b"b", b"a", false),
        positive(b"a", b"b", true),
    ];
    assert_eq!(edge_count(&collect_edges(&axioms)), 3);
    assert!(matches!(check_forest(&axioms), ForestCheck::Forest));
    // The separate edge-multiplicity gate must reject the distinct assertions.
}

#[test]
fn actual_closure_collects_only_positive_anonymous_to_anonymous_edges_in_order() {
    let axioms = vec![
        positive(b"a", b"b", false),
        item(Axiom::ObjectPropertyAssertion(
            property(b"urn:p", false),
            anonymous(b"a"),
            Individual::Named(NamedIndividual {
                iri: Iri {
                    spelling: b"urn:machine".to_vec(),
                },
            }),
        )),
        item(Axiom::NegativeObjectPropertyAssertion(
            property(b"urn:p", false),
            anonymous(b"a"),
            anonymous(b"c"),
        )),
        item(Axiom::AnnotationAssertion(
            AnnotationProperty {
                iri: Iri {
                    spelling: b"urn:note".to_vec(),
                },
            },
            AnnotationSubject::Anonymous(node(b"doc", b"a")),
            AnnotationValue::Anonymous(node(b"doc", b"c")),
        )),
        positive(b"b", b"c", true),
    ];
    let graph = collect_edges(&axioms);
    assert_eq!(edge_count(&graph), 2);
    let AnonymousEdges::Edge { left, right, next } = graph else {
        panic!("first edge")
    };
    assert_eq!(left.label, b"a");
    assert_eq!(right.label, b"b");
    let AnonymousEdges::Edge { left, right, .. } = *next else {
        panic!("second edge")
    };
    assert_eq!(left.label, b"b");
    assert_eq!(right.label, b"c");
    assert!(matches!(check_forest(&axioms), ForestCheck::Forest));
    // Forest acceptance alone cannot excuse the illegal negative assertion.
}

#[test]
fn exact_byte_identity_joins_separately_allocated_occurrences_and_keeps_scopes_apart() {
    let triangle = vec![
        positive(b"a", b"b", false),
        positive(b"b", b"c", false),
        positive(b"c", b"a", false),
    ];
    assert!(matches!(check_forest(&triangle), ForestCheck::Cycle { .. }));
    let first = node(b"one", b"x");
    let other = node(b"two", b"x");
    assert!(matches!(
        check_edges(AnonymousEdges::Edge {
            left: &first,
            right: &other,
            next: Box::new(AnonymousEdges::Empty)
        }),
        ForestCheck::Forest
    ));
    let alias = node(b"one", b"x");
    assert!(matches!(
        check_edges(AnonymousEdges::Edge {
            left: &first,
            right: &alias,
            next: Box::new(AnonymousEdges::Empty)
        }),
        ForestCheck::SelfLoop(_)
    ));
}

#[test]
fn all_four_vertex_graphs_agree_with_independent_component_merging() {
    let nodes = [
        node(b"doc", b"a"),
        node(b"doc", b"b"),
        node(b"doc", b"c"),
        node(b"doc", b"d"),
    ];
    let slots: Vec<_> = (0..4).flat_map(|a| (a..4).map(move |b| (a, b))).collect();
    for mask in 0..(1u32 << slots.len()) {
        let pairs: Vec<_> = slots
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(bit, pair)| ((mask & (1 << bit)) != 0).then_some(pair))
            .collect();
        let mut groups = [0, 1, 2, 3];
        let mut forest = true;
        for &(a, b) in &pairs {
            if groups[a] == groups[b] {
                forest = false;
                break;
            }
            let old = groups[b];
            let new = groups[a];
            for group in &mut groups {
                if *group == old {
                    *group = new;
                }
            }
        }
        assert_eq!(
            matches!(check_edges(edges(&nodes, &pairs)), ForestCheck::Forest),
            forest,
            "mask {mask}"
        );
    }
}
