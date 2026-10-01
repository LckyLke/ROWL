use rowl_frontend::rdf::*;

fn iri(name: &str) -> RdfIri {
    RdfIri {
        spelling: name.as_bytes().to_vec(),
    }
}

fn blank(scope: &str, label: &str) -> BlankNode {
    BlankNode {
        scope: scope.as_bytes().to_vec(),
        label: label.as_bytes().to_vec(),
    }
}

fn empty() -> RawGraph {
    RawGraph { triples: vec![] }
}

fn fact(machine: &str) -> Triple {
    Triple {
        subject: Subject::Iri(iri(machine)),
        predicate: iri("urn:maintenance:hasPart"),
        object: Object::Blank(blank("dataset:1", "motor")),
    }
}

fn entry(name: GraphName, graph: RawGraph, next: NamedGraphs) -> NamedGraphs {
    NamedGraphs::Entry {
        name,
        graph,
        next: Box::new(next),
    }
}

#[test]
fn explicit_selection_retains_the_whole_dataset_and_exact_graph_storage() {
    let dataset = RawDataset {
        default: RawGraph {
            triples: vec![fact("urn:default:pump")],
        },
        named: entry(
            GraphName::Iri(iri("urn:maintenance")),
            RawGraph {
                triples: vec![fact("urn:pump:1"), fact("urn:pump:1")],
            },
            entry(
                GraphName::Iri(iri("urn:audit")),
                RawGraph {
                    triples: vec![fact("urn:pump:2")],
                },
                NamedGraphs::Empty,
            ),
        ),
    };
    let choice = GraphChoice::Named(GraphName::Iri(iri("urn:maintenance")));
    let SelectionResult::Selected(selection) = select_graph(&dataset, &choice) else {
        panic!("present unique graph rejected")
    };
    assert!(std::ptr::eq(original_dataset(&selection), &dataset));
    assert_eq!(selected_graph(&selection).triples.len(), 2);
    let NamedGraphs::Entry { graph, next, .. } = &dataset.named else {
        panic!("missing stored graph")
    };
    assert!(std::ptr::eq(selected_graph(&selection), graph));
    let NamedGraphs::Entry { graph: audit, .. } = next.as_ref() else {
        panic!("unselected audit graph discarded")
    };
    assert_eq!(audit.triples.len(), 1);
    let SelectionResult::Selected(default) = select_graph(&dataset, &GraphChoice::Default) else {
        panic!("explicit default selection rejected")
    };
    assert!(std::ptr::eq(selected_graph(&default), &dataset.default));
    assert_eq!(selected_graph(&default).triples.len(), 1);
}

#[test]
fn present_empty_default_and_named_graphs_differ_from_missing_graphs() {
    let dataset = RawDataset {
        default: empty(),
        named: entry(
            GraphName::Blank(blank("dataset:1", "empty-graph")),
            empty(),
            NamedGraphs::Empty,
        ),
    };
    for choice in [
        GraphChoice::Default,
        GraphChoice::Named(GraphName::Blank(blank("dataset:1", "empty-graph"))),
    ] {
        let SelectionResult::Selected(selection) = select_graph(&dataset, &choice) else {
            panic!("an empty existing graph was treated as missing")
        };
        assert!(selected_graph(&selection).triples.is_empty());
    }
    assert!(matches!(
        select_graph(
            &dataset,
            &GraphChoice::Named(GraphName::Iri(iri("urn:missing")))
        ),
        SelectionResult::MissingGraph
    ));
}

#[test]
fn graph_names_use_exact_bytes_and_scoped_blank_identity() {
    for (left, right) in [
        ("http://example.org/g", "HTTP://example.org/g"),
        ("http://example.org/%61", "http://example.org/a"),
        ("urn:é", "urn:e\u{301}"),
    ] {
        assert!(!same_graph_name(
            &GraphName::Iri(iri(left)),
            &GraphName::Iri(iri(right))
        ));
    }
    assert!(same_graph_name(
        &GraphName::Blank(blank("dataset:1", "g")),
        &GraphName::Blank(blank("dataset:1", "g"))
    ));
    assert!(!same_graph_name(
        &GraphName::Blank(blank("dataset:1", "g")),
        &GraphName::Blank(blank("dataset:2", "g"))
    ));
    assert!(!same_graph_name(
        &GraphName::Iri(iri("g")),
        &GraphName::Blank(blank("", "g"))
    ));
    // Even raw invalid UTF-8 is compared safely; lexical validation is separate.
    assert!(same_graph_name(
        &GraphName::Iri(RdfIri {
            spelling: vec![255]
        }),
        &GraphName::Iri(RdfIri {
            spelling: vec![255]
        })
    ));
}

#[test]
fn repeated_names_are_rejected_even_in_unselected_graphs() {
    let dataset = RawDataset {
        default: empty(),
        named: entry(
            GraphName::Iri(iri("urn:unique")),
            empty(),
            entry(
                GraphName::Iri(iri("urn:repeated")),
                empty(),
                entry(
                    GraphName::Iri(iri("urn:repeated")),
                    RawGraph {
                        triples: vec![fact("urn:pump")],
                    },
                    NamedGraphs::Empty,
                ),
            ),
        ),
    };
    for choice in [
        GraphChoice::Default,
        GraphChoice::Named(GraphName::Iri(iri("urn:unique"))),
        GraphChoice::Named(GraphName::Iri(iri("urn:absent"))),
    ] {
        let SelectionResult::DuplicateGraphName(GraphName::Iri(name)) =
            select_graph(&dataset, &choice)
        else {
            panic!("repeated name was hidden by graph selection")
        };
        assert_eq!(name.spelling, b"urn:repeated");
    }
}

#[test]
fn cross_graph_blank_nodes_literal_forms_and_language_tags_are_retained() {
    let maintenance = RawGraph {
        triples: vec![fact("urn:pump")],
    };
    let audit = RawGraph {
        triples: vec![
            Triple {
                subject: Subject::Blank(blank("dataset:1", "motor")),
                predicate: iri("urn:revision"),
                object: Object::Literal(RdfLiteral {
                    lexical: b"01".to_vec(),
                    kind: LiteralKind::Datatype(iri("http://www.w3.org/2001/XMLSchema#integer")),
                }),
            },
            Triple {
                subject: Subject::Blank(blank("dataset:1", "motor")),
                predicate: iri("http://www.w3.org/2000/01/rdf-schema#label"),
                object: Object::Literal(RdfLiteral {
                    lexical: "Motor".as_bytes().to_vec(),
                    kind: LiteralKind::Language(b"de-DE".to_vec()),
                }),
            },
        ],
    };
    let dataset = RawDataset {
        default: empty(),
        named: entry(
            GraphName::Iri(iri("urn:maintenance")),
            maintenance,
            entry(GraphName::Iri(iri("urn:audit")), audit, NamedGraphs::Empty),
        ),
    };
    let SelectionResult::Selected(selection) = select_graph(
        &dataset,
        &GraphChoice::Named(GraphName::Iri(iri("urn:maintenance"))),
    ) else {
        panic!("selection failed")
    };
    let Object::Blank(motor) = &selected_graph(&selection).triples[0].object else {
        panic!("blank node changed kind")
    };
    let NamedGraphs::Entry { next, .. } = &original_dataset(&selection).named else {
        panic!("record missing")
    };
    let NamedGraphs::Entry { graph: audit, .. } = next.as_ref() else {
        panic!("audit graph missing")
    };
    let Subject::Blank(audit_motor) = &audit.triples[0].subject else {
        panic!("cross-graph blank subject changed")
    };
    assert_eq!(motor.scope, audit_motor.scope);
    assert_eq!(motor.label, audit_motor.label);
    let Object::Literal(revision) = &audit.triples[0].object else {
        panic!("literal disappeared")
    };
    assert_eq!(revision.lexical, b"01");
    let Object::Literal(label) = &audit.triples[1].object else {
        panic!("label disappeared")
    };
    let LiteralKind::Language(tag) = &label.kind else {
        panic!("language tag erased")
    };
    assert_eq!(tag, b"de-DE");
}
