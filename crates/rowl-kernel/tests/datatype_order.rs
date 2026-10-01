use rowl_kernel::datatype_order::{
    check_acyclic, check_dependencies, collect_dependencies, reachable, Dependencies,
    DependencyCheck,
};
use rowl_kernel::model::*;

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn datatype(s: &[u8]) -> Datatype {
    Datatype { iri: iri(s) }
}
fn atom(s: &[u8]) -> DataRange {
    DataRange::Datatype(datatype(s))
}
fn annotated(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom,
    }
}
fn definition(name: &[u8], range: DataRange) -> AnnotatedAxiom {
    annotated(Axiom::DatatypeDefinition(datatype(name), range))
}
fn union(a: &[u8], b: &[u8]) -> DataRange {
    DataRange::Union(Box::new(AtLeastTwo {
        first: atom(a),
        second: atom(b),
        rest: vec![],
    }))
}
fn graph<'a>(names: &'a [Iri], pairs: &[(usize, usize)]) -> Dependencies<'a> {
    pairs
        .iter()
        .rev()
        .fold(Dependencies::Empty, |next, &(a, b)| Dependencies::Edge {
            smaller: &names[a],
            larger: &names[b],
            next: Box::new(next),
        })
}
fn rows(mut edges: Dependencies<'_>) -> Vec<(Vec<u8>, Vec<u8>)> {
    let mut output = vec![];
    while let Dependencies::Edge {
        smaller,
        larger,
        next,
    } = edges
    {
        output.push((smaller.spelling.clone(), larger.spelling.clone()));
        edges = *next;
    }
    output
}

#[test]
fn directed_reachability_preserves_ordered_input_and_reflexive_isolates() {
    let names = vec![iri(b"A"), iri(b"B"), iri(b"C"), iri(b"isolated")];
    let pairs = [(0, 1), (1, 2), (0, 1)];
    let expected = rows(graph(&names, &pairs));
    let (forward, restored) = reachable(graph(&names, &pairs), &names[0], &names[2]);
    assert!(forward);
    assert_eq!(rows(restored), expected);
    let (reverse, restored) = reachable(graph(&names, &pairs), &names[2], &names[0]);
    assert!(!reverse);
    assert_eq!(rows(restored), expected);
    assert!(reachable(Dependencies::Empty, &names[3], &names[3]).0);
    assert!(!reachable(Dependencies::Empty, &names[3], &names[0]).0);
}

#[test]
fn cycles_include_self_edges_but_not_diamonds_or_duplicate_edges() {
    let names = vec![iri(b"A"), iri(b"B"), iri(b"C"), iri(b"D")];
    assert!(matches!(
        check_dependencies(graph(&names, &[(0, 0)])),
        DependencyCheck::Cycle { .. }
    ));
    assert!(matches!(
        check_dependencies(graph(&names, &[(0, 1), (1, 2), (2, 0)])),
        DependencyCheck::Cycle { .. }
    ));
    assert!(matches!(
        check_dependencies(graph(&names, &[(0, 1), (0, 2), (1, 3), (2, 3), (0, 1)])),
        DependencyCheck::Acyclic
    ));
}

#[test]
fn every_three_node_graph_matches_an_independent_transitive_matrix() {
    let names = vec![iri(b"A"), iri(b"B"), iri(b"C")];
    for mask in 0..512usize {
        let mut positive = [[false; 3]; 3];
        let mut pairs = vec![];
        for (a, row) in positive.iter_mut().enumerate() {
            for (b, value) in row.iter_mut().enumerate() {
                *value = (mask & (1 << (3 * a + b))) != 0;
                if *value {
                    pairs.push((a, b));
                }
            }
        }
        for k in 0..3 {
            for a in 0..3 {
                for b in 0..3 {
                    positive[a][b] |= positive[a][k] && positive[k][b];
                }
            }
        }
        let expected = rows(graph(&names, &pairs));
        for (a, row) in positive.iter().enumerate() {
            for (b, value) in row.iter().enumerate() {
                let (found, restored) = reachable(graph(&names, &pairs), &names[a], &names[b]);
                assert_eq!(found, a == b || *value, "mask={mask}, query={a}->{b}");
                assert_eq!(rows(restored), expected);
            }
        }
        match check_dependencies(graph(&names, &pairs)) {
            DependencyCheck::Acyclic => assert!((0..3).all(|i| !positive[i][i]), "mask={mask}"),
            DependencyCheck::Cycle { smaller, larger } => {
                assert!((0..3).any(|i| positive[i][i]), "mask={mask}");
                let a = names
                    .iter()
                    .position(|n| n.spelling == smaller.spelling)
                    .unwrap();
                let b = names
                    .iter()
                    .position(|n| n.spelling == larger.spelling)
                    .unwrap();
                assert!(pairs.contains(&(a, b)));
                assert!(a == b || positive[b][a]);
            }
        }
    }
}

#[test]
fn all_range_forms_contribute_exact_typed_dependencies_and_exclude_annotations() {
    let literal = || Literal {
        lexical: b"1".to_vec(),
        datatype: datatype(b"literalDT"),
    };
    let range = DataRange::Intersection(Box::new(AtLeastTwo {
        first: atom(b"A"),
        second: union(b"B", b"C"),
        rest: vec![
            DataRange::Complement(Box::new(atom(b"D"))),
            DataRange::OneOf(NonEmpty {
                first: literal(),
                rest: vec![],
            }),
            DataRange::Restriction(
                datatype(b"baseDT"),
                NonEmpty {
                    first: FacetRestriction {
                        facet: iri(b"notADatatype"),
                        value: literal(),
                    },
                    rest: vec![],
                },
            ),
        ],
    }));
    let mut item = definition(b"Defined", range);
    item.annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty { iri: iri(b"note") },
        value: AnnotationValue::Literal(Literal {
            lexical: b"text".to_vec(),
            datatype: datatype(b"annotationDT"),
        }),
    });
    let axioms = vec![item];
    assert_eq!(
        rows(collect_dependencies(&axioms)),
        [
            b"A".as_slice(),
            b"B",
            b"C",
            b"D",
            b"literalDT",
            b"baseDT",
            b"literalDT"
        ]
        .into_iter()
        .map(|source| (source.to_vec(), b"Defined".to_vec()))
        .collect::<Vec<_>>()
    );
}

#[test]
fn w3c_tax_number_example_accepts_and_added_reverse_dependency_rejects() {
    let mut axioms = vec![
        definition(b"SSN", atom(b"xsd:string")),
        definition(b"TIN", atom(b"xsd:string")),
        definition(b"TaxNumber", union(b"SSN", b"TIN")),
    ];
    assert!(matches!(check_acyclic(&axioms), DependencyCheck::Acyclic));
    axioms.push(definition(b"SSN", union(b"TIN", b"TaxNumber")));
    assert!(matches!(
        check_acyclic(&axioms),
        DependencyCheck::Cycle { .. }
    ));
}

#[test]
fn literal_datatypes_in_one_of_and_facet_values_can_close_cycles() {
    let literal = || Literal {
        lexical: b"1".to_vec(),
        datatype: datatype(b"A"),
    };
    let axioms = vec![
        definition(b"A", atom(b"B")),
        definition(
            b"B",
            DataRange::OneOf(NonEmpty {
                first: literal(),
                rest: vec![],
            }),
        ),
    ];
    assert!(matches!(
        check_acyclic(&axioms),
        DependencyCheck::Cycle { .. }
    ));
    let axioms = vec![
        definition(b"A", atom(b"B")),
        definition(
            b"B",
            DataRange::Restriction(
                datatype(b"base"),
                NonEmpty {
                    first: FacetRestriction {
                        facet: iri(b"facet"),
                        value: literal(),
                    },
                    rest: vec![],
                },
            ),
        ),
    ];
    assert!(matches!(
        check_acyclic(&axioms),
        DependencyCheck::Cycle { .. }
    ));
}

#[test]
fn byte_identity_other_axioms_and_definition_availability_are_separate() {
    let names = vec![iri(b"A"), iri(b"a")];
    assert!(matches!(
        check_dependencies(graph(&names, &[(0, 1)])),
        DependencyCheck::Acyclic
    ));
    let axioms = vec![
        definition(b"A", atom(b"undefined")),
        annotated(Axiom::Declaration(Entity::Datatype(datatype(b"A")))),
    ];
    assert!(matches!(check_acyclic(&axioms), DependencyCheck::Acyclic));
    let axioms = vec![annotated(Axiom::DataPropertyAssertion(
        DataProperty { iri: iri(b"p") },
        Individual::Named(NamedIndividual { iri: iri(b"x") }),
        Literal {
            lexical: b"invalid".to_vec(),
            datatype: datatype(b"A"),
        },
    ))];
    assert!(rows(collect_dependencies(&axioms)).is_empty());
    assert!(matches!(check_acyclic(&axioms), DependencyCheck::Acyclic));
}
