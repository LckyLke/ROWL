use rowl_kernel::arity::axiom_allowed;
use rowl_kernel::axiom_set::*;
use rowl_kernel::batch::AxiomOrigin;
use rowl_kernel::model::*;
use std::collections::BTreeMap;
#[path = "support/axiom_fixtures.rs"]
mod axiom_fixtures;
use axiom_fixtures::*;

fn occurrence_at(tag: usize, variant: usize, document: u32, ordinal: u32) -> AxiomOccurrence {
    AxiomOccurrence {
        origin: AxiomOrigin { document, ordinal },
        axiom: annotated(tag, variant),
    }
}
fn accepted(rows: &Vec<AxiomOccurrence>) -> AxiomSet<'_> {
    match build(rows) {
        BuildResult::Set(set) => set,
        BuildResult::InvalidArity(row) => {
            panic!("unexpected invalid original {}", row.origin.ordinal)
        }
    }
}

#[test]
fn all_37_forms_group_against_independent_fixture_classes_preserving_every_original() {
    let mut rows = vec![];
    let mut expected = vec![];
    let mut first = BTreeMap::new();
    for variant in [2, 0, 1, 0, 2] {
        for tag in 0..37 {
            let row = occurrence_at(tag, variant, variant as u32, rows.len() as u32);
            // The five disjoint/different fixtures intentionally repeat members
            // in variant 1; those are tested as failures below, never repaired.
            if !axiom_allowed(&row.axiom) {
                assert_eq!(variant, 1);
                assert!([3, 4, 7, 20, 27].contains(&tag));
                continue;
            }
            let class = (tag, usize::from(variant == 2));
            let representative = *first.entry(class).or_insert(rows.len());
            expected.push(representative);
            rows.push(row);
        }
    }
    let set = accepted(&rows);
    let mut expected_roots: Vec<_> = first.values().copied().collect();
    expected_roots.sort_unstable();
    assert_eq!(representatives(&set), &expected_roots);
    assert_eq!(representative_indices(&set), &expected);
    assert!(std::ptr::eq(originals(&set), &rows));
    for (i, &r) in expected.iter().enumerate() {
        assert!(std::ptr::eq(occurrence(&set, i).unwrap(), &rows[i]));
        assert!(std::ptr::eq(representative_of(&set, i).unwrap(), &rows[r]));
        assert_eq!(representative_indices(&set)[r], r);
        assert!(r <= i);
        assert!(representatives(&set).contains(&r));
        assert_eq!(originals(&set)[i].origin.document, rows[i].origin.document);
        assert_eq!(originals(&set)[i].origin.ordinal, rows[i].origin.ordinal);
    }
    assert!(occurrence(&set, rows.len()).is_none());
    assert!(representative_of(&set, rows.len()).is_none());
    assert!(occurrence(&set, usize::MAX).is_none());
    assert!(representative_of(&set, usize::MAX).is_none());
}

#[test]
fn invalid_originals_are_rejected_before_equivalent_copies_can_hide_them() {
    for tag in [3, 4, 7, 20, 27] {
        for invalid_first in [true, false] {
            let variants = if invalid_first { [1, 0, 1] } else { [0, 1, 1] };
            let rows: Vec<_> = variants
                .into_iter()
                .enumerate()
                .map(|(i, variant)| occurrence_at(tag, variant, 17, i as u32))
                .collect();
            let expected = usize::from(!invalid_first);
            match build(&rows) {
                BuildResult::InvalidArity(row) => {
                    assert!(std::ptr::eq(row, &rows[expected]));
                    assert_eq!(row.origin.document, 17);
                    assert_eq!(row.origin.ordinal, expected as u32);
                }
                BuildResult::Set(_) => panic!("invalid duplicate disjointness was hidden"),
            }
        }
    }
    let rows = vec![
        occurrence_at(0, 0, 1, 0),
        occurrence_at(3, 1, 9, 5),
        occurrence_at(27, 1, 9, 6),
    ];
    match build(&rows) {
        BuildResult::InvalidArity(row) => assert!(std::ptr::eq(row, &rows[1])),
        BuildResult::Set(_) => panic!("first invalid occurrence was missed"),
    }
}

#[test]
fn annotation_changes_and_ordered_chains_remain_separate_classes() {
    let chain = |reverse| AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Chain(AtLeastTwo {
                first: op(if reverse { 2 } else { 0 }),
                second: op(if reverse { 0 } else { 2 }),
                rest: vec![],
            }),
            op(4),
        ),
    };
    let mut changed = annotated(1, 0);
    changed.annotations.push(annotation(888, true));
    let rows = vec![
        occurrence_at(1, 0, 1, 0),
        occurrence_at(1, 1, 2, 0),
        AxiomOccurrence {
            origin: AxiomOrigin {
                document: 2,
                ordinal: 1,
            },
            axiom: changed,
        },
        AxiomOccurrence {
            origin: AxiomOrigin {
                document: 3,
                ordinal: 0,
            },
            axiom: chain(false),
        },
        AxiomOccurrence {
            origin: AxiomOrigin {
                document: 3,
                ordinal: 1,
            },
            axiom: chain(true),
        },
        AxiomOccurrence {
            origin: AxiomOrigin {
                document: 4,
                ordinal: 0,
            },
            axiom: chain(false),
        },
    ];
    let set = accepted(&rows);
    assert_eq!(representatives(&set), &[0, 2, 3, 4]);
    assert_eq!(representative_indices(&set), &[0, 0, 2, 3, 4, 3]);
}

#[test]
fn empty_and_single_source_views_have_exact_boundary_behavior() {
    let empty = vec![];
    let set = accepted(&empty);
    assert!(representatives(&set).is_empty());
    assert!(representative_indices(&set).is_empty());
    assert!(std::ptr::eq(originals(&set), &empty));
    assert!(representative_of(&set, 0).is_none());
    let one = vec![occurrence_at(0, 0, 5, 42)];
    let set = accepted(&one);
    assert_eq!(representatives(&set), &[0]);
    assert_eq!(representative_indices(&set), &[0]);
    assert!(std::ptr::eq(representative_of(&set, 0).unwrap(), &one[0]));
    assert!(representative_of(&set, 1).is_none());
}

#[test]
fn anonymous_scope_and_lexical_identity_do_not_coalesce_semantic_aliases() {
    let blank = |scope: &[u8]| AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::ClassAssertion(
            atom(0),
            Individual::Anonymous(AnonymousIndividual {
                scope: scope.to_vec(),
                label: b"motor".to_vec(),
            }),
        ),
    };
    let value = |lexical: &[u8]| AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::DataPropertyAssertion(
            dp(0),
            named(0),
            Literal {
                lexical: lexical.to_vec(),
                datatype: Datatype {
                    iri: Iri {
                        spelling: b"http://www.w3.org/2001/XMLSchema#integer".to_vec(),
                    },
                },
            },
        ),
    };
    let rows: Vec<_> = [
        blank(b"manual-a"),
        blank(b"manual-b"),
        blank(b"manual-a"),
        value(b"1"),
        value(b"01"),
        value(b"1"),
    ]
    .into_iter()
    .enumerate()
    .map(|(i, axiom)| AxiomOccurrence {
        origin: AxiomOrigin {
            document: 0,
            ordinal: i as u32,
        },
        axiom,
    })
    .collect();
    let set = accepted(&rows);
    assert_eq!(representatives(&set), &[0, 1, 3, 4]);
    assert_eq!(representative_indices(&set), &[0, 1, 0, 3, 4, 3]);
}
