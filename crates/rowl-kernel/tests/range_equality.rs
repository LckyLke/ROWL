use rowl_kernel::model::*;
use rowl_kernel::range_equality::{
    same_definition, same_facet, same_facet_set, same_literal_set, same_range, same_range_set,
};
use std::collections::BTreeSet;
fn iri(text: &[u8]) -> Iri {
    Iri {
        spelling: text.to_vec(),
    }
}
fn dtype(text: &[u8]) -> Datatype {
    Datatype { iri: iri(text) }
}
fn literal(text: &[u8], dt: &[u8]) -> Literal {
    Literal {
        lexical: text.to_vec(),
        datatype: dtype(dt),
    }
}
fn facet(name: &[u8], text: &[u8]) -> FacetRestriction {
    FacetRestriction {
        facet: iri(name),
        value: literal(text, b"urn:integer"),
    }
}
fn atom(text: &[u8]) -> DataRange {
    DataRange::Datatype(dtype(text))
}
fn ne<T>(first: T, rest: Vec<T>) -> NonEmpty<T> {
    NonEmpty { first, rest }
}
fn two<T>(first: T, second: T, rest: Vec<T>) -> AtLeastTwo<T> {
    AtLeastTwo {
        first,
        second,
        rest,
    }
}
fn annotation(text: &[u8]) -> Annotation {
    Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"urn:note"),
        },
        value: AnnotationValue::Iri(iri(text)),
    }
}
fn definition(range: DataRange, annotations: Vec<Annotation>) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations,
        axiom: Axiom::DatatypeDefinition(dtype(b"urn:PartCode"), range),
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Canon {
    Datatype(Vec<u8>),
    Intersection(BTreeSet<Canon>),
    Union(BTreeSet<Canon>),
    Complement(Box<Canon>),
    OneOf(BTreeSet<(Vec<u8>, Vec<u8>)>),
    Restriction(Vec<u8>, BTreeSet<(Vec<u8>, Vec<u8>, Vec<u8>)>),
}
fn normalized(range: &DataRange) -> Canon {
    match range {
        DataRange::Datatype(d) => Canon::Datatype(d.iri.spelling.to_vec()),
        DataRange::Intersection(xs) | DataRange::Union(xs) => {
            let set = std::iter::once(&xs.first)
                .chain(std::iter::once(&xs.second))
                .chain(xs.rest.iter())
                .map(normalized)
                .collect();
            if matches!(range, DataRange::Intersection(_)) {
                Canon::Intersection(set)
            } else {
                Canon::Union(set)
            }
        }
        DataRange::Complement(x) => Canon::Complement(Box::new(normalized(x))),
        DataRange::OneOf(xs) => Canon::OneOf(
            std::iter::once(&xs.first)
                .chain(xs.rest.iter())
                .map(|x| (x.lexical.to_vec(), x.datatype.iri.spelling.to_vec()))
                .collect(),
        ),
        DataRange::Restriction(d, xs) => Canon::Restriction(
            d.iri.spelling.to_vec(),
            std::iter::once(&xs.first)
                .chain(xs.rest.iter())
                .map(|x| {
                    (
                        x.facet.spelling.to_vec(),
                        x.value.lexical.to_vec(),
                        x.value.datatype.iri.spelling.to_vec(),
                    )
                })
                .collect(),
        ),
    }
}
#[test]
fn facet_identity_preserves_uri_and_literal_spelling() {
    assert!(same_facet(
        &facet(b"urn:min", b"1"),
        &facet(b"urn:min", b"1")
    ));
    assert!(!same_facet(
        &facet(b"urn:min", b"1"),
        &facet(b"urn:max", b"1")
    ));
    assert!(!same_facet(
        &facet(b"urn:min", b"1"),
        &facet(b"urn:min", b"01")
    ));
}
#[test]
fn literal_and_facet_associations_ignore_order_and_equivalent_repetitions() {
    assert!(same_literal_set(
        &ne(literal(b"1", b"urn:int"), vec![literal(b"2", b"urn:int")]),
        &ne(
            literal(b"2", b"urn:int"),
            vec![literal(b"1", b"urn:int"), literal(b"2", b"urn:int")]
        )
    ));
    assert!(!same_literal_set(
        &ne(literal(b"1", b"urn:int"), vec![]),
        &ne(literal(b"01", b"urn:int"), vec![])
    ));
    assert!(same_facet_set(
        &ne(facet(b"urn:min", b"1"), vec![facet(b"urn:max", b"9")]),
        &ne(
            facet(b"urn:max", b"9"),
            vec![facet(b"urn:min", b"1"), facet(b"urn:min", b"1")]
        )
    ));
}
#[test]
fn nested_range_associations_are_sets_at_every_level() {
    let left = DataRange::Intersection(Box::new(two(
        atom(b"A"),
        DataRange::Union(Box::new(two(atom(b"B"), atom(b"C"), vec![]))),
        vec![],
    )));
    let right = DataRange::Intersection(Box::new(two(
        DataRange::Union(Box::new(two(atom(b"C"), atom(b"B"), vec![atom(b"B")]))),
        atom(b"A"),
        vec![atom(b"A")],
    )));
    assert!(same_range(&left, &right));
    assert!(same_range_set(
        &two(atom(b"A"), atom(b"B"), vec![atom(b"A")]),
        &two(atom(b"B"), atom(b"A"), vec![])
    ));
}
#[test]
fn constructors_and_nesting_are_not_logically_simplified() {
    assert!(!same_range(
        &atom(b"A"),
        &DataRange::Intersection(Box::new(two(atom(b"A"), atom(b"A"), vec![])))
    ));
    assert!(!same_range(
        &DataRange::Union(Box::new(two(atom(b"A"), atom(b"B"), vec![]))),
        &DataRange::Intersection(Box::new(two(atom(b"A"), atom(b"B"), vec![])))
    ));
    assert!(!same_range(
        &DataRange::Complement(Box::new(DataRange::Complement(Box::new(atom(b"A"))))),
        &atom(b"A")
    ));
    let nested = DataRange::Union(Box::new(two(
        atom(b"A"),
        DataRange::Union(Box::new(two(atom(b"B"), atom(b"C"), vec![]))),
        vec![],
    )));
    let flat = DataRange::Union(Box::new(two(atom(b"A"), atom(b"B"), vec![atom(b"C")])));
    assert!(!same_range(&nested, &flat));
}
#[test]
fn restrictions_preserve_base_datatype_and_facet_membership() {
    let a = DataRange::Restriction(
        dtype(b"D"),
        ne(facet(b"min", b"1"), vec![facet(b"max", b"9")]),
    );
    let b = DataRange::Restriction(
        dtype(b"D"),
        ne(facet(b"max", b"9"), vec![facet(b"min", b"1")]),
    );
    assert!(same_range(&a, &b));
    assert!(!same_range(
        &a,
        &DataRange::Restriction(
            dtype(b"E"),
            ne(facet(b"min", b"1"), vec![facet(b"max", b"9")])
        )
    ));
    assert!(!same_range(
        &a,
        &DataRange::Restriction(
            dtype(b"D"),
            ne(facet(b"min", b"1"), vec![facet(b"max", b"09")])
        )
    ));
}
#[test]
fn definition_identity_includes_recursive_range_and_annotation_sets() {
    let a = definition(
        DataRange::OneOf(ne(
            literal(b"A", b"urn:string"),
            vec![literal(b"B", b"urn:string")],
        )),
        vec![annotation(b"x"), annotation(b"y")],
    );
    let b = definition(
        DataRange::OneOf(ne(
            literal(b"B", b"urn:string"),
            vec![literal(b"A", b"urn:string"), literal(b"A", b"urn:string")],
        )),
        vec![annotation(b"y"), annotation(b"x"), annotation(b"x")],
    );
    assert!(same_definition(&a, &b));
    assert!(!same_definition(
        &a,
        &definition(
            DataRange::OneOf(ne(
                literal(b"A", b"urn:string"),
                vec![literal(b"B", b"urn:string")]
            )),
            vec![annotation(b"other")]
        )
    ));
    let mut c = definition(atom(b"X"), vec![]);
    c.axiom = Axiom::DatatypeDefinition(dtype(b"urn:Other"), atom(b"X"));
    assert!(!same_definition(&definition(atom(b"X"), vec![]), &c));
    let other = AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::Declaration(Entity::Datatype(dtype(b"D"))),
    };
    assert!(!same_definition(&other, &other));
}
fn sample(case: usize) -> DataRange {
    let variant = case / 6;
    match case % 6 {
        0 => atom(if variant.is_multiple_of(2) {
            b"A"
        } else {
            b"B"
        }),
        1 => DataRange::Intersection(Box::new(two(
            atom(b"A"),
            atom(b"B"),
            if variant.is_multiple_of(2) {
                vec![atom(b"C")]
            } else {
                vec![atom(b"B")]
            },
        ))),
        2 => DataRange::Union(Box::new(two(
            atom(b"B"),
            atom(b"A"),
            if variant.is_multiple_of(2) {
                vec![atom(b"A")]
            } else {
                vec![atom(b"C")]
            },
        ))),
        3 => DataRange::Complement(Box::new(atom(if variant.is_multiple_of(2) {
            b"A"
        } else {
            b"B"
        }))),
        4 => DataRange::OneOf(ne(
            literal(
                if variant.is_multiple_of(3) {
                    b"1"
                } else {
                    b"01"
                },
                b"urn:int",
            ),
            vec![literal(b"2", b"urn:int")],
        )),
        _ => DataRange::Restriction(
            dtype(b"D"),
            ne(
                facet(
                    b"min",
                    if variant.is_multiple_of(3) {
                        b"1"
                    } else {
                        b"01"
                    },
                ),
                vec![facet(b"max", b"9")],
            ),
        ),
    }
}
#[test]
fn complete_constructor_matrix_matches_an_independent_recursive_set_normal_form() {
    let mut samples: Vec<_> = (0..24).map(sample).collect();
    for i in 0..12 {
        samples.push(DataRange::Union(Box::new(two(
            sample(i),
            sample(i + 1),
            vec![sample(i)],
        ))));
        samples.push(DataRange::Intersection(Box::new(two(
            sample(i + 1),
            sample(i),
            vec![sample(i + 1)],
        ))));
        samples.push(DataRange::Complement(Box::new(sample(i))));
    }
    for a in &samples {
        for b in &samples {
            assert_eq!(same_range(a, b), normalized(a) == normalized(b));
        }
    }
}
