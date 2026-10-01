use rowl_kernel::class_equality::{
    is_literal, is_thing, same_class, same_class_set, same_individual_set, same_natural,
    same_optional_class, same_optional_range,
};
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
use std::collections::BTreeSet;
const THING: &[u8] = b"http://www.w3.org/2002/07/owl#Thing";
const LITERAL: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#Literal";
fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn class(s: &[u8]) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(s) })
}
fn range(s: &[u8]) -> DataRange {
    DataRange::Datatype(Datatype { iri: iri(s) })
}
fn op(inverse: bool) -> ObjectPropertyExpression {
    let p = ObjectProperty {
        iri: iri(b"urn:hasPart"),
    };
    if inverse {
        ObjectPropertyExpression::Inverse(p)
    } else {
        ObjectPropertyExpression::Property(p)
    }
}
fn dp() -> DataProperty {
    DataProperty {
        iri: iri(b"urn:reading"),
    }
}
fn named(s: &[u8]) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(s) })
}
fn blank(scope: &[u8]) -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: scope.to_vec(),
        label: b"x".to_vec(),
    })
}
fn lit(s: &[u8]) -> Literal {
    Literal {
        lexical: s.to_vec(),
        datatype: Datatype {
            iri: iri(b"urn:integer"),
        },
    }
}
fn nat(n: usize) -> Natural {
    if n == 0 {
        Natural::Zero
    } else {
        Natural::Succ(Box::new(nat(n - 1)))
    }
}
fn two(
    a: ClassExpression,
    b: ClassExpression,
    rest: Vec<ClassExpression>,
) -> Box<AtLeastTwo<ClassExpression>> {
    Box::new(AtLeastTwo {
        first: a,
        second: b,
        rest,
    })
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Atom(Vec<u8>),
    Seq(u8, Vec<Node>),
    Set(u8, BTreeSet<Node>),
}
fn atom(bytes: &[u8]) -> Node {
    Node::Atom(bytes.to_vec())
}
fn seq(tag: u8, fields: Vec<Node>) -> Node {
    Node::Seq(tag, fields)
}
fn set(tag: u8, fields: impl Iterator<Item = Node>) -> Node {
    Node::Set(tag, fields.collect())
}
fn indiv(i: &Individual) -> Node {
    match i {
        Individual::Named(n) => seq(0, vec![atom(&n.iri.spelling)]),
        Individual::Anonymous(a) => seq(1, vec![atom(&a.scope), atom(&a.label)]),
    }
}
fn property(p: &ObjectPropertyExpression) -> Node {
    match p {
        ObjectPropertyExpression::Property(p) => seq(0, vec![atom(&p.iri.spelling)]),
        ObjectPropertyExpression::Inverse(p) => seq(1, vec![atom(&p.iri.spelling)]),
    }
}
fn literal(l: &Literal) -> Node {
    seq(0, vec![atom(&l.lexical), atom(&l.datatype.iri.spelling)])
}
fn number(n: &Natural) -> Node {
    match n {
        Natural::Zero => seq(0, vec![]),
        Natural::Succ(p) => seq(1, vec![number(p)]),
    }
}
fn dr(r: &DataRange) -> Node {
    match r {
        DataRange::Datatype(d) => seq(0, vec![atom(&d.iri.spelling)]),
        DataRange::Intersection(xs) | DataRange::Union(xs) => set(
            if matches!(r, DataRange::Intersection(_)) {
                1
            } else {
                2
            },
            std::iter::once(&xs.first)
                .chain(std::iter::once(&xs.second))
                .chain(xs.rest.iter())
                .map(dr),
        ),
        DataRange::Complement(x) => seq(3, vec![dr(x)]),
        DataRange::OneOf(xs) => set(
            4,
            std::iter::once(&xs.first)
                .chain(xs.rest.iter())
                .map(literal),
        ),
        DataRange::Restriction(d, xs) => seq(
            5,
            vec![
                atom(&d.iri.spelling),
                set(
                    0,
                    std::iter::once(&xs.first)
                        .chain(xs.rest.iter())
                        .map(|x| seq(0, vec![atom(&x.facet.spelling), literal(&x.value)])),
                ),
            ],
        ),
    }
}
fn canonical(c: &ClassExpression) -> Node {
    match c {
        ClassExpression::Class(c) => seq(0, vec![atom(&c.iri.spelling)]),
        ClassExpression::ObjectIntersectionOf(xs) | ClassExpression::ObjectUnionOf(xs) => set(
            if matches!(c, ClassExpression::ObjectIntersectionOf(_)) {
                1
            } else {
                2
            },
            std::iter::once(&xs.first)
                .chain(std::iter::once(&xs.second))
                .chain(xs.rest.iter())
                .map(canonical),
        ),
        ClassExpression::ObjectComplementOf(x) => seq(3, vec![canonical(x)]),
        ClassExpression::ObjectOneOf(xs) => set(
            4,
            std::iter::once(&xs.first).chain(xs.rest.iter()).map(indiv),
        ),
        ClassExpression::ObjectSomeValuesFrom(p, x) => seq(5, vec![property(p), canonical(x)]),
        ClassExpression::ObjectAllValuesFrom(p, x) => seq(6, vec![property(p), canonical(x)]),
        ClassExpression::ObjectHasValue(p, i) => seq(7, vec![property(p), indiv(i)]),
        ClassExpression::ObjectHasSelf(p) => seq(8, vec![property(p)]),
        ClassExpression::ObjectMinCardinality(n, p, x)
        | ClassExpression::ObjectMaxCardinality(n, p, x)
        | ClassExpression::ObjectExactCardinality(n, p, x) => seq(
            match c {
                ClassExpression::ObjectMinCardinality(..) => 9,
                ClassExpression::ObjectMaxCardinality(..) => 10,
                _ => 11,
            },
            vec![
                number(n),
                property(p),
                x.as_ref()
                    .map_or_else(|| canonical(&class(THING)), |x| canonical(x)),
            ],
        ),
        ClassExpression::DataSomeValuesFrom(p, x) => seq(12, vec![atom(&p.iri.spelling), dr(x)]),
        ClassExpression::DataAllValuesFrom(p, x) => seq(13, vec![atom(&p.iri.spelling), dr(x)]),
        ClassExpression::DataHasValue(p, l) => seq(14, vec![atom(&p.iri.spelling), literal(l)]),
        ClassExpression::DataMinCardinality(n, p, x)
        | ClassExpression::DataMaxCardinality(n, p, x)
        | ClassExpression::DataExactCardinality(n, p, x) => seq(
            match c {
                ClassExpression::DataMinCardinality(..) => 15,
                ClassExpression::DataMaxCardinality(..) => 16,
                _ => 17,
            },
            vec![
                number(n),
                atom(&p.iri.spelling),
                x.as_ref().map_or_else(|| dr(&range(LITERAL)), dr),
            ],
        ),
    }
}
fn sample(form: usize, variant: usize) -> ClassExpression {
    let a = || {
        class(if variant.is_multiple_of(2) {
            b"urn:Machine"
        } else {
            b"urn:Pump"
        })
    };
    let x = || {
        if variant == 0 {
            None
        } else {
            Some(Box::new(class(THING)))
        }
    };
    let r = || {
        if variant == 0 {
            None
        } else {
            Some(range(LITERAL))
        }
    };
    match form {
        0 => a(),
        1 => ClassExpression::ObjectIntersectionOf(if variant == 2 {
            two(class(b"urn:Part"), a(), vec![a()])
        } else {
            two(a(), class(b"urn:Part"), vec![])
        }),
        2 => ClassExpression::ObjectUnionOf(if variant == 2 {
            two(class(b"urn:Part"), a(), vec![a()])
        } else {
            two(a(), class(b"urn:Part"), vec![])
        }),
        3 => ClassExpression::ObjectComplementOf(Box::new(a())),
        4 => ClassExpression::ObjectOneOf(NonEmpty {
            first: named(b"urn:pump1"),
            rest: vec![blank(if variant == 1 { b"other" } else { b"source" })],
        }),
        5 => ClassExpression::ObjectSomeValuesFrom(op(variant == 1), Box::new(a())),
        6 => ClassExpression::ObjectAllValuesFrom(op(variant == 1), Box::new(a())),
        7 => ClassExpression::ObjectHasValue(op(variant == 1), named(b"urn:pump1")),
        8 => ClassExpression::ObjectHasSelf(op(variant == 1)),
        9 => ClassExpression::ObjectMinCardinality(nat(2), op(variant == 1), x()),
        10 => ClassExpression::ObjectMaxCardinality(nat(2), op(variant == 1), x()),
        11 => ClassExpression::ObjectExactCardinality(nat(2), op(variant == 1), x()),
        12 => ClassExpression::DataSomeValuesFrom(
            dp(),
            range(if variant == 1 {
                b"urn:string"
            } else {
                b"urn:integer"
            }),
        ),
        13 => ClassExpression::DataAllValuesFrom(
            dp(),
            range(if variant == 1 {
                b"urn:string"
            } else {
                b"urn:integer"
            }),
        ),
        14 => ClassExpression::DataHasValue(dp(), lit(if variant == 1 { b"01" } else { b"1" })),
        15 => ClassExpression::DataMinCardinality(nat(2), dp(), r()),
        16 => ClassExpression::DataMaxCardinality(nat(2), dp(), r()),
        _ => ClassExpression::DataExactCardinality(nat(2), dp(), r()),
    }
}
#[test]
fn all_eighteen_forms_match_an_independent_set_and_default_oracle() {
    let values: Vec<_> = (0..18)
        .flat_map(|form| (0..3).map(move |v| sample(form, v)))
        .collect();
    for (i, left) in values.iter().enumerate() {
        for (j, right) in values.iter().enumerate() {
            assert_eq!(
                same_class(left, right),
                canonical(left) == canonical(right),
                "forms {i} and {j}"
            );
        }
    }
}
#[test]
fn defaults_are_exact_named_builtins_for_all_six_cardinalities() {
    assert!(same_optional_class(&None, &Some(Box::new(class(THING)))));
    assert!(same_optional_class(&Some(Box::new(class(THING))), &None));
    assert!(same_optional_range(&None, &Some(range(LITERAL))));
    assert!(same_optional_range(&Some(range(LITERAL)), &None));
    assert!(!same_optional_class(
        &None,
        &Some(Box::new(class(b"owl:Thing")))
    ));
    assert!(!same_optional_range(&None, &Some(range(b"rdfs:Literal"))));
    assert!(!is_thing(&class(b"http://www.w3.org/2002/07/owl#thing")));
    assert!(!is_literal(&DataRange::Complement(Box::new(
        DataRange::Complement(Box::new(range(LITERAL)))
    ))));
    for form in [9, 10, 11, 15, 16, 17] {
        assert!(same_class(&sample(form, 0), &sample(form, 2)));
    }
    assert!(same_natural(&nat(120), &nat(120)));
    assert!(!same_natural(&nat(120), &nat(119)));
}
#[test]
fn nested_sets_ignore_order_and_repetitions_without_flattening() {
    let nested = || ClassExpression::ObjectUnionOf(two(class(b"urn:A"), class(b"urn:B"), vec![]));
    let reversed = || {
        ClassExpression::ObjectUnionOf(two(class(b"urn:B"), class(b"urn:A"), vec![class(b"urn:A")]))
    };
    assert!(same_class(
        &ClassExpression::ObjectSomeValuesFrom(op(false), Box::new(nested())),
        &ClassExpression::ObjectSomeValuesFrom(op(false), Box::new(reversed()))
    ));
    assert!(same_class_set(
        &two(nested(), class(b"urn:C"), vec![]),
        &two(class(b"urn:C"), reversed(), vec![nested()])
    ));
    assert!(!same_class(
        &ClassExpression::ObjectUnionOf(two(nested(), class(b"urn:C"), vec![])),
        &ClassExpression::ObjectUnionOf(two(
            class(b"urn:A"),
            class(b"urn:B"),
            vec![class(b"urn:C")]
        ))
    ));
}
#[test]
fn structural_identity_retains_scope_orientation_lexical_forms_and_constructors() {
    assert!(!same_class(
        &ClassExpression::ObjectComplementOf(Box::new(ClassExpression::ObjectComplementOf(
            Box::new(class(THING))
        ))),
        &class(THING)
    ));
    assert!(!same_class(
        &ClassExpression::ObjectHasValue(op(false), named(b"urn:x")),
        &ClassExpression::ObjectHasValue(op(true), named(b"urn:x"))
    ));
    assert!(!same_class(
        &ClassExpression::DataHasValue(dp(), lit(b"1")),
        &ClassExpression::DataHasValue(dp(), lit(b"01"))
    ));
    assert!(same_individual_set(
        &NonEmpty {
            first: blank(b"doc1"),
            rest: vec![named(b"urn:x")]
        },
        &NonEmpty {
            first: named(b"urn:x"),
            rest: vec![blank(b"doc1"), blank(b"doc1")]
        }
    ));
    assert!(!same_individual_set(
        &NonEmpty {
            first: blank(b"doc1"),
            rest: vec![]
        },
        &NonEmpty {
            first: blank(b"doc2"),
            rest: vec![]
        }
    ));
}
