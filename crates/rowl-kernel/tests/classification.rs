use rowl_kernel::classification::{classify, told};
use rowl_kernel::data_ontology::{prepare, prepared_class_satisfiable, prepared_subsumed};
use rowl_kernel::model::*;

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn named(s: &[u8]) -> Class {
    Class { iri: iri(s) }
}
fn class(s: &[u8]) -> ClassExpression {
    ClassExpression::Class(named(s))
}
fn two<T>(first: T, second: T, rest: Vec<T>) -> AtLeastTwo<T> {
    AtLeastTwo {
        first,
        second,
        rest,
    }
}
fn and(a: ClassExpression, b: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(two(a, b, Vec::new())))
}
fn or(a: ClassExpression, b: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectUnionOf(Box::new(two(a, b, Vec::new())))
}
fn not(a: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(a))
}
fn some(r: &[u8], c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Property(ObjectProperty { iri: iri(r) }),
        Box::new(c),
    )
}
fn axiom(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: Vec::new(),
        axiom,
    }
}

const NAMES: [&[u8]; 6] = [b"A", b"B", b"C", b"D", b"E", b"F"];

struct Seed(u64);
impl Seed {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % bound
    }
    fn name(&mut self) -> &'static [u8] {
        NAMES[self.next(NAMES.len() as u64) as usize]
    }
}

fn expression(seed: &mut Seed, depth: u32) -> ClassExpression {
    match if depth == 0 { 0 } else { seed.next(6) } {
        0 | 1 => class(seed.name()),
        2 => and(expression(seed, depth - 1), expression(seed, depth - 1)),
        3 => or(expression(seed, depth - 1), expression(seed, depth - 1)),
        4 => not(expression(seed, depth - 1)),
        _ => some(b"r", expression(seed, depth - 1)),
    }
}

fn ontology(seed: &mut Seed) -> Vec<AnnotatedAxiom> {
    let mut items = Vec::new();
    for _ in 0..seed.next(6) + 1 {
        items.push(match seed.next(5) {
            0 | 1 => axiom(Axiom::SubClassOf(class(seed.name()), expression(seed, 2))),
            2 => axiom(Axiom::SubClassOf(expression(seed, 1), expression(seed, 1))),
            3 => axiom(Axiom::EquivalentClasses(two(
                class(seed.name()),
                expression(seed, 2),
                Vec::new(),
            ))),
            _ => axiom(Axiom::DisjointUnion(
                named(seed.name()),
                two(class(seed.name()), class(seed.name()), Vec::new()),
            )),
        });
    }
    items
}

#[test]
fn classification_agrees_with_every_pairwise_query() {
    let mut seed = Seed(5);
    let classes: Vec<Class> = NAMES.iter().map(|name| named(name)).collect();
    let mut compared = 0;
    for _ in 0..150 {
        let items = ontology(&mut seed);
        let Some(prepared) = prepare(&items) else {
            continue;
        };
        let Some(result) = classify(&prepared, &items, &classes) else {
            continue;
        };
        for (i, a) in classes.iter().enumerate() {
            let a = ClassExpression::Class(Class {
                iri: iri(&a.iri.spelling),
            });
            assert_eq!(
                prepared_class_satisfiable(&prepared, &a),
                Some(result.satisfiable[i])
            );
            for (j, b) in classes.iter().enumerate() {
                let b = ClassExpression::Class(Class {
                    iri: iri(&b.iri.spelling),
                });
                let a = ClassExpression::Class(Class {
                    iri: iri(match &a {
                        ClassExpression::Class(c) => &c.iri.spelling,
                        _ => unreachable!(),
                    }),
                });
                assert_eq!(
                    prepared_subsumed(&prepared, &a, &b),
                    Some(result.subsumed[i][j])
                );
                compared += 1;
            }
        }
    }
    assert!(compared > 2000, "the sample must be classified");
}

#[test]
fn told_parents_come_from_subclass_equivalence_and_union_axioms() {
    let items = vec![
        axiom(Axiom::SubClassOf(
            class(b"A"),
            and(class(b"B"), class(b"C")),
        )),
        axiom(Axiom::EquivalentClasses(two(
            class(b"D"),
            and(class(b"E"), some(b"r", class(b"F"))),
            Vec::new(),
        ))),
        axiom(Axiom::DisjointUnion(
            named(b"F"),
            two(class(b"A"), class(b"B"), Vec::new()),
        )),
    ];
    let classes: Vec<Class> = NAMES.iter().map(|name| named(name)).collect();
    let parents = told(&items, &classes);
    assert!(parents[0].contains(&1) && parents[0].contains(&2));
    assert!(parents[3].contains(&4));
    assert!(parents[0].contains(&5) && parents[1].contains(&5));
    assert!(parents[4].is_empty());
}
