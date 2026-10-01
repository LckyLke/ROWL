use rowl_kernel::model::*;
use rowl_kernel::nnf::{nnf, NnfConcept};
use rowl_kernel::tableau::satisfiable;

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn atom(s: &[u8]) -> NnfConcept {
    NnfConcept::Atom(Class { iri: iri(s) })
}
fn no(s: &[u8]) -> NnfConcept {
    NnfConcept::NotAtom(Class { iri: iri(s) })
}
fn and(a: NnfConcept, b: NnfConcept) -> NnfConcept {
    NnfConcept::And(Box::new(a), Box::new(b))
}
fn or(a: NnfConcept, b: NnfConcept) -> NnfConcept {
    NnfConcept::Or(Box::new(a), Box::new(b))
}
fn some(r: &[u8], c: NnfConcept) -> NnfConcept {
    NnfConcept::Exists(ObjectProperty { iri: iri(r) }, Box::new(c))
}
fn all(r: &[u8], c: NnfConcept) -> NnfConcept {
    NnfConcept::Forall(ObjectProperty { iri: iri(r) }, Box::new(c))
}

#[test]
fn propositional_clashes_and_branches() {
    assert!(satisfiable(&atom(b"A")));
    assert!(satisfiable(&no(b"A")));
    assert!(satisfiable(&NnfConcept::Top));
    assert!(!satisfiable(&NnfConcept::Bottom));
    assert!(!satisfiable(&and(atom(b"A"), no(b"A"))));
    assert!(satisfiable(&or(atom(b"A"), no(b"A"))));
    assert!(!satisfiable(&and(
        or(atom(b"A"), atom(b"B")),
        and(no(b"A"), no(b"B"))
    )));
    assert!(satisfiable(&and(or(atom(b"A"), atom(b"B")), no(b"A"))));
    // Classes are compared by their exact spelling only.
    assert!(satisfiable(&and(atom(b"A"), no(b"a"))));
}

#[test]
fn restrictions_need_successors_for_existentials_only() {
    assert!(!satisfiable(&and(
        some(b"R", atom(b"A")),
        all(b"R", no(b"A"))
    )));
    assert!(satisfiable(&and(
        some(b"R", atom(b"A")),
        all(b"S", no(b"A"))
    )));
    assert!(satisfiable(&all(b"R", NnfConcept::Bottom)));
    assert!(!satisfiable(&some(b"R", NnfConcept::Bottom)));
    assert!(!satisfiable(&and(
        some(b"R", NnfConcept::Top),
        all(b"R", NnfConcept::Bottom)
    )));
    // Two successors, each meeting the shared universal restriction differently.
    assert!(satisfiable(&and(
        and(some(b"R", atom(b"A")), some(b"R", no(b"A"))),
        all(b"R", or(atom(b"A"), atom(b"B")))
    )));
}

#[test]
fn nested_restrictions_propagate_to_deeper_successors() {
    let deep = and(
        some(b"R", and(atom(b"A"), some(b"R", atom(b"B")))),
        all(b"R", all(b"R", no(b"B"))),
    );
    assert!(!satisfiable(&deep));
    // Only the branch that avoids the clash two levels down survives.
    let branching = and(
        some(b"R", some(b"R", atom(b"B"))),
        all(b"R", or(all(b"R", no(b"B")), atom(b"C"))),
    );
    assert!(satisfiable(&branching));
}

fn class(s: &[u8]) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(s) })
}
fn both(a: ClassExpression, b: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first: a,
        second: b,
        rest: Vec::new(),
    }))
}
fn exists(r: &[u8], c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Property(ObjectProperty { iri: iri(r) }),
        Box::new(c),
    )
}
/// `sub` is subsumed by `sup` exactly when `sub ⊓ ¬sup` is unsatisfiable.
fn subsumed(sub: ClassExpression, sup: ClassExpression) -> bool {
    let test = both(sub, ClassExpression::ObjectComplementOf(Box::new(sup)));
    !satisfiable(&nnf(&test, true).expect("ALC"))
}

#[test]
fn owl_subsumption_through_negation_normal_form() {
    assert!(subsumed(both(class(b"A"), class(b"B")), class(b"A")));
    assert!(!subsumed(class(b"A"), both(class(b"A"), class(b"B"))));
    assert!(subsumed(
        exists(b"R", both(class(b"A"), class(b"B"))),
        exists(b"R", class(b"A"))
    ));
    assert!(!subsumed(
        exists(b"R", class(b"A")),
        exists(b"S", class(b"A"))
    ));
    let nothing = class(b"http://www.w3.org/2002/07/owl#Nothing");
    let thing = class(b"http://www.w3.org/2002/07/owl#Thing");
    assert!(subsumed(nothing, class(b"A")));
    assert!(subsumed(class(b"A"), thing));
}

/// A finite interpretation with classes A, B and one role R.
struct Finite {
    size: usize,
    a: u32,
    b: u32,
    r: u32,
}
fn holds(i: &Finite, c: &NnfConcept, x: usize) -> bool {
    let class = |class: &Class, x: usize| match class.iri.spelling.as_slice() {
        b"A" => i.a >> x & 1 == 1,
        b"B" => i.b >> x & 1 == 1,
        _ => panic!("unknown test class"),
    };
    let edge = |x: usize, y: usize| i.r >> (x * i.size + y) & 1 == 1;
    match c {
        NnfConcept::Top => true,
        NnfConcept::Bottom => false,
        NnfConcept::Atom(a) => class(a, x),
        NnfConcept::NotAtom(a) => !class(a, x),
        NnfConcept::And(a, b) => holds(i, a, x) && holds(i, b, x),
        NnfConcept::Or(a, b) => holds(i, a, x) || holds(i, b, x),
        NnfConcept::Exists(_, c) => (0..i.size).any(|y| edge(x, y) && holds(i, c, y)),
        NnfConcept::Forall(_, c) => (0..i.size).all(|y| !edge(x, y) || holds(i, c, y)),
    }
}
fn small_model_exists(c: &NnfConcept) -> bool {
    (1..=3).any(|size| {
        (0..1u32 << size).any(|a| {
            (0..1u32 << size).any(|b| {
                (0..1u32 << (size * size)).any(|r| {
                    let i = Finite { size, a, b, r };
                    (0..size).any(|x| holds(&i, c, x))
                })
            })
        })
    })
}
/// A deterministic pseudo-random concept over A, B and R.
fn random_concept(seed: &mut u64, depth: u32) -> NnfConcept {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 6 } else { 10 };
    match choice {
        0 => atom(b"A"),
        1 => no(b"A"),
        2 => atom(b"B"),
        3 => no(b"B"),
        4 => NnfConcept::Top,
        5 => NnfConcept::Bottom,
        6 => and(
            random_concept(seed, depth - 1),
            random_concept(seed, depth - 1),
        ),
        7 => or(
            random_concept(seed, depth - 1),
            random_concept(seed, depth - 1),
        ),
        8 => some(b"R", random_concept(seed, depth - 1)),
        _ => all(b"R", random_concept(seed, depth - 1)),
    }
}

#[test]
fn every_concept_with_a_small_model_is_reported_satisfiable() {
    let mut seed = 7;
    let mut with_model = 0;
    for _ in 0..2000 {
        let c = random_concept(&mut seed, 3);
        if small_model_exists(&c) {
            assert!(
                satisfiable(&c),
                "a model exists, so the tableau must accept"
            );
            with_model += 1;
        }
    }
    assert!(
        with_model > 100,
        "the sample must exercise satisfiable concepts"
    );
}
