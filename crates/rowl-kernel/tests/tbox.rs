use rowl_kernel::model::*;
use rowl_kernel::nnf::NnfConcept;
use rowl_kernel::tableau::satisfiable;
use rowl_kernel::tbox::satisfiable_in;

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
/// The TBox concept of `sub ⊑ sup` for a named class `sub`.
fn below(sub: &[u8], sup: NnfConcept) -> NnfConcept {
    or(no(sub), sup)
}

#[test]
fn cyclic_axioms_terminate_through_blocking() {
    // A ⊑ ∃R.A needs an infinite chain; blocking reuses the first A element.
    let tbox = below(b"A", some(b"R", atom(b"A")));
    assert!(satisfiable_in(&atom(b"A"), &tbox));
    // Two mutually generating classes.
    let tbox = and(
        below(b"A", some(b"R", atom(b"B"))),
        below(b"B", some(b"S", atom(b"A"))),
    );
    assert!(satisfiable_in(&atom(b"A"), &tbox));
    assert!(satisfiable_in(&and(atom(b"A"), atom(b"B")), &tbox));
}

#[test]
fn axioms_propagate_to_every_element() {
    // A ⊑ ∃R.B and B ⊑ ⊥ make A unsatisfiable, but not ¬A.
    let tbox = and(
        below(b"A", some(b"R", atom(b"B"))),
        below(b"B", NnfConcept::Bottom),
    );
    assert!(!satisfiable_in(&atom(b"A"), &tbox));
    assert!(satisfiable_in(&no(b"A"), &tbox));
    // A ⊑ B and B ⊑ C entail A ⊑ C.
    let chain = and(below(b"A", atom(b"B")), below(b"B", atom(b"C")));
    assert!(!satisfiable_in(&and(atom(b"A"), no(b"C")), &chain));
    assert!(satisfiable_in(&and(atom(b"C"), no(b"A")), &chain));
    // A cycle that clashes: A ⊑ ∃R.A ⊓ ∀R.¬A.
    let tbox = below(b"A", and(some(b"R", atom(b"A")), all(b"R", no(b"A"))));
    assert!(!satisfiable_in(&atom(b"A"), &tbox));
    // A range restriction ⊤ ⊑ ∀R.B meets A ⊑ ∃R.¬B.
    let tbox = and(all(b"R", atom(b"B")), below(b"A", some(b"R", no(b"B"))));
    assert!(!satisfiable_in(&atom(b"A"), &tbox));
    assert!(satisfiable_in(&some(b"R", atom(b"B")), &tbox));
    // An unsatisfiable TBox admits nothing at all.
    assert!(!satisfiable_in(&NnfConcept::Top, &NnfConcept::Bottom));
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
fn a_top_tbox_agrees_with_the_plain_tableau() {
    let mut seed = 11;
    for _ in 0..1000 {
        let c = random_concept(&mut seed, 4);
        assert_eq!(satisfiable_in(&c, &NnfConcept::Top), satisfiable(&c));
    }
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
fn small_model_exists(c: &NnfConcept, tbox: &NnfConcept) -> bool {
    (1..=3).any(|size| {
        (0..1u32 << size).any(|a| {
            (0..1u32 << size).any(|b| {
                (0..1u32 << (size * size)).any(|r| {
                    let i = Finite { size, a, b, r };
                    (0..size).all(|x| holds(&i, tbox, x)) && (0..size).any(|x| holds(&i, c, x))
                })
            })
        })
    })
}

#[test]
fn every_concept_with_a_small_model_of_the_tbox_is_accepted() {
    let mut seed = 23;
    let mut with_model = 0;
    for _ in 0..600 {
        let c = random_concept(&mut seed, 2);
        let tbox = random_concept(&mut seed, 2);
        if small_model_exists(&c, &tbox) {
            assert!(
                satisfiable_in(&c, &tbox),
                "a model exists, so the tableau must accept"
            );
            with_model += 1;
        }
    }
    assert!(
        with_model > 50,
        "the sample must exercise satisfiable inputs"
    );
}
