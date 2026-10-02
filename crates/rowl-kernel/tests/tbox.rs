use rowl_kernel::model::*;
use rowl_kernel::nnf::NnfConcept;
use rowl_kernel::role_box::{RoleBox, RoleInclusion};
use rowl_kernel::tableau::satisfiable;
use rowl_kernel::tbox::{satisfiable_in, satisfiable_with};

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

fn property(s: &[u8]) -> ObjectProperty {
    ObjectProperty { iri: iri(s) }
}
/// Role axioms from inclusions, which the caller closes under composition, and
/// transitive properties.
fn roles(inclusions: &[(&[u8], &[u8])], transitive: &[&[u8]]) -> RoleBox {
    RoleBox {
        inclusions: inclusions
            .iter()
            .map(|(sub, sup)| RoleInclusion {
                sub: property(sub),
                sup: property(sup),
            })
            .collect(),
        transitive: transitive.iter().map(|t| property(t)).collect(),
    }
}

#[test]
fn universal_restrictions_reach_successors_along_included_properties() {
    let c = and(some(b"s", atom(b"A")), all(b"r", no(b"A")));
    assert!(!satisfiable_with(
        &c,
        &NnfConcept::Top,
        &roles(&[(b"s", b"r")], &[])
    ));
    assert!(satisfiable_with(&c, &NnfConcept::Top, &roles(&[], &[])));
    // An inclusion has a direction.
    assert!(satisfiable_with(
        &c,
        &NnfConcept::Top,
        &roles(&[(b"r", b"s")], &[])
    ));
    // Without role axioms the procedure agrees with the plain TBox tableau.
    let tbox = below(b"A", some(b"s", atom(b"A")));
    assert_eq!(
        satisfiable_with(&atom(b"A"), &tbox, &roles(&[], &[])),
        satisfiable_in(&atom(b"A"), &tbox)
    );
}

#[test]
fn transitive_properties_carry_universal_restrictions_along_paths() {
    let c = and(some(b"t", some(b"t", atom(b"A"))), all(b"t", no(b"A")));
    assert!(!satisfiable_with(
        &c,
        &NnfConcept::Top,
        &roles(&[], &[b"t"])
    ));
    assert!(satisfiable_with(&c, &NnfConcept::Top, &roles(&[], &[])));
    // Two steps along a sub-property of a transitive t reach every super-property of t.
    let closed = [(&b"s"[..], &b"t"[..]), (b"t", b"r"), (b"s", b"r")];
    let c = and(some(b"s", some(b"s", atom(b"A"))), all(b"r", no(b"A")));
    assert!(!satisfiable_with(
        &c,
        &NnfConcept::Top,
        &roles(&closed, &[b"t"])
    ));
    assert!(satisfiable_with(&c, &NnfConcept::Top, &roles(&closed, &[])));
    // Steps along r itself stay single steps: r is not transitive.
    let c = and(some(b"r", some(b"r", atom(b"A"))), all(b"r", no(b"A")));
    assert!(satisfiable_with(
        &c,
        &NnfConcept::Top,
        &roles(&closed, &[b"t"])
    ));
}

#[test]
fn blocked_nodes_keep_the_restrictions_of_transitive_properties() {
    // Every A has a t-successor in A and one in C; every C has one outside B.
    let tbox = and(
        and(
            below(b"A", some(b"t", atom(b"A"))),
            below(b"A", some(b"t", atom(b"C"))),
        ),
        below(b"C", some(b"t", no(b"B"))),
    );
    let c = and(atom(b"A"), all(b"t", atom(b"B")));
    assert!(!satisfiable_with(&c, &tbox, &roles(&[], &[b"t"])));
    assert!(satisfiable_with(&c, &tbox, &roles(&[], &[])));
    assert!(satisfiable_with(&atom(b"A"), &tbox, &roles(&[], &[b"t"])));
}

/// A deterministic pseudo-random concept over A, B and the properties s and t.
fn random_sh_concept(seed: &mut u64, depth: u32) -> NnfConcept {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 5 } else { 11 };
    match choice {
        0 => atom(b"A"),
        1 => no(b"A"),
        2 => atom(b"B"),
        3 => no(b"B"),
        4 => NnfConcept::Top,
        5 => and(
            random_sh_concept(seed, depth - 1),
            random_sh_concept(seed, depth - 1),
        ),
        6 => or(
            random_sh_concept(seed, depth - 1),
            random_sh_concept(seed, depth - 1),
        ),
        7 => some(b"s", random_sh_concept(seed, depth - 1)),
        8 => some(b"t", random_sh_concept(seed, depth - 1)),
        9 => all(b"s", random_sh_concept(seed, depth - 1)),
        _ => all(b"t", random_sh_concept(seed, depth - 1)),
    }
}
/// A finite interpretation with classes A, B and properties s and t.
struct FiniteSh {
    size: usize,
    a: u32,
    b: u32,
    s: u32,
    t: u32,
}
fn holds_sh(i: &FiniteSh, c: &NnfConcept, x: usize) -> bool {
    let class = |class: &Class, x: usize| match class.iri.spelling.as_slice() {
        b"A" => i.a >> x & 1 == 1,
        b"B" => i.b >> x & 1 == 1,
        _ => panic!("unknown test class"),
    };
    let edge = |role: &ObjectProperty, x: usize, y: usize| {
        let relation = match role.iri.spelling.as_slice() {
            b"s" => i.s,
            b"t" => i.t,
            _ => panic!("unknown test property"),
        };
        relation >> (x * i.size + y) & 1 == 1
    };
    match c {
        NnfConcept::Top => true,
        NnfConcept::Bottom => false,
        NnfConcept::Atom(a) => class(a, x),
        NnfConcept::NotAtom(a) => !class(a, x),
        NnfConcept::And(a, b) => holds_sh(i, a, x) && holds_sh(i, b, x),
        NnfConcept::Or(a, b) => holds_sh(i, a, x) || holds_sh(i, b, x),
        NnfConcept::Exists(r, c) => (0..i.size).any(|y| edge(r, x, y) && holds_sh(i, c, y)),
        NnfConcept::Forall(r, c) => (0..i.size).all(|y| !edge(r, x, y) || holds_sh(i, c, y)),
    }
}
fn transitive(relation: u32, size: usize) -> bool {
    let edge = |x: usize, y: usize| relation >> (x * size + y) & 1 == 1;
    (0..size)
        .all(|x| (0..size).all(|y| (0..size).all(|z| !(edge(x, y) && edge(y, z)) || edge(x, z))))
}
/// Some interpretation with at most three elements in which s is included in t
/// and t is transitive satisfies the TBox everywhere and the concept somewhere.
fn small_sh_model_exists(c: &NnfConcept, tbox: &NnfConcept) -> bool {
    (1..=3).any(|size| {
        let relations = 1u32 << (size * size);
        (0..relations).filter(|&t| transitive(t, size)).any(|t| {
            (0..relations).filter(|&s| s & !t == 0).any(|s| {
                (0..1u32 << size).any(|a| {
                    (0..1u32 << size).any(|b| {
                        let i = FiniteSh { size, a, b, s, t };
                        (0..size).all(|x| holds_sh(&i, tbox, x))
                            && (0..size).any(|x| holds_sh(&i, c, x))
                    })
                })
            })
        })
    })
}

#[test]
fn every_concept_with_a_small_model_of_the_role_axioms_is_accepted() {
    let axioms = roles(&[(b"s", b"t")], &[b"t"]);
    let mut seed = 31;
    let mut with_model = 0;
    let mut rejected = 0;
    for _ in 0..300 {
        let c = random_sh_concept(&mut seed, 3);
        let tbox = random_sh_concept(&mut seed, 1);
        let accepted = satisfiable_with(&c, &tbox, &axioms);
        if small_sh_model_exists(&c, &tbox) {
            assert!(accepted, "a model exists, so the tableau must accept");
            with_model += 1;
        }
        if !accepted {
            rejected += 1;
        }
    }
    assert!(
        with_model > 50,
        "the sample must exercise satisfiable inputs"
    );
    assert!(rejected > 10, "the sample must exercise rejections");
}
