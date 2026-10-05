use rowl_kernel::completion::{base, satisfiable, satisfiable_from, Definition, Fact, Link};
use rowl_kernel::concepts::Concept;
use rowl_kernel::hierarchy::{Inclusion, RoleHierarchy};
use rowl_kernel::model::*;
use rowl_kernel::nnf::NnfConcept;
use rowl_kernel::role_box::{RoleBox, RoleInclusion};
use rowl_kernel::tbox::satisfiable_with;

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn class(s: &[u8]) -> Class {
    Class { iri: iri(s) }
}
fn atom(s: &[u8]) -> Concept {
    Concept::Atom(class(s))
}
fn no(s: &[u8]) -> Concept {
    Concept::NotAtom(class(s))
}
fn and(a: Concept, b: Concept) -> Concept {
    Concept::And(Box::new(a), Box::new(b))
}
fn or(a: Concept, b: Concept) -> Concept {
    Concept::Or(Box::new(a), Box::new(b))
}
fn named(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(s) })
}
fn inverted(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(s) })
}
fn some(r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::Exists(r, Box::new(c))
}
fn all(r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::Forall(r, Box::new(c))
}
fn flip(r: &ObjectPropertyExpression) -> ObjectPropertyExpression {
    match r {
        ObjectPropertyExpression::Property(p) => {
            ObjectPropertyExpression::Inverse(ObjectProperty {
                iri: iri(&p.iri.spelling),
            })
        }
        ObjectPropertyExpression::Inverse(p) => {
            ObjectPropertyExpression::Property(ObjectProperty {
                iri: iri(&p.iri.spelling),
            })
        }
    }
}
/// A closed hierarchy: every inclusion with its inverse, every transitive role
/// with its inverse. The given inclusions must already include compositions.
fn hierarchy(
    inclusions: &[(ObjectPropertyExpression, ObjectPropertyExpression)],
    transitive: &[ObjectPropertyExpression],
) -> RoleHierarchy {
    let mut all_inclusions = Vec::new();
    for (sub, sup) in inclusions {
        all_inclusions.push(Inclusion {
            sub: flip(&flip(sub)),
            sup: flip(&flip(sup)),
        });
        all_inclusions.push(Inclusion {
            sub: flip(sub),
            sup: flip(sup),
        });
    }
    let mut all_transitive = Vec::new();
    for t in transitive {
        all_transitive.push(flip(&flip(t)));
        all_transitive.push(flip(t));
    }
    RoleHierarchy {
        inclusions: all_inclusions,
        transitive: all_transitive,
        disjoint: Vec::new(),
    }
}
fn none() -> RoleHierarchy {
    hierarchy(&[], &[])
}
/// Satisfiability of one concept under a TBox concept and role axioms.
fn concept_sat(c: Concept, tbox: &Concept, roles: &RoleHierarchy) -> Option<bool> {
    satisfiable(
        1,
        &vec![Fact {
            node: 0,
            concept: c,
        }],
        &Vec::new(),
        &Vec::new(),
        tbox,
        &Vec::new(),
        roles,
    )
}

#[test]
fn inverse_roles_reach_back_to_the_predecessor() {
    let r = || named(b"r");
    let back = || inverted(b"r");
    // A successor that rules out A for its predecessors contradicts A.
    let c = and(atom(b"A"), some(r(), all(back(), no(b"A"))));
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(false));
    // Without A at the root it is satisfiable.
    let c = some(r(), all(back(), no(b"A")));
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(true));
    // ∃r.⊤ ⊓ ∀r.∀r⁻.B forces B at the root.
    let c = and(
        and(some(r(), Concept::Top), all(r(), all(back(), atom(b"B")))),
        no(b"B"),
    );
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(false));
    // ∃r⁻.A is an r-predecessor in A.
    let c = and(some(back(), atom(b"A")), all(back(), no(b"A")));
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(false));
}

#[test]
fn transitive_inverse_roles_carry_restrictions_up_paths() {
    let t = || named(b"t");
    let up = || inverted(b"t");
    // Two t-steps below an A-element, ∀t⁻.¬A reaches it when t is transitive.
    let c = and(atom(b"A"), some(t(), some(t(), all(up(), no(b"A")))));
    assert_eq!(
        concept_sat(c, &Concept::Top, &hierarchy(&[], &[t()])),
        Some(false)
    );
    let c = and(atom(b"A"), some(t(), some(t(), all(up(), no(b"A")))));
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(true));
    // A sub-role of a transitive role: s ⊑ t, s-successors of s-successors are t-successors.
    let s = || named(b"s");
    let roles = hierarchy(&[(s(), t())], &[t()]);
    let c = and(atom(b"A"), some(s(), some(s(), all(up(), no(b"A")))));
    assert_eq!(concept_sat(c, &Concept::Top, &roles), Some(false));
}

#[test]
fn cycles_through_inverse_roles_terminate_by_blocking() {
    let r = || named(b"r");
    // Every element has an r-successor in A whose r-predecessors are in B.
    let tbox = some(r(), and(atom(b"A"), all(inverted(b"r"), atom(b"B"))));
    assert_eq!(concept_sat(atom(b"A"), &tbox, &none()), Some(true));
    // ... and nothing in B may exist.
    let tbox = and(tbox, no(b"B"));
    assert_eq!(concept_sat(Concept::Top, &tbox, &none()), Some(false));
}

#[test]
fn definitions_unfold_only_where_their_class_holds() {
    let definitions = vec![Definition {
        class: class(b"Amoxicillin"),
        concept: atom(b"Penicillin"),
    }];
    let fact = |c: Concept| {
        vec![Fact {
            node: 0,
            concept: c,
        }]
    };
    let decide = |c: Concept| {
        satisfiable(
            1,
            &fact(c),
            &Vec::new(),
            &Vec::new(),
            &Concept::Top,
            &definitions,
            &none(),
        )
    };
    assert_eq!(
        decide(and(atom(b"Amoxicillin"), no(b"Penicillin"))),
        Some(false)
    );
    assert_eq!(decide(no(b"Penicillin")), Some(true));
    // The unfolding reaches anonymous successors too.
    let r = named(b"contains");
    assert_eq!(
        decide(and(
            some(r.clone_role(), atom(b"Amoxicillin")),
            all(r, no(b"Penicillin"))
        )),
        Some(false)
    );
}

trait CloneRole {
    fn clone_role(&self) -> ObjectPropertyExpression;
}
impl CloneRole for ObjectPropertyExpression {
    fn clone_role(&self) -> ObjectPropertyExpression {
        flip(&flip(self))
    }
}

#[test]
fn named_individuals_constrain_each_other_through_inverse_links() {
    let r = named(b"r");
    // r(a, b), b ∈ ∀r⁻.C, a ∈ ¬C.
    let links = || {
        vec![Link {
            role: r.clone_role(),
            from: 0,
            to: 1,
        }]
    };
    let facts = vec![
        Fact {
            node: 1,
            concept: all(inverted(b"r"), atom(b"C")),
        },
        Fact {
            node: 0,
            concept: no(b"C"),
        },
    ];
    let decide = |facts: &Vec<Fact>, links: Vec<Link>| {
        satisfiable(
            2,
            &Vec::new(),
            facts,
            &links,
            &Concept::Top,
            &Vec::new(),
            &none(),
        )
    };
    assert_eq!(decide(&facts, links()), Some(false));
    assert_eq!(decide(&facts, Vec::new()), Some(true));
    // An inverse link is the same edge reversed.
    let reversed = vec![Link {
        role: inverted(b"r"),
        from: 1,
        to: 0,
    }];
    assert_eq!(decide(&facts, reversed), Some(false));
}

/// The inverse-free concepts of the earlier tableaux, as concepts with roles.
fn lift(c: &NnfConcept) -> Concept {
    match c {
        NnfConcept::Top => Concept::Top,
        NnfConcept::Bottom => Concept::Bottom,
        NnfConcept::Atom(a) => Concept::Atom(class(&a.iri.spelling)),
        NnfConcept::NotAtom(a) => Concept::NotAtom(class(&a.iri.spelling)),
        NnfConcept::And(a, b) => and(lift(a), lift(b)),
        NnfConcept::Or(a, b) => or(lift(a), lift(b)),
        NnfConcept::Exists(r, c) => some(named(&r.iri.spelling), lift(c)),
        NnfConcept::Forall(r, c) => all(named(&r.iri.spelling), lift(c)),
    }
}
fn nnf_atom(s: &[u8]) -> NnfConcept {
    NnfConcept::Atom(class(s))
}
fn nnf_no(s: &[u8]) -> NnfConcept {
    NnfConcept::NotAtom(class(s))
}
/// A deterministic pseudo-random inverse-free concept over A, B, s and t.
fn random_sh(seed: &mut u64, depth: u32) -> NnfConcept {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 5 } else { 11 };
    let role = |s: &[u8]| ObjectProperty { iri: iri(s) };
    match choice {
        0 => nnf_atom(b"A"),
        1 => nnf_no(b"A"),
        2 => nnf_atom(b"B"),
        3 => nnf_no(b"B"),
        4 => NnfConcept::Top,
        5 => NnfConcept::And(
            Box::new(random_sh(seed, depth - 1)),
            Box::new(random_sh(seed, depth - 1)),
        ),
        6 => NnfConcept::Or(
            Box::new(random_sh(seed, depth - 1)),
            Box::new(random_sh(seed, depth - 1)),
        ),
        7 => NnfConcept::Exists(role(b"s"), Box::new(random_sh(seed, depth - 1))),
        8 => NnfConcept::Exists(role(b"t"), Box::new(random_sh(seed, depth - 1))),
        9 => NnfConcept::Forall(role(b"s"), Box::new(random_sh(seed, depth - 1))),
        _ => NnfConcept::Forall(role(b"t"), Box::new(random_sh(seed, depth - 1))),
    }
}

#[test]
fn inverse_free_inputs_agree_with_the_sh_tableau() {
    let old_roles = RoleBox {
        inclusions: vec![RoleInclusion {
            sub: ObjectProperty { iri: iri(b"s") },
            sup: ObjectProperty { iri: iri(b"t") },
        }],
        transitive: vec![ObjectProperty { iri: iri(b"t") }],
    };
    let new_roles = hierarchy(&[(named(b"s"), named(b"t"))], &[named(b"t")]);
    let mut seed = 41;
    let mut rejected = 0;
    for _ in 0..400 {
        let c = random_sh(&mut seed, 3);
        let tbox = random_sh(&mut seed, 1);
        let old = satisfiable_with(&c, &tbox, &old_roles);
        let new = concept_sat(lift(&c), &lift(&tbox), &new_roles);
        assert_eq!(new, Some(old), "the two tableaux disagree");
        if !old {
            rejected += 1;
        }
    }
    assert!(rejected > 20, "the sample must exercise rejections");
}

/// A deterministic pseudo-random concept over A, B, r and its inverse.
fn random_alci(seed: &mut u64, depth: u32) -> Concept {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 5 } else { 11 };
    match choice {
        0 => atom(b"A"),
        1 => no(b"A"),
        2 => atom(b"B"),
        3 => no(b"B"),
        4 => Concept::Top,
        5 => and(random_alci(seed, depth - 1), random_alci(seed, depth - 1)),
        6 => or(random_alci(seed, depth - 1), random_alci(seed, depth - 1)),
        7 => some(named(b"r"), random_alci(seed, depth - 1)),
        8 => some(inverted(b"r"), random_alci(seed, depth - 1)),
        9 => all(named(b"r"), random_alci(seed, depth - 1)),
        _ => all(inverted(b"r"), random_alci(seed, depth - 1)),
    }
}
/// A finite interpretation with classes A, B and the relation r.
struct Finite {
    size: usize,
    a: u32,
    b: u32,
    r: u32,
}
fn holds(i: &Finite, c: &Concept, x: usize) -> bool {
    let class = |class: &Class, x: usize| match class.iri.spelling.as_slice() {
        b"A" => i.a >> x & 1 == 1,
        b"B" => i.b >> x & 1 == 1,
        _ => panic!("unknown test class"),
    };
    let edge = |role: &ObjectPropertyExpression, x: usize, y: usize| match role {
        ObjectPropertyExpression::Property(_) => i.r >> (x * i.size + y) & 1 == 1,
        ObjectPropertyExpression::Inverse(_) => i.r >> (y * i.size + x) & 1 == 1,
    };
    match c {
        Concept::Top => true,
        Concept::Bottom => false,
        Concept::Atom(a) => class(a, x),
        Concept::NotAtom(a) => !class(a, x),
        Concept::One(_) | Concept::NotOne(_) => panic!("the samples have no nominals"),
        Concept::HasSelf(r) => edge(r, x, x),
        Concept::NotSelf(r) => !edge(r, x, x),
        Concept::And(a, b) => holds(i, a, x) && holds(i, b, x),
        Concept::Or(a, b) => holds(i, a, x) || holds(i, b, x),
        Concept::Exists(r, c) => (0..i.size).any(|y| edge(r, x, y) && holds(i, c, y)),
        Concept::Forall(r, c) => (0..i.size).all(|y| !edge(r, x, y) || holds(i, c, y)),
        Concept::AtLeast(n, r, c) => {
            (0..i.size)
                .filter(|&y| edge(r, x, y) && holds(i, c, y))
                .count()
                >= *n
        }
        Concept::AtMost(n, r, c) => {
            (0..i.size)
                .filter(|&y| edge(r, x, y) && holds(i, c, y))
                .count()
                <= *n
        }
    }
}
fn small_model_exists(c: &Concept, tbox: &Concept) -> bool {
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
fn every_concept_with_a_small_model_is_accepted_and_inverse_roles_reject() {
    let mut seed = 53;
    let mut with_model = 0;
    let mut rejected = 0;
    for _ in 0..400 {
        let c = random_alci(&mut seed, 3);
        let tbox = random_alci(&mut seed, 1);
        let small = small_model_exists(&c, &tbox);
        let answer = concept_sat(c, &tbox, &none());
        if small {
            assert_eq!(
                answer,
                Some(true),
                "a model exists, so the tableau must accept"
            );
            with_model += 1;
        }
        if answer == Some(false) {
            rejected += 1;
        }
    }
    assert!(
        with_model > 50,
        "the sample must exercise satisfiable inputs"
    );
    assert!(rejected > 20, "the sample must exercise rejections");
}

#[test]
fn cardinality_restrictions_are_not_answered() {
    // This tableau does not count: a cardinality restriction it would add to a
    // label gives no answer.
    let c = Concept::AtMost(1, named(b"r"), Box::new(atom(b"A")));
    assert_eq!(concept_sat(c, &Concept::Top, &none()), None);
    let c = and(atom(b"A"), no(b"A"));
    let tbox = Concept::AtLeast(2, named(b"r"), Box::new(Concept::Top));
    // A clash found before the restriction is added still answers.
    assert_eq!(concept_sat(c, &tbox, &none()), Some(false));
}

#[test]
fn queries_on_a_prepared_base_answer_like_fresh_tables() {
    let mut seed = 71;
    let mut answered = 0;
    for _ in 0..300 {
        let query = random_alci(&mut seed, 3);
        let tbox = random_alci(&mut seed, 1);
        let fact = random_alci(&mut seed, 1);
        let definition = Definition {
            class: class(b"B"),
            concept: random_alci(&mut seed, 2),
        };
        let facts = vec![Fact {
            node: 1,
            concept: fact,
        }];
        let definitions = vec![definition];
        let links = vec![Link {
            role: named(b"r"),
            from: 0,
            to: 1,
        }];
        let queries = vec![Fact {
            node: 0,
            concept: query,
        }];
        let roles = none();
        let fresh = satisfiable(2, &queries, &facts, &links, &tbox, &definitions, &roles);
        let prepared = base(&facts, &tbox, &definitions, &roles).expect("a small base fits");
        let reused = satisfiable_from(&prepared, 2, &queries, &links, &roles);
        assert_eq!(fresh, reused);
        if fresh.is_some() {
            answered += 1;
        }
    }
    assert!(answered > 200, "the sample must be answered");
}
