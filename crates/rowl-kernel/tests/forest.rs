use rowl_kernel::completion::{self, Definition, Fact, Link};
use rowl_kernel::concepts::Concept;
use rowl_kernel::forest::satisfiable;
use rowl_kernel::hierarchy::{Inclusion, RoleHierarchy};
use rowl_kernel::model::*;

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
fn at_least(n: usize, r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::AtLeast(n, r, Box::new(c))
}
fn at_most(n: usize, r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::AtMost(n, r, Box::new(c))
}
fn none() -> RoleHierarchy {
    RoleHierarchy {
        inclusions: Vec::new(),
        transitive: Vec::new(),
    }
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
/// Run a test body on a thread with a large stack: the search recurses once per
/// rule application, and debug builds use large frames.
fn with_stack(body: fn()) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(body)
        .expect("a test thread")
        .join()
        .expect("the test body passes");
}
fn r() -> ObjectPropertyExpression {
    named(b"r")
}
fn back() -> ObjectPropertyExpression {
    inverted(b"r")
}

#[test]
fn number_restrictions_bound_the_neighbours() {
    let top = || Concept::Top;
    let cases = [
        // Two successors in A, but at most one successor at all.
        (
            and(at_least(2, r(), atom(b"A")), at_most(1, r(), top())),
            false,
        ),
        (
            and(at_least(2, r(), atom(b"A")), at_most(1, r(), atom(b"A"))),
            false,
        ),
        // The two A-successors need not be in B.
        (
            and(at_least(2, r(), atom(b"A")), at_most(1, r(), atom(b"B"))),
            true,
        ),
        // Three successors, each in A or not, at most one of each kind.
        (
            and(
                at_least(3, r(), top()),
                and(at_most(1, r(), atom(b"A")), at_most(1, r(), no(b"A"))),
            ),
            false,
        ),
        // Two existential successors merge into one with both fillers...
        (
            and(
                and(some(r(), atom(b"A")), some(r(), atom(b"B"))),
                at_most(1, r(), top()),
            ),
            true,
        ),
        // ...unless the fillers contradict each other.
        (
            and(
                and(some(r(), atom(b"A")), some(r(), no(b"A"))),
                at_most(1, r(), top()),
            ),
            false,
        ),
        // No neighbour at all, but a required one.
        (and(some(r(), top()), at_most(0, r(), top())), false),
        (at_least(0, r(), Concept::Bottom), true),
        (at_least(1, r(), Concept::Bottom), false),
    ];
    for (concept, expected) in cases {
        assert_eq!(concept_sat(concept, &Concept::Top, &none()), Some(expected));
    }
}

#[test]
fn inverse_counting_merges_into_the_predecessor() {
    // An r-successor with exactly one r-predecessor, which must then be in A.
    let c = and(
        no(b"A"),
        some(
            r(),
            and(some(back(), atom(b"A")), at_most(1, back(), Concept::Top)),
        ),
    );
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(false));
    let c = and(
        atom(b"A"),
        some(
            r(),
            and(some(back(), atom(b"A")), at_most(1, back(), Concept::Top)),
        ),
    );
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(true));
}

#[test]
fn pairwise_blocking_admits_infinite_models() {
    // Every A has an A-successor and every element at most one predecessor, so
    // a chain from a non-A element never returns: only infinite models exist.
    let tbox = or(
        no(b"A"),
        and(some(r(), atom(b"A")), at_most(1, back(), Concept::Top)),
    );
    let tbox = and(tbox, at_most(1, back(), Concept::Top));
    let c = and(no(b"A"), some(r(), atom(b"A")));
    assert_eq!(concept_sat(c, &tbox, &none()), Some(true));
    // With a bound on the A-elements' successors that excludes the chain.
    let closed = and(tbox, or(no(b"A"), at_most(0, r(), atom(b"A"))));
    let c = and(no(b"A"), some(r(), atom(b"A")));
    assert_eq!(concept_sat(c, &closed, &none()), Some(false));
}

fn link(role: ObjectPropertyExpression, from: usize, to: usize) -> Link {
    Link { role, from, to }
}
fn fact(node: usize, concept: Concept) -> Fact {
    Fact { node, concept }
}
fn abox(count: usize, facts: Vec<Fact>, links: Vec<Link>, tbox: &Concept) -> Option<bool> {
    satisfiable(
        count,
        &Vec::new(),
        &facts,
        &links,
        tbox,
        &Vec::new(),
        &none(),
    )
}

#[test]
fn functional_roles_merge_named_individuals() {
    let functional = at_most(1, r(), Concept::Top);
    // a has two r-successors b and c, so they are the same: B and ¬B clash.
    let facts = vec![fact(1, atom(b"B")), fact(2, no(b"B"))];
    assert_eq!(
        abox(
            3,
            facts,
            vec![link(r(), 0, 1), link(r(), 0, 2)],
            &functional
        ),
        Some(false)
    );
    // Without the clash, b and c merge and stay consistent...
    let facts = vec![fact(1, atom(b"B"))];
    assert_eq!(
        abox(
            3,
            facts,
            vec![link(r(), 0, 1), link(r(), 0, 2)],
            &functional
        ),
        Some(true)
    );
    // ...and c is then necessarily in B.
    let facts = vec![fact(1, atom(b"B")), fact(2, no(b"B"))];
    assert_eq!(
        abox(
            3,
            facts,
            vec![link(r(), 0, 1), link(r(), 0, 2)],
            &Concept::Top
        ),
        Some(true)
    );
    // A successor that a functional role forces onto a named individual.
    let facts = vec![fact(0, some(r(), atom(b"C"))), fact(1, no(b"C"))];
    assert_eq!(
        abox(2, facts, vec![link(r(), 0, 1)], &functional),
        Some(false)
    );
    // Inverse functional: two r-predecessors of b are the same individual.
    let inverse_functional = at_most(1, back(), Concept::Top);
    let facts = vec![fact(0, atom(b"B")), fact(2, no(b"B"))];
    assert_eq!(
        abox(
            3,
            facts,
            vec![link(r(), 0, 1), link(r(), 2, 1)],
            &inverse_functional
        ),
        Some(false)
    );
}

#[test]
fn number_restrictions_need_simple_roles() {
    let transitive = RoleHierarchy {
        inclusions: Vec::new(),
        transitive: vec![r(), back()],
    };
    let c = at_most(1, r(), Concept::Top);
    assert_eq!(concept_sat(c, &Concept::Top, &transitive), None);
    // A role with a transitive subrole is not simple either.
    let below = RoleHierarchy {
        inclusions: vec![
            Inclusion {
                sub: named(b"t"),
                sup: r(),
            },
            Inclusion {
                sub: inverted(b"t"),
                sup: back(),
            },
        ],
        transitive: vec![named(b"t"), inverted(b"t")],
    };
    let c = at_least(2, back(), Concept::Top);
    assert_eq!(concept_sat(c, &Concept::Top, &below), None);
    // Existential restrictions on transitive roles stay supported.
    let c = some(r(), atom(b"A"));
    assert_eq!(concept_sat(c, &Concept::Top, &transitive), Some(true));
}

#[test]
fn many_merge_choices_are_searched() {
    // Five successors, pairwise able to merge, into at most two: some merges
    // must fail on A and ¬A before a combination fits.
    let c = and(
        and(
            and(some(r(), atom(b"A")), some(r(), no(b"A"))),
            and(some(r(), atom(b"B")), some(r(), no(b"B"))),
        ),
        and(
            some(r(), and(atom(b"A"), atom(b"B"))),
            at_most(2, r(), Concept::Top),
        ),
    );
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(true));
    let c = and(
        and(
            and(some(r(), atom(b"A")), some(r(), no(b"A"))),
            and(some(r(), atom(b"B")), some(r(), no(b"B"))),
        ),
        and(
            some(r(), and(atom(b"A"), no(b"B"))),
            and(
                some(r(), and(no(b"A"), atom(b"B"))),
                at_most(2, r(), Concept::Top),
            ),
        ),
    );
    // The six successors need A∧¬B, ¬A∧B, and one of each of A, ¬A, B, ¬B:
    // two elements A∧¬B and ¬A∧B cover all of them.
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(true));
    let c = and(
        and(
            some(r(), and(atom(b"A"), atom(b"B"))),
            some(r(), and(no(b"A"), no(b"B"))),
        ),
        and(
            some(r(), and(atom(b"A"), no(b"B"))),
            at_most(2, r(), Concept::Top),
        ),
    );
    assert_eq!(concept_sat(c, &Concept::Top, &none()), Some(false));
}

/// A deterministic pseudo-random concept over A, B, r and its inverse, with
/// cardinality restrictions when `counting`.
fn random_concept(seed: &mut u64, depth: u32, counting: bool) -> Concept {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let kinds = if depth == 0 {
        5
    } else if counting {
        15
    } else {
        11
    };
    let choice = (*seed >> 33) % kinds;
    let role = if (*seed >> 40).is_multiple_of(2) {
        r()
    } else {
        back()
    };
    let n = ((*seed >> 44) % 3) as usize;
    match choice {
        0 => atom(b"A"),
        1 => no(b"A"),
        2 => atom(b"B"),
        3 => no(b"B"),
        4 => Concept::Top,
        5 => and(
            random_concept(seed, depth - 1, counting),
            random_concept(seed, depth - 1, counting),
        ),
        6 => or(
            random_concept(seed, depth - 1, counting),
            random_concept(seed, depth - 1, counting),
        ),
        7 | 8 => some(role, random_concept(seed, depth - 1, counting)),
        9 | 10 => all(role, random_concept(seed, depth - 1, counting)),
        11 | 12 => at_least(n + 1, role, random_concept(seed, depth - 1, counting)),
        _ => at_most(n, role, random_concept(seed, depth - 1, counting)),
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
    let count = |role: &ObjectPropertyExpression, c: &Concept| {
        (0..i.size)
            .filter(|&y| edge(role, x, y) && holds(i, c, y))
            .count()
    };
    match c {
        Concept::Top => true,
        Concept::Bottom => false,
        Concept::Atom(a) => class(a, x),
        Concept::NotAtom(a) => !class(a, x),
        Concept::And(a, b) => holds(i, a, x) && holds(i, b, x),
        Concept::Or(a, b) => holds(i, a, x) || holds(i, b, x),
        Concept::Exists(r, c) => count(r, c) >= 1,
        Concept::Forall(r, c) => (0..i.size).all(|y| !edge(r, x, y) || holds(i, c, y)),
        Concept::AtLeast(n, r, c) => count(r, c) >= *n,
        Concept::AtMost(n, r, c) => count(r, c) <= *n,
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
fn counting_free_inputs_agree_with_the_completion_graph() {
    with_stack(counting_free_inputs_agree_with_the_completion_graph_body);
}
fn counting_free_inputs_agree_with_the_completion_graph_body() {
    let mut seed = 61;
    let mut rejected = 0;
    for _ in 0..400 {
        let c = random_concept(&mut seed, 3, false);
        let tbox = random_concept(&mut seed, 1, false);
        let old = completion::satisfiable(
            1,
            &vec![Fact {
                node: 0,
                concept: copy(&c),
            }],
            &Vec::new(),
            &Vec::new(),
            &tbox,
            &Vec::<Definition>::new(),
            &none(),
        );
        let new = concept_sat(c, &tbox, &none());
        assert_eq!(new, old, "the tableaux disagree");
        if new == Some(false) {
            rejected += 1;
        }
    }
    assert!(rejected > 20, "the sample must exercise rejections");
}

#[test]
fn every_counting_concept_with_a_small_model_is_accepted() {
    with_stack(every_counting_concept_with_a_small_model_is_accepted_body);
}
fn every_counting_concept_with_a_small_model_is_accepted_body() {
    let mut seed = 67;
    let mut with_model = 0;
    let mut rejected = 0;
    for _ in 0..400 {
        let c = random_concept(&mut seed, 3, true);
        let tbox = random_concept(&mut seed, 1, true);
        let small = small_model_exists(&c, &tbox);
        let answer = concept_sat(c, &tbox, &none());
        if small {
            assert_eq!(
                answer,
                Some(true),
                "a model exists, so the forest must accept"
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

/// Whether some interpretation of at most three elements satisfies the TBox
/// everywhere and the facts and links at the elements of three individuals,
/// which need not be different.
fn small_abox_model(facts: &[Fact], links: &[Link], tbox: &Concept) -> bool {
    (1..=3usize).any(|size| {
        (0..1u32 << size).any(|a| {
            (0..1u32 << size).any(|b| {
                (0..1u32 << (size * size)).any(|r| {
                    let i = Finite { size, a, b, r };
                    if !(0..size).all(|x| holds(&i, tbox, x)) {
                        return false;
                    }
                    (0..size.pow(3)).any(|code| {
                        let place = [code % size, code / size % size, code / size / size % size];
                        facts.iter().all(|f| holds(&i, &f.concept, place[f.node]))
                            && links.iter().all(|l| {
                                let (x, y) = (place[l.from], place[l.to]);
                                match &l.role {
                                    ObjectPropertyExpression::Property(_) => {
                                        i.r >> (x * size + y) & 1 == 1
                                    }
                                    ObjectPropertyExpression::Inverse(_) => {
                                        i.r >> (y * size + x) & 1 == 1
                                    }
                                }
                            })
                    })
                })
            })
        })
    })
}

#[test]
fn every_abox_with_a_small_model_is_accepted() {
    with_stack(every_abox_with_a_small_model_is_accepted_body);
}
fn every_abox_with_a_small_model_is_accepted_body() {
    let mut seed = 71;
    let mut with_model = 0;
    let mut rejected = 0;
    for _ in 0..300 {
        let tbox = random_concept(&mut seed, 1, true);
        let facts: Vec<Fact> = (0..3)
            .map(|node| fact(node, random_concept(&mut seed, 2, true)))
            .collect();
        let mut links = Vec::new();
        for _ in 0..3 {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let role = if (seed >> 40).is_multiple_of(2) {
                r()
            } else {
                back()
            };
            links.push(link(
                role,
                ((seed >> 33) % 3) as usize,
                ((seed >> 36) % 3) as usize,
            ));
        }
        let small = small_abox_model(&facts, &links, &tbox);
        let copies: Vec<Fact> = facts
            .iter()
            .map(|f| fact(f.node, copy(&f.concept)))
            .collect();
        let answer = abox(3, copies, links, &tbox);
        if small {
            assert_eq!(
                answer,
                Some(true),
                "a model exists, so the forest must accept"
            );
            with_model += 1;
        }
        if answer == Some(false) {
            rejected += 1;
        }
    }
    assert!(
        with_model > 50,
        "the sample must exercise consistent inputs"
    );
    assert!(
        rejected > 20,
        "the sample must exercise inconsistent inputs"
    );
}

fn copy(c: &Concept) -> Concept {
    match c {
        Concept::Top => Concept::Top,
        Concept::Bottom => Concept::Bottom,
        Concept::Atom(a) => Concept::Atom(class(&a.iri.spelling)),
        Concept::NotAtom(a) => Concept::NotAtom(class(&a.iri.spelling)),
        Concept::And(a, b) => and(copy(a), copy(b)),
        Concept::Or(a, b) => or(copy(a), copy(b)),
        Concept::Exists(r, c) => some(role_copy(r), copy(c)),
        Concept::Forall(r, c) => all(role_copy(r), copy(c)),
        Concept::AtLeast(n, r, c) => at_least(*n, role_copy(r), copy(c)),
        Concept::AtMost(n, r, c) => at_most(*n, role_copy(r), copy(c)),
    }
}
fn role_copy(role: &ObjectPropertyExpression) -> ObjectPropertyExpression {
    match role {
        ObjectPropertyExpression::Property(p) => named(&p.iri.spelling),
        ObjectPropertyExpression::Inverse(p) => inverted(&p.iri.spelling),
    }
}
