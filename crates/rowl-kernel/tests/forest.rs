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
        Concept::One(_) | Concept::NotOne(_) => panic!("the samples have no nominals"),
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
        Concept::One(_) | Concept::NotOne(_) => panic!("the samples have no nominals"),
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

#[test]
fn every_input_is_answered() {
    // The final check that every restriction has enough neighbours never fails:
    // the nodes a restriction created differ, so they are never merged.
    with_stack(|| {
        let mut seed = 101;
        for round in 0..1000 {
            let c = random_concept(&mut seed, 3, true);
            let tbox = random_concept(&mut seed, 1, true);
            assert!(
                concept_sat(c, &tbox, &none()).is_some(),
                "stuck in round {round}"
            );
        }
        let mut seed = 103;
        for round in 0..200 {
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
            assert!(
                abox(3, facts, links, &tbox).is_some(),
                "stuck in abox round {round}"
            );
        }
    });
}

fn individual(s: &[u8]) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(s) })
}
fn one(s: &[u8]) -> Concept {
    Concept::One(individual(s))
}
fn not_one(s: &[u8]) -> Concept {
    Concept::NotOne(individual(s))
}

#[test]
fn nominals_merge_into_their_named_node() {
    with_stack(|| {
        let top = Concept::Top;
        // Each individual's node carries its nominal; a node with another
        // individual's nominal is that individual.
        let nominals = || vec![fact(1, one(b"a")), fact(2, one(b"b"))];
        let mut facts = nominals();
        facts.push(fact(1, one(b"b")));
        facts.push(fact(1, atom(b"A")));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(true));
        let mut facts = nominals();
        facts.push(fact(1, one(b"b")));
        facts.push(fact(1, atom(b"A")));
        facts.push(fact(2, no(b"A")));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(false));
        // A nominal and its complement clash.
        let mut facts = nominals();
        facts.push(fact(1, not_one(b"a")));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(false));
        let mut facts = nominals();
        facts.push(fact(1, not_one(b"b")));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(true));
        // ∃r.{b} at a: the new successor is b, which then gets ∀r's filler.
        let mut facts = nominals();
        facts.push(fact(1, and(some(r(), one(b"b")), all(r(), atom(b"A")))));
        facts.push(fact(2, no(b"A")));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(false));
        let mut facts = nominals();
        facts.push(fact(1, and(some(r(), one(b"b")), all(r(), atom(b"A")))));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(true));
        // Two different successors cannot both be b.
        let mut facts = nominals();
        facts.push(fact(
            1,
            and(at_least(2, r(), Concept::Top), all(r(), one(b"b"))),
        ));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(false));
        let mut facts = nominals();
        facts.push(fact(
            1,
            and(
                at_least(2, r(), Concept::Top),
                all(r(), or(one(b"a"), one(b"b"))),
            ),
        ));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(true));
        // An enumeration of two individuals has at most two instances.
        let mut facts = nominals();
        facts.push(fact(0, at_least(3, r(), or(one(b"a"), one(b"b")))));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(false));
        // A nominal deeper in a tree merges its node into the named node, which
        // gets an edge from the parent.
        let mut facts = nominals();
        facts.push(fact(0, some(r(), some(r(), one(b"b")))));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(true));
        let mut facts = nominals();
        facts.push(fact(0, some(r(), some(r(), and(one(b"b"), atom(b"A"))))));
        facts.push(fact(2, no(b"A")));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(false));
        // Restrictions pass along the added edge in both directions.
        let mut facts = nominals();
        facts.push(fact(0, some(r(), and(atom(b"B"), some(r(), one(b"b"))))));
        facts.push(fact(2, all(back(), no(b"B"))));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(false));
        let mut facts = nominals();
        facts.push(fact(0, some(r(), and(atom(b"B"), some(r(), one(b"b"))))));
        facts.push(fact(2, all(back(), atom(b"B"))));
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(true));
        // Every element of an infinite chain points at b; blocking stops it.
        let chain = and(some(r(), Concept::Top), all(r(), some(back(), one(b"b"))));
        assert_eq!(abox(3, nominals(), Vec::new(), &chain), Some(true));
        // A maximum restriction of a named node that counts a tree node along
        // an added edge gets no answer yet, and so does a nominal without a
        // named node.
        let mut facts = nominals();
        facts.push(fact(
            0,
            and(
                some(r(), and(atom(b"A"), some(r(), one(b"b")))),
                some(r(), and(no(b"A"), some(r(), one(b"b")))),
            ),
        ));
        facts.push(fact(2, at_most(1, back(), Concept::Top)));
        assert_eq!(abox(3, facts, Vec::new(), &top), None);
        let facts = vec![fact(1, some(r(), one(b"c")))];
        assert_eq!(abox(3, facts, Vec::new(), &top), None);
        // A requirement {c} makes its node the named node of c.
        let facts = vec![fact(1, one(b"c")), fact(2, some(r(), one(b"c")))];
        assert_eq!(abox(3, facts, Vec::new(), &top), Some(true));
    });
}

/// A pseudo-random concept over A, r and its inverse, and the nominals of a
/// and b.
fn random_nominal_concept(seed: &mut u64, depth: u32) -> Concept {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 6 } else { 14 };
    let role = if (*seed >> 40).is_multiple_of(2) {
        r()
    } else {
        back()
    };
    let n = ((*seed >> 44) % 2) as usize;
    match choice {
        0 => atom(b"A"),
        1 => no(b"A"),
        2 => one(b"a"),
        3 => one(b"b"),
        4 => not_one(b"a"),
        5 => Concept::Top,
        6 | 7 => and(
            random_nominal_concept(seed, depth - 1),
            random_nominal_concept(seed, depth - 1),
        ),
        8 => or(
            random_nominal_concept(seed, depth - 1),
            random_nominal_concept(seed, depth - 1),
        ),
        9 | 10 => some(role, random_nominal_concept(seed, depth - 1)),
        11 => all(role, random_nominal_concept(seed, depth - 1)),
        12 => at_least(n + 1, role, random_nominal_concept(seed, depth - 1)),
        _ => at_most(n, role, random_nominal_concept(seed, depth - 1)),
    }
}
/// The meaning of a concept with nominals, a and b placed at `na` and `nb`.
fn nominal_holds(i: &Finite, na: usize, nb: usize, c: &Concept, x: usize) -> bool {
    let edge = |role: &ObjectPropertyExpression, x: usize, y: usize| match role {
        ObjectPropertyExpression::Property(_) => i.r >> (x * i.size + y) & 1 == 1,
        ObjectPropertyExpression::Inverse(_) => i.r >> (y * i.size + x) & 1 == 1,
    };
    let place = |individual: &Individual| match individual {
        Individual::Named(named) if named.iri.spelling == b"a" => na,
        _ => nb,
    };
    let count = |role: &ObjectPropertyExpression, c: &Concept| {
        (0..i.size)
            .filter(|&y| edge(role, x, y) && nominal_holds(i, na, nb, c, y))
            .count()
    };
    match c {
        Concept::Top => true,
        Concept::Bottom => false,
        Concept::Atom(_) => i.a >> x & 1 == 1,
        Concept::NotAtom(_) => i.a >> x & 1 == 0,
        Concept::One(individual) => place(individual) == x,
        Concept::NotOne(individual) => place(individual) != x,
        Concept::And(a, b) => nominal_holds(i, na, nb, a, x) && nominal_holds(i, na, nb, b, x),
        Concept::Or(a, b) => nominal_holds(i, na, nb, a, x) || nominal_holds(i, na, nb, b, x),
        Concept::Exists(r, c) => count(r, c) >= 1,
        Concept::Forall(r, c) => {
            (0..i.size).all(|y| !edge(r, x, y) || nominal_holds(i, na, nb, c, y))
        }
        Concept::AtLeast(n, r, c) => count(r, c) >= *n,
        Concept::AtMost(n, r, c) => count(r, c) <= *n,
    }
}
fn nominal_copy(c: &Concept) -> Concept {
    match c {
        Concept::Top => Concept::Top,
        Concept::Bottom => Concept::Bottom,
        Concept::Atom(_) => atom(b"A"),
        Concept::NotAtom(_) => no(b"A"),
        Concept::One(Individual::Named(named)) => one(&named.iri.spelling),
        Concept::NotOne(Individual::Named(named)) => not_one(&named.iri.spelling),
        Concept::One(_) | Concept::NotOne(_) => panic!("the samples name their individuals"),
        Concept::And(a, b) => and(nominal_copy(a), nominal_copy(b)),
        Concept::Or(a, b) => or(nominal_copy(a), nominal_copy(b)),
        Concept::Exists(r, c) => some(role_copy(r), nominal_copy(c)),
        Concept::Forall(r, c) => all(role_copy(r), nominal_copy(c)),
        Concept::AtLeast(n, r, c) => at_least(*n, role_copy(r), nominal_copy(c)),
        Concept::AtMost(n, r, c) => at_most(*n, role_copy(r), nominal_copy(c)),
    }
}

#[test]
fn no_nominal_input_with_a_small_model_is_rejected() {
    with_stack(no_nominal_input_with_a_small_model_is_rejected_body);
}
fn no_nominal_input_with_a_small_model_is_rejected_body() {
    let mut seed = 89;
    let mut with_model = 0;
    let mut accepted = 0;
    let mut rejected = 0;
    for _ in 0..600 {
        let c = and(
            random_nominal_concept(&mut seed, 3),
            random_nominal_concept(&mut seed, 2),
        );
        let tbox = random_nominal_concept(&mut seed, 1);
        let small = (1..=3usize).any(|size| {
            (0..1u32 << size).any(|a| {
                (0..1u32 << (size * size)).any(|r| {
                    let i = Finite { size, a, b: 0, r };
                    (0..size).any(|na| {
                        (0..size).any(|nb| {
                            (0..size).all(|x| nominal_holds(&i, na, nb, &tbox, x))
                                && (0..size).any(|x| nominal_holds(&i, na, nb, &c, x))
                        })
                    })
                })
            })
        });
        let facts = vec![
            fact(1, one(b"a")),
            fact(2, one(b"b")),
            fact(0, nominal_copy(&c)),
        ];
        let answer = abox(3, facts, Vec::new(), &tbox);
        if small {
            assert_ne!(
                answer,
                Some(false),
                "a model exists, so the forest must not reject"
            );
            with_model += 1;
        }
        match answer {
            Some(true) => accepted += 1,
            Some(false) => rejected += 1,
            None => {}
        }
    }
    assert!(
        with_model > 50,
        "the sample must exercise satisfiable inputs"
    );
    assert!(accepted > 50, "the sample must exercise acceptances");
    assert!(rejected > 20, "the sample must exercise rejections");
}

#[test]
fn two_element_domains_are_decided_exactly() {
    with_stack(two_element_domains_are_decided_exactly_body);
}
/// With `⊤ ⊑ {a} ⊔ {b}` every model has at most two elements, so the models of
/// size one and two decide each input, and both answers can be checked.
fn two_element_domains_are_decided_exactly_body() {
    let mut seed = 211;
    let mut accepted = 0;
    let mut rejected = 0;
    let mut unanswered = 0;
    for _ in 0..800 {
        let c = and(
            random_nominal_concept(&mut seed, 3),
            random_nominal_concept(&mut seed, 2),
        );
        let extra = random_nominal_concept(&mut seed, 1);
        let tbox = and(or(one(b"a"), one(b"b")), extra);
        let model = (1..=2usize).any(|size| {
            (0..1u32 << size).any(|a| {
                (0..1u32 << (size * size)).any(|r| {
                    let i = Finite { size, a, b: 0, r };
                    (0..size).any(|na| {
                        (0..size).any(|nb| {
                            (0..size).all(|x| nominal_holds(&i, na, nb, &tbox, x))
                                && (0..size).any(|x| nominal_holds(&i, na, nb, &c, x))
                        })
                    })
                })
            })
        });
        let facts = vec![
            fact(1, one(b"a")),
            fact(2, one(b"b")),
            fact(0, nominal_copy(&c)),
        ];
        match abox(3, facts, Vec::new(), &tbox) {
            Some(true) => {
                assert!(model, "an acceptance has a model of at most two elements");
                accepted += 1;
            }
            Some(false) => {
                assert!(!model, "a rejection has no model");
                rejected += 1;
            }
            None => unanswered += 1,
        }
    }
    assert!(accepted > 100, "the sample must exercise acceptances");
    assert!(rejected > 100, "the sample must exercise rejections");
    assert!(
        unanswered < 200,
        "most inputs must be answered: {unanswered} without an answer"
    );
}
