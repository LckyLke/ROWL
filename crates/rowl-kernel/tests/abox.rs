use rowl_kernel::abox::{abox_satisfiable, abox_satisfiable_with, Edges, Facts};
use rowl_kernel::model::*;
use rowl_kernel::nnf::NnfConcept;
use rowl_kernel::role_box::{RoleBox, RoleInclusion};

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
fn facts<'a>(list: &[(usize, &'a NnfConcept)]) -> Facts<'a> {
    let mut result = Facts::Empty;
    for (node, concept) in list.iter().rev() {
        result = Facts::Entry {
            node: *node,
            concept,
            next: Box::new(result),
        };
    }
    result
}
fn edges<'a>(list: &[(&'a ObjectProperty, usize, usize)]) -> Edges<'a> {
    let mut result = Edges::Empty;
    for (role, source, target) in list.iter().rev() {
        result = Edges::Entry {
            role,
            source: *source,
            target: *target,
            next: Box::new(result),
        };
    }
    result
}

#[test]
fn the_maintenance_inference_holds_for_named_individuals() {
    // Machines with a faulty part need inspection: ∃hasPart.Faulty ⊑ NeedsInspection.
    let tbox = or(all(b"hasPart", no(b"Faulty")), atom(b"NeedsInspection"));
    let has_part = ObjectProperty {
        iri: iri(b"hasPart"),
    };
    let machine = atom(b"Machine");
    let faulty = atom(b"Faulty");
    let not_inspected = no(b"NeedsInspection");
    // pump1 is a machine, motor1 is faulty, pump1 hasPart motor1: consistent.
    assert!(abox_satisfiable(
        2,
        facts(&[(0, &machine), (1, &faulty)]),
        edges(&[(&has_part, 0, 1)]),
        &tbox
    ));
    // Adding that pump1 does not need inspection is inconsistent.
    assert!(!abox_satisfiable(
        2,
        facts(&[(0, &machine), (1, &faulty), (0, &not_inspected)]),
        edges(&[(&has_part, 0, 1)]),
        &tbox
    ));
    // Without the edge it is consistent again.
    assert!(abox_satisfiable(
        2,
        facts(&[(0, &machine), (1, &faulty), (0, &not_inspected)]),
        Edges::Empty,
        &tbox
    ));
}

#[test]
fn restrictions_reach_successors_and_named_neighbours() {
    let top = NnfConcept::Top;
    let r = ObjectProperty { iri: iri(b"r") };
    let only_not_a = all(b"r", no(b"A"));
    let a = atom(b"A");
    // ∀r.¬A at node 0 reaches node 1, which is A.
    assert!(!abox_satisfiable(
        2,
        facts(&[(0, &only_not_a), (1, &a)]),
        edges(&[(&r, 0, 1)]),
        &top
    ));
    // The edge in the other direction does not carry the restriction.
    assert!(abox_satisfiable(
        2,
        facts(&[(0, &only_not_a), (1, &a)]),
        edges(&[(&r, 1, 0)]),
        &top
    ));
    // An existential restriction meets the universal restrictions at its node.
    let both = and(some(b"r", atom(b"A")), only_not_a);
    assert!(!abox_satisfiable(
        1,
        facts(&[(0, &both)]),
        Edges::Empty,
        &top
    ));
    // A disjunction is decided by branching.
    let choice = or(atom(b"A"), atom(b"B"));
    let not_a = no(b"A");
    assert!(abox_satisfiable(
        1,
        facts(&[(0, &choice), (0, &not_a)]),
        Edges::Empty,
        &top
    ));
    let not_b = no(b"B");
    assert!(!abox_satisfiable(
        1,
        facts(&[(0, &choice), (0, &not_a), (0, &not_b)]),
        Edges::Empty,
        &top
    ));
}

#[test]
fn the_tbox_concept_holds_at_every_node_and_successor() {
    // ⊤ ⊑ ⊥ has no model, even without facts.
    let bottom = NnfConcept::Bottom;
    assert!(!abox_satisfiable(1, Facts::Empty, Edges::Empty, &bottom));
    // A ⊑ ∃r.A needs successors, found through blocking.
    let tbox = or(no(b"A"), some(b"r", atom(b"A")));
    let a = atom(b"A");
    assert!(abox_satisfiable(1, facts(&[(0, &a)]), Edges::Empty, &tbox));
    // Every element is B, so a node that is not B is inconsistent.
    let b = atom(b"B");
    let not_b = no(b"B");
    assert!(!abox_satisfiable(
        3,
        facts(&[(2, &not_b)]),
        Edges::Empty,
        &b
    ));
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
fn universal_restrictions_follow_edges_of_included_properties() {
    // ∃hasPart.Faulty ⊑ NeedsInspection, with hasComponent ⊑ hasPart.
    let tbox = or(all(b"hasPart", no(b"Faulty")), atom(b"NeedsInspection"));
    let has_component = property(b"hasComponent");
    let faulty = atom(b"Faulty");
    let not_inspected = no(b"NeedsInspection");
    let inclusion = roles(&[(b"hasComponent", b"hasPart")], &[]);
    let assertions = || facts(&[(1, &faulty), (0, &not_inspected)]);
    let component = || edges(&[(&has_component, 0, 1)]);
    assert!(!abox_satisfiable_with(
        2,
        assertions(),
        component(),
        &tbox,
        &inclusion
    ));
    assert!(abox_satisfiable_with(
        2,
        assertions(),
        component(),
        &tbox,
        &roles(&[], &[])
    ));
    // The inclusion has a direction.
    assert!(abox_satisfiable_with(
        2,
        assertions(),
        component(),
        &tbox,
        &roles(&[(b"hasPart", b"hasComponent")], &[])
    ));
}

#[test]
fn transitive_properties_reach_named_and_anonymous_parts() {
    let tbox = or(all(b"hasPart", no(b"Faulty")), atom(b"NeedsInspection"));
    let has_part = property(b"hasPart");
    let faulty = atom(b"Faulty");
    let not_inspected = no(b"NeedsInspection");
    let transitive = roles(&[], &[b"hasPart"]);
    // pump1 hasPart motor1 hasPart bearing1, and bearing1 is faulty.
    let chain = || edges(&[(&has_part, 0, 1), (&has_part, 1, 2)]);
    let named = || facts(&[(2, &faulty), (0, &not_inspected)]);
    assert!(!abox_satisfiable_with(
        3,
        named(),
        chain(),
        &tbox,
        &transitive
    ));
    assert!(abox_satisfiable_with(
        3,
        named(),
        chain(),
        &tbox,
        &roles(&[], &[])
    ));
    // motor1 has some faulty part, an element no assertion names.
    let some_faulty = some(b"hasPart", atom(b"Faulty"));
    let anonymous = || facts(&[(1, &some_faulty), (0, &not_inspected)]);
    let one = || edges(&[(&has_part, 0, 1)]);
    assert!(!abox_satisfiable_with(
        2,
        anonymous(),
        one(),
        &tbox,
        &transitive
    ));
    assert!(abox_satisfiable_with(
        2,
        anonymous(),
        one(),
        &tbox,
        &roles(&[], &[])
    ));
    // The ALC entry point is the procedure without role axioms.
    assert!(abox_satisfiable(2, anonymous(), one(), &tbox));
}

/// A deterministic pseudo-random concept over A, B and the properties s and t.
fn random_concept(seed: &mut u64, depth: u32) -> NnfConcept {
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
            random_concept(seed, depth - 1),
            random_concept(seed, depth - 1),
        ),
        6 => or(
            random_concept(seed, depth - 1),
            random_concept(seed, depth - 1),
        ),
        7 => some(b"s", random_concept(seed, depth - 1)),
        8 => some(b"t", random_concept(seed, depth - 1)),
        9 => all(b"s", random_concept(seed, depth - 1)),
        _ => all(b"t", random_concept(seed, depth - 1)),
    }
}
/// A finite interpretation with classes A, B and properties s and t.
struct Finite {
    size: usize,
    a: u32,
    b: u32,
    s: u32,
    t: u32,
}
fn related(i: &Finite, role: &ObjectProperty, x: usize, y: usize) -> bool {
    let relation = match role.iri.spelling.as_slice() {
        b"s" => i.s,
        b"t" => i.t,
        _ => panic!("unknown test property"),
    };
    relation >> (x * i.size + y) & 1 == 1
}
fn holds(i: &Finite, c: &NnfConcept, x: usize) -> bool {
    let class = |class: &Class, x: usize| match class.iri.spelling.as_slice() {
        b"A" => i.a >> x & 1 == 1,
        b"B" => i.b >> x & 1 == 1,
        _ => panic!("unknown test class"),
    };
    match c {
        NnfConcept::Top => true,
        NnfConcept::Bottom => false,
        NnfConcept::Atom(a) => class(a, x),
        NnfConcept::NotAtom(a) => !class(a, x),
        NnfConcept::And(a, b) => holds(i, a, x) && holds(i, b, x),
        NnfConcept::Or(a, b) => holds(i, a, x) || holds(i, b, x),
        NnfConcept::Exists(r, c) => (0..i.size).any(|y| related(i, r, x, y) && holds(i, c, y)),
        NnfConcept::Forall(r, c) => (0..i.size).all(|y| !related(i, r, x, y) || holds(i, c, y)),
    }
}
fn transitive(relation: u32, size: usize) -> bool {
    let edge = |x: usize, y: usize| relation >> (x * size + y) & 1 == 1;
    (0..size)
        .all(|x| (0..size).all(|y| (0..size).all(|z| !(edge(x, y) && edge(y, z)) || edge(x, z))))
}
/// Some interpretation with at most two elements in which s is included in t
/// and t is transitive satisfies the TBox everywhere and, for some placement of
/// the two nodes, every fact and edge.
fn small_model_exists(
    placed: &[(usize, &NnfConcept)],
    related_nodes: &[(&ObjectProperty, usize, usize)],
    tbox: &NnfConcept,
) -> bool {
    (1..=2).any(|size| {
        let relations = 1u32 << (size * size);
        (0..relations).filter(|&t| transitive(t, size)).any(|t| {
            (0..relations).filter(|&s| s & !t == 0).any(|s| {
                (0..1u32 << size).any(|a| {
                    (0..1u32 << size).any(|b| {
                        let i = Finite { size, a, b, s, t };
                        (0..size).all(|x| holds(&i, tbox, x))
                            && (0..size * size).any(|placement| {
                                let at = |node: usize| {
                                    if node == 0 {
                                        placement % size
                                    } else {
                                        placement / size
                                    }
                                };
                                placed.iter().all(|(node, c)| holds(&i, c, at(*node)))
                                    && related_nodes
                                        .iter()
                                        .all(|(r, x, y)| related(&i, r, at(*x), at(*y)))
                            })
                    })
                })
            })
        })
    })
}

#[test]
fn every_individual_set_with_a_small_model_of_the_role_axioms_is_accepted() {
    let axioms = roles(&[(b"s", b"t")], &[b"t"]);
    let s = property(b"s");
    let t = property(b"t");
    let mut seed = 47;
    let mut with_model = 0;
    let mut rejected = 0;
    for _ in 0..300 {
        let first = random_concept(&mut seed, 2);
        let second = random_concept(&mut seed, 2);
        let tbox = random_concept(&mut seed, 1);
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let shape = seed >> 33;
        let mut related_nodes: Vec<(&ObjectProperty, usize, usize)> = Vec::new();
        if shape & 1 == 1 {
            related_nodes.push((&s, 0, 1));
        }
        if shape & 2 == 2 {
            related_nodes.push((&t, 1, 0));
        }
        if shape & 4 == 4 {
            related_nodes.push((&t, 1, 1));
        }
        let placed = [(0, &first), (1, &second)];
        let accepted =
            abox_satisfiable_with(2, facts(&placed), edges(&related_nodes), &tbox, &axioms);
        if small_model_exists(&placed, &related_nodes, &tbox) {
            assert!(accepted, "a model exists, so the completion must accept");
            with_model += 1;
        }
        if !accepted {
            rejected += 1;
        }
    }
    assert!(
        with_model > 30,
        "the sample must exercise satisfiable inputs"
    );
    assert!(rejected > 10, "the sample must exercise rejections");
}
