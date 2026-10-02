use rowl_kernel::abox::{abox_satisfiable, Edges, Facts};
use rowl_kernel::model::*;
use rowl_kernel::nnf::NnfConcept;

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
