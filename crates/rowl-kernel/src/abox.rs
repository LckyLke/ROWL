//! ALC reasoning with named individuals: a completion of the facts about
//! individuals in front of the TBox tableau.
//!
//! Nodes stand for individuals. A fact says that a concept in negation normal
//! form holds at a node; an edge says that a named object property relates two
//! nodes. The TBox concept, which must hold at every element, is added at every
//! node first. The completion expands conjunctions, branches on disjunctions and
//! pushes the filler of every universal restriction along the edges of its role,
//! adding each fact once. Once no fact is pending, it checks every node for a
//! clash and decides every existential restriction with the TBox tableau,
//! together with the fillers of the universal restrictions on its role at the
//! same node. Each added fact is new and drawn from a finite closure, so the
//! completion always terminates.
#![allow(clippy::ptr_arg, clippy::question_mark)] // Explicit branches for the pinned extraction subset.
use crate::model::{Class, ObjectProperty};
use crate::nnf::NnfConcept;
use crate::symbols::same_spelling;
use crate::tableau::Concepts;
use crate::tbox::{same_concept, satisfiable_all};

/// Facts in a list: `concept` holds at `node`.
pub enum Facts<'a> {
    Empty,
    Entry {
        node: usize,
        concept: &'a NnfConcept,
        next: Box<Facts<'a>>,
    },
}
/// Edges in a list: `role` relates `source` to `target`.
pub enum Edges<'a> {
    Empty,
    Entry {
        role: &'a ObjectProperty,
        source: usize,
        target: usize,
        next: Box<Edges<'a>>,
    },
}

fn duplicate_facts(list: Facts<'_>) -> (Facts<'_>, Facts<'_>) {
    match list {
        Facts::Empty => (Facts::Empty, Facts::Empty),
        Facts::Entry {
            node,
            concept,
            next,
        } => {
            let (left, right) = duplicate_facts(*next);
            (
                Facts::Entry {
                    node,
                    concept,
                    next: Box::new(left),
                },
                Facts::Entry {
                    node,
                    concept,
                    next: Box::new(right),
                },
            )
        }
    }
}
fn duplicate_edges(list: Edges<'_>) -> (Edges<'_>, Edges<'_>) {
    match list {
        Edges::Empty => (Edges::Empty, Edges::Empty),
        Edges::Entry {
            role,
            source,
            target,
            next,
        } => {
            let (left, right) = duplicate_edges(*next);
            (
                Edges::Entry {
                    role,
                    source,
                    target,
                    next: Box::new(left),
                },
                Edges::Entry {
                    role,
                    source,
                    target,
                    next: Box::new(right),
                },
            )
        }
    }
}
/// Whether `sought` already holds at `node`; the list is handed back.
fn contains_fact<'a>(list: Facts<'a>, node: usize, sought: &NnfConcept) -> (bool, Facts<'a>) {
    match list {
        Facts::Empty => (false, Facts::Empty),
        Facts::Entry {
            node: other,
            concept,
            next,
        } => {
            let here = other == node && same_concept(concept, sought);
            let (later, rest) = contains_fact(*next, node, sought);
            (
                here || later,
                Facts::Entry {
                    node: other,
                    concept,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// `pending` with `filler` at the target of every edge of `role` from `node`;
/// the edges are handed back.
fn propagate<'a>(
    edges: Edges<'a>,
    node: usize,
    role: &ObjectProperty,
    filler: &'a NnfConcept,
    pending: Facts<'a>,
) -> (Facts<'a>, Edges<'a>) {
    match edges {
        Edges::Empty => (pending, Edges::Empty),
        Edges::Entry {
            role: other,
            source,
            target,
            next,
        } => {
            let (pending, rest) = propagate(*next, node, role, filler, pending);
            let edges = Edges::Entry {
                role: other,
                source,
                target,
                next: Box::new(rest),
            };
            if source == node && same_spelling(&other.iri.spelling, &role.iri.spelling) {
                (
                    Facts::Entry {
                        node: target,
                        concept: filler,
                        next: Box::new(pending),
                    },
                    edges,
                )
            } else {
                (pending, edges)
            }
        }
    }
}
/// Whether `class` holds positively at `node`; the list is handed back.
fn has_atom<'a>(list: Facts<'a>, node: usize, class: &Class) -> (bool, Facts<'a>) {
    match list {
        Facts::Empty => (false, Facts::Empty),
        Facts::Entry {
            node: other,
            concept,
            next,
        } => {
            let here = match concept {
                NnfConcept::Atom(k) => {
                    other == node && same_spelling(&k.iri.spelling, &class.iri.spelling)
                }
                _ => false,
            };
            let (later, rest) = has_atom(*next, node, class);
            (
                here || later,
                Facts::Entry {
                    node: other,
                    concept,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Whether some node has a named class negated in `cursor` and positive in
/// `all`; `all` is handed back.
fn has_clash<'a>(all: Facts<'a>, cursor: Facts<'a>) -> (bool, Facts<'a>) {
    match cursor {
        Facts::Empty => (false, all),
        Facts::Entry {
            node,
            concept,
            next,
        } => {
            let (here, all) = match concept {
                NnfConcept::NotAtom(k) => has_atom(all, node, k),
                _ => (false, all),
            };
            let (later, all) = has_clash(all, *next);
            (here || later, all)
        }
    }
}
/// The fillers of the universal restrictions on `role` at `node`, in list
/// order; the list is handed back.
fn node_fillers<'a>(
    list: Facts<'a>,
    node: usize,
    role: &ObjectProperty,
) -> (Concepts<'a>, Facts<'a>) {
    match list {
        Facts::Empty => (Concepts::Empty, Facts::Empty),
        Facts::Entry {
            node: other,
            concept,
            next,
        } => {
            let (fillers, rest) = node_fillers(*next, node, role);
            let list = Facts::Entry {
                node: other,
                concept,
                next: Box::new(rest),
            };
            match concept {
                NnfConcept::Forall(r, filler) => {
                    if other == node && same_spelling(&r.iri.spelling, &role.iri.spelling) {
                        (
                            Concepts::Entry {
                                concept: filler,
                                next: Box::new(fillers),
                            },
                            list,
                        )
                    } else {
                        (fillers, list)
                    }
                }
                _ => (fillers, list),
            }
        }
    }
}
/// Whether every existential restriction in `cursor` has a successor: an element
/// satisfying its filler, the fillers of the universal restrictions on its role
/// at the same node in `all`, and the TBox concept. `all` is handed back.
fn obligations_hold<'a>(
    all: Facts<'a>,
    cursor: Facts<'a>,
    axioms: &'a NnfConcept,
) -> (bool, Facts<'a>) {
    match cursor {
        Facts::Empty => (true, all),
        Facts::Entry {
            node,
            concept,
            next,
        } => {
            let (here, all) = match concept {
                NnfConcept::Exists(role, filler) => {
                    let (fillers, all) = node_fillers(all, node, role);
                    (
                        satisfiable_all(
                            Concepts::Entry {
                                concept: filler,
                                next: Box::new(fillers),
                            },
                            axioms,
                        ),
                        all,
                    )
                }
                _ => (true, all),
            };
            let (later, all) = obligations_hold(all, *next, axioms);
            (here && later, all)
        }
    }
}
/// Decide the `pending` facts together with the facts already added, under the
/// edges and the TBox concept.
fn complete<'a>(
    pending: Facts<'a>,
    facts: Facts<'a>,
    edges: Edges<'a>,
    axioms: &'a NnfConcept,
) -> bool {
    match pending {
        Facts::Empty => {
            let (cursor, facts) = duplicate_facts(facts);
            let (clash, facts) = has_clash(facts, cursor);
            if clash {
                return false;
            }
            let (cursor, facts) = duplicate_facts(facts);
            obligations_hold(facts, cursor, axioms).0
        }
        Facts::Entry {
            node,
            concept,
            next,
        } => {
            let (present, facts) = contains_fact(facts, node, concept);
            if present {
                return complete(*next, facts, edges, axioms);
            }
            let facts = Facts::Entry {
                node,
                concept,
                next: Box::new(facts),
            };
            match concept {
                NnfConcept::Bottom => false,
                NnfConcept::And(left, right) => complete(
                    Facts::Entry {
                        node,
                        concept: left,
                        next: Box::new(Facts::Entry {
                            node,
                            concept: right,
                            next,
                        }),
                    },
                    facts,
                    edges,
                    axioms,
                ),
                NnfConcept::Or(left, right) => {
                    let (next, other_pending) = duplicate_facts(*next);
                    let (facts, other_facts) = duplicate_facts(facts);
                    let (edges, other_edges) = duplicate_edges(edges);
                    complete(
                        Facts::Entry {
                            node,
                            concept: left,
                            next: Box::new(next),
                        },
                        facts,
                        edges,
                        axioms,
                    ) || complete(
                        Facts::Entry {
                            node,
                            concept: right,
                            next: Box::new(other_pending),
                        },
                        other_facts,
                        other_edges,
                        axioms,
                    )
                }
                NnfConcept::Forall(role, filler) => {
                    let (pending, edges) = propagate(edges, node, role, filler, *next);
                    complete(pending, facts, edges, axioms)
                }
                _ => complete(*next, facts, edges, axioms),
            }
        }
    }
}
/// `pending` with the TBox concept at every node below `count`.
fn with_axioms<'a>(count: usize, pending: Facts<'a>, axioms: &'a NnfConcept) -> Facts<'a> {
    if count == 0 {
        pending
    } else {
        with_axioms(
            count - 1,
            Facts::Entry {
                node: count - 1,
                concept: axioms,
                next: Box::new(pending),
            },
            axioms,
        )
    }
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// has elements for the nodes below `count` that satisfy `facts` and are related
/// by `edges`. Every node in `facts` and `edges` must be below `count`, and
/// `count` must be positive, since an interpretation has at least one element.
pub fn abox_satisfiable<'a>(
    count: usize,
    facts: Facts<'a>,
    edges: Edges<'a>,
    axioms: &'a NnfConcept,
) -> bool {
    complete(
        with_axioms(count, facts, axioms),
        Facts::Empty,
        edges,
        axioms,
    )
}
