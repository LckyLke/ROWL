//! Reasoning with named individuals: a completion of the facts about
//! individuals in front of the TBox tableau, with role axioms (SH).
//!
//! Nodes stand for individuals. A fact says that a concept in negation normal
//! form holds at a node, or (`Through`) that the universal restriction of a
//! transitive property on a filler holds there; an edge says that a named object
//! property relates two nodes. The role box lists inclusions between named
//! object properties, closed under composition, and transitive properties. The
//! TBox concept, which must hold at every element, is added at every node first.
//! The completion expands conjunctions, branches on disjunctions and pushes
//! every universal restriction along each edge whose property it includes: the
//! target receives the filler and, for every transitive property in between, the
//! universal restriction on that property. Each fact is added once. Once no fact
//! is pending, it checks every node for a clash and decides every existential
//! restriction with the TBox tableau, together with what the universal
//! restrictions at the same node require along its role. Each added fact is new
//! and drawn from a finite closure, so the completion always terminates.
#![allow(clippy::ptr_arg, clippy::question_mark)] // Explicit branches for the pinned extraction subset.
use crate::model::{Class, ObjectProperty};
use crate::nnf::NnfConcept;
use crate::role_box::RoleBox;
use crate::symbols::same_spelling;
use crate::tbox::{no_roles, same_concept, satisfiable_items, universal, universal_is, Items};

/// Facts in a list: `concept` holds at `node`, or (`Through`) the universal
/// restriction of the transitive `role` on `filler` holds at `node`.
pub enum Facts<'a> {
    Empty,
    Entry {
        node: usize,
        concept: &'a NnfConcept,
        next: Box<Facts<'a>>,
    },
    Through {
        node: usize,
        role: &'a ObjectProperty,
        filler: &'a NnfConcept,
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
        Facts::Through {
            node,
            role,
            filler,
            next,
        } => {
            let (left, right) = duplicate_facts(*next);
            (
                Facts::Through {
                    node,
                    role,
                    filler,
                    next: Box::new(left),
                },
                Facts::Through {
                    node,
                    role,
                    filler,
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
/// Whether `sought` already holds at `node`, reading every `Through` fact as
/// its universal restriction; the list is handed back.
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
        Facts::Through {
            node: other,
            role,
            filler,
            next,
        } => {
            let here = other == node && universal_is(role, filler, sought);
            let (later, rest) = contains_fact(*next, node, sought);
            (
                here || later,
                Facts::Through {
                    node: other,
                    role,
                    filler,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Whether `∀role.filler` already holds at `node`, as a concept or a `Through`
/// fact; the list is handed back.
fn contains_through<'a>(
    list: Facts<'a>,
    node: usize,
    role: &ObjectProperty,
    filler: &NnfConcept,
) -> (bool, Facts<'a>) {
    match list {
        Facts::Empty => (false, Facts::Empty),
        Facts::Entry {
            node: other,
            concept,
            next,
        } => {
            let here = other == node && universal_is(role, filler, concept);
            let (later, rest) = contains_through(*next, node, role, filler);
            (
                here || later,
                Facts::Entry {
                    node: other,
                    concept,
                    next: Box::new(rest),
                },
            )
        }
        Facts::Through {
            node: other,
            role: other_role,
            filler: other_filler,
            next,
        } => {
            let here = other == node
                && same_spelling(&role.iri.spelling, &other_role.iri.spelling)
                && same_concept(filler, other_filler);
            let (later, rest) = contains_through(*next, node, role, filler);
            (
                here || later,
                Facts::Through {
                    node: other,
                    role: other_role,
                    filler: other_filler,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// `tail` with every item of `items` as a fact at `node`, in list order.
fn place<'a>(node: usize, items: Items<'a>, tail: Facts<'a>) -> Facts<'a> {
    match items {
        Items::Empty => tail,
        Items::Concept { concept, next } => Facts::Entry {
            node,
            concept,
            next: Box::new(place(node, *next, tail)),
        },
        Items::Through { role, filler, next } => Facts::Through {
            node,
            role,
            filler,
            next: Box::new(place(node, *next, tail)),
        },
    }
}
/// `pending` with what the universal restriction `∀role.filler` at `node`
/// requires of the target of every edge from `node`; the edges are handed back.
fn propagate<'a>(
    edges: Edges<'a>,
    node: usize,
    role: &ObjectProperty,
    filler: &'a NnfConcept,
    pending: Facts<'a>,
    roles: &'a RoleBox,
) -> (Facts<'a>, Edges<'a>) {
    match edges {
        Edges::Empty => (pending, Edges::Empty),
        Edges::Entry {
            role: other,
            source,
            target,
            next,
        } => {
            let (pending, rest) = propagate(*next, node, role, filler, pending, roles);
            let edges = Edges::Entry {
                role: other,
                source,
                target,
                next: Box::new(rest),
            };
            if source == node {
                let required = universal(roles, other, role, filler, Items::Empty);
                (place(target, required, pending), edges)
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
        Facts::Through {
            node: other,
            role,
            filler,
            next,
        } => {
            let (later, rest) = has_atom(*next, node, class);
            (
                later,
                Facts::Through {
                    node: other,
                    role,
                    filler,
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
        Facts::Through {
            node: _,
            role: _,
            filler: _,
            next,
        } => has_clash(all, *next),
    }
}
/// What the universal restrictions at `node` require of an element reached
/// along `role`, in list order; the list is handed back.
fn node_fillers<'a>(
    list: Facts<'a>,
    node: usize,
    role: &ObjectProperty,
    roles: &'a RoleBox,
) -> (Items<'a>, Facts<'a>) {
    match list {
        Facts::Empty => (Items::Empty, Facts::Empty),
        Facts::Entry {
            node: other,
            concept,
            next,
        } => {
            let (fillers, rest) = node_fillers(*next, node, role, roles);
            let list = Facts::Entry {
                node: other,
                concept,
                next: Box::new(rest),
            };
            match concept {
                NnfConcept::Forall(sup, filler) => {
                    if other == node {
                        (universal(roles, role, sup, filler, fillers), list)
                    } else {
                        (fillers, list)
                    }
                }
                _ => (fillers, list),
            }
        }
        Facts::Through {
            node: other,
            role: sup,
            filler,
            next,
        } => {
            let (fillers, rest) = node_fillers(*next, node, role, roles);
            let list = Facts::Through {
                node: other,
                role: sup,
                filler,
                next: Box::new(rest),
            };
            if other == node {
                (universal(roles, role, sup, filler, fillers), list)
            } else {
                (fillers, list)
            }
        }
    }
}
/// Whether some element satisfies `filler`, what the universal restrictions at
/// `node` in `all` require along `role`, and the TBox concept; `all` is handed
/// back.
fn obligation_holds<'a>(
    all: Facts<'a>,
    node: usize,
    role: &ObjectProperty,
    filler: &'a NnfConcept,
    axioms: &'a NnfConcept,
    roles: &'a RoleBox,
) -> (bool, Facts<'a>) {
    let (fillers, all) = node_fillers(all, node, role, roles);
    let items = Items::Concept {
        concept: filler,
        next: Box::new(fillers),
    };
    (satisfiable_items(items, axioms, roles), all)
}
/// Whether every existential restriction in `cursor` has a successor: an element
/// satisfying its filler, what the universal restrictions at the same node in
/// `all` require along its role, and the TBox concept. `all` is handed back.
fn obligations_hold<'a>(
    all: Facts<'a>,
    cursor: Facts<'a>,
    axioms: &'a NnfConcept,
    roles: &'a RoleBox,
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
                    obligation_holds(all, node, role, filler, axioms, roles)
                }
                _ => (true, all),
            };
            let (later, all) = obligations_hold(all, *next, axioms, roles);
            (here && later, all)
        }
        Facts::Through {
            node: _,
            role: _,
            filler: _,
            next,
        } => obligations_hold(all, *next, axioms, roles),
    }
}
/// Decide the `pending` facts together with the facts already added, under the
/// edges, the TBox concept and the role axioms.
fn complete<'a>(
    pending: Facts<'a>,
    facts: Facts<'a>,
    edges: Edges<'a>,
    axioms: &'a NnfConcept,
    roles: &'a RoleBox,
) -> bool {
    match pending {
        Facts::Empty => {
            let (cursor, facts) = duplicate_facts(facts);
            let (clash, facts) = has_clash(facts, cursor);
            if clash {
                return false;
            }
            let (cursor, facts) = duplicate_facts(facts);
            obligations_hold(facts, cursor, axioms, roles).0
        }
        Facts::Entry {
            node,
            concept,
            next,
        } => {
            let (present, facts) = contains_fact(facts, node, concept);
            if present {
                return complete(*next, facts, edges, axioms, roles);
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
                    roles,
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
                        roles,
                    ) || complete(
                        Facts::Entry {
                            node,
                            concept: right,
                            next: Box::new(other_pending),
                        },
                        other_facts,
                        other_edges,
                        axioms,
                        roles,
                    )
                }
                NnfConcept::Forall(role, filler) => {
                    let (pending, edges) = propagate(edges, node, role, filler, *next, roles);
                    complete(pending, facts, edges, axioms, roles)
                }
                _ => complete(*next, facts, edges, axioms, roles),
            }
        }
        Facts::Through {
            node,
            role,
            filler,
            next,
        } => {
            let (present, facts) = contains_through(facts, node, role, filler);
            if present {
                return complete(*next, facts, edges, axioms, roles);
            }
            let facts = Facts::Through {
                node,
                role,
                filler,
                next: Box::new(facts),
            };
            let (pending, edges) = propagate(edges, node, role, filler, *next, roles);
            complete(pending, facts, edges, axioms, roles)
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
/// and the object properties satisfy `roles` has elements for the nodes below
/// `count` that satisfy `facts` and are related by `edges`. Every node in
/// `facts` and `edges` must be below `count`, `count` must be positive, since an
/// interpretation has at least one element, and the inclusions of `roles` must
/// be closed under composition.
pub fn abox_satisfiable_with<'a>(
    count: usize,
    facts: Facts<'a>,
    edges: Edges<'a>,
    axioms: &'a NnfConcept,
    roles: &'a RoleBox,
) -> bool {
    complete(
        with_axioms(count, facts, axioms),
        Facts::Empty,
        edges,
        axioms,
        roles,
    )
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
    let roles = no_roles();
    abox_satisfiable_with(count, facts, edges, axioms, &roles)
}
