//! Concept satisfiability with respect to a TBox and role axioms, by a tableau
//! with blocking.
//!
//! The TBox is given as one concept in negation normal form that must hold at
//! every element (for example the conjunction of `¬C ⊔ D` for every `C ⊑ D`).
//! The role axioms are inclusions between named object properties and
//! transitive named object properties (`role_box`), which makes the logic SH.
//! The procedure is the plain tableau of `tableau` with three changes. Every
//! successor also receives the TBox concept. A successor along `s` receives the
//! filler of every universal restriction on a property that includes `s`, and,
//! for every transitive property `t` between them, the restriction `∀t.filler`
//! itself, so that elements reached along `t` in several steps satisfy the
//! filler too. A node whose items are all among the items of an ancestor is
//! blocked and accepted without new successors. Unblocked nodes therefore carry
//! distinct item sets drawn from a finite closure, so every branch is finite.
#![allow(clippy::ptr_arg, clippy::question_mark)] // Explicit branches for the pinned extraction subset.
use crate::model::{Class, ObjectProperty};
use crate::nnf::NnfConcept;
use crate::role_box::{below, RoleBox};
use crate::symbols::same_spelling;
use crate::tableau::Concepts;

/// Concepts that must all hold at one element. `Through` stands for the
/// universal restriction `∀role.filler` on a transitive property, which the
/// tableau adds along that property; its filler is a subconcept of the input.
pub enum Items<'a> {
    Empty,
    Concept {
        concept: &'a NnfConcept,
        next: Box<Items<'a>>,
    },
    Through {
        role: &'a ObjectProperty,
        filler: &'a NnfConcept,
        next: Box<Items<'a>>,
    },
}

/// The item sets of the ancestors of a node, nearest first.
pub enum History<'a> {
    Empty,
    Entry {
        label: Items<'a>,
        next: Box<History<'a>>,
    },
}

pub(crate) fn duplicate(list: Items<'_>) -> (Items<'_>, Items<'_>) {
    match list {
        Items::Empty => (Items::Empty, Items::Empty),
        Items::Concept { concept, next } => {
            let (left, right) = duplicate(*next);
            (
                Items::Concept {
                    concept,
                    next: Box::new(left),
                },
                Items::Concept {
                    concept,
                    next: Box::new(right),
                },
            )
        }
        Items::Through { role, filler, next } => {
            let (left, right) = duplicate(*next);
            (
                Items::Through {
                    role,
                    filler,
                    next: Box::new(left),
                },
                Items::Through {
                    role,
                    filler,
                    next: Box::new(right),
                },
            )
        }
    }
}
fn duplicate_history(history: History<'_>) -> (History<'_>, History<'_>) {
    match history {
        History::Empty => (History::Empty, History::Empty),
        History::Entry { label, next } => {
            let (left_label, right_label) = duplicate(label);
            let (left, right) = duplicate_history(*next);
            (
                History::Entry {
                    label: left_label,
                    next: Box::new(left),
                },
                History::Entry {
                    label: right_label,
                    next: Box::new(right),
                },
            )
        }
    }
}
/// Structural equality, comparing classes and properties by exact spelling.
pub(crate) fn same_concept(left: &NnfConcept, right: &NnfConcept) -> bool {
    match (left, right) {
        (NnfConcept::Top, NnfConcept::Top) => true,
        (NnfConcept::Bottom, NnfConcept::Bottom) => true,
        (NnfConcept::Atom(a), NnfConcept::Atom(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (NnfConcept::NotAtom(a), NnfConcept::NotAtom(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (NnfConcept::And(a1, b1), NnfConcept::And(a2, b2)) => {
            same_concept(a1, a2) && same_concept(b1, b2)
        }
        (NnfConcept::Or(a1, b1), NnfConcept::Or(a2, b2)) => {
            same_concept(a1, a2) && same_concept(b1, b2)
        }
        (NnfConcept::Exists(r1, c1), NnfConcept::Exists(r2, c2)) => {
            same_spelling(&r1.iri.spelling, &r2.iri.spelling) && same_concept(c1, c2)
        }
        (NnfConcept::Forall(r1, c1), NnfConcept::Forall(r2, c2)) => {
            same_spelling(&r1.iri.spelling, &r2.iri.spelling) && same_concept(c1, c2)
        }
        _ => false,
    }
}
/// Whether the named class occurs positively in the list.
fn contains_atom<'a>(list: Items<'a>, class: &Class) -> (bool, Items<'a>) {
    match list {
        Items::Empty => (false, Items::Empty),
        Items::Concept { concept, next } => {
            let here = match concept {
                NnfConcept::Atom(other) => same_spelling(&other.iri.spelling, &class.iri.spelling),
                _ => false,
            };
            let (later, rest) = contains_atom(*next, class);
            (
                here || later,
                Items::Concept {
                    concept,
                    next: Box::new(rest),
                },
            )
        }
        Items::Through { role, filler, next } => {
            let (later, rest) = contains_atom(*next, class);
            (
                later,
                Items::Through {
                    role,
                    filler,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Whether some negated class in `cursor` also occurs positively in `all`.
fn has_clash<'a>(all: Items<'a>, cursor: Items<'a>) -> (bool, Items<'a>) {
    match cursor {
        Items::Empty => (false, all),
        Items::Concept { concept, next } => {
            let (here, all) = match concept {
                NnfConcept::NotAtom(class) => contains_atom(all, class),
                _ => (false, all),
            };
            let (later, all) = has_clash(all, *next);
            (here || later, all)
        }
        Items::Through {
            role: _,
            filler: _,
            next,
        } => has_clash(all, *next),
    }
}
/// Whether the concept is the universal restriction `∀role.filler`.
fn universal_is(role: &ObjectProperty, filler: &NnfConcept, concept: &NnfConcept) -> bool {
    match concept {
        NnfConcept::Forall(other, inner) => {
            same_spelling(&role.iri.spelling, &other.iri.spelling) && same_concept(filler, inner)
        }
        _ => false,
    }
}
/// Whether the concept occurs in the list, reading every `Through` item as its
/// universal restriction.
fn contains_concept<'a>(list: Items<'a>, sought: &NnfConcept) -> (bool, Items<'a>) {
    match list {
        Items::Empty => (false, Items::Empty),
        Items::Concept { concept, next } => {
            let here = same_concept(concept, sought);
            let (later, rest) = contains_concept(*next, sought);
            (
                here || later,
                Items::Concept {
                    concept,
                    next: Box::new(rest),
                },
            )
        }
        Items::Through { role, filler, next } => {
            let here = universal_is(role, filler, sought);
            let (later, rest) = contains_concept(*next, sought);
            (
                here || later,
                Items::Through {
                    role,
                    filler,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Whether `∀role.filler` occurs in the list, as a concept or a `Through` item.
fn contains_universal<'a>(
    list: Items<'a>,
    role: &ObjectProperty,
    filler: &NnfConcept,
) -> (bool, Items<'a>) {
    match list {
        Items::Empty => (false, Items::Empty),
        Items::Concept { concept, next } => {
            let here = universal_is(role, filler, concept);
            let (later, rest) = contains_universal(*next, role, filler);
            (
                here || later,
                Items::Concept {
                    concept,
                    next: Box::new(rest),
                },
            )
        }
        Items::Through {
            role: other,
            filler: inner,
            next,
        } => {
            let here = same_spelling(&role.iri.spelling, &other.iri.spelling)
                && same_concept(filler, inner);
            let (later, rest) = contains_universal(*next, role, filler);
            (
                here || later,
                Items::Through {
                    role: other,
                    filler: inner,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Whether every item of `small` occurs in `large`; both lists are handed back.
fn subset<'a>(small: Items<'a>, large: Items<'a>) -> (bool, Items<'a>, Items<'a>) {
    match small {
        Items::Empty => (true, Items::Empty, large),
        Items::Concept { concept, next } => {
            let (here, large) = contains_concept(large, concept);
            let (later, rest, large) = subset(*next, large);
            (
                here && later,
                Items::Concept {
                    concept,
                    next: Box::new(rest),
                },
                large,
            )
        }
        Items::Through { role, filler, next } => {
            let (here, large) = contains_universal(large, role, filler);
            let (later, rest, large) = subset(*next, large);
            (
                here && later,
                Items::Through {
                    role,
                    filler,
                    next: Box::new(rest),
                },
                large,
            )
        }
    }
}
/// Whether the items are all among the items of some ancestor.
fn blocked<'a>(label: Items<'a>, history: History<'a>) -> (bool, Items<'a>, History<'a>) {
    match history {
        History::Empty => (false, label, History::Empty),
        History::Entry {
            label: ancestor,
            next,
        } => {
            let (here, label, ancestor) = subset(label, ancestor);
            let (later, label, rest) = blocked(label, *next);
            (
                here || later,
                label,
                History::Entry {
                    label: ancestor,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// `tail` with `∀role.filler` for every transitive property `role` from
/// `roles.transitive[index..]` that includes `sub` and is included in `sup`.
fn transitive_from<'a>(
    roles: &'a RoleBox,
    index: usize,
    sub: &ObjectProperty,
    sup: &ObjectProperty,
    filler: &'a NnfConcept,
    tail: Items<'a>,
) -> Items<'a> {
    if index < roles.transitive.len() {
        let role = &roles.transitive[index];
        let rest = transitive_from(roles, index + 1, sub, sup, filler, tail);
        if below(roles, sub, role) && below(roles, role, sup) {
            Items::Through {
                role,
                filler,
                next: Box::new(rest),
            }
        } else {
            rest
        }
    } else {
        tail
    }
}
/// What the universal restriction `∀sup.filler` requires of an element reached
/// along `sub`, in front of `tail`: nothing unless `sub` is included in `sup`;
/// otherwise the filler and `∀t.filler` for every transitive `t` between them.
fn universal<'a>(
    roles: &'a RoleBox,
    sub: &ObjectProperty,
    sup: &ObjectProperty,
    filler: &'a NnfConcept,
    tail: Items<'a>,
) -> Items<'a> {
    if below(roles, sub, sup) {
        Items::Concept {
            concept: filler,
            next: Box::new(transitive_from(roles, 0, sub, sup, filler, tail)),
        }
    } else {
        tail
    }
}
/// What the universal restrictions in the list require of an element reached
/// along `role`, in list order, and the unchanged list.
fn role_fillers<'a>(
    list: Items<'a>,
    role: &ObjectProperty,
    roles: &'a RoleBox,
) -> (Items<'a>, Items<'a>) {
    match list {
        Items::Empty => (Items::Empty, Items::Empty),
        Items::Concept { concept, next } => {
            let (fillers, rest) = role_fillers(*next, role, roles);
            let list = Items::Concept {
                concept,
                next: Box::new(rest),
            };
            match concept {
                NnfConcept::Forall(other, filler) => {
                    (universal(roles, role, other, filler, fillers), list)
                }
                _ => (fillers, list),
            }
        }
        Items::Through {
            role: other,
            filler,
            next,
        } => {
            let (fillers, rest) = role_fillers(*next, role, roles);
            (
                universal(roles, role, other, filler, fillers),
                Items::Through {
                    role: other,
                    filler,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Decide `pending` together with `literals` at a node below `history`, where
/// every element must also satisfy `axioms` and the relations `roles`.
fn expand<'a>(
    pending: Items<'a>,
    literals: Items<'a>,
    history: History<'a>,
    axioms: &'a NnfConcept,
    roles: &'a RoleBox,
) -> bool {
    match pending {
        Items::Empty => {
            let (cursor, literals) = duplicate(literals);
            let (clash, literals) = has_clash(literals, cursor);
            if clash {
                return false;
            }
            let (is_blocked, literals, history) = blocked(literals, history);
            if is_blocked {
                return true;
            }
            let (label, literals) = duplicate(literals);
            let (cursor, literals) = duplicate(literals);
            let extended = History::Entry {
                label,
                next: Box::new(history),
            };
            existentials_hold(literals, cursor, extended, axioms, roles).0
        }
        Items::Concept { concept, next } => match concept {
            NnfConcept::Top => expand(*next, literals, history, axioms, roles),
            NnfConcept::Bottom => false,
            NnfConcept::And(left, right) => expand(
                Items::Concept {
                    concept: left,
                    next: Box::new(Items::Concept {
                        concept: right,
                        next,
                    }),
                },
                literals,
                history,
                axioms,
                roles,
            ),
            NnfConcept::Or(left, right) => {
                let (next, other_pending) = duplicate(*next);
                let (literals, other_literals) = duplicate(literals);
                let (history, other_history) = duplicate_history(history);
                expand(
                    Items::Concept {
                        concept: left,
                        next: Box::new(next),
                    },
                    literals,
                    history,
                    axioms,
                    roles,
                ) || expand(
                    Items::Concept {
                        concept: right,
                        next: Box::new(other_pending),
                    },
                    other_literals,
                    other_history,
                    axioms,
                    roles,
                )
            }
            _ => expand(
                *next,
                Items::Concept {
                    concept,
                    next: Box::new(literals),
                },
                history,
                axioms,
                roles,
            ),
        },
        Items::Through { role, filler, next } => expand(
            *next,
            Items::Through {
                role,
                filler,
                next: Box::new(literals),
            },
            history,
            axioms,
            roles,
        ),
    }
}
/// Every existential restriction in `cursor` needs a successor satisfying its
/// filler, what the universal restrictions in `all` require along its role,
/// and the TBox concept. `all` and `history` are handed back unchanged.
fn existentials_hold<'a>(
    all: Items<'a>,
    cursor: Items<'a>,
    history: History<'a>,
    axioms: &'a NnfConcept,
    roles: &'a RoleBox,
) -> (bool, Items<'a>, History<'a>) {
    match cursor {
        Items::Empty => (true, all, history),
        Items::Concept { concept, next } => match concept {
            NnfConcept::Exists(role, filler) => {
                let (fillers, all) = role_fillers(all, role, roles);
                let (successor_history, history) = duplicate_history(history);
                let here = expand(
                    Items::Concept {
                        concept: filler,
                        next: Box::new(Items::Concept {
                            concept: axioms,
                            next: Box::new(fillers),
                        }),
                    },
                    Items::Empty,
                    successor_history,
                    axioms,
                    roles,
                );
                let (later, all, history) = existentials_hold(all, *next, history, axioms, roles);
                (here && later, all, history)
            }
            _ => existentials_hold(all, *next, history, axioms, roles),
        },
        Items::Through {
            role: _,
            filler: _,
            next,
        } => existentials_hold(all, *next, history, axioms, roles),
    }
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// and the object properties satisfy `roles` has an element in `concept`. The
/// inclusions of `roles` must be closed under composition.
pub fn satisfiable_with(concept: &NnfConcept, axioms: &NnfConcept, roles: &RoleBox) -> bool {
    expand(
        Items::Concept {
            concept,
            next: Box::new(Items::Concept {
                concept: axioms,
                next: Box::new(Items::Empty),
            }),
        },
        Items::Empty,
        History::Empty,
        axioms,
        roles,
    )
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// and the object properties satisfy `roles` has an element satisfying every
/// item of `items`. The inclusions of `roles` must be closed under composition.
pub(crate) fn satisfiable_items<'a>(
    items: Items<'a>,
    axioms: &'a NnfConcept,
    roles: &'a RoleBox,
) -> bool {
    expand(
        Items::Concept {
            concept: axioms,
            next: Box::new(items),
        },
        Items::Empty,
        History::Empty,
        axioms,
        roles,
    )
}
/// No role axioms: plain ALC.
fn no_roles() -> RoleBox {
    RoleBox {
        inclusions: Vec::new(),
        transitive: Vec::new(),
    }
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// has an element in `concept`.
pub fn satisfiable_in(concept: &NnfConcept, axioms: &NnfConcept) -> bool {
    satisfiable_with(concept, axioms, &no_roles())
}
fn items_of(list: Concepts<'_>) -> Items<'_> {
    match list {
        Concepts::Empty => Items::Empty,
        Concepts::Entry { concept, next } => Items::Concept {
            concept,
            next: Box::new(items_of(*next)),
        },
    }
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// has an element satisfying every concept of `concepts`.
pub(crate) fn satisfiable_all<'a>(concepts: Concepts<'a>, axioms: &'a NnfConcept) -> bool {
    let roles = no_roles();
    satisfiable_items(items_of(concepts), axioms, &roles)
}
