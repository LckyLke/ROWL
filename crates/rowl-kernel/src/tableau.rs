//! A decision procedure for ALC concept satisfiability, without a TBox.
//!
//! The input is a concept in negation normal form, as produced by `nnf`. The
//! procedure expands conjunctions, branches on disjunctions and, once only
//! named-class literals and restrictions remain, checks for a clash and
//! recursively decides every existential restriction together with the
//! universal restrictions on the same property. Every step shrinks the total
//! size of the concepts still to decide, so it always terminates. General
//! concept inclusions (a TBox) need blocking and are a later stage.
//!
//! Lists are passed by value and handed back, as elsewhere in the kernel's
//! extraction subset.
#![allow(clippy::ptr_arg, clippy::question_mark)] // Explicit branches for the pinned extraction subset.
use crate::model::{Class, ObjectProperty};
use crate::nnf::NnfConcept;
use crate::symbols::same_spelling;

/// Concepts that must all hold at the same element.
pub enum Concepts<'a> {
    Empty,
    Entry {
        concept: &'a NnfConcept,
        next: Box<Concepts<'a>>,
    },
}

fn duplicate(list: Concepts<'_>) -> (Concepts<'_>, Concepts<'_>) {
    match list {
        Concepts::Empty => (Concepts::Empty, Concepts::Empty),
        Concepts::Entry { concept, next } => {
            let (left, right) = duplicate(*next);
            (
                Concepts::Entry {
                    concept,
                    next: Box::new(left),
                },
                Concepts::Entry {
                    concept,
                    next: Box::new(right),
                },
            )
        }
    }
}
/// Whether the named class occurs positively in the list.
fn contains_atom<'a>(list: Concepts<'a>, class: &Class) -> (bool, Concepts<'a>) {
    match list {
        Concepts::Empty => (false, Concepts::Empty),
        Concepts::Entry { concept, next } => {
            let here = match concept {
                NnfConcept::Atom(other) => same_spelling(&other.iri.spelling, &class.iri.spelling),
                _ => false,
            };
            let (later, rest) = contains_atom(*next, class);
            (
                here || later,
                Concepts::Entry {
                    concept,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Whether some negated class in `cursor` also occurs positively in `all`.
fn has_clash<'a>(all: Concepts<'a>, cursor: Concepts<'a>) -> (bool, Concepts<'a>) {
    match cursor {
        Concepts::Empty => (false, all),
        Concepts::Entry { concept, next } => {
            let (here, all) = match concept {
                NnfConcept::NotAtom(class) => contains_atom(all, class),
                _ => (false, all),
            };
            let (later, all) = has_clash(all, *next);
            (here || later, all)
        }
    }
}
/// The fillers of every universal restriction on `role`, in list order, and
/// the unchanged list.
fn universal_fillers<'a>(
    list: Concepts<'a>,
    role: &ObjectProperty,
) -> (Concepts<'a>, Concepts<'a>) {
    match list {
        Concepts::Empty => (Concepts::Empty, Concepts::Empty),
        Concepts::Entry { concept, next } => {
            let (fillers, rest) = universal_fillers(*next, role);
            let list = Concepts::Entry {
                concept,
                next: Box::new(rest),
            };
            match concept {
                NnfConcept::Forall(other, filler) => {
                    if same_spelling(&other.iri.spelling, &role.iri.spelling) {
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
/// Decide `pending` together with `literals`, which holds only named-class
/// literals and restrictions.
fn expand<'a>(pending: Concepts<'a>, literals: Concepts<'a>) -> bool {
    match pending {
        Concepts::Empty => {
            let (cursor, literals) = duplicate(literals);
            let (clash, literals) = has_clash(literals, cursor);
            if clash {
                false
            } else {
                let (cursor, literals) = duplicate(literals);
                existentials_hold(literals, cursor).0
            }
        }
        Concepts::Entry { concept, next } => match concept {
            NnfConcept::Top => expand(*next, literals),
            NnfConcept::Bottom => false,
            NnfConcept::And(left, right) => expand(
                Concepts::Entry {
                    concept: left,
                    next: Box::new(Concepts::Entry {
                        concept: right,
                        next,
                    }),
                },
                literals,
            ),
            NnfConcept::Or(left, right) => {
                let (next, other_pending) = duplicate(*next);
                let (literals, other_literals) = duplicate(literals);
                expand(
                    Concepts::Entry {
                        concept: left,
                        next: Box::new(next),
                    },
                    literals,
                ) || expand(
                    Concepts::Entry {
                        concept: right,
                        next: Box::new(other_pending),
                    },
                    other_literals,
                )
            }
            _ => expand(
                *next,
                Concepts::Entry {
                    concept,
                    next: Box::new(literals),
                },
            ),
        },
    }
}
/// Every existential restriction in `cursor` must have a successor satisfying
/// its filler and the fillers of all universal restrictions on its role in
/// `all`, which is handed back unchanged.
fn existentials_hold<'a>(all: Concepts<'a>, cursor: Concepts<'a>) -> (bool, Concepts<'a>) {
    match cursor {
        Concepts::Empty => (true, all),
        Concepts::Entry { concept, next } => match concept {
            NnfConcept::Exists(role, filler) => {
                let (fillers, all) = universal_fillers(all, role);
                let here = expand(
                    Concepts::Entry {
                        concept: filler,
                        next: Box::new(fillers),
                    },
                    Concepts::Empty,
                );
                let (later, all) = existentials_hold(all, *next);
                (here && later, all)
            }
            _ => existentials_hold(all, *next),
        },
    }
}
/// Decide whether some interpretation has an element in the concept.
pub fn satisfiable(concept: &NnfConcept) -> bool {
    expand(
        Concepts::Entry {
            concept,
            next: Box::new(Concepts::Empty),
        },
        Concepts::Empty,
    )
}
