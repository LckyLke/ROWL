//! ALC concept satisfiability with respect to a TBox, by a tableau with blocking.
//!
//! The TBox is given as one concept in negation normal form that must hold at
//! every element (for example the conjunction of `¬C ⊔ D` for every `C ⊑ D`).
//! The procedure is the plain tableau of `tableau`, with two changes: every
//! successor also receives the TBox concept, and a node whose literals are all
//! among the literals of an ancestor is blocked and accepted without new
//! successors. Unblocked nodes therefore carry distinct literal sets drawn from a
//! finite closure, so every branch is finite.
#![allow(clippy::ptr_arg, clippy::question_mark)] // Explicit branches for the pinned extraction subset.
use crate::nnf::NnfConcept;
use crate::symbols::same_spelling;
use crate::tableau::{duplicate, has_clash, universal_fillers, Concepts};

/// The literal sets of the ancestors of a node, nearest first.
pub enum History<'a> {
    Empty,
    Entry {
        label: Concepts<'a>,
        next: Box<History<'a>>,
    },
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
fn same_concept(left: &NnfConcept, right: &NnfConcept) -> bool {
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
/// Whether the concept occurs in the list.
fn contains_concept<'a>(list: Concepts<'a>, sought: &NnfConcept) -> (bool, Concepts<'a>) {
    match list {
        Concepts::Empty => (false, Concepts::Empty),
        Concepts::Entry { concept, next } => {
            let here = same_concept(concept, sought);
            let (later, rest) = contains_concept(*next, sought);
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
/// Whether every concept of `small` occurs in `large`; both lists are handed back.
fn subset<'a>(small: Concepts<'a>, large: Concepts<'a>) -> (bool, Concepts<'a>, Concepts<'a>) {
    match small {
        Concepts::Empty => (true, Concepts::Empty, large),
        Concepts::Entry { concept, next } => {
            let (here, large) = contains_concept(large, concept);
            let (later, rest, large) = subset(*next, large);
            (
                here && later,
                Concepts::Entry {
                    concept,
                    next: Box::new(rest),
                },
                large,
            )
        }
    }
}
/// Whether the literals are all among the literals of some ancestor.
fn blocked<'a>(label: Concepts<'a>, history: History<'a>) -> (bool, Concepts<'a>, History<'a>) {
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
/// Decide `pending` together with `literals` at a node below `history`, where
/// every element must also satisfy `axioms`.
fn expand<'a>(
    pending: Concepts<'a>,
    literals: Concepts<'a>,
    history: History<'a>,
    axioms: &'a NnfConcept,
) -> bool {
    match pending {
        Concepts::Empty => {
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
            existentials_hold(literals, cursor, extended, axioms).0
        }
        Concepts::Entry { concept, next } => match concept {
            NnfConcept::Top => expand(*next, literals, history, axioms),
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
                history,
                axioms,
            ),
            NnfConcept::Or(left, right) => {
                let (next, other_pending) = duplicate(*next);
                let (literals, other_literals) = duplicate(literals);
                let (history, other_history) = duplicate_history(history);
                expand(
                    Concepts::Entry {
                        concept: left,
                        next: Box::new(next),
                    },
                    literals,
                    history,
                    axioms,
                ) || expand(
                    Concepts::Entry {
                        concept: right,
                        next: Box::new(other_pending),
                    },
                    other_literals,
                    other_history,
                    axioms,
                )
            }
            _ => expand(
                *next,
                Concepts::Entry {
                    concept,
                    next: Box::new(literals),
                },
                history,
                axioms,
            ),
        },
    }
}
/// Every existential restriction in `cursor` needs a successor satisfying its
/// filler, the fillers of the universal restrictions on its role in `all`, and
/// the TBox concept. `all` and `history` are handed back unchanged.
fn existentials_hold<'a>(
    all: Concepts<'a>,
    cursor: Concepts<'a>,
    history: History<'a>,
    axioms: &'a NnfConcept,
) -> (bool, Concepts<'a>, History<'a>) {
    match cursor {
        Concepts::Empty => (true, all, history),
        Concepts::Entry { concept, next } => match concept {
            NnfConcept::Exists(role, filler) => {
                let (fillers, all) = universal_fillers(all, role);
                let (successor_history, history) = duplicate_history(history);
                let here = expand(
                    Concepts::Entry {
                        concept: filler,
                        next: Box::new(Concepts::Entry {
                            concept: axioms,
                            next: Box::new(fillers),
                        }),
                    },
                    Concepts::Empty,
                    successor_history,
                    axioms,
                );
                let (later, all, history) = existentials_hold(all, *next, history, axioms);
                (here && later, all, history)
            }
            _ => existentials_hold(all, *next, history, axioms),
        },
    }
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// has an element in `concept`.
pub fn satisfiable_in(concept: &NnfConcept, axioms: &NnfConcept) -> bool {
    expand(
        Concepts::Entry {
            concept,
            next: Box::new(Concepts::Entry {
                concept: axioms,
                next: Box::new(Concepts::Empty),
            }),
        },
        Concepts::Empty,
        History::Empty,
        axioms,
    )
}
