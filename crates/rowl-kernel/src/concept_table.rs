//! A table of interned concepts for the completion graph tableau.
//!
//! Every concept is stored once, as an entry whose parts are the indices of
//! earlier entries, so equal subconcepts share an index and the tableau's labels
//! are lists of indices. An entry `≤n r.C` also records the index of the
//! complement of `C`, which the tableau needs to decide `C` at each neighbour. `close` adds the universal restriction `∀t.d` for every
//! universal restriction `∀q.d` in the table and every transitive role `t`
//! included in `q`: the restrictions that transitive roles pass along a path.
#![allow(clippy::ptr_arg, clippy::question_mark, clippy::collapsible_match)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::concepts::{copy_role, negate, same_role, Concept};
use crate::hierarchy::{below, RoleHierarchy};
use crate::model::{Class, ObjectPropertyExpression};
use crate::nnf::copy_iri;
use crate::symbols::same_spelling;

/// One interned concept: its constructor with the indices of its parts.
pub enum Entry {
    Top,
    Bottom,
    Atom(Class),
    NotAtom(Class),
    And(usize, usize),
    Or(usize, usize),
    Exists(ObjectPropertyExpression, usize),
    Forall(ObjectPropertyExpression, usize),
    /// At least `n` neighbours along the role satisfy the filler.
    AtLeast(usize, ObjectPropertyExpression, usize),
    /// At most `n` neighbours along the role satisfy the filler; the last index
    /// is the complement of the filler.
    AtMost(usize, ObjectPropertyExpression, usize, usize),
}

/// Structural equality of entries: classes and roles by exact spelling, parts
/// by index.
pub(crate) fn same_entry(left: &Entry, right: &Entry) -> bool {
    match (left, right) {
        (Entry::Top, Entry::Top) => true,
        (Entry::Bottom, Entry::Bottom) => true,
        (Entry::Atom(a), Entry::Atom(b)) => same_spelling(&a.iri.spelling, &b.iri.spelling),
        (Entry::NotAtom(a), Entry::NotAtom(b)) => same_spelling(&a.iri.spelling, &b.iri.spelling),
        (Entry::And(a1, b1), Entry::And(a2, b2)) => *a1 == *a2 && *b1 == *b2,
        (Entry::Or(a1, b1), Entry::Or(a2, b2)) => *a1 == *a2 && *b1 == *b2,
        (Entry::Exists(r1, c1), Entry::Exists(r2, c2)) => {
            if *c1 == *c2 {
                same_role(r1, r2)
            } else {
                false
            }
        }
        (Entry::Forall(r1, c1), Entry::Forall(r2, c2)) => {
            if *c1 == *c2 {
                same_role(r1, r2)
            } else {
                false
            }
        }
        (Entry::AtLeast(n1, r1, c1), Entry::AtLeast(n2, r2, c2)) => {
            if *n1 == *n2 && *c1 == *c2 {
                same_role(r1, r2)
            } else {
                false
            }
        }
        (Entry::AtMost(n1, r1, c1, d1), Entry::AtMost(n2, r2, c2, d2)) => {
            if *n1 == *n2 && *c1 == *c2 && *d1 == *d2 {
                same_role(r1, r2)
            } else {
                false
            }
        }
        _ => false,
    }
}
/// The index of the first entry of `entries[index..]` equal to `entry`, or the
/// length of the table.
fn position_from(entries: &Vec<Entry>, entry: &Entry, index: usize) -> usize {
    if index < entries.len() {
        if same_entry(&entries[index], entry) {
            index
        } else {
            position_from(entries, entry, index + 1)
        }
    } else {
        entries.len()
    }
}
/// The table with `entry` at the end and its index; `None` when there is no
/// room.
fn push_new(mut entries: Vec<Entry>, entry: Entry) -> Option<(Vec<Entry>, usize)> {
    if entries.len() < usize::MAX {
        let position = entries.len();
        entries.push(entry);
        Some((entries, position))
    } else {
        None
    }
}
/// The index of `entry`, added at the end when the table does not have it yet;
/// `None` when there is no room.
fn add(entries: Vec<Entry>, entry: Entry) -> Option<(Vec<Entry>, usize)> {
    let position = position_from(&entries, &entry, 0);
    if position < entries.len() {
        return Some((entries, position));
    }
    push_new(entries, entry)
}
fn intern_pair(
    entries: Vec<Entry>,
    left: &Concept,
    right: &Concept,
    conjunctive: bool,
) -> Option<(Vec<Entry>, usize)> {
    let (entries, first) = match intern(entries, left) {
        Some(pair) => pair,
        None => return None,
    };
    let (entries, second) = match intern(entries, right) {
        Some(pair) => pair,
        None => return None,
    };
    if conjunctive {
        add(entries, Entry::And(first, second))
    } else {
        add(entries, Entry::Or(first, second))
    }
}
fn intern_restriction(
    entries: Vec<Entry>,
    role: &ObjectPropertyExpression,
    filler: &Concept,
    existential: bool,
) -> Option<(Vec<Entry>, usize)> {
    let (entries, inner) = match intern(entries, filler) {
        Some(pair) => pair,
        None => return None,
    };
    if existential {
        add(entries, Entry::Exists(copy_role(role), inner))
    } else {
        add(entries, Entry::Forall(copy_role(role), inner))
    }
}
fn intern_at_least(
    entries: Vec<Entry>,
    n: usize,
    role: &ObjectPropertyExpression,
    filler: &Concept,
) -> Option<(Vec<Entry>, usize)> {
    let (entries, inner) = match intern(entries, filler) {
        Some(pair) => pair,
        None => return None,
    };
    add(entries, Entry::AtLeast(n, copy_role(role), inner))
}
fn intern_at_most(
    entries: Vec<Entry>,
    n: usize,
    role: &ObjectPropertyExpression,
    filler: &Concept,
) -> Option<(Vec<Entry>, usize)> {
    let (entries, inner) = match intern(entries, filler) {
        Some(pair) => pair,
        None => return None,
    };
    let complement = match negate(filler) {
        Some(complement) => complement,
        None => return None,
    };
    let (entries, other) = match intern(entries, &complement) {
        Some(pair) => pair,
        None => return None,
    };
    add(entries, Entry::AtMost(n, copy_role(role), inner, other))
}
/// The table with the concept and all its subconcepts (and the complements of
/// the fillers of maximum restrictions), and the concept's index; `None` when
/// there is no room.
pub fn intern(entries: Vec<Entry>, concept: &Concept) -> Option<(Vec<Entry>, usize)> {
    match concept {
        Concept::Top => add(entries, Entry::Top),
        Concept::Bottom => add(entries, Entry::Bottom),
        Concept::Atom(class) => add(
            entries,
            Entry::Atom(Class {
                iri: copy_iri(&class.iri),
            }),
        ),
        Concept::NotAtom(class) => add(
            entries,
            Entry::NotAtom(Class {
                iri: copy_iri(&class.iri),
            }),
        ),
        Concept::And(left, right) => intern_pair(entries, left, right, true),
        Concept::Or(left, right) => intern_pair(entries, left, right, false),
        Concept::Exists(role, filler) => intern_restriction(entries, role, filler, true),
        Concept::Forall(role, filler) => intern_restriction(entries, role, filler, false),
        Concept::AtLeast(n, role, filler) => intern_at_least(entries, *n, role, filler),
        Concept::AtMost(n, role, filler) => intern_at_most(entries, *n, role, filler),
    }
}
/// The table with `∀t.filler` for every transitive role `t` of
/// `roles.transitive[index..]` that is included in `sup`.
fn transitive_restrictions(
    entries: Vec<Entry>,
    roles: &RoleHierarchy,
    index: usize,
    sup: &ObjectPropertyExpression,
    filler: usize,
) -> Option<Vec<Entry>> {
    if index < roles.transitive.len() {
        let entries = if below(roles, &roles.transitive[index], sup) {
            match add(
                entries,
                Entry::Forall(copy_role(&roles.transitive[index]), filler),
            ) {
                Some((entries, _)) => entries,
                None => return None,
            }
        } else {
            entries
        };
        transitive_restrictions(entries, roles, index + 1, sup, filler)
    } else {
        Some(entries)
    }
}
/// The table with the transitive restrictions of every universal restriction
/// among `entries[index..limit]`.
fn close_from(
    entries: Vec<Entry>,
    roles: &RoleHierarchy,
    index: usize,
    limit: usize,
) -> Option<Vec<Entry>> {
    if index < limit && index < entries.len() {
        let universal = match &entries[index] {
            Entry::Forall(role, filler) => Some((copy_role(role), *filler)),
            _ => None,
        };
        let entries = match universal {
            Some((role, filler)) => {
                match transitive_restrictions(entries, roles, 0, &role, filler) {
                    Some(entries) => entries,
                    None => return None,
                }
            }
            None => entries,
        };
        close_from(entries, roles, index + 1, limit)
    } else {
        Some(entries)
    }
}
/// The table with `∀t.d` for every universal restriction `∀q.d` it has and every
/// transitive role `t` included in `q`; `None` when there is no room.
pub fn close(entries: Vec<Entry>, roles: &RoleHierarchy) -> Option<Vec<Entry>> {
    let limit = entries.len();
    close_from(entries, roles, 0, limit)
}
/// Whether the entry is `∀role.filler`.
pub(crate) fn universal_is(entry: &Entry, role: &ObjectPropertyExpression, filler: usize) -> bool {
    match entry {
        Entry::Forall(other, inner) => {
            if *inner == filler {
                same_role(other, role)
            } else {
                false
            }
        }
        _ => false,
    }
}
/// The index of the first entry `∀role.filler` of `entries[index..]`, or the
/// length of the table.
pub fn universal_from(
    entries: &Vec<Entry>,
    role: &ObjectPropertyExpression,
    filler: usize,
    index: usize,
) -> usize {
    if index < entries.len() {
        if universal_is(&entries[index], role, filler) {
            index
        } else {
            universal_from(entries, role, filler, index + 1)
        }
    } else {
        entries.len()
    }
}
