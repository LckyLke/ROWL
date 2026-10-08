//! Counting the strings of combinations of the regular expressions of the
//! facet `xsd:pattern`, alongside the subtypes of `xsd:string` and the lengths
//! of `lengths`.
//!
//! The expressions are compiled into one node table (`compiled`). The XML
//! characters fall into atoms: the intervals of the nine atoms of `lengths`,
//! cut wherever an interval node of the table begins or ends (`refine`), so
//! that all characters of an atom are in the same base atom and in the same
//! interval nodes. A joint state is a state of the automaton of the strings of
//! `lengths` and, for each expression, a state of continuation stacks of
//! `compiled`; reading an atom moves the former by the atom's base atom and the
//! latter by its first character (`joint_step`). The joint states reachable
//! from the start are found one after the other (`explore`), two joint states
//! being the same when their strings' states are equal and their stacks are
//! the same sets. A joint state's profile is the rank of its strings' state
//! and which expressions accept the empty word there.
//!
//! `profile_count` counts, capped, the words with lengths from `low` on and
//! before `high`, or without end, that the joint automaton takes from its
//! first state to a state of a rank from `first` on and before `last` where
//! exactly the expressions of `profile` accept: the capped numbers of the
//! words of each length from each state follow from those one letter shorter,
//! and the count stops once its sum reaches the cap, the lengths reach `high`
//! or the numbers repeat; `None` when they do not within `PROFILE_SETTLE`
//! lengths.
#![allow(
    clippy::ptr_arg,
    clippy::manual_range_contains,
    clippy::len_zero,
    clippy::needless_return,
    clippy::too_many_arguments,
    clippy::vec_init_then_push,
    clippy::if_same_then_else,
    clippy::collapsible_else_if,
    clippy::manual_map,
    clippy::question_mark
)] // Indexed operations and explicit branches for the pinned extraction subset.

use crate::compiled::{accepting, compile, start, step, table, Kind, Node};
use crate::lengths::{capped_product, capped_sum, next_text, rank, same_counts};
use crate::regular::Expression;

/// The XML characters from `lower` to `upper`, all of the base atom `base` of
/// `lengths`.
pub struct Atom {
    pub lower: u32,
    pub upper: u32,
    pub base: usize,
}

/// A state of the automaton of the strings and, for each expression, a state
/// of continuation stacks.
pub struct Joint {
    pub text: usize,
    pub stacks: Vec<Vec<Vec<usize>>>,
}

/// The joint automaton: its atoms, the rank of the strings' state of each
/// joint state, which expressions accept there, and the state after each atom.
pub struct Automaton {
    pub atoms: Vec<Atom>,
    pub ranks: Vec<u8>,
    pub accepts: Vec<Vec<bool>>,
    pub next: Vec<Vec<usize>>,
}

/// The most joint states that `explore` finds.
pub const JOINT_STATES: usize = 4096;

/// How many lengths the counts of a profile may take to settle.
pub const PROFILE_SETTLE: usize = 4096;

/// The code point after the last.
const END: u32 = 0x110000;

// ---------------------------------------------------------------------------
// Atoms
// ---------------------------------------------------------------------------

fn atom(lower: u32, upper: u32, base: usize) -> Atom {
    Atom { lower, upper, base }
}

/// The intervals of the nine atoms of `lengths`: tab, line feed and carriage
/// return; the space; `:`; the ASCII letters; the ASCII digits; `-`; the other
/// name start characters; the other name characters; and the other XML
/// characters.
fn base_atoms() -> Vec<Atom> {
    let mut out = Vec::new();
    out.push(atom(9, 10, 0));
    out.push(atom(13, 13, 0));
    out.push(atom(32, 32, 1));
    out.push(atom(58, 58, 2));
    out.push(atom(65, 90, 3));
    out.push(atom(97, 122, 3));
    out.push(atom(48, 57, 4));
    out.push(atom(45, 45, 5));
    out.push(atom(0x5F, 0x5F, 6));
    out.push(atom(0xC0, 0xD6, 6));
    out.push(atom(0xD8, 0xF6, 6));
    out.push(atom(0xF8, 0x2FF, 6));
    out.push(atom(0x370, 0x37D, 6));
    out.push(atom(0x37F, 0x1FFF, 6));
    out.push(atom(0x200C, 0x200D, 6));
    out.push(atom(0x2070, 0x218F, 6));
    out.push(atom(0x2C00, 0x2FEF, 6));
    out.push(atom(0x3001, 0xD7FF, 6));
    out.push(atom(0xF900, 0xFDCF, 6));
    out.push(atom(0xFDF0, 0xFFFD, 6));
    out.push(atom(0x10000, 0xEFFFF, 6));
    out.push(atom(0x2E, 0x2E, 7));
    out.push(atom(0xB7, 0xB7, 7));
    out.push(atom(0x300, 0x36F, 7));
    out.push(atom(0x203F, 0x2040, 7));
    out.push(atom(0x21, 0x2C, 8));
    out.push(atom(0x2F, 0x2F, 8));
    out.push(atom(0x3B, 0x40, 8));
    out.push(atom(0x5B, 0x5E, 8));
    out.push(atom(0x60, 0x60, 8));
    out.push(atom(0x7B, 0xB6, 8));
    out.push(atom(0xB8, 0xBF, 8));
    out.push(atom(0xD7, 0xD7, 8));
    out.push(atom(0xF7, 0xF7, 8));
    out.push(atom(0x37E, 0x37E, 8));
    out.push(atom(0x2000, 0x200B, 8));
    out.push(atom(0x200E, 0x203E, 8));
    out.push(atom(0x2041, 0x206F, 8));
    out.push(atom(0x2190, 0x2BFF, 8));
    out.push(atom(0x2FF0, 0x3000, 8));
    out.push(atom(0xE000, 0xF8FF, 8));
    out.push(atom(0xFDD0, 0xFDEF, 8));
    out.push(atom(0xF0000, 0x10FFFF, 8));
    out
}

/// `out` followed by the atoms of `atoms[index..]`, each cut in two where `cut`
/// falls after its first character; `None` when there is no room.
fn split_from(atoms: &Vec<Atom>, cut: u32, index: usize, mut out: Vec<Atom>) -> Option<Vec<Atom>> {
    if index < atoms.len() {
        let lower = atoms[index].lower;
        let upper = atoms[index].upper;
        let base = atoms[index].base;
        if (lower < cut) & (cut <= upper) {
            if out.len() < usize::MAX - 1 {
                out.push(atom(lower, cut - 1, base));
                out.push(atom(cut, upper, base));
                split_from(atoms, cut, index + 1, out)
            } else {
                None
            }
        } else if out.len() < usize::MAX {
            out.push(atom(lower, upper, base));
            split_from(atoms, cut, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}

/// The atoms cut where each interval node of `nodes[index..]` begins and after
/// it ends.
fn refine(nodes: &Vec<Node>, index: usize, atoms: Vec<Atom>) -> Option<Vec<Atom>> {
    if index < nodes.len() {
        match &nodes[index].kind {
            Kind::Interval { lower, upper } => {
                let after = if *upper < END - 1 { *upper + 1 } else { END };
                match split_from(&atoms, *lower, 0, Vec::new()) {
                    Some(once) => match split_from(&once, after, 0, Vec::new()) {
                        Some(twice) => refine(nodes, index + 1, twice),
                        None => None,
                    },
                    None => None,
                }
            }
            _ => refine(nodes, index + 1, atoms),
        }
    } else {
        Some(atoms)
    }
}

// ---------------------------------------------------------------------------
// The joint automaton
// ---------------------------------------------------------------------------

/// `out` followed by the states after `codepoint` of the stack states of
/// `stacks[index..]`; `None` when a state has no room.
fn step_all(
    nodes: &Vec<Node>,
    stacks: &Vec<Vec<Vec<usize>>>,
    index: usize,
    codepoint: u32,
    mut out: Vec<Vec<Vec<usize>>>,
) -> Option<Vec<Vec<Vec<usize>>>> {
    if index < stacks.len() {
        let mut next = Vec::new();
        if step(nodes, &stacks[index], 0, codepoint, &mut next) {
            if out.len() < usize::MAX {
                out.push(next);
                step_all(nodes, stacks, index + 1, codepoint, out)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        Some(out)
    }
}

/// The joint state after an atom.
fn joint_step(nodes: &Vec<Node>, joint: &Joint, atom: &Atom) -> Option<Joint> {
    match step_all(nodes, &joint.stacks, 0, atom.lower, Vec::new()) {
        Some(stacks) => Some(Joint {
            text: next_text(joint.text, atom.base),
            stacks,
        }),
        None => None,
    }
}

/// Whether the stacks of `left[index..]` are all among `right`.
fn within(left: &Vec<Vec<usize>>, right: &Vec<Vec<usize>>, index: usize) -> bool {
    if index < left.len() {
        if listed_stack(right, &left[index], 0) {
            within(left, right, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether `left[index..]` and `right[index..]` agree, for equal lengths.
fn same_from(left: &Vec<usize>, right: &Vec<usize>, index: usize) -> bool {
    if index < left.len() && index < right.len() {
        if left[index] == right[index] {
            same_from(left, right, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether two stacks are the same.
fn same_stack(left: &Vec<usize>, right: &Vec<usize>) -> bool {
    if left.len() == right.len() {
        same_from(left, right, 0)
    } else {
        false
    }
}

/// Whether `states[index..]` lists the stack.
fn listed_stack(states: &Vec<Vec<usize>>, stack: &Vec<usize>, index: usize) -> bool {
    if index < states.len() {
        if same_stack(&states[index], stack) {
            true
        } else {
            listed_stack(states, stack, index + 1)
        }
    } else {
        false
    }
}

/// Whether the stack states of `left[index..]` and `right[index..]` are the
/// same sets, for equal lengths.
fn same_sets(left: &Vec<Vec<Vec<usize>>>, right: &Vec<Vec<Vec<usize>>>, index: usize) -> bool {
    if index < left.len() && index < right.len() {
        if within(&left[index], &right[index], 0) && within(&right[index], &left[index], 0) {
            same_sets(left, right, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether two joint states are the same.
fn same_joint(left: &Joint, right: &Joint) -> bool {
    (left.text == right.text)
        && (left.stacks.len() == right.stacks.len())
        && same_sets(&left.stacks, &right.stacks, 0)
}

/// The index of a joint state of `states[index..]` that is the same as
/// `joint`.
fn find_joint(states: &Vec<Joint>, joint: &Joint, index: usize) -> Option<usize> {
    if index < states.len() {
        if same_joint(&states[index], joint) {
            Some(index)
        } else {
            find_joint(states, joint, index + 1)
        }
    } else {
        None
    }
}

/// `row` followed by the joint states after the atoms of `atoms[atom..]` from
/// the joint state at `state`, with `states` and the new joint states found.
fn row(
    nodes: &Vec<Node>,
    atoms: &Vec<Atom>,
    state: usize,
    atom_index: usize,
    mut states: Vec<Joint>,
    mut out: Vec<usize>,
) -> Option<(Vec<Joint>, Vec<usize>)> {
    if (atom_index < atoms.len()) & (state < states.len()) {
        match joint_step(nodes, &states[state], &atoms[atom_index]) {
            Some(joint) => {
                let target = match find_joint(&states, &joint, 0) {
                    Some(found) => found,
                    None => {
                        let fresh = states.len();
                        if fresh < usize::MAX {
                            states.push(joint);
                        }
                        fresh
                    }
                };
                if (target < states.len()) & (out.len() < usize::MAX) {
                    out.push(target);
                    row(nodes, atoms, state, atom_index + 1, states, out)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some((states, out))
    }
}

/// The joint states and their rows of next states, from the rows of the first
/// `next.len()` states on; `None` when more than `fuel` states would be read.
fn explore(
    nodes: &Vec<Node>,
    atoms: &Vec<Atom>,
    states: Vec<Joint>,
    mut next: Vec<Vec<usize>>,
    fuel: usize,
) -> Option<(Vec<Joint>, Vec<Vec<usize>>)> {
    let state = next.len();
    if state < states.len() {
        if fuel == 0 {
            None
        } else {
            match row(nodes, atoms, state, 0, states, Vec::new()) {
                Some((found, out)) => {
                    if next.len() < usize::MAX {
                        next.push(out);
                        explore(nodes, atoms, found, next, fuel - 1)
                    } else {
                        None
                    }
                }
                None => None,
            }
        }
    } else {
        Some((states, next))
    }
}

/// `out` followed by the start states of the roots of `roots[index..]`.
fn starts(
    roots: &Vec<usize>,
    index: usize,
    mut out: Vec<Vec<Vec<usize>>>,
) -> Option<Vec<Vec<Vec<usize>>>> {
    if index < roots.len() {
        if out.len() < usize::MAX {
            out.push(start(roots[index]));
            starts(roots, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}

/// `out` followed by whether the stack states of `stacks[index..]` accept.
fn accepts_from(
    nodes: &Vec<Node>,
    stacks: &Vec<Vec<Vec<usize>>>,
    index: usize,
    mut out: Vec<bool>,
) -> Vec<bool> {
    if index < stacks.len() {
        if out.len() < usize::MAX {
            out.push(accepting(nodes, &stacks[index], 0));
        }
        accepts_from(nodes, stacks, index + 1, out)
    } else {
        out
    }
}

/// The ranks and accepting expressions of the joint states of
/// `states[index..]`, after `ranks` and `accepts`.
fn profiles_from(
    nodes: &Vec<Node>,
    states: &Vec<Joint>,
    index: usize,
    mut ranks: Vec<u8>,
    mut accepts: Vec<Vec<bool>>,
) -> (Vec<u8>, Vec<Vec<bool>>) {
    if index < states.len() {
        if (ranks.len() < usize::MAX) & (accepts.len() < usize::MAX) {
            ranks.push(rank(states[index].text));
            accepts.push(accepts_from(nodes, &states[index].stacks, 0, Vec::new()));
        }
        profiles_from(nodes, states, index + 1, ranks, accepts)
    } else {
        (ranks, accepts)
    }
}

/// `out` followed by the roots of the expressions of `expressions[index..]`
/// compiled into the table.
fn compile_all(
    nodes: &mut crate::compiled::Table,
    expressions: &Vec<Expression>,
    index: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if index < expressions.len() {
        let root = compile(nodes, &expressions[index]);
        if out.len() < usize::MAX {
            out.push(root);
        }
        compile_all(nodes, expressions, index + 1, out)
    } else {
        out
    }
}

/// The joint automaton of the expressions; `None` when the table or a state
/// has no room, or there are more than `JOINT_STATES` joint states.
pub fn automaton(expressions: &Vec<Expression>) -> Option<Automaton> {
    let mut compiled = table();
    let roots = compile_all(&mut compiled, expressions, 0, Vec::new());
    if compiled.full | (roots.len() != expressions.len()) {
        return None;
    }
    let nodes = compiled.nodes;
    match refine(&nodes, 0, base_atoms()) {
        Some(atoms) => match starts(&roots, 0, Vec::new()) {
            Some(first) => {
                let mut states = Vec::new();
                states.push(Joint {
                    text: 0,
                    stacks: first,
                });
                match explore(&nodes, &atoms, states, Vec::new(), JOINT_STATES) {
                    Some((found, next)) => {
                        let (ranks, accepts) =
                            profiles_from(&nodes, &found, 0, Vec::new(), Vec::new());
                        Some(Automaton {
                            atoms,
                            ranks,
                            accepts,
                            next,
                        })
                    }
                    None => None,
                }
            }
            None => None,
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Counting
// ---------------------------------------------------------------------------

/// Whether `left[index..]` and `right[index..]` are the same flags.
fn same_flags(left: &Vec<bool>, right: &Vec<bool>, index: usize) -> bool {
    if index < left.len() {
        if index < right.len() {
            (left[index] == right[index]) && same_flags(left, right, index + 1)
        } else {
            false
        }
    } else {
        right.len() <= index
    }
}

/// `out` followed by the capped numbers of the empty words from the states
/// from `state` on: one at a state of a rank from `first` on and before `last`
/// where exactly the expressions of `profile` accept.
fn initial_from(
    automaton: &Automaton,
    first: u8,
    last: u8,
    profile: &Vec<bool>,
    cap: usize,
    state: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if (state < automaton.ranks.len()) & (state < automaton.accepts.len()) {
        let counted = (first <= automaton.ranks[state])
            & (automaton.ranks[state] < last)
            & same_flags(&automaton.accepts[state], profile, 0);
        let value = if counted { capped_sum(0, 1, cap) } else { 0 };
        if out.len() < usize::MAX {
            out.push(value);
        }
        initial_from(automaton, first, last, profile, cap, state + 1, out)
    } else {
        out
    }
}

/// `total` plus the capped numbers of the words one letter longer than those
/// counted by `counts` that start with a letter of the atoms from `atom_index`
/// on from `state`, capped.
fn state_sum(
    automaton: &Automaton,
    counts: &Vec<usize>,
    cap: usize,
    state: usize,
    atom_index: usize,
    total: usize,
) -> usize {
    if (state < automaton.next.len()) & (atom_index < automaton.atoms.len()) {
        if atom_index < automaton.next[state].len() {
            let target = automaton.next[state][atom_index];
            let words = if target < counts.len() {
                counts[target]
            } else {
                0
            };
            let lower = automaton.atoms[atom_index].lower;
            let upper = automaton.atoms[atom_index].upper;
            let size = if (lower <= upper) & (upper < END) {
                (upper - lower) as usize + 1
            } else {
                0
            };
            state_sum(
                automaton,
                counts,
                cap,
                state,
                atom_index + 1,
                capped_sum(total, capped_product(size, words, cap), cap),
            )
        } else {
            total
        }
    } else {
        total
    }
}

/// `out` with the capped numbers of the words one letter longer than those
/// counted by `counts` from the states from `state` on.
fn step_from(
    automaton: &Automaton,
    counts: &Vec<usize>,
    cap: usize,
    state: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if state < automaton.next.len() {
        let value = state_sum(automaton, counts, cap, state, 0, 0);
        if out.len() < usize::MAX {
            out.push(value);
        }
        step_from(automaton, counts, cap, state + 1, out)
    } else {
        out
    }
}

/// `total` plus the capped number of the counted words with lengths from
/// `low` on and before `high`, or without end, from `length` on, that start in
/// the first state, where `counts` are the capped numbers of the counted words
/// of length `length` from each state; `None` when the numbers neither reach
/// the cap nor repeat within `fuel` more lengths.
fn count_from(
    automaton: &Automaton,
    cap: usize,
    counts: Vec<usize>,
    length: usize,
    low: usize,
    high: Option<usize>,
    total: usize,
    fuel: usize,
) -> Option<usize> {
    let ended = match high {
        Some(end) => end <= length,
        None => false,
    };
    if ended {
        Some(total)
    } else {
        let here = if 0 < counts.len() { counts[0] } else { 0 };
        let sum = if low <= length {
            capped_sum(total, here, cap)
        } else {
            total
        };
        if cap <= sum {
            Some(sum)
        } else {
            let next = step_from(automaton, &counts, cap, 0, Vec::new());
            if same_counts(&next, &counts, 0) {
                let from = if low <= length { length + 1 } else { low };
                let rest = match high {
                    Some(end) => {
                        if from < end {
                            capped_product(end - from, here, cap)
                        } else {
                            0
                        }
                    }
                    None => {
                        if here == 0 {
                            0
                        } else {
                            cap
                        }
                    }
                };
                Some(capped_sum(sum, rest, cap))
            } else if (fuel == 0) | (length == usize::MAX) {
                None
            } else {
                count_from(automaton, cap, next, length + 1, low, high, sum, fuel - 1)
            }
        }
    }
}

/// The number of the words with lengths from `low` on and before `high`, or
/// without end, that the joint automaton takes from its first state to a
/// state of a rank from `first` on and before `last` where exactly the
/// expressions of `profile` accept, or `cap` when that is not less; `None`
/// when the numbers do not settle within `PROFILE_SETTLE` lengths.
pub fn profile_count(
    automaton: &Automaton,
    first: u8,
    last: u8,
    profile: &Vec<bool>,
    low: usize,
    high: Option<usize>,
    cap: usize,
) -> Option<usize> {
    let counts = initial_from(automaton, first, last, profile, cap, 0, Vec::new());
    count_from(automaton, cap, counts, 0, low, high, 0, PROFILE_SETTLE)
}
