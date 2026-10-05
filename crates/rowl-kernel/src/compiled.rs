//! Regular expressions compiled into node tables and matched by partial
//! derivatives over continuation stacks.
//!
//! A table lists nodes whose parts come before them. A stack lists the nodes
//! that remain to be matched, the next one last. Consuming a code point
//! replaces every stack of the state by the stacks that remain after it, so no
//! part of the grammar is copied while matching and the work per code point
//! depends only on the nodes that can begin the rest of the text. A table or a
//! state that would exceed the `usize` range is reported as `None`, and the
//! callers then use the derivative matcher instead.
// Vec parameters, explicit pushes and nested matches stay within the pinned
// extraction subset.
#![allow(clippy::ptr_arg, clippy::vec_init_then_push, clippy::collapsible_match)]

use crate::longest::PrefixResult;
use crate::regular::{Expression, MatchResult};
use crate::unicode::{decode_next, Decoded};

pub enum Kind {
    Empty,
    Epsilon,
    Interval { lower: u32, upper: u32 },
    Alternative(usize, usize),
    Sequence(usize, usize),
    Repeat(usize),
}

/// A node and whether its language has the empty word.
pub struct Node {
    pub kind: Kind,
    pub nullable: bool,
}

/// A table under construction; `full` records that a node did not fit.
pub struct Table {
    pub nodes: Vec<Node>,
    pub full: bool,
}

/// An empty table.
pub fn table() -> Table {
    Table {
        nodes: Vec::new(),
        full: false,
    }
}

/// Whether the node at `part` exists and accepts the empty word.
fn accepts_empty(nodes: &Vec<Node>, part: usize) -> bool {
    if part < nodes.len() {
        nodes[part].nullable
    } else {
        false
    }
}

/// Whether a node of this kind, added at the end, accepts the empty word. A
/// part that is not already in the table reads as the empty language.
fn nullable_of(nodes: &Vec<Node>, kind: &Kind) -> bool {
    match kind {
        Kind::Empty | Kind::Interval { .. } => false,
        Kind::Epsilon | Kind::Repeat(_) => true,
        Kind::Alternative(left, right) => {
            if accepts_empty(nodes, *left) {
                true
            } else {
                accepts_empty(nodes, *right)
            }
        }
        Kind::Sequence(left, right) => {
            if accepts_empty(nodes, *left) {
                accepts_empty(nodes, *right)
            } else {
                false
            }
        }
    }
}

/// Add a node at the end and return its index. When the table has no room it
/// is marked full and the result is its length, which is no node.
pub fn add(table: &mut Table, kind: Kind) -> usize {
    let position = table.nodes.len();
    if position < usize::MAX {
        let nullable = nullable_of(&table.nodes, &kind);
        table.nodes.push(Node { kind, nullable });
        position
    } else {
        table.full = true;
        position
    }
}

/// Add the nodes of an expression and return the index of its root.
pub fn compile(table: &mut Table, expression: &Expression) -> usize {
    match expression {
        Expression::Empty => add(table, Kind::Empty),
        Expression::Epsilon => add(table, Kind::Epsilon),
        Expression::Interval { lower, upper } => add(
            table,
            Kind::Interval {
                lower: *lower,
                upper: *upper,
            },
        ),
        Expression::Alternative(left, right) => {
            let first = compile(table, left);
            let second = compile(table, right);
            add(table, Kind::Alternative(first, second))
        }
        Expression::Sequence(left, right) => {
            let first = compile(table, left);
            let second = compile(table, right);
            add(table, Kind::Sequence(first, second))
        }
        Expression::Repeat(inner) => {
            let body = compile(table, inner);
            add(table, Kind::Repeat(body))
        }
    }
}

/// `out` followed by `stack[index..end]`.
fn copy_from(stack: &Vec<usize>, index: usize, end: usize, mut out: Vec<usize>) -> Vec<usize> {
    if index < end && index < stack.len() {
        if out.len() < usize::MAX {
            out.push(stack[index]);
        }
        copy_from(stack, index + 1, end, out)
    } else {
        out
    }
}

/// `base` with `top` above it; `None` when there is no room.
fn above(base: &Vec<usize>, top: usize) -> Option<Vec<usize>> {
    let mut stack = copy_from(base, 0, base.len(), Vec::new());
    if stack.len() < usize::MAX {
        stack.push(top);
        Some(stack)
    } else {
        None
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

fn same(left: &Vec<usize>, right: &Vec<usize>) -> bool {
    if left.len() == right.len() {
        same_from(left, right, 0)
    } else {
        false
    }
}

/// Whether `states[index..]` lists the stack.
fn listed(states: &Vec<Vec<usize>>, stack: &Vec<usize>, index: usize) -> bool {
    if index < states.len() {
        if same(&states[index], stack) {
            true
        } else {
            listed(states, stack, index + 1)
        }
    } else {
        false
    }
}

/// Add a copy of the stack to `out` unless it is listed; false when `out` has
/// no room.
fn insert(out: &mut Vec<Vec<usize>>, stack: &Vec<usize>) -> bool {
    if listed(out, stack, 0) {
        true
    } else if out.len() < usize::MAX {
        out.push(copy_from(stack, 0, stack.len(), Vec::new()));
        true
    } else {
        false
    }
}

/// Add to `out` the stacks that remain after `codepoint` begins a word of node
/// `index` followed by a word of `base`; false when a vector has no room.
fn derive(
    nodes: &Vec<Node>,
    index: usize,
    base: &Vec<usize>,
    codepoint: u32,
    out: &mut Vec<Vec<usize>>,
) -> bool {
    if index < nodes.len() {
        match &nodes[index].kind {
            Kind::Empty | Kind::Epsilon => true,
            Kind::Interval { lower, upper } => {
                if *lower <= codepoint && codepoint <= *upper {
                    insert(out, base)
                } else {
                    true
                }
            }
            Kind::Alternative(left, right) => {
                let first = *left;
                let second = *right;
                let done = if first < index {
                    derive(nodes, first, base, codepoint, out)
                } else {
                    true
                };
                if done {
                    if second < index {
                        derive(nodes, second, base, codepoint, out)
                    } else {
                        true
                    }
                } else {
                    false
                }
            }
            Kind::Sequence(left, right) => {
                let first = *left;
                let second = *right;
                if first < index && second < index {
                    match above(base, second) {
                        Some(stack) => {
                            if derive(nodes, first, &stack, codepoint, out) {
                                if nodes[first].nullable {
                                    derive(nodes, second, base, codepoint, out)
                                } else {
                                    true
                                }
                            } else {
                                false
                            }
                        }
                        None => false,
                    }
                } else {
                    true
                }
            }
            Kind::Repeat(inner) => {
                let body = *inner;
                if body < index {
                    match above(base, index) {
                        Some(stack) => derive(nodes, body, &stack, codepoint, out),
                        None => false,
                    }
                } else {
                    true
                }
            }
        }
    } else {
        true
    }
}

/// Add to `out` the stacks that remain after `codepoint` begins a word of
/// `stack[..length]`, whose next node is the last.
fn derive_stack(
    nodes: &Vec<Node>,
    stack: &Vec<usize>,
    length: usize,
    codepoint: u32,
    out: &mut Vec<Vec<usize>>,
) -> bool {
    if 0 < length && length <= stack.len() {
        let top = stack[length - 1];
        let base = copy_from(stack, 0, length - 1, Vec::new());
        if derive(nodes, top, &base, codepoint, out) {
            if accepts_empty(nodes, top) {
                derive_stack(nodes, stack, length - 1, codepoint, out)
            } else {
                true
            }
        } else {
            false
        }
    } else {
        true
    }
}

/// Add to `out` the stacks that remain after `codepoint` begins a word of a
/// stack of `state[index..]`.
fn step(
    nodes: &Vec<Node>,
    state: &Vec<Vec<usize>>,
    index: usize,
    codepoint: u32,
    out: &mut Vec<Vec<usize>>,
) -> bool {
    if index < state.len() {
        if derive_stack(nodes, &state[index], state[index].len(), codepoint, out) {
            step(nodes, state, index + 1, codepoint, out)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether every node of `stack[index..]` accepts the empty word.
fn empty_from(nodes: &Vec<Node>, stack: &Vec<usize>, index: usize) -> bool {
    if index < stack.len() {
        if accepts_empty(nodes, stack[index]) {
            empty_from(nodes, stack, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether some stack of `state[index..]` accepts the empty word.
fn accepting(nodes: &Vec<Node>, state: &Vec<Vec<usize>>, index: usize) -> bool {
    if index < state.len() {
        if empty_from(nodes, &state[index], 0) {
            true
        } else {
            accepting(nodes, state, index + 1)
        }
    } else {
        false
    }
}

/// The state of the single stack with the root.
fn start(root: usize) -> Vec<Vec<usize>> {
    let mut stack = Vec::new();
    stack.push(root);
    let mut state = Vec::new();
    state.push(stack);
    state
}

fn match_from(
    nodes: &Vec<Node>,
    state: Vec<Vec<usize>>,
    bytes: &Vec<u8>,
    offset: usize,
) -> Option<MatchResult> {
    match decode_next(bytes, offset) {
        Decoded::End => Some(MatchResult::Matched(accepting(nodes, &state, 0))),
        Decoded::Error(error) => Some(MatchResult::MalformedUtf8(error)),
        Decoded::Scalar { codepoint, next } => {
            let mut out = Vec::new();
            if step(nodes, &state, 0, codepoint, &mut out) {
                match_from(nodes, out, bytes, next)
            } else {
                None
            }
        }
    }
}

/// Whether the entire input is a word of node `root`, with the derivative
/// matcher's result; `None` when the table or a state has no room.
pub fn matches(table: &Table, root: usize, bytes: &Vec<u8>) -> Option<MatchResult> {
    if table.full {
        None
    } else {
        match_from(&table.nodes, start(root), bytes, 0)
    }
}

#[allow(clippy::len_zero)] // Vec::is_empty lacks a model in the pinned extraction.
fn scan_from(
    nodes: &Vec<Node>,
    state: Vec<Vec<usize>>,
    bytes: &Vec<u8>,
    offset: usize,
    last: Option<usize>,
) -> Option<PrefixResult> {
    if state.len() == 0 {
        return Some(PrefixResult::Matched(last));
    }
    let latest = if accepting(nodes, &state, 0) {
        Some(offset)
    } else {
        last
    };
    match decode_next(bytes, offset) {
        Decoded::End => Some(PrefixResult::Matched(latest)),
        Decoded::Error(error) => Some(PrefixResult::MalformedUtf8(error)),
        Decoded::Scalar { codepoint, next } => {
            let mut out = Vec::new();
            if step(nodes, &state, 0, codepoint, &mut out) {
                scan_from(nodes, out, bytes, next, latest)
            } else {
                None
            }
        }
    }
}

/// The greatest endpoint of a word of node `root` from `offset`, for text whose
/// suffix is valid UTF-8, where it is `longest_prefix`'s result; the scan stops
/// once no stack is left. `None` when the table or a state has no room.
pub fn longest_valid(
    table: &Table,
    root: usize,
    bytes: &Vec<u8>,
    offset: usize,
) -> Option<PrefixResult> {
    if table.full {
        None
    } else {
        scan_from(&table.nodes, start(root), bytes, offset, None)
    }
}
