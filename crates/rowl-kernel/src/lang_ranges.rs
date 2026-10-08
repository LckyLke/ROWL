//! The facet `rdf:langRange` of `rdf:PlainLiteral` (rdf:PlainLiteral §4,
//! RFC 4647 §2.1, §3.3.1): a basic language range, `*` or subtags of one to
//! eight ASCII letters, the first, or letters and digits, the others, joined
//! by `-`, matches the language tags that are the range or continue it after
//! a `-`, ignoring case, and `*` matches every language tag.
//!
//! The context keeps its ranges in lower case, and the values' tags are in
//! lower case, so a range matches a tag when it is `*`, the tag itself or the
//! tag up to a `-` (`range_matches`); a range continues another when the other
//! matches it as a tag. The free tags of a range are the well-formed language
//! tags in lower case that it matches and that none of the ranges continuing
//! it match (`free_tags`); the free tags of no range are the tags no range
//! matches (`root_free`). Whether there are any is found by a search along the
//! derivatives of the grammar of `langtag` over the letters of lower-case tags,
//! `-`, the digits and `a` to `z`, past the ranges that block it: a word is
//! blocked by a range it ends at or continues after a `-`.
#![allow(
    clippy::ptr_arg,
    clippy::manual_range_contains,
    clippy::len_zero,
    clippy::needless_return,
    clippy::collapsible_if
)] // Indexed operations and explicit branches for the pinned extraction subset.

use crate::langtag::{grammar, range_grammar};
use crate::regular::{
    copy_expression, derivative, matches_utf8, nullable, Expression, MatchResult,
};

/// Whether the bytes are `*`.
pub fn star(bytes: &Vec<u8>) -> bool {
    if bytes.len() == 1 {
        bytes[0] == 42
    } else {
        false
    }
}
/// Whether the bytes are a basic language range: `*`, or subtags of one to
/// eight ASCII letters, the first, or letters and digits, joined by `-`.
pub fn basic_range(bytes: &Vec<u8>) -> bool {
    matches!(
        matches_utf8(range_grammar(), bytes),
        MatchResult::Matched(true)
    )
}
/// `out` followed by `bytes[index..]` with the ASCII capital letters in lower
/// case.
fn lowered_from(bytes: &Vec<u8>, index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < bytes.len() {
        if out.len() < usize::MAX {
            let byte = bytes[index];
            if (65 <= byte) & (byte <= 90) {
                out.push(byte + 32);
            } else {
                out.push(byte);
            }
        }
        lowered_from(bytes, index + 1, out)
    } else {
        out
    }
}
/// The bytes with the ASCII capital letters in lower case.
pub fn lowered(bytes: &Vec<u8>) -> Vec<u8> {
    lowered_from(bytes, 0, Vec::new())
}
/// Whether `range[index..]` is `tag[index..]` up to the length of `range`.
fn prefix_from(range: &Vec<u8>, tag: &Vec<u8>, index: usize) -> bool {
    if index < range.len() {
        if index < tag.len() {
            if range[index] == tag[index] {
                prefix_from(range, tag, index + 1)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the range matches the tag: `*` every tag, and otherwise the tag
/// itself and the tags that continue it after a `-`.
pub fn range_matches(range: &Vec<u8>, tag: &Vec<u8>) -> bool {
    if star(range) {
        true
    } else if range.len() < tag.len() {
        if tag[range.len()] == 45 {
            prefix_from(range, tag, 0)
        } else {
            false
        }
    } else if range.len() == tag.len() {
        prefix_from(range, tag, 0)
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The search for free tags
// ---------------------------------------------------------------------------

/// Whether the language of an expression has a word.
pub fn nonempty(expression: &Expression) -> bool {
    match expression {
        Expression::Empty => false,
        Expression::Epsilon => true,
        Expression::Interval { lower, upper } => *lower <= *upper,
        Expression::Alternative(left, right) => nonempty(left) | nonempty(right),
        Expression::Sequence(left, right) => nonempty(left) & nonempty(right),
        Expression::Repeat(_) => true,
    }
}
/// The derivative of an expression along `bytes[index..]`.
fn derive(expression: Expression, bytes: &Vec<u8>, index: usize) -> Expression {
    if index < bytes.len() {
        derive(
            derivative(expression, bytes[index] as u32),
            bytes,
            index + 1,
        )
    } else {
        expression
    }
}
/// The letter of the language tags in lower case at `index`: `-`, then the
/// digits, then `a` to `z`; 37 of them.
fn tag_letter(index: u8) -> u8 {
    if index == 0 {
        45
    } else if index < 11 {
        47 + index
    } else {
        86 + index
    }
}
/// Whether a block of `blocks[index..]` has ended: the word so far is a range.
fn ended(blocks: &Vec<Vec<u8>>, index: usize) -> bool {
    if index < blocks.len() {
        if blocks[index].len() == 0 {
            true
        } else {
            ended(blocks, index + 1)
        }
    } else {
        false
    }
}
/// `out` followed by `bytes[index..]`.
fn copy_from(bytes: &Vec<u8>, index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < bytes.len() {
        if out.len() < usize::MAX {
            out.push(bytes[index]);
        }
        copy_from(bytes, index + 1, out)
    } else {
        out
    }
}
/// `out` with the blocks of `blocks[index..]` that go on with `letter`, each
/// past it.
fn blocks_after(
    blocks: &Vec<Vec<u8>>,
    letter: u8,
    index: usize,
    mut out: Vec<Vec<u8>>,
) -> Vec<Vec<u8>> {
    if index < blocks.len() {
        if 0 < blocks[index].len() {
            if blocks[index][0] == letter {
                if out.len() < usize::MAX {
                    out.push(copy_from(&blocks[index], 1, Vec::new()));
                }
            }
        }
        blocks_after(blocks, letter, index + 1, out)
    } else {
        out
    }
}
/// Whether some word of the expression of the letters of lower-case tags
/// passes every block: it is none of them and continues none of them after a
/// `-`. Each letter shortens the blocks that go on with it and drops the
/// others, so the search ends.
fn avoids(expression: Expression, blocks: &Vec<Vec<u8>>) -> bool {
    if blocks.len() == 0 {
        nonempty(&expression)
    } else {
        let stop = ended(blocks, 0);
        if !stop & nullable(&expression) {
            true
        } else {
            letters_avoid(&expression, blocks, stop, 0)
        }
    }
}
/// Whether some word of the expression that starts with a letter from the
/// letter at `letter` on passes every block; after a block that has ended, not
/// with `-` (`stop`).
fn letters_avoid(expression: &Expression, blocks: &Vec<Vec<u8>>, stop: bool, letter: u8) -> bool {
    if letter < 37 {
        let byte = tag_letter(letter);
        if stop & (byte == 45) {
            letters_avoid(expression, blocks, stop, letter + 1)
        } else if avoids(
            derivative(copy_expression(expression), byte as u32),
            &blocks_after(blocks, byte, 0, Vec::new()),
        ) {
            true
        } else {
            letters_avoid(expression, blocks, stop, letter + 1)
        }
    } else {
        false
    }
}
/// `out` with the parts after `range` and a `-` of the ranges of
/// `ranges[index..]` that continue it past a `-`.
fn continuations(
    range: &Vec<u8>,
    ranges: &Vec<Vec<u8>>,
    index: usize,
    mut out: Vec<Vec<u8>>,
) -> Vec<Vec<u8>> {
    if index < ranges.len() {
        if range.len() < ranges[index].len() {
            if range_matches(range, &ranges[index]) {
                if out.len() < usize::MAX {
                    out.push(copy_from(&ranges[index], range.len() + 1, Vec::new()));
                }
            }
        }
        continuations(range, ranges, index + 1, out)
    } else {
        out
    }
}
/// `out` with the ranges of `ranges[index..]` but `*`.
fn plain_ranges(ranges: &Vec<Vec<u8>>, index: usize, mut out: Vec<Vec<u8>>) -> Vec<Vec<u8>> {
    if index < ranges.len() {
        if !star(&ranges[index]) {
            if out.len() < usize::MAX {
                out.push(copy_from(&ranges[index], 0, Vec::new()));
            }
        }
        plain_ranges(ranges, index + 1, out)
    } else {
        out
    }
}
/// Whether some well-formed language tag in lower case matches no range of
/// `ranges` but `*`.
pub fn root_free(ranges: &Vec<Vec<u8>>) -> bool {
    avoids(grammar(), &plain_ranges(ranges, 0, Vec::new()))
}
/// Whether some well-formed language tag in lower case matches the range and
/// none of the ranges of `ranges` that continue it.
pub fn free_tags(range: &Vec<u8>, ranges: &Vec<Vec<u8>>) -> bool {
    if star(range) {
        root_free(ranges)
    } else {
        let blocks = continuations(range, ranges, 0, Vec::new());
        let rest = derive(grammar(), range, 0);
        if nullable(&rest) {
            true
        } else {
            avoids(derivative(rest, 45), &blocks)
        }
    }
}
