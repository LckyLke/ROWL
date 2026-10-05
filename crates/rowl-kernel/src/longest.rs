//! Longest regular-language prefix at a supplied UTF-8 byte position.
//!
//! The complete suffix is validated, so malformed UTF-8 remains an explicit
//! outcome even after an earlier accepted prefix. An empty match is distinct
//! from no match. Lexer grammars must separately exclude empty token matches.
use crate::regular::{derivative, nullable, Expression};
use crate::unicode::{decode_next, Decoded, TextError};

pub enum PrefixResult {
    Matched(Option<usize>),
    MalformedUtf8(TextError),
}

fn scan(
    expression: Expression,
    bytes: &Vec<u8>,
    offset: usize,
    last: Option<usize>,
) -> PrefixResult {
    let latest = if nullable(&expression) {
        Some(offset)
    } else {
        last
    };
    match decode_next(bytes, offset) {
        Decoded::End => PrefixResult::Matched(latest),
        Decoded::Error(error) => PrefixResult::MalformedUtf8(error),
        Decoded::Scalar { codepoint, next } => {
            scan(derivative(expression, codepoint), bytes, next, latest)
        }
    }
}

/// Return the greatest accepted exclusive byte endpoint, or None if no prefix
/// matches. Some(offset) denotes an empty match. All suffix bytes are checked
/// as strict UTF-8; no normalization or XML character filtering is performed.
#[allow(clippy::ptr_arg)] // Same source-linked Vec contract as the UTF-8 decoder.
pub fn longest_prefix(expression: Expression, bytes: &Vec<u8>, offset: usize) -> PrefixResult {
    scan(expression, bytes, offset, None)
}

fn dead(expression: &Expression) -> bool {
    matches!(expression, Expression::Empty)
}
fn scan_valid(
    expression: Expression,
    bytes: &Vec<u8>,
    offset: usize,
    last: Option<usize>,
) -> PrefixResult {
    if dead(&expression) {
        return PrefixResult::Matched(last);
    }
    let latest = if nullable(&expression) {
        Some(offset)
    } else {
        last
    };
    match decode_next(bytes, offset) {
        Decoded::End => PrefixResult::Matched(latest),
        Decoded::Error(error) => PrefixResult::MalformedUtf8(error),
        Decoded::Scalar { codepoint, next } => {
            scan_valid(derivative(expression, codepoint), bytes, next, latest)
        }
    }
}

/// `longest_prefix` for a suffix the caller has already validated as UTF-8:
/// the scan stops as soon as no longer prefix can match, instead of checking
/// the rest of the suffix. On a valid suffix the result is exactly the result of
/// `longest_prefix`, which the lexer uses after validating the whole text once.
#[allow(clippy::ptr_arg)] // Same source-linked Vec contract as the UTF-8 decoder.
pub fn longest_valid_prefix(
    expression: Expression,
    bytes: &Vec<u8>,
    offset: usize,
) -> PrefixResult {
    scan_valid(expression, bytes, offset, None)
}
