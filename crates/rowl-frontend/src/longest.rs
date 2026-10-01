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
