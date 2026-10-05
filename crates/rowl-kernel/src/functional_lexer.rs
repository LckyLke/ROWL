//! Functional Syntax token streams with XML text and separator validation.
//! Terminal kinds are proved disjoint; full ontology parsing remains pending.
#![allow(clippy::ptr_arg)]
use crate::functional::{longest_valid, next_terminal_fast, Selection, Terminal, Token};
use crate::longest::PrefixResult;
use crate::unicode::{decode_next, read_text, Decoded, TextError, TextScan};

pub enum Tokens {
    Empty,
    Cons { token: Token, next: Box<Tokens> },
}
pub enum LexResult {
    Tokens(Tokens),
    InvalidText(TextError),
    NoToken { offset: usize },
    MissingSeparator { offset: usize },
    TokenLimit { offset: usize },
    InvalidSpan { offset: usize },
}
enum Gap {
    Next(usize),
    Missing,
    InvalidText(TextError),
    InvalidSpan,
}
fn delimiter(cp: u32) -> bool {
    cp == 61 || cp == 40 || cp == 41 || cp == 60 || cp == 62 || cp == 64 || cp == 94
}
fn special(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Whitespace | Terminal::Comment)
}
// Every caller supplies an actually selected nonempty source segment. The None
// outcome keeps arbitrary malformed/split spans explicit and is proved excluded
// for those callers.
fn last_codepoint(bytes: &Vec<u8>, position: usize, end: usize, last: Option<u32>) -> Option<u32> {
    if position == end {
        return last;
    }
    if position > end {
        return None;
    }
    match decode_next(bytes, position) {
        Decoded::Scalar { codepoint, next } if next <= end => {
            last_codepoint(bytes, next, end, Some(codepoint))
        }
        _ => None,
    }
}
fn separator(bytes: &Vec<u8>, token: &Token) -> Gap {
    let last = match last_codepoint(bytes, token.start, token.end, None) {
        Some(cp) => cp,
        None => return Gap::InvalidSpan,
    };
    if delimiter(last) {
        return Gap::Next(token.end);
    }
    match decode_next(bytes, token.end) {
        Decoded::End => return Gap::Next(token.end),
        Decoded::Error(error) => return Gap::InvalidText(error),
        Decoded::Scalar { codepoint, .. } if delimiter(codepoint) => {
            return Gap::Next(token.end);
        }
        _ => {}
    }
    match longest_valid(Terminal::Whitespace, bytes, token.end) {
        PrefixResult::Matched(Some(end)) => return Gap::Next(end),
        PrefixResult::MalformedUtf8(error) => return Gap::InvalidText(error),
        PrefixResult::Matched(None) => {}
    }
    match longest_valid(Terminal::Comment, bytes, token.end) {
        PrefixResult::Matched(Some(end)) => Gap::Next(end),
        PrefixResult::MalformedUtf8(error) => Gap::InvalidText(error),
        PrefixResult::Matched(None) => Gap::Missing,
    }
}
fn scan(bytes: &Vec<u8>, position: usize, remaining: usize) -> LexResult {
    if position == bytes.len() {
        return LexResult::Tokens(Tokens::Empty);
    }
    match next_terminal_fast(bytes, position) {
        Selection::NoMatch => LexResult::NoToken { offset: position },
        Selection::MalformedUtf8(error) => LexResult::InvalidText(error),
        Selection::Token(token) => {
            if special(token.terminal) {
                return scan(bytes, token.end, remaining);
            }
            if remaining == 0 {
                return LexResult::TokenLimit { offset: position };
            }
            let end = match separator(bytes, &token) {
                Gap::Next(end) => end,
                Gap::Missing => {
                    return LexResult::MissingSeparator { offset: token.end };
                }
                Gap::InvalidText(error) => return LexResult::InvalidText(error),
                Gap::InvalidSpan => {
                    return LexResult::InvalidSpan { offset: position };
                }
            };
            match scan(bytes, end, remaining - 1) {
                LexResult::Tokens(tail) => LexResult::Tokens(Tokens::Cons {
                    token,
                    next: Box::new(tail),
                }),
                error => error,
            }
        }
    }
}
/// Lex the entire immutable UTF-8/XML source. Discard whitespace/comments and
/// enforce the standard delimiter/separator condition after regular tokens.
/// A token limit counts emitted regular tokens, excluding discarded trivia.
/// No successful partial stream is returned after a later error.
pub fn lex(bytes: &Vec<u8>, max_tokens: usize) -> LexResult {
    match read_text(bytes) {
        TextScan::Invalid(error) => LexResult::InvalidText(error),
        TextScan::Valid(_) => scan(bytes, 0, max_tokens),
    }
}
