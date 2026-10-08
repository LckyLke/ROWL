//! The regular expressions of the facet `xsd:pattern` (XML Schema 1.1 Part 2
//! §4.3.4, Appendix G), read from their code points into `regular`
//! expressions with the same strings of code points up to `#x10FFFF`.
//!
//! The reading follows the productions [64]-[98] left to right: a regular
//! expression is branches separated by `|`, a branch takes pieces for as long
//! as an atom can begin, a piece is an atom with the quantifier that follows
//! it, if one does, and an atom is a normal character, a character class or a
//! regular expression in parentheses. A character group is negative when it
//! begins with `^`, and after a single character a hyphen is a subtraction
//! before `[`, a character of its own before `]` or `-[`, and otherwise ends a
//! range at the next single character, neither of them an unescaped hyphen
//! (§G.4.1). Sets of characters are lists of code point intervals
//! (`Span`); a negative group or a subtraction takes complements among the
//! code points up to `#x10FFFF`. A quantifier repeats its atom's expression:
//! `{n,m}` as `n` copies followed by up to `m - n` optional ones.
//!
//! The reading gives no expression for the category escapes `\p{…}` and
//! `\P{…}`, nor for `\d`, `\D`, `\w` and `\W`, which depend on the Unicode
//! database, nor for a numeral of more than six digits' worth, nor for a
//! quantifier whose copies would make an expression of more than `SIZE` nodes.
#![allow(
    clippy::ptr_arg,
    clippy::manual_range_contains,
    clippy::len_zero,
    clippy::collapsible_else_if,
    clippy::needless_return,
    clippy::manual_map,
    clippy::question_mark,
    clippy::vec_init_then_push,
    clippy::if_same_then_else
)] // Indexed operations and explicit branches for the pinned extraction subset.

use crate::regular::{
    alternate, copy_expression, matches_utf8, repeat, sequence, Expression, MatchResult,
};
use crate::unicode::{decode_next, Decoded};

/// The code points from `lower` to `upper`, none when `upper < lower`.
pub struct Span {
    pub lower: u32,
    pub upper: u32,
}

/// The last code point.
pub const LAST: u32 = 0x10FFFF;

/// The most nodes that a quantifier's expression may have.
pub const SIZE: usize = 65536;

/// The numbers a numeral may write: below 2^20.
const NUMBERS: usize = 1048576;

// ---------------------------------------------------------------------------
// Sets of characters
// ---------------------------------------------------------------------------

fn span(lower: u32, upper: u32) -> Span {
    Span { lower, upper }
}

/// `out` followed by the spans of `spans[index..]`; `None` when there is no
/// room for them.
fn append_from(spans: &Vec<Span>, index: usize, mut out: Vec<Span>) -> Option<Vec<Span>> {
    if index < spans.len() {
        if out.len() < usize::MAX {
            out.push(span(spans[index].lower, spans[index].upper));
            append_from(spans, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}

/// `out` followed by the parts of the spans of `spans[index..]` from `lower`
/// to `upper`; `None` when there is no room for them.
fn meet_from(
    spans: &Vec<Span>,
    lower: u32,
    upper: u32,
    index: usize,
    mut out: Vec<Span>,
) -> Option<Vec<Span>> {
    if index < spans.len() {
        let low = if spans[index].lower < lower {
            lower
        } else {
            spans[index].lower
        };
        let high = if upper < spans[index].upper {
            upper
        } else {
            spans[index].upper
        };
        if low <= high {
            if out.len() < usize::MAX {
                out.push(span(low, high));
                meet_from(spans, lower, upper, index + 1, out)
            } else {
                None
            }
        } else {
            meet_from(spans, lower, upper, index + 1, out)
        }
    } else {
        Some(out)
    }
}

/// The code points of `spans` below `lower` and those above `upper` up to
/// `LAST`.
fn without(spans: &Vec<Span>, lower: u32, upper: u32) -> Option<Vec<Span>> {
    let below = if 0 < lower {
        meet_from(spans, 0, lower - 1, 0, Vec::new())
    } else {
        Some(Vec::new())
    };
    match below {
        Some(below) => {
            if upper < LAST {
                meet_from(spans, upper + 1, LAST, 0, below)
            } else {
                Some(below)
            }
        }
        None => None,
    }
}

/// The code points of `rest` outside the spans of `spans[index..]`.
fn without_from(spans: &Vec<Span>, index: usize, rest: Vec<Span>) -> Option<Vec<Span>> {
    if index < spans.len() {
        match without(&rest, spans[index].lower, spans[index].upper) {
            Some(next) => without_from(spans, index + 1, next),
            None => None,
        }
    } else {
        Some(rest)
    }
}

/// The code points up to `LAST` outside the spans.
fn complement(spans: &Vec<Span>) -> Option<Vec<Span>> {
    let mut all = Vec::new();
    all.push(span(0, LAST));
    without_from(spans, 0, all)
}

/// `out` followed by the code points of `left` in the spans of
/// `right[index..]`.
fn meet_all(
    left: &Vec<Span>,
    right: &Vec<Span>,
    index: usize,
    out: Vec<Span>,
) -> Option<Vec<Span>> {
    if index < right.len() {
        match meet_from(left, right[index].lower, right[index].upper, 0, out) {
            Some(out) => meet_all(left, right, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}

/// The code points of `left` outside `right`.
fn subtract(left: &Vec<Span>, right: &Vec<Span>) -> Option<Vec<Span>> {
    match complement(right) {
        Some(other) => meet_all(left, &other, 0, Vec::new()),
        None => None,
    }
}

/// The character `c`.
fn one(c: u32) -> Vec<Span> {
    let mut out = Vec::new();
    out.push(span(c, c));
    out
}

/// The characters `c` and `d`.
fn two(c: u32, d: u32) -> Vec<Span> {
    let mut out = Vec::new();
    out.push(span(c, c));
    out.push(span(d, d));
    out
}

/// The spaces of `\s`: tab, line feed, carriage return and space.
fn spaces() -> Vec<Span> {
    let mut out = Vec::new();
    out.push(span(9, 10));
    out.push(span(13, 13));
    out.push(span(32, 32));
    out
}

/// The name start characters of XML, `\i`.
fn name_starts() -> Vec<Span> {
    let mut out = Vec::new();
    out.push(span(58, 58));
    out.push(span(65, 90));
    out.push(span(95, 95));
    out.push(span(97, 122));
    out.push(span(0xC0, 0xD6));
    out.push(span(0xD8, 0xF6));
    out.push(span(0xF8, 0x2FF));
    out.push(span(0x370, 0x37D));
    out.push(span(0x37F, 0x1FFF));
    out.push(span(0x200C, 0x200D));
    out.push(span(0x2070, 0x218F));
    out.push(span(0x2C00, 0x2FEF));
    out.push(span(0x3001, 0xD7FF));
    out.push(span(0xF900, 0xFDCF));
    out.push(span(0xFDF0, 0xFFFD));
    out.push(span(0x10000, 0xEFFFF));
    out
}

/// The name characters of XML, `\c`.
fn name_chars() -> Vec<Span> {
    let mut out = name_starts();
    out.push(span(45, 46));
    out.push(span(48, 57));
    out.push(span(0xB7, 0xB7));
    out.push(span(0x300, 0x36F));
    out.push(span(0x203F, 0x2040));
    out
}

/// The characters of `.`: all but line feed and carriage return.
fn wildcard() -> Vec<Span> {
    let mut out = Vec::new();
    out.push(span(0, 9));
    out.push(span(11, 12));
    out.push(span(14, LAST));
    out
}

/// The expression of the strings of one character of `spans[index..]`.
fn spans_expression(spans: &Vec<Span>, index: usize) -> Expression {
    if index < spans.len() {
        alternate(
            Expression::Interval {
                lower: spans[index].lower,
                upper: spans[index].upper,
            },
            spans_expression(spans, index + 1),
        )
    } else {
        Expression::Empty
    }
}

// ---------------------------------------------------------------------------
// Characters
// ---------------------------------------------------------------------------

/// The code points of `bytes[offset..]` after `out`; `None` for malformed
/// UTF-8, or when there is no room for them.
fn decode_from(bytes: &Vec<u8>, offset: usize, mut out: Vec<u32>) -> Option<Vec<u32>> {
    match decode_next(bytes, offset) {
        Decoded::End => Some(out),
        Decoded::Error(_) => None,
        Decoded::Scalar { codepoint, next } => {
            if out.len() < usize::MAX {
                out.push(codepoint);
                decode_from(bytes, next, out)
            } else {
                None
            }
        }
    }
}

/// Whether the code point at `index` is `cp`.
fn is_at(cps: &Vec<u32>, index: usize, cp: u32) -> bool {
    if index < cps.len() {
        cps[index] == cp
    } else {
        false
    }
}

/// Whether the code points at `index` and after it are `first` and `second`.
fn pair_at(cps: &Vec<u32>, index: usize, first: u32, second: u32) -> bool {
    if index < cps.len() {
        if cps[index] == first {
            is_at(cps, index + 1, second)
        } else {
            false
        }
    } else {
        false
    }
}

/// Whether a code point is a metacharacter: `.`, `\`, `?`, `*`, `+`, `{`,
/// `}`, `(`, `)`, `|`, `[` or `]`.
fn meta(c: u32) -> bool {
    (c == 46)
        | (c == 92)
        | (c == 63)
        | (c == 42)
        | (c == 43)
        | (c == 123)
        | (c == 125)
        | (c == 40)
        | (c == 41)
        | (c == 124)
        | (c == 91)
        | (c == 93)
}

/// Whether an atom can begin at `index`: with a normal character, `\`, `[`,
/// `.` or `(`.
fn atom_start(cps: &Vec<u32>, index: usize) -> bool {
    if index < cps.len() {
        let c = cps[index];
        !meta(c) | (c == 92) | (c == 91) | (c == 46) | (c == 40)
    } else {
        false
    }
}

/// Whether a quantifier begins at `index`: with `?`, `*`, `+` or `{`.
fn quantifier_start(cps: &Vec<u32>, index: usize) -> bool {
    if index < cps.len() {
        let c = cps[index];
        (c == 63) | (c == 42) | (c == 43) | (c == 123)
    } else {
        false
    }
}

/// The character of a single-character escape by its letter.
fn escaped_char(x: u32) -> Option<u32> {
    if x == 110 {
        Some(10)
    } else if x == 114 {
        Some(13)
    } else if x == 116 {
        Some(9)
    } else if (x == 92)
        | (x == 124)
        | (x == 46)
        | (x == 63)
        | (x == 42)
        | (x == 43)
        | (x == 40)
        | (x == 41)
        | (x == 123)
        | (x == 125)
        | (x == 45)
        | (x == 91)
        | (x == 93)
        | (x == 94)
    {
        Some(x)
    } else {
        None
    }
}

/// Whether a letter after `\` makes a character class escape: `s`, `S`, `i`,
/// `I`, `c`, `C`, `d`, `D`, `w`, `W`, `p` or `P`.
fn class_letter(x: u32) -> bool {
    (x == 115)
        | (x == 83)
        | (x == 105)
        | (x == 73)
        | (x == 99)
        | (x == 67)
        | (x == 100)
        | (x == 68)
        | (x == 119)
        | (x == 87)
        | (x == 112)
        | (x == 80)
}

/// The characters of a multi-character escape by its letter: `\s`, `\S`,
/// `\i`, `\I`, `\c` and `\C`; `None` for the others.
fn multi_spans(x: u32) -> Option<Vec<Span>> {
    if x == 115 {
        Some(spaces())
    } else if x == 83 {
        complement(&spaces())
    } else if x == 105 {
        Some(name_starts())
    } else if x == 73 {
        complement(&name_starts())
    } else if x == 99 {
        Some(name_chars())
    } else if x == 67 {
        complement(&name_chars())
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Character classes
// ---------------------------------------------------------------------------

/// [80] The single character at `index` and the index after it.
fn single_char(cps: &Vec<u32>, index: usize) -> Option<(u32, usize)> {
    if index < cps.len() {
        let c = cps[index];
        if c == 92 {
            if index + 1 < cps.len() {
                match escaped_char(cps[index + 1]) {
                    Some(d) => Some((d, index + 2)),
                    None => None,
                }
            } else {
                None
            }
        } else if (c == 91) | (c == 93) {
            None
        } else {
            Some((c, index + 1))
        }
    } else {
        None
    }
}

/// The letter of the character class escape at `index`, if one begins there.
fn escape_letter(cps: &Vec<u32>, index: usize) -> Option<u32> {
    if index < cps.len() {
        if cps[index] == 92 {
            if index + 1 < cps.len() {
                if class_letter(cps[index + 1]) {
                    Some(cps[index + 1])
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// [79] The character group part at `index`, its characters and the index
/// after it.
fn part(cps: &Vec<u32>, index: usize) -> Option<(Vec<Span>, usize)> {
    match escape_letter(cps, index) {
        Some(x) => match multi_spans(x) {
            Some(spans) => Some((spans, index + 2)),
            None => None,
        },
        None => match single_char(cps, index) {
            Some((c, next)) => {
                if is_at(cps, next, 45) {
                    if is_at(cps, next + 1, 91) {
                        Some((one(c), next))
                    } else if is_at(cps, next + 1, 93) {
                        Some((two(c, 45), next + 1))
                    } else if pair_at(cps, next + 1, 45, 91) {
                        Some((two(c, 45), next + 1))
                    } else if is_at(cps, index, 45) | is_at(cps, next + 1, 45) {
                        None
                    } else {
                        match single_char(cps, next + 1) {
                            Some((d, after)) => {
                                let mut spans = Vec::new();
                                spans.push(span(c, d));
                                Some((spans, after))
                            }
                            None => None,
                        }
                    }
                } else {
                    Some((one(c), next))
                }
            }
            None => None,
        },
    }
}

/// Whether the parts of a character group end at `index`: before `]` or `-[`.
fn parts_end(cps: &Vec<u32>, index: usize) -> bool {
    is_at(cps, index, 93) | pair_at(cps, index, 45, 91)
}

/// [77] The parts from `index` on until they end: `out` with their characters,
/// and the index where they end.
fn parts(cps: &Vec<u32>, index: usize, out: Vec<Span>) -> Option<(Vec<Span>, usize)> {
    match part(cps, index) {
        Some((spans, next)) => match append_from(&spans, 0, out) {
            Some(joined) => {
                if parts_end(cps, next) {
                    Some((joined, next))
                } else if index < next {
                    parts(cps, next, joined)
                } else {
                    None
                }
            }
            None => None,
        },
        None => None,
    }
}

/// [76] The character group at `index`, its characters and the index after
/// it.
fn char_group(cps: &Vec<u32>, index: usize) -> Option<(Vec<Span>, usize)> {
    let negative = is_at(cps, index, 94);
    let start = if negative { index + 1 } else { index };
    match parts(cps, start, Vec::new()) {
        Some((spans, next)) => {
            let base = if negative {
                complement(&spans)
            } else {
                Some(spans)
            };
            match base {
                Some(base) => {
                    if is_at(cps, next, 45) {
                        match class_expr(cps, next + 1) {
                            Some((minus, after)) => match subtract(&base, &minus) {
                                Some(left) => Some((left, after)),
                                None => None,
                            },
                            None => None,
                        }
                    } else {
                        Some((base, next))
                    }
                }
                None => None,
            }
        }
        None => None,
    }
}

/// [75] The character class expression at `index`, its characters and the
/// index after its `]`.
fn class_expr(cps: &Vec<u32>, index: usize) -> Option<(Vec<Span>, usize)> {
    if is_at(cps, index, 91) {
        match char_group(cps, index + 1) {
            Some((spans, next)) => {
                if is_at(cps, next, 93) {
                    Some((spans, next + 1))
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        None
    }
}

/// [74] The character class at `index`, its characters and the index after
/// it.
fn char_class(cps: &Vec<u32>, index: usize) -> Option<(Vec<Span>, usize)> {
    if is_at(cps, index, 92) {
        if index + 1 < cps.len() {
            let x = cps[index + 1];
            match escaped_char(x) {
                Some(c) => Some((one(c), index + 2)),
                None => match multi_spans(x) {
                    Some(spans) => Some((spans, index + 2)),
                    None => None,
                },
            }
        } else {
            None
        }
    } else if is_at(cps, index, 91) {
        class_expr(cps, index)
    } else if is_at(cps, index, 46) {
        Some((wildcard(), index + 1))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Quantifiers
// ---------------------------------------------------------------------------

/// [71] The numeral from `index` on after the digits that make `value`: its
/// number and the index after its digits; `None` without digits or for a
/// number of `NUMBERS` or more.
fn digits_from(cps: &Vec<u32>, index: usize, value: usize, seen: bool) -> Option<(usize, usize)> {
    if index < cps.len() {
        let c = cps[index];
        if (48 <= c) & (c <= 57) {
            if value < NUMBERS / 10 {
                digits_from(cps, index + 1, value * 10 + (c - 48) as usize, true)
            } else {
                None
            }
        } else if seen {
            Some((value, index))
        } else {
            None
        }
    } else if seen {
        Some((value, index))
    } else {
        None
    }
}

/// [67] The quantifier at `index`: the least number of repetitions, the
/// greatest, if there is one, and the index after it.
fn quantifier(cps: &Vec<u32>, index: usize) -> Option<(usize, Option<usize>, usize)> {
    if is_at(cps, index, 63) {
        Some((0, Some(1), index + 1))
    } else if is_at(cps, index, 42) {
        Some((0, None, index + 1))
    } else if is_at(cps, index, 43) {
        Some((1, None, index + 1))
    } else if is_at(cps, index, 123) {
        match digits_from(cps, index + 1, 0, false) {
            Some((least, next)) => {
                if is_at(cps, next, 125) {
                    Some((least, Some(least), next + 1))
                } else if is_at(cps, next, 44) {
                    if is_at(cps, next + 1, 125) {
                        Some((least, None, next + 2))
                    } else {
                        match digits_from(cps, next + 1, 0, false) {
                            Some((most, after)) => {
                                if (least <= most) & is_at(cps, after, 125) {
                                    Some((least, Some(most), after + 1))
                                } else {
                                    None
                                }
                            }
                            None => None,
                        }
                    }
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        None
    }
}

/// `count` plus the nodes of the expression, or `cap` when that is not less.
fn size_from(expression: &Expression, count: usize, cap: usize) -> usize {
    if cap <= count {
        cap
    } else {
        match expression {
            Expression::Empty => count + 1,
            Expression::Epsilon => count + 1,
            Expression::Interval { .. } => count + 1,
            Expression::Alternative(left, right) => {
                size_from(right, size_from(left, count + 1, cap), cap)
            }
            Expression::Sequence(left, right) => {
                size_from(right, size_from(left, count + 1, cap), cap)
            }
            Expression::Repeat(inner) => size_from(inner, count + 1, cap),
        }
    }
}

/// `count` copies of the expression one after the other.
fn power(expression: &Expression, count: usize) -> Expression {
    if count == 0 {
        Expression::Epsilon
    } else {
        sequence(copy_expression(expression), power(expression, count - 1))
    }
}

/// Up to `count` copies of the expression one after the other.
fn at_most(expression: &Expression, count: usize) -> Expression {
    if count == 0 {
        Expression::Epsilon
    } else {
        alternate(
            Expression::Epsilon,
            sequence(copy_expression(expression), at_most(expression, count - 1)),
        )
    }
}

/// The expression repeated from `least` to `most` times, or at least `least`
/// times without `most`; `None` when the copies would make more than `SIZE`
/// nodes.
fn repeated(expression: Expression, least: usize, most: Option<usize>) -> Option<Expression> {
    let copies = match most {
        Some(m) => m,
        None => least + 1,
    };
    let size = size_from(&expression, 0, SIZE + 1);
    if (0 < size) && (copies <= SIZE / size) {
        let first = power(&expression, least);
        match most {
            Some(m) => Some(sequence(first, at_most(&expression, m - least))),
            None => Some(sequence(first, repeat(expression))),
        }
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Regular expressions
// ---------------------------------------------------------------------------

/// [64] The regular expression at `index`, its expression and the index after
/// it.
fn reg_exp(cps: &Vec<u32>, index: usize) -> Option<(Expression, usize)> {
    match branch(cps, index) {
        Some((left, next)) => {
            if is_at(cps, next, 124) {
                match reg_exp(cps, next + 1) {
                    Some((right, after)) => Some((alternate(left, right), after)),
                    None => None,
                }
            } else {
                Some((left, next))
            }
        }
        None => None,
    }
}

/// [65] The branch at `index`, its expression and the index after it.
fn branch(cps: &Vec<u32>, index: usize) -> Option<(Expression, usize)> {
    if atom_start(cps, index) {
        match piece(cps, index) {
            Some((first, next)) => {
                if index < next {
                    match branch(cps, next) {
                        Some((rest, after)) => Some((sequence(first, rest), after)),
                        None => None,
                    }
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some((Expression::Epsilon, index))
    }
}

/// [66] The piece at `index`, its expression and the index after it.
fn piece(cps: &Vec<u32>, index: usize) -> Option<(Expression, usize)> {
    match atom(cps, index) {
        Some((expression, next)) => {
            if quantifier_start(cps, next) {
                match quantifier(cps, next) {
                    Some((least, most, after)) => match repeated(expression, least, most) {
                        Some(result) => Some((result, after)),
                        None => None,
                    },
                    None => None,
                }
            } else {
                Some((expression, next))
            }
        }
        None => None,
    }
}

/// [72] The atom at `index`, its expression and the index after it.
fn atom(cps: &Vec<u32>, index: usize) -> Option<(Expression, usize)> {
    if index < cps.len() {
        let c = cps[index];
        if c == 40 {
            match reg_exp(cps, index + 1) {
                Some((expression, next)) => {
                    if is_at(cps, next, 41) {
                        Some((expression, next + 1))
                    } else {
                        None
                    }
                }
                None => None,
            }
        } else if (c == 92) | (c == 91) | (c == 46) {
            match char_class(cps, index) {
                Some((spans, next)) => Some((spans_expression(&spans, 0), next)),
                None => None,
            }
        } else if meta(c) {
            None
        } else {
            Some((Expression::Interval { lower: c, upper: c }, index + 1))
        }
    } else {
        None
    }
}

/// The expression of the strings of the regular expression that `bytes`
/// encode in UTF-8, all of them; `None` when they are none, or one that this
/// reading leaves out.
pub fn pattern_expression(bytes: &Vec<u8>) -> Option<Expression> {
    match decode_from(bytes, 0, Vec::new()) {
        Some(cps) => match reg_exp(&cps, 0) {
            Some((expression, next)) => {
                if next == cps.len() {
                    Some(expression)
                } else {
                    None
                }
            }
            None => None,
        },
        None => None,
    }
}

/// Whether the UTF-8 text `bytes` is a string of the expression; `None` for
/// malformed UTF-8.
pub fn pattern_matches(expression: &Expression, bytes: &Vec<u8>) -> Option<bool> {
    match matches_utf8(copy_expression(expression), bytes) {
        MatchResult::Matched(accepted) => Some(accepted),
        MatchResult::MalformedUtf8(_) => None,
    }
}
