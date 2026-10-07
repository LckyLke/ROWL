//! OWL 2 Functional Syntax names from the referenced SPARQL 2008 grammar.
//!
//! These whole-buffer recognizers cover PNAME_NS, PN_LOCAL, PNAME_LN and
//! BLANK_NODE_LABEL. They preserve strict UTF-8 diagnostics. They do not apply
//! the broader Turtle/SPARQL 1.1 local-name escape grammar or tokenize a document.
//! The ASCII scanners find the longest PNAME_NS and PNAME_LN at a position
//! without the grammars when the bytes that decide it are ASCII, and
//! `full_iri` the longest full IRI token `<…>` from the first `>` after it,
//! which no IRI contains.
use crate::iri::validate_iri;
use crate::longest::PrefixResult;
use crate::regular::{matches_utf8, Expression, MatchResult};

fn range(lower: u32, upper: u32) -> Expression {
    Expression::Interval { lower, upper }
}
fn ch(codepoint: u32) -> Expression {
    range(codepoint, codepoint)
}
fn alt(left: Expression, right: Expression) -> Expression {
    Expression::Alternative(Box::new(left), Box::new(right))
}
fn cat(left: Expression, right: Expression) -> Expression {
    Expression::Sequence(Box::new(left), Box::new(right))
}
fn opt(value: Expression) -> Expression {
    alt(Expression::Epsilon, value)
}
fn star(value: Expression) -> Expression {
    Expression::Repeat(Box::new(value))
}
fn base() -> Expression {
    alt(
        range(0x41, 0x5a),
        alt(
            range(0x61, 0x7a),
            alt(
                range(0xc0, 0xd6),
                alt(
                    range(0xd8, 0xf6),
                    alt(
                        range(0xf8, 0x2ff),
                        alt(
                            range(0x370, 0x37d),
                            alt(
                                range(0x37f, 0x1fff),
                                alt(
                                    range(0x200c, 0x200d),
                                    alt(
                                        range(0x2070, 0x218f),
                                        alt(
                                            range(0x2c00, 0x2fef),
                                            alt(
                                                range(0x3001, 0xd7ff),
                                                alt(
                                                    range(0xf900, 0xfdcf),
                                                    alt(
                                                        range(0xfdf0, 0xfffd),
                                                        range(0x10000, 0xeffff),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}
fn chars_u() -> Expression {
    alt(base(), ch(95))
}
fn chars() -> Expression {
    alt(
        chars_u(),
        alt(
            ch(45),
            alt(
                range(48, 57),
                alt(ch(0xb7), alt(range(0x300, 0x36f), range(0x203f, 0x2040))),
            ),
        ),
    )
}
fn ending() -> Expression {
    opt(cat(star(alt(chars(), ch(46))), chars()))
}
fn prefix_word() -> Expression {
    cat(base(), ending())
}
pub(crate) fn local_word() -> Expression {
    cat(alt(chars_u(), range(48, 57)), ending())
}
pub(crate) fn prefix_grammar() -> Expression {
    cat(opt(prefix_word()), ch(58))
}
pub(crate) fn abbreviated_grammar() -> Expression {
    cat(prefix_grammar(), local_word())
}
pub(crate) fn node_grammar() -> Expression {
    cat(cat(ch(95), ch(58)), local_word())
}

/// Whether an ASCII scan from the start of a buffer of `length` bytes read it
/// whole as one word.
pub(crate) fn whole(result: Option<PrefixResult>, length: usize) -> bool {
    match result {
        Some(PrefixResult::Matched(Some(end))) => end == length,
        _ => false,
    }
}
/// Whole-buffer PNAME_NS recognition; ASCII names are scanned without the
/// grammar.
pub fn validate_prefix(bytes: &Vec<u8>) -> MatchResult {
    if whole(ascii_prefix(bytes, 0), bytes.len()) {
        MatchResult::Matched(true)
    } else {
        matches_utf8(prefix_grammar(), bytes)
    }
}
/// Whole-buffer PN_LOCAL recognition; ASCII names are scanned without the
/// grammar.
pub fn validate_local(bytes: &Vec<u8>) -> MatchResult {
    if whole(ascii_local(bytes, 0), bytes.len()) {
        MatchResult::Matched(true)
    } else {
        matches_utf8(local_word(), bytes)
    }
}
/// Whole-buffer PNAME_LN recognition; ASCII names are scanned without the
/// grammar.
pub fn validate_abbreviated(bytes: &Vec<u8>) -> MatchResult {
    if whole(ascii_abbreviated(bytes, 0), bytes.len()) {
        MatchResult::Matched(true)
    } else {
        matches_utf8(abbreviated_grammar(), bytes)
    }
}
pub fn validate_node(bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(node_grammar(), bytes)
}

/// An ASCII letter: the ASCII members of PN_CHARS_BASE.
#[allow(clippy::manual_range_contains)] // Keep comparisons explicit for extraction.
fn ascii_letter(byte: u8) -> bool {
    (65 <= byte && byte <= 90) || (97 <= byte && byte <= 122)
}
/// A byte that can begin a local name: an ASCII letter, `_` or a digit.
#[allow(clippy::manual_range_contains)]
fn local_start(byte: u8) -> bool {
    ascii_letter(byte) || byte == 95 || (48 <= byte && byte <= 57)
}
/// An ASCII byte of a label: a PN_CHARS member (a letter, a digit, `_` or
/// `-`) or a dot.
fn label_byte(byte: u8) -> bool {
    local_start(byte) || byte == 45 || byte == 46
}
/// The end of the run of label bytes from `index`.
#[allow(clippy::ptr_arg)]
fn label_end(bytes: &Vec<u8>, index: usize) -> usize {
    if index < bytes.len() {
        if label_byte(bytes[index]) {
            label_end(bytes, index + 1)
        } else {
            index
        }
    } else {
        index
    }
}
/// Whether the label run from `position` to `colon` is empty or a PN_PREFIX:
/// a letter first and no dot last.
#[allow(clippy::ptr_arg)]
fn prefix_label(bytes: &Vec<u8>, position: usize, colon: usize) -> bool {
    colon == position || (ascii_letter(bytes[position]) && bytes[colon - 1] != 46)
}
/// Where a PNAME_NS from `position` ends when ASCII bytes decide it:
/// `Some(Some(end))` for the prefix name ending at `end`, `Some(None)` when no
/// prefix name starts there, and `None` when a byte outside ASCII follows the
/// label run. A prefix name has exactly one colon, right after its label.
#[allow(clippy::ptr_arg)]
fn ascii_prefix_end(bytes: &Vec<u8>, position: usize) -> Option<Option<usize>> {
    let colon = label_end(bytes, position);
    if colon < bytes.len() {
        if bytes[colon] == 58 {
            if prefix_label(bytes, position, colon) {
                Some(Some(colon + 1))
            } else {
                Some(None)
            }
        } else if bytes[colon] < 128 {
            Some(None)
        } else {
            None
        }
    } else {
        Some(None)
    }
}
/// The greatest endpoint in `(start, end]` that does not follow a dot, for a
/// label run from `start` to `end` that does not begin with a dot.
#[allow(clippy::ptr_arg)]
fn trim_dots(bytes: &Vec<u8>, start: usize, end: usize) -> usize {
    if start + 1 < end {
        if bytes[end - 1] == 46 {
            trim_dots(bytes, start, end - 1)
        } else {
            end
        }
    } else {
        end
    }
}
/// The longest local name in the label run from `start` to `end`: up to its
/// last byte other than a dot, when the run begins with a letter, `_` or a
/// digit.
#[allow(clippy::ptr_arg)]
fn local_end(bytes: &Vec<u8>, start: usize, end: usize) -> Option<usize> {
    if start < end {
        if local_start(bytes[start]) {
            Some(trim_dots(bytes, start, end))
        } else {
            None
        }
    } else {
        None
    }
}
/// Whether the byte at `index`, if any, is ASCII.
#[allow(clippy::ptr_arg)]
fn ascii_at(bytes: &Vec<u8>, index: usize) -> bool {
    if index < bytes.len() {
        bytes[index] < 128
    } else {
        true
    }
}
/// The longest local name from `start` when ASCII bytes decide it.
#[allow(clippy::ptr_arg)]
fn ascii_local(bytes: &Vec<u8>, start: usize) -> Option<PrefixResult> {
    let end = label_end(bytes, start);
    if ascii_at(bytes, end) {
        Some(PrefixResult::Matched(local_end(bytes, start, end)))
    } else {
        None
    }
}
/// The longest PNAME_NS from `position` when the bytes that decide it are
/// ASCII, or `None` when a byte outside ASCII must be decoded first.
#[allow(clippy::ptr_arg, clippy::manual_map)] // Explicit match for the pinned extraction.
pub fn ascii_prefix(bytes: &Vec<u8>, position: usize) -> Option<PrefixResult> {
    match ascii_prefix_end(bytes, position) {
        Some(end) => Some(PrefixResult::Matched(end)),
        None => None,
    }
}
/// The longest PNAME_LN from `position` when the bytes that decide it are
/// ASCII, or `None` when a byte outside ASCII must be decoded first.
#[allow(clippy::ptr_arg)]
pub fn ascii_abbreviated(bytes: &Vec<u8>, position: usize) -> Option<PrefixResult> {
    match ascii_prefix_end(bytes, position) {
        Some(Some(start)) => ascii_local(bytes, start),
        Some(None) => Some(PrefixResult::Matched(None)),
        None => None,
    }
}

/// The first index of `bytes[index..]` that holds `>`, or the length.
#[allow(clippy::ptr_arg)]
fn gt_from(bytes: &Vec<u8>, mut index: usize) -> usize {
    while index < bytes.len() && bytes[index] != 62 {
        index += 1;
    }
    index
}

/// The bytes `bytes[start..end]`, for `start ≤ end ≤ bytes.len()`.
#[allow(clippy::ptr_arg)]
fn copy_between(bytes: &Vec<u8>, start: usize, end: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut index = start;
    while index < end && index < bytes.len() {
        out.push(bytes[index]);
        index += 1;
    }
    out
}

/// Whether `close` is inside the bytes and `bytes[start..close]` spells an
/// RFC 3987 IRI.
fn iri_until(bytes: &Vec<u8>, start: usize, close: usize) -> bool {
    close < bytes.len()
        && matches!(
            validate_iri(&copy_between(bytes, start, close)),
            MatchResult::Matched(true)
        )
}

/// The full IRI from `position`, whose content ends at `close`: the first `>`
/// after it, or the length when there is none.
fn full_iri_from(bytes: &Vec<u8>, position: usize, close: usize) -> PrefixResult {
    if iri_until(bytes, position + 1, close) {
        PrefixResult::Matched(Some(close + 1))
    } else {
        PrefixResult::Matched(None)
    }
}

/// The longest full IRI token from `position`: `<`, an IRI and `>`. No IRI
/// contains `>`, so a token can only end at the first `>` after the `<`, and
/// it exists exactly when the bytes between spell an IRI; `None` when the byte
/// at `position` is not `<`.
pub fn full_iri(bytes: &Vec<u8>, position: usize) -> Option<PrefixResult> {
    if position < bytes.len() && bytes[position] == 60 {
        Some(full_iri_from(bytes, position, gt_from(bytes, position + 1)))
    } else {
        None
    }
}
