//! The data values of the literals of five OWL 2 datatypes: `xsd:integer`,
//! `xsd:decimal`, `xsd:string`, `rdf:PlainLiteral` and `xsd:boolean`.
//!
//! A literal of one of them whose lexical form is in the datatype's lexical
//! space has a value:
//!
//! - an integer `(\+|-)?[0-9]+` or a decimal
//!   `(\+|-)?([0-9]+(\.[0-9]*)?|\.[0-9]+)` is a number, kept as its sign, the
//!   digits of its integer part without leading zeros and the digits of its
//!   fraction without trailing zeros, so that two lexical forms have the same
//!   value exactly when they give the same number (zero is not negative);
//! - a string is its UTF-8 bytes, which must encode XML characters;
//! - a plain literal `text@tag` is the string `text` when the tag after the
//!   last `@` is empty, and otherwise the pair of `text` and the tag in lower
//!   case, which must be a well-formed language tag;
//! - a boolean `true`, `1`, `false` or `0` is a truth value.
//!
//! Integers are decimal numbers, strings are plain literals, and numbers,
//! plain literals and truth values are pairwise different. Every other literal
//! has no value here: its datatype is another one, or its lexical form is not
//! in the lexical space.
#![allow(
    clippy::ptr_arg,
    clippy::needless_bool,
    clippy::manual_range_contains,
    clippy::len_zero,
    clippy::match_like_matches_macro
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::langtag::well_formed;
use crate::model::{Datatype, Literal};
use crate::unicode::{read_text, TextScan};

/// A data value.
pub enum DataValue {
    /// A decimal number: whether it is negative, the ASCII digits of its
    /// integer part without leading zeros and of its fraction without trailing
    /// zeros. Zero has no digits and is not negative.
    Number(bool, Vec<u8>, Vec<u8>),
    /// A string without a language tag, as its UTF-8 bytes.
    Text(Vec<u8>),
    /// A string with a language tag, the tag in lower case.
    Tagged(Vec<u8>, Vec<u8>),
    /// A truth value.
    Truth(bool),
}

/// The five datatypes.
#[derive(Clone, Copy)]
pub enum Kind {
    Integer,
    Decimal,
    String,
    Plain,
    Boolean,
}

fn equal_from(key: &Vec<u8>, pattern: &[u8], index: usize) -> bool {
    if index < key.len() {
        key[index] == pattern[index] && equal_from(key, pattern, index + 1)
    } else {
        true
    }
}
fn same_pattern(key: &Vec<u8>, pattern: &[u8]) -> bool {
    key.len() == pattern.len() && equal_from(key, pattern, 0)
}
/// The kind of a datatype, if it is one of the five.
pub fn kind_of(datatype: &Datatype) -> Option<Kind> {
    let iri = &datatype.iri.spelling;
    if same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#integer") {
        Some(Kind::Integer)
    } else if same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#decimal") {
        Some(Kind::Decimal)
    } else if same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#string") {
        Some(Kind::String)
    } else if same_pattern(
        iri,
        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
    ) {
        Some(Kind::Plain)
    } else if same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#boolean") {
        Some(Kind::Boolean)
    } else {
        None
    }
}

fn is_digit(byte: u8) -> bool {
    (48 <= byte) & (byte <= 57)
}
/// Whether `bytes[index..end]` are all ASCII digits.
fn digits_from(bytes: &Vec<u8>, index: usize, end: usize) -> bool {
    if index < end && index < bytes.len() {
        if is_digit(bytes[index]) {
            digits_from(bytes, index + 1, end)
        } else {
            false
        }
    } else {
        true
    }
}
/// The first index of `bytes[index..end]` that does not hold `0`, or `end`.
fn skip_zeros(bytes: &Vec<u8>, index: usize, end: usize) -> usize {
    if index < end && index < bytes.len() {
        if bytes[index] == 48 {
            skip_zeros(bytes, index + 1, end)
        } else {
            index
        }
    } else {
        end
    }
}
/// The end of `bytes[start..end]` without its trailing `0`s.
fn trim_zeros(bytes: &Vec<u8>, start: usize, end: usize) -> usize {
    if start < end && end <= bytes.len() {
        if bytes[end - 1] == 48 {
            trim_zeros(bytes, start, end - 1)
        } else {
            end
        }
    } else {
        start
    }
}
/// `out` followed by `bytes[index..end]`.
fn copy_range(bytes: &Vec<u8>, index: usize, end: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < end && index < bytes.len() {
        out.push(bytes[index]);
        copy_range(bytes, index + 1, end, out)
    } else {
        out
    }
}
/// The first index of `bytes[index..]` that holds `byte`, or the length.
fn find_byte(bytes: &Vec<u8>, byte: u8, index: usize) -> usize {
    if index < bytes.len() {
        if bytes[index] == byte {
            index
        } else {
            find_byte(bytes, byte, index + 1)
        }
    } else {
        bytes.len()
    }
}
/// Whether the bytes start with a sign.
fn signed(lexical: &Vec<u8>) -> bool {
    if 0 < lexical.len() {
        lexical[0] == 43 || lexical[0] == 45
    } else {
        false
    }
}
/// Whether the bytes start with a minus sign.
fn minus(lexical: &Vec<u8>) -> bool {
    if 0 < lexical.len() {
        lexical[0] == 45
    } else {
        false
    }
}
/// The number whose integer part is `lexical[start..dot]` and whose fraction is
/// `lexical[after..]`, negative when `negative` and it is not zero.
fn number_from(
    lexical: &Vec<u8>,
    negative: bool,
    start: usize,
    dot: usize,
    after: usize,
) -> DataValue {
    let first = skip_zeros(lexical, start, dot);
    let last = trim_zeros(lexical, after, lexical.len());
    let integer = copy_range(lexical, first, dot, Vec::new());
    let fraction = copy_range(lexical, after, last, Vec::new());
    let zero = integer.len() == 0 && fraction.len() == 0;
    DataValue::Number(negative && !zero, integer, fraction)
}
/// Whether `lexical` has the shape of a decimal lexical form, or an integer
/// one when `whole`, with its sign before `start`, its first point at `dot`
/// (the length when there is none) and its fraction from `after` on.
fn shaped(lexical: &Vec<u8>, whole: bool, start: usize, dot: usize, after: usize) -> bool {
    let length = lexical.len();
    !(whole && dot < length)
        && digits_from(lexical, start, dot)
        && digits_from(lexical, after, length)
        && !(dot == start && after == length)
}
/// The number of a decimal lexical form, or of an integer lexical form when
/// `whole`; `None` for any other bytes.
fn number_value(lexical: &Vec<u8>, whole: bool) -> Option<DataValue> {
    let length = lexical.len();
    let start = if signed(lexical) { 1 } else { 0 };
    let dot = find_byte(lexical, 46, start);
    let after = if dot < length { dot + 1 } else { length };
    if shaped(lexical, whole, start, dot, after) {
        Some(number_from(lexical, minus(lexical), start, dot, after))
    } else {
        None
    }
}
/// Whether the bytes are the UTF-8 encoding of XML characters.
fn xml_text(bytes: &Vec<u8>) -> bool {
    match read_text(bytes) {
        TextScan::Valid(_) => true,
        TextScan::Invalid(_) => false,
    }
}
/// The last index of `bytes[..end]` that holds `byte`, or the length.
fn last_byte(bytes: &Vec<u8>, byte: u8, end: usize) -> usize {
    if 0 < end && end <= bytes.len() {
        if bytes[end - 1] == byte {
            end - 1
        } else {
            last_byte(bytes, byte, end - 1)
        }
    } else {
        bytes.len()
    }
}
/// The ASCII lower case of a byte.
fn lower(byte: u8) -> u8 {
    if (65 <= byte) & (byte <= 90) {
        byte + 32
    } else {
        byte
    }
}
/// `out` followed by `bytes[index..]` in ASCII lower case.
fn lower_from(bytes: &Vec<u8>, index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < bytes.len() {
        out.push(lower(bytes[index]));
        lower_from(bytes, index + 1, out)
    } else {
        out
    }
}
/// The value of a plain literal with the text and the tag of its lexical form.
fn tagged_value(text: Vec<u8>, tag: &Vec<u8>) -> Option<DataValue> {
    if tag.len() == 0 {
        Some(DataValue::Text(text))
    } else if well_formed(tag) {
        Some(DataValue::Tagged(text, lower_from(tag, 0, Vec::new())))
    } else {
        None
    }
}
/// The value of a plain literal's lexical form `text@tag`, split at the last
/// `@`.
fn plain_value(lexical: &Vec<u8>) -> Option<DataValue> {
    let at = last_byte(lexical, 64, lexical.len());
    if at < lexical.len() {
        let text = copy_range(lexical, 0, at, Vec::new());
        if xml_text(&text) {
            tagged_value(
                text,
                &copy_range(lexical, at + 1, lexical.len(), Vec::new()),
            )
        } else {
            None
        }
    } else {
        None
    }
}
/// The value of a boolean lexical form.
fn truth_value(lexical: &Vec<u8>) -> Option<DataValue> {
    if same_pattern(lexical, b"true") || same_pattern(lexical, b"1") {
        Some(DataValue::Truth(true))
    } else if same_pattern(lexical, b"false") || same_pattern(lexical, b"0") {
        Some(DataValue::Truth(false))
    } else {
        None
    }
}
/// The value of a lexical form of the datatype of the kind, if it is in the
/// lexical space.
pub fn kind_value(kind: Kind, lexical: &Vec<u8>) -> Option<DataValue> {
    match kind {
        Kind::Integer => number_value(lexical, true),
        Kind::Decimal => number_value(lexical, false),
        Kind::String => {
            if xml_text(lexical) {
                Some(DataValue::Text(copy_range(
                    lexical,
                    0,
                    lexical.len(),
                    Vec::new(),
                )))
            } else {
                None
            }
        }
        Kind::Plain => plain_value(lexical),
        Kind::Boolean => truth_value(lexical),
    }
}
/// The value of a literal: `None` for another datatype or a lexical form
/// outside the lexical space.
pub fn literal_value(literal: &Literal) -> Option<DataValue> {
    match kind_of(&literal.datatype) {
        Some(kind) => kind_value(kind, &literal.lexical),
        None => None,
    }
}
fn same_bytes_from(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> bool {
    if index < left.len() && index < right.len() {
        left[index] == right[index] && same_bytes_from(left, right, index + 1)
    } else {
        true
    }
}
fn same_bytes(left: &Vec<u8>, right: &Vec<u8>) -> bool {
    left.len() == right.len() && same_bytes_from(left, right, 0)
}
/// Whether two values are the same.
pub fn same_value(left: &DataValue, right: &DataValue) -> bool {
    match left {
        DataValue::Number(a, b, c) => match right {
            DataValue::Number(d, e, f) => *a == *d && same_bytes(b, e) && same_bytes(c, f),
            _ => false,
        },
        DataValue::Text(a) => match right {
            DataValue::Text(b) => same_bytes(a, b),
            _ => false,
        },
        DataValue::Tagged(a, b) => match right {
            DataValue::Tagged(c, d) => same_bytes(a, c) && same_bytes(b, d),
            _ => false,
        },
        DataValue::Truth(a) => match right {
            DataValue::Truth(b) => *a == *b,
            _ => false,
        },
    }
}
/// Whether the value is in the value space of the datatype of the kind.
pub fn in_kind(value: &DataValue, kind: Kind) -> bool {
    match value {
        DataValue::Number(_, _, fraction) => match kind {
            Kind::Integer => fraction.len() == 0,
            Kind::Decimal => true,
            _ => false,
        },
        DataValue::Text(_) => match kind {
            Kind::String => true,
            Kind::Plain => true,
            _ => false,
        },
        DataValue::Tagged(_, _) => match kind {
            Kind::Plain => true,
            _ => false,
        },
        DataValue::Truth(_) => match kind {
            Kind::Boolean => true,
            _ => false,
        },
    }
}
