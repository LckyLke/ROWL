//! The data values of the literals of the OWL 2 datatypes the reasoner knows:
//! `owl:real`, `owl:rational`, `xsd:decimal`, `xsd:integer` and its twelve
//! subtypes, `xsd:string`, `rdf:PlainLiteral` and `xsd:boolean`.
//!
//! A literal of one of them whose lexical form is in the datatype's lexical
//! space has a value:
//!
//! - an integer `(\+|-)?[0-9]+` or a decimal
//!   `(\+|-)?([0-9]+(\.[0-9]*)?|\.[0-9]+)` is a number, kept as its sign, the
//!   digits of its integer part without leading zeros and the digits of its
//!   fraction without trailing zeros, so that two lexical forms have the same
//!   value exactly when they give the same number (zero is not negative);
//! - a literal of an integer subtype is an integer lexical form whose number
//!   lies within the subtype's bounds (`xsd:byte` from -128 to 127, ...);
//! - an `owl:rational` lexical form `numerator/denominator`, an integer lexical
//!   form, `/` and digits for a positive denominator, is the quotient: a number
//!   when it is a decimal, and otherwise a fraction in lowest terms;
//!   `owl:real` has no lexical forms;
//! - a string is its UTF-8 bytes, which must encode XML characters;
//! - a plain literal `text@tag` is the string `text` when the tag after the
//!   last `@` is empty, and otherwise the pair of `text` and the tag in lower
//!   case, which must be a well-formed language tag;
//! - a boolean `true`, `1`, `false` or `0` is a truth value.
//!
//! Numbers are compared exactly (`compare_values`), and the four range facets
//! `xsd:minInclusive`, `xsd:maxInclusive`, `xsd:minExclusive` and
//! `xsd:maxExclusive` are evaluated on single values (`facet_holds`). Every
//! other literal has no value here: its datatype is another one, or its
//! lexical form is not in the lexical space.
#![allow(
    clippy::ptr_arg,
    clippy::needless_bool,
    clippy::manual_range_contains,
    clippy::len_zero,
    clippy::match_like_matches_macro,
    clippy::vec_init_then_push,
    clippy::manual_filter,
    clippy::manual_map
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::langtag::well_formed;
use crate::model::{Datatype, Iri, Literal};
use crate::numbers::{
    canonical, compare_naturals, divide_naturals, gcd_naturals, multiply_naturals, ten_power,
    times_power,
};
use crate::unicode::{read_text, TextScan};

/// A data value.
pub enum DataValue {
    /// A decimal number: whether it is negative, the ASCII digits of its
    /// integer part without leading zeros and of its fraction without trailing
    /// zeros. Zero has no digits and is not negative.
    Number(bool, Vec<u8>, Vec<u8>),
    /// A rational number that is not a decimal: whether it is negative, and the
    /// ASCII digits of its numerator and of its denominator in lowest terms,
    /// without leading zeros.
    Fraction(bool, Vec<u8>, Vec<u8>),
    /// A string without a language tag, as its UTF-8 bytes.
    Text(Vec<u8>),
    /// A string with a language tag, the tag in lower case.
    Tagged(Vec<u8>, Vec<u8>),
    /// A truth value.
    Truth(bool),
}

/// The datatypes.
#[derive(Clone, Copy)]
pub enum Kind {
    Integer,
    Decimal,
    String,
    Plain,
    Boolean,
    Real,
    Rational,
    NonNegativeInteger,
    NonPositiveInteger,
    PositiveInteger,
    NegativeInteger,
    Long,
    Int,
    Short,
    Byte,
    UnsignedLong,
    UnsignedInt,
    UnsignedShort,
    UnsignedByte,
}

/// The range facets.
#[derive(Clone, Copy)]
pub enum Facet {
    MinInclusive,
    MaxInclusive,
    MinExclusive,
    MaxExclusive,
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
/// The kind at a position of the list of kinds.
fn kind_at(index: u8) -> Kind {
    match index {
        0 => Kind::Integer,
        1 => Kind::Decimal,
        2 => Kind::String,
        3 => Kind::Plain,
        4 => Kind::Boolean,
        5 => Kind::Real,
        6 => Kind::Rational,
        7 => Kind::NonNegativeInteger,
        8 => Kind::NonPositiveInteger,
        9 => Kind::PositiveInteger,
        10 => Kind::NegativeInteger,
        11 => Kind::Long,
        12 => Kind::Int,
        13 => Kind::Short,
        14 => Kind::Byte,
        15 => Kind::UnsignedLong,
        16 => Kind::UnsignedInt,
        17 => Kind::UnsignedShort,
        _ => Kind::UnsignedByte,
    }
}
/// Whether the IRI is the kind's datatype.
fn is_type(iri: &Vec<u8>, kind: Kind) -> bool {
    match kind {
        Kind::Integer => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#integer"),
        Kind::Decimal => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#decimal"),
        Kind::String => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#string"),
        Kind::Plain => same_pattern(
            iri,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
        ),
        Kind::Boolean => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#boolean"),
        Kind::Real => same_pattern(iri, b"http://www.w3.org/2002/07/owl#real"),
        Kind::Rational => same_pattern(iri, b"http://www.w3.org/2002/07/owl#rational"),
        Kind::NonNegativeInteger => {
            same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#nonNegativeInteger")
        }
        Kind::NonPositiveInteger => {
            same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#nonPositiveInteger")
        }
        Kind::PositiveInteger => {
            same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#positiveInteger")
        }
        Kind::NegativeInteger => {
            same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#negativeInteger")
        }
        Kind::Long => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#long"),
        Kind::Int => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#int"),
        Kind::Short => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#short"),
        Kind::Byte => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#byte"),
        Kind::UnsignedLong => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#unsignedLong"),
        Kind::UnsignedInt => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#unsignedInt"),
        Kind::UnsignedShort => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#unsignedShort"),
        Kind::UnsignedByte => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#unsignedByte"),
    }
}
/// The first kind from the position `index` on whose datatype the IRI is.
fn kind_from(iri: &Vec<u8>, index: u8) -> Option<Kind> {
    if index < 19 {
        if is_type(iri, kind_at(index)) {
            Some(kind_at(index))
        } else {
            kind_from(iri, index + 1)
        }
    } else {
        None
    }
}
/// The kind of a datatype, if it is one of the datatypes.
pub fn kind_of(datatype: &Datatype) -> Option<Kind> {
    kind_from(&datatype.iri.spelling, 0)
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
/// Whether the bytes are a nonempty run of ASCII digits.
fn all_digits(bytes: &Vec<u8>) -> bool {
    (0 < bytes.len()) & digits_from(bytes, 0, bytes.len())
}
/// The number of `2`s and `5`s that divide `digits`, and what remains:
/// `digits` divided by them, after `count` such factors so far.
fn strip_factors(digits: Vec<u8>, count: usize) -> (Vec<u8>, usize) {
    if count < usize::MAX {
        strip_by(digits, count)
    } else {
        (digits, count)
    }
}
/// `strip_factors` for a count with room for one more factor.
fn strip_by(digits: Vec<u8>, count: usize) -> (Vec<u8>, usize) {
    let mut two = Vec::new();
    two.push(50);
    let mut five = Vec::new();
    five.push(53);
    let (half, rest2) = divide_naturals(&digits, &two);
    let (fifth, rest5) = divide_naturals(&digits, &five);
    if 0 < digits.len() {
        if rest2.len() == 0 {
            strip_factors(half, count + 1)
        } else if rest5.len() == 0 {
            strip_factors(fifth, count + 1)
        } else {
            (digits, count)
        }
    } else {
        (digits, count)
    }
}
/// Whether the canonical digits write 1.
fn is_one(digits: &Vec<u8>) -> bool {
    if digits.len() == 1 {
        digits[0] == 49
    } else {
        false
    }
}
/// `out` followed by `count` zeros.
fn zeros(count: usize, mut out: Vec<u8>) -> Vec<u8> {
    if 0 < count {
        if out.len() < usize::MAX {
            out.push(48);
        }
        zeros(count - 1, out)
    } else {
        out
    }
}
/// The decimal number `digits / 10^places`, negative when `negative` and it is
/// not zero.
fn decimal_of(negative: bool, digits: &Vec<u8>, places: usize) -> DataValue {
    if places < digits.len() {
        let split = digits.len() - places;
        number_from(digits, negative, 0, split, split)
    } else {
        let padded = zeros(places - digits.len(), Vec::new());
        let written = copy_range(digits, 0, digits.len(), padded);
        let fraction_end = trim_zeros(&written, 0, written.len());
        let fraction = copy_range(&written, 0, fraction_end, Vec::new());
        DataValue::Number(negative && 0 < fraction.len(), Vec::new(), fraction)
    }
}
/// The value of `numerator / denominator` in lowest terms, both canonical, the
/// denominator not zero and their only common divisor 1: a number when the
/// denominator divides a power of ten, and otherwise a fraction.
fn lowest_value(negative: bool, numerator: Vec<u8>, denominator: Vec<u8>) -> DataValue {
    let (rest, places) = strip_factors(
        copy_range(&denominator, 0, denominator.len(), Vec::new()),
        0,
    );
    if is_one(&rest) {
        let scaled = times_power(numerator, places);
        let (digits, _) = divide_naturals(&scaled, &denominator);
        decimal_of(negative, &digits, places)
    } else {
        DataValue::Fraction(negative && 0 < numerator.len(), numerator, denominator)
    }
}
/// The value of `numerator / denominator` for canonical digits, the denominator
/// not zero.
fn quotient_value(negative: bool, numerator: &Vec<u8>, denominator: &Vec<u8>) -> DataValue {
    let common = gcd_naturals(numerator, denominator);
    let (top, _) = divide_naturals(numerator, &common);
    let (bottom, _) = divide_naturals(denominator, &common);
    lowest_value(negative, top, bottom)
}
/// The value of an `owl:rational` lexical form whose integer part is
/// canonical, given its sign, and whose denominator is written `written`.
fn over_value(negative: bool, numerator: &Vec<u8>, written: &Vec<u8>) -> Option<DataValue> {
    if all_digits(written) {
        let denominator = canonical(written);
        if 0 < denominator.len() {
            Some(quotient_value(negative, numerator, &denominator))
        } else {
            None
        }
    } else {
        None
    }
}
/// Whether the lexical form is short enough for exact arithmetic on it: the
/// decimal expansion of the quotient writes at most five digits per digit.
fn short(bytes: &Vec<u8>) -> bool {
    bytes.len() < usize::MAX / 16
}
/// The value of an `owl:rational` lexical form `numerator/denominator`.
fn rational_value(lexical: &Vec<u8>) -> Option<DataValue> {
    let slash = find_byte(lexical, 47, 0);
    if short(lexical) {
        if slash < lexical.len() {
            let written = copy_range(lexical, slash + 1, lexical.len(), Vec::new());
            match number_value(&copy_range(lexical, 0, slash, Vec::new()), true) {
                Some(DataValue::Number(negative, numerator, _)) => {
                    over_value(negative, &numerator, &written)
                }
                _ => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// A nonnegative integer from its ASCII digits.
fn positive_number(digits: &[u8]) -> DataValue {
    DataValue::Number(false, pattern_copy(digits, 0, Vec::new()), Vec::new())
}
/// A negative integer from the ASCII digits of its magnitude.
fn negative_number(digits: &[u8]) -> DataValue {
    DataValue::Number(true, pattern_copy(digits, 0, Vec::new()), Vec::new())
}
/// `out` followed by `pattern[index..]`.
fn pattern_copy(pattern: &[u8], index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < pattern.len() {
        if out.len() < usize::MAX {
            out.push(pattern[index]);
        }
        pattern_copy(pattern, index + 1, out)
    } else {
        out
    }
}
/// The least value of an integer subtype, if it has one.
pub fn lower_bound(kind: Kind) -> Option<DataValue> {
    match kind {
        Kind::NonNegativeInteger => Some(positive_number(b"")),
        Kind::PositiveInteger => Some(positive_number(b"1")),
        Kind::Long => Some(negative_number(b"9223372036854775808")),
        Kind::Int => Some(negative_number(b"2147483648")),
        Kind::Short => Some(negative_number(b"32768")),
        Kind::Byte => Some(negative_number(b"128")),
        Kind::UnsignedLong => Some(positive_number(b"")),
        Kind::UnsignedInt => Some(positive_number(b"")),
        Kind::UnsignedShort => Some(positive_number(b"")),
        Kind::UnsignedByte => Some(positive_number(b"")),
        _ => None,
    }
}
/// The greatest value of an integer subtype, if it has one.
pub fn upper_bound(kind: Kind) -> Option<DataValue> {
    match kind {
        Kind::NonPositiveInteger => Some(positive_number(b"")),
        Kind::NegativeInteger => Some(negative_number(b"1")),
        Kind::Long => Some(positive_number(b"9223372036854775807")),
        Kind::Int => Some(positive_number(b"2147483647")),
        Kind::Short => Some(positive_number(b"32767")),
        Kind::Byte => Some(positive_number(b"127")),
        Kind::UnsignedLong => Some(positive_number(b"18446744073709551615")),
        Kind::UnsignedInt => Some(positive_number(b"4294967295")),
        Kind::UnsignedShort => Some(positive_number(b"65535")),
        Kind::UnsignedByte => Some(positive_number(b"255")),
        _ => None,
    }
}
/// Whether the number is at least the kind's least value, if it has one.
fn above_lower(value: &DataValue, kind: Kind) -> bool {
    match lower_bound(kind) {
        Some(bound) => compare_numbers(value, &bound) != 0,
        None => true,
    }
}
/// Whether the number is at most the kind's greatest value, if it has one.
fn below_upper(value: &DataValue, kind: Kind) -> bool {
    match upper_bound(kind) {
        Some(bound) => compare_numbers(value, &bound) != 2,
        None => true,
    }
}
/// Whether a number, an integer when `whole`, is in the value space of the
/// kind's datatype.
fn number_in_kind(value: &DataValue, whole: bool, kind: Kind) -> bool {
    match kind {
        Kind::Integer => whole,
        Kind::Decimal => true,
        Kind::String => false,
        Kind::Plain => false,
        Kind::Boolean => false,
        Kind::Real => true,
        Kind::Rational => true,
        _ => whole & above_lower(value, kind) & below_upper(value, kind),
    }
}
/// The value of an integer lexical form of an integer subtype.
fn bounded_value(kind: Kind, lexical: &Vec<u8>) -> Option<DataValue> {
    match number_value(lexical, true) {
        Some(value) => {
            if number_in_kind(&value, true, kind) {
                Some(value)
            } else {
                None
            }
        }
        None => None,
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
        Kind::Real => None,
        Kind::Rational => rational_value(lexical),
        _ => bounded_value(kind, lexical),
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
        DataValue::Fraction(a, b, c) => match right {
            DataValue::Fraction(d, e, f) => *a == *d && same_bytes(b, e) && same_bytes(c, f),
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
        DataValue::Number(_, _, fraction) => number_in_kind(value, fraction.len() == 0, kind),
        DataValue::Fraction(_, _, _) => match kind {
            Kind::Real => true,
            Kind::Rational => true,
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

// ---------------------------------------------------------------------------
// The order of numbers
// ---------------------------------------------------------------------------

/// Whether the value is a number.
pub fn numeric(value: &DataValue) -> bool {
    match value {
        DataValue::Number(_, _, _) => true,
        DataValue::Fraction(_, _, _) => true,
        _ => false,
    }
}
/// Whether the value is a negative number.
fn negative(value: &DataValue) -> bool {
    match value {
        DataValue::Number(sign, _, _) => *sign,
        DataValue::Fraction(sign, _, _) => *sign,
        _ => false,
    }
}
/// The order of two canonical fractions of decimal numbers, written without
/// trailing zeros, from the digit `index` on.
fn compare_places(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> u8 {
    if index < left.len() {
        if index < right.len() {
            if left[index] < right[index] {
                0
            } else if right[index] < left[index] {
                2
            } else {
                compare_places(left, right, index + 1)
            }
        } else {
            2
        }
    } else if index < right.len() {
        0
    } else {
        1
    }
}
/// The order of the magnitudes of two canonical decimal numbers.
fn compare_decimals(
    left_whole: &Vec<u8>,
    left_fraction: &Vec<u8>,
    right_whole: &Vec<u8>,
    right_fraction: &Vec<u8>,
) -> u8 {
    let order = compare_naturals(left_whole, right_whole);
    if order == 1 {
        compare_places(left_fraction, right_fraction, 0)
    } else {
        order
    }
}
/// The numerator of a number's magnitude written as a fraction.
fn top_of(value: &DataValue) -> Vec<u8> {
    match value {
        DataValue::Number(_, whole, fraction) => canonical(&copy_range(
            fraction,
            0,
            fraction.len(),
            copy_range(whole, 0, whole.len(), Vec::new()),
        )),
        DataValue::Fraction(_, numerator, _) => {
            copy_range(numerator, 0, numerator.len(), Vec::new())
        }
        _ => Vec::new(),
    }
}
/// The denominator of a number's magnitude written as a fraction.
fn bottom_of(value: &DataValue) -> Vec<u8> {
    match value {
        DataValue::Number(_, _, fraction) => ten_power(fraction.len()),
        DataValue::Fraction(_, _, denominator) => {
            copy_range(denominator, 0, denominator.len(), Vec::new())
        }
        _ => ten_power(0),
    }
}
/// The order of the magnitudes of two numbers by cross-multiplication.
fn compare_crosswise(left: &DataValue, right: &DataValue) -> u8 {
    compare_naturals(
        &multiply_naturals(&top_of(left), &bottom_of(right)),
        &multiply_naturals(&top_of(right), &bottom_of(left)),
    )
}
/// The order of the magnitudes of two canonical numbers.
fn compare_magnitudes(left: &DataValue, right: &DataValue) -> u8 {
    match left {
        DataValue::Number(_, left_whole, left_fraction) => match right {
            DataValue::Number(_, right_whole, right_fraction) => {
                compare_decimals(left_whole, left_fraction, right_whole, right_fraction)
            }
            _ => compare_crosswise(left, right),
        },
        _ => compare_crosswise(left, right),
    }
}
/// How the signs decide an order: 0 when only `left` is negative, 1 when only
/// `right` is, 2 when neither is and 3 when both are.
fn sign_rule(left: &DataValue, right: &DataValue) -> u8 {
    if negative(left) {
        if negative(right) {
            3
        } else {
            0
        }
    } else if negative(right) {
        1
    } else {
        2
    }
}
/// The order of two canonical numbers: 0 when `left` is smaller, 1 when they
/// are equal and 2 when `left` is greater.
fn compare_numbers(left: &DataValue, right: &DataValue) -> u8 {
    match sign_rule(left, right) {
        0 => 0,
        1 => 2,
        2 => compare_magnitudes(left, right),
        _ => compare_magnitudes(right, left),
    }
}
/// The sum of two lengths, or the largest `usize` when it might not fit.
fn sum_of(first: usize, second: usize) -> usize {
    if (first < usize::MAX / 8) & (second < usize::MAX / 8) {
        first + second
    } else {
        usize::MAX
    }
}
/// The number of digits a number is written with.
fn width(value: &DataValue) -> usize {
    match value {
        DataValue::Number(_, whole, fraction) => sum_of(whole.len(), fraction.len()),
        DataValue::Fraction(_, numerator, denominator) => {
            sum_of(numerator.len(), denominator.len())
        }
        _ => 0,
    }
}
/// The order of two canonical numbers, `None` when either is not a number or
/// they are too long to compare.
pub fn compare_values(left: &DataValue, right: &DataValue) -> Option<u8> {
    if numeric(left) {
        if numeric(right) {
            if width(left) < usize::MAX / 8 {
                if width(right) < usize::MAX / 8 {
                    Some(compare_numbers(left, right))
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

// ---------------------------------------------------------------------------
// The range facets
// ---------------------------------------------------------------------------

/// The facet an IRI names, if it is one of the four range facets.
pub fn facet_of(iri: &Iri) -> Option<Facet> {
    let spelling = &iri.spelling;
    if same_pattern(spelling, b"http://www.w3.org/2001/XMLSchema#minInclusive") {
        Some(Facet::MinInclusive)
    } else if same_pattern(spelling, b"http://www.w3.org/2001/XMLSchema#maxInclusive") {
        Some(Facet::MaxInclusive)
    } else if same_pattern(spelling, b"http://www.w3.org/2001/XMLSchema#minExclusive") {
        Some(Facet::MinExclusive)
    } else if same_pattern(spelling, b"http://www.w3.org/2001/XMLSchema#maxExclusive") {
        Some(Facet::MaxExclusive)
    } else {
        None
    }
}
/// Whether an order of a value against a bound meets the facet.
fn facet_order(facet: Facet, order: u8) -> bool {
    match facet {
        Facet::MinInclusive => order != 0,
        Facet::MaxInclusive => order != 2,
        Facet::MinExclusive => order == 2,
        Facet::MaxExclusive => order == 0,
    }
}
/// Whether the value is in the facet value of the facet with the bound, for a
/// canonical number and bound; `None` when either is not a number.
pub fn facet_holds(facet: Facet, bound: &DataValue, value: &DataValue) -> Option<bool> {
    match compare_values(value, bound) {
        Some(order) => Some(facet_order(facet, order)),
        None => None,
    }
}
/// Whether the facet with the bound is in the facet space of the kind's
/// datatype: for `owl:real` and `owl:rational` every number, and for the
/// numeric datatypes of XML Schema every number of their value space.
pub fn facet_applies(kind: Kind, bound: &DataValue) -> bool {
    if numeric(bound) {
        match kind {
            Kind::Real => true,
            Kind::Rational => true,
            Kind::String => false,
            Kind::Plain => false,
            Kind::Boolean => false,
            _ => in_kind(bound, kind),
        }
    } else {
        false
    }
}
