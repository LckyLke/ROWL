//! The data values of the literals of the OWL 2 datatypes the reasoner knows:
//! `owl:real`, `owl:rational`, `xsd:decimal`, `xsd:integer` and its twelve
//! subtypes, `xsd:string` and its six subtypes `xsd:normalizedString`,
//! `xsd:token`, `xsd:language`, `xsd:NMTOKEN`, `xsd:Name` and `xsd:NCName`,
//! `rdf:PlainLiteral`, `xsd:boolean`, `xsd:anyURI`, `xsd:hexBinary` and
//! `xsd:base64Binary`.
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
//! - a string is its UTF-8 bytes, which must encode XML characters; a literal
//!   of a subtype of `xsd:string` is the string of its lexical form, which
//!   must be in the subtype (XML Schema 1.1 §3.4: no tab, line feed or carriage
//!   return in a normalized string; no space first, last or twice in a row in
//!   a token; `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*` for a language; the XML 1.1
//!   productions `Nmtoken` and `Name`, and `Name` without `:` for `NCName`);
//! - a plain literal `text@tag` is the string `text` when the tag after the
//!   last `@` is empty, and otherwise the pair of `text` and the tag in lower
//!   case, which must be a well-formed language tag;
//! - a boolean `true`, `1`, `false` or `0` is a truth value;
//! - an `xsd:anyURI` literal is the IRI of its characters, which must be XML
//!   characters (XML Schema 1.1: the lexical mapping is the identity);
//! - an `xsd:hexBinary` literal `([0-9a-fA-F]{2})*` is the octets its digit
//!   pairs write, and an `xsd:base64Binary` literal, Base64 groups with at most
//!   one space after each character but the last, the octets they encode; the
//!   two datatypes have disjoint copies of the octet sequences as values.
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
    clippy::manual_map,
    clippy::manual_is_multiple_of
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::floats::binary_value;
use crate::langtag::well_formed;
use crate::model::{Datatype, Iri, Literal};
use crate::moments::moment_value;
use crate::numbers::{
    canonical, compare_naturals, divide_naturals, gcd_naturals, multiply_naturals, ten_power,
    times_power,
};
use crate::unicode::{read_text, Scalars, TextScan};

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
    /// An IRI of `xsd:anyURI`, as the UTF-8 bytes of its characters.
    Uri(Vec<u8>),
    /// The octets of an `xsd:hexBinary` value.
    Hex(Vec<u8>),
    /// The octets of an `xsd:base64Binary` value.
    Base64(Vec<u8>),
    /// A time instant of `xsd:dateTime`.
    Moment(Moment),
    /// A value of `xsd:double`.
    Double(Binary),
    /// A value of `xsd:float`.
    Float(Binary),
}

/// A value of `xsd:double` or `xsd:float` (XML Schema 1.1 Part 2 §3.3.5): a
/// finite value `±m × 2^(scale − floats::BIAS)` with an odd `m` (zero for the
/// two zeros, whose scale is `floats::BIAS`), an infinity, or NaN.
pub enum Binary {
    Finite(bool, u64, usize),
    Infinite(bool),
    NotANumber,
}

/// A time instant of `xsd:dateTime` (XML Schema 1.1 Part 2 §D.2.1): the date
/// and the time as written in its time zone, if it has one.
pub struct Moment {
    /// Whether the year is negative.
    pub negative: bool,
    /// The ASCII digits of the year without leading zeros: year zero has none
    /// and is not negative.
    pub year: Vec<u8>,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    /// The whole seconds.
    pub second: u8,
    /// The ASCII digits of the fraction of a second without trailing zeros.
    pub fraction: Vec<u8>,
    /// The time zone offset: whether it is west of UTC, its hours and its
    /// minutes. An offset of zero is not west.
    pub zone: Option<(bool, u8, u8)>,
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
    AnyUri,
    HexBinary,
    Base64Binary,
    NormalizedString,
    Token,
    Language,
    NmToken,
    Name,
    NcName,
    DateTime,
    DateTimeStamp,
    Double,
    Float,
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
        18 => Kind::UnsignedByte,
        19 => Kind::AnyUri,
        20 => Kind::HexBinary,
        21 => Kind::Base64Binary,
        22 => Kind::NormalizedString,
        23 => Kind::Token,
        24 => Kind::Language,
        25 => Kind::NmToken,
        26 => Kind::Name,
        27 => Kind::NcName,
        28 => Kind::DateTime,
        29 => Kind::DateTimeStamp,
        30 => Kind::Double,
        _ => Kind::Float,
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
        Kind::AnyUri => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#anyURI"),
        Kind::HexBinary => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#hexBinary"),
        Kind::Base64Binary => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#base64Binary"),
        Kind::NormalizedString => {
            same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#normalizedString")
        }
        Kind::Token => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#token"),
        Kind::Language => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#language"),
        Kind::NmToken => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#NMTOKEN"),
        Kind::Name => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#Name"),
        Kind::NcName => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#NCName"),
        Kind::DateTime => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#dateTime"),
        Kind::DateTimeStamp => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#dateTimeStamp"),
        Kind::Double => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#double"),
        Kind::Float => same_pattern(iri, b"http://www.w3.org/2001/XMLSchema#float"),
    }
}
/// The first kind from the position `index` on whose datatype the IRI is.
fn kind_from(iri: &Vec<u8>, index: u8) -> Option<Kind> {
    if index < 32 {
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
        Kind::AnyUri => false,
        Kind::HexBinary => false,
        Kind::Base64Binary => false,
        Kind::NormalizedString => false,
        Kind::Token => false,
        Kind::Language => false,
        Kind::NmToken => false,
        Kind::Name => false,
        Kind::NcName => false,
        Kind::DateTime => false,
        Kind::DateTimeStamp => false,
        Kind::Double => false,
        Kind::Float => false,
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
/// The value of a hexadecimal digit.
fn hex_digit(byte: u8) -> Option<u8> {
    if (48 <= byte) & (byte <= 57) {
        Some(byte - 48)
    } else if (65 <= byte) & (byte <= 70) {
        Some(byte - 55)
    } else if (97 <= byte) & (byte <= 102) {
        Some(byte - 87)
    } else {
        None
    }
}
/// `out` followed by the octet, when there is room.
fn push_octet(mut out: Vec<u8>, octet: u8) -> Option<Vec<u8>> {
    if out.len() < usize::MAX {
        out.push(octet);
        Some(out)
    } else {
        None
    }
}
/// `out` followed by the octets that the hexadecimal digit pairs of
/// `lexical[index..]` write; `None` when they are no such pairs.
fn hex_from(lexical: &Vec<u8>, index: usize, out: Vec<u8>) -> Option<Vec<u8>> {
    if index < lexical.len() {
        if index + 1 < lexical.len() {
            match hex_digit(lexical[index]) {
                Some(high) => match hex_digit(lexical[index + 1]) {
                    Some(low) => match push_octet(out, high * 16 + low) {
                        Some(out) => hex_from(lexical, index + 2, out),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The value of a character of the Base64 alphabet.
fn sextet(byte: u8) -> Option<u8> {
    if (65 <= byte) & (byte <= 90) {
        Some(byte - 65)
    } else if (97 <= byte) & (byte <= 122) {
        Some(byte - 71)
    } else if (48 <= byte) & (byte <= 57) {
        Some(byte + 4)
    } else if byte == 43 {
        Some(62)
    } else if byte == 47 {
        Some(63)
    } else {
        None
    }
}
/// `out` followed by the characters of `lexical[index..]` without the single
/// spaces that may follow each character but the last; `None` for any other
/// space.
fn unspaced(lexical: &Vec<u8>, index: usize, out: Vec<u8>) -> Option<Vec<u8>> {
    if index < lexical.len() {
        if lexical[index] == 32 {
            None
        } else {
            match push_octet(out, lexical[index]) {
                Some(out) => {
                    if index + 1 < lexical.len() {
                        if lexical[index + 1] == 32 {
                            if index + 2 < lexical.len() {
                                unspaced(lexical, index + 2, out)
                            } else {
                                None
                            }
                        } else {
                            unspaced(lexical, index + 1, out)
                        }
                    } else {
                        Some(out)
                    }
                }
                None => None,
            }
        }
    } else {
        Some(out)
    }
}
/// `out` followed by the octets of a final group `a b = =` of one octet.
fn padded_one(chars: &Vec<u8>, index: usize, a: u8, b: u8, out: Vec<u8>) -> Option<Vec<u8>> {
    if chars[index + 3] == 61 {
        if index + 4 == chars.len() {
            if b % 16 == 0 {
                push_octet(out, a * 4 + b / 16)
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
/// `out` followed by the octets of a final group `a b c =` of two octets.
fn padded_two(chars: &Vec<u8>, index: usize, a: u8, b: u8, c: u8, out: Vec<u8>) -> Option<Vec<u8>> {
    if index + 4 == chars.len() {
        if c % 4 == 0 {
            match push_octet(out, a * 4 + b / 16) {
                Some(out) => push_octet(out, (b % 16) * 16 + c / 4),
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// `out` followed by the three octets of a full group `a b c d`.
fn full_group(out: Vec<u8>, a: u8, b: u8, c: u8, d: u8) -> Option<Vec<u8>> {
    match push_octet(out, a * 4 + b / 16) {
        Some(out) => match push_octet(out, (b % 16) * 16 + c / 4) {
            Some(out) => push_octet(out, (c % 4) * 64 + d),
            None => None,
        },
        None => None,
    }
}
/// `out` followed by the octets that the Base64 groups of `chars[index..]`
/// encode; `None` when they are no such groups.
fn base64_from(chars: &Vec<u8>, index: usize, out: Vec<u8>) -> Option<Vec<u8>> {
    if index < chars.len() {
        if 3 < chars.len() - index {
            match sextet(chars[index]) {
                Some(a) => match sextet(chars[index + 1]) {
                    Some(b) => {
                        if chars[index + 2] == 61 {
                            padded_one(chars, index, a, b, out)
                        } else {
                            match sextet(chars[index + 2]) {
                                Some(c) => {
                                    if chars[index + 3] == 61 {
                                        padded_two(chars, index, a, b, c, out)
                                    } else {
                                        match sextet(chars[index + 3]) {
                                            Some(d) => match full_group(out, a, b, c, d) {
                                                Some(out) => base64_from(chars, index + 4, out),
                                                None => None,
                                            },
                                            None => None,
                                        }
                                    }
                                }
                                None => None,
                            }
                        }
                    }
                    None => None,
                },
                None => None,
            }
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The octets of an `xsd:base64Binary` lexical form.
fn base64_value(lexical: &Vec<u8>) -> Option<Vec<u8>> {
    match unspaced(lexical, 0, Vec::new()) {
        Some(chars) => base64_from(&chars, 0, Vec::new()),
        None => None,
    }
}
/// Whether no byte of `text[index..]` is a tab, a line feed or a carriage
/// return.
fn unbroken(text: &Vec<u8>, index: usize) -> bool {
    if index < text.len() {
        let byte = text[index];
        (byte != 9) & (byte != 10) & (byte != 13) && unbroken(text, index + 1)
    } else {
        true
    }
}
/// Whether every space of `text[index..]` is followed by a byte that is no
/// space.
fn spaced_once(text: &Vec<u8>, index: usize) -> bool {
    if index < text.len() {
        if text[index] == 32 {
            index + 1 < text.len() && text[index + 1] != 32 && spaced_once(text, index + 1)
        } else {
            spaced_once(text, index + 1)
        }
    } else {
        true
    }
}
/// Whether the text is a token: no tab, line feed or carriage return, and no
/// space first, last or after another space.
fn tokenized(text: &Vec<u8>) -> bool {
    unbroken(text, 0) && (text.len() == 0 || text[0] != 32) && spaced_once(text, 0)
}
fn is_letter(byte: u8) -> bool {
    ((65 <= byte) & (byte <= 90)) | ((97 <= byte) & (byte <= 122))
}
/// Whether `text[index..]` ends a language tag
/// `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*` whose current subtag has `count`
/// characters, digits allowed after the first subtag.
fn subtags_from(text: &Vec<u8>, index: usize, count: usize, first: bool) -> bool {
    if index < text.len() {
        let byte = text[index];
        if byte == 45 {
            (0 < count) && subtags_from(text, index + 1, 0, false)
        } else {
            (count < 8) & (is_letter(byte) | (!first & is_digit(byte)))
                && subtags_from(text, index + 1, count + 1, first)
        }
    } else {
        0 < count
    }
}
/// XML 1.1 `NameStartChar`, also that of XML 1.0, fifth edition.
fn name_start(codepoint: u32) -> bool {
    (codepoint == 58)
        | ((65 <= codepoint) & (codepoint <= 90))
        | (codepoint == 95)
        | ((97 <= codepoint) & (codepoint <= 122))
        | ((0xC0 <= codepoint) & (codepoint <= 0xD6))
        | ((0xD8 <= codepoint) & (codepoint <= 0xF6))
        | ((0xF8 <= codepoint) & (codepoint <= 0x2FF))
        | ((0x370 <= codepoint) & (codepoint <= 0x37D))
        | ((0x37F <= codepoint) & (codepoint <= 0x1FFF))
        | ((0x200C <= codepoint) & (codepoint <= 0x200D))
        | ((0x2070 <= codepoint) & (codepoint <= 0x218F))
        | ((0x2C00 <= codepoint) & (codepoint <= 0x2FEF))
        | ((0x3001 <= codepoint) & (codepoint <= 0xD7FF))
        | ((0xF900 <= codepoint) & (codepoint <= 0xFDCF))
        | ((0xFDF0 <= codepoint) & (codepoint <= 0xFFFD))
        | ((0x10000 <= codepoint) & (codepoint <= 0xEFFFF))
}
/// XML 1.1 `NameChar`.
fn name_character(codepoint: u32) -> bool {
    name_start(codepoint)
        | (codepoint == 45)
        | (codepoint == 46)
        | ((48 <= codepoint) & (codepoint <= 57))
        | (codepoint == 0xB7)
        | ((0x300 <= codepoint) & (codepoint <= 0x36F))
        | ((0x203F <= codepoint) & (codepoint <= 0x2040))
}
/// Whether every character is a name character.
fn name_characters(scalars: &Scalars) -> bool {
    match scalars {
        Scalars::Empty => true,
        Scalars::Cons {
            codepoint, next, ..
        } => name_character(*codepoint) && name_characters(next),
    }
}
/// Whether the text matches `Nmtoken`: one or more name characters.
fn name_token(text: &Vec<u8>) -> bool {
    match read_text(text) {
        TextScan::Valid(Scalars::Cons {
            codepoint, next, ..
        }) => name_character(codepoint) && name_characters(&next),
        _ => false,
    }
}
/// Whether the text matches `Name`: a name start character and name
/// characters.
fn xml_name(text: &Vec<u8>) -> bool {
    match read_text(text) {
        TextScan::Valid(Scalars::Cons {
            codepoint, next, ..
        }) => name_start(codepoint) && name_characters(&next),
        _ => false,
    }
}
/// Whether the XML text is in the value space of the kind's datatype.
fn text_in_kind(text: &Vec<u8>, kind: Kind) -> bool {
    match kind {
        Kind::String => true,
        Kind::Plain => true,
        Kind::NormalizedString => unbroken(text, 0),
        Kind::Token => tokenized(text),
        Kind::Language => subtags_from(text, 0, 0, true),
        Kind::NmToken => name_token(text),
        Kind::Name => xml_name(text),
        Kind::NcName => xml_name(text) && find_byte(text, 58, 0) == text.len(),
        _ => false,
    }
}
/// The value of a lexical form of `xsd:string` or one of its subtypes: the
/// string itself, if it is XML text in the kind.
fn string_value(kind: Kind, lexical: &Vec<u8>) -> Option<DataValue> {
    if xml_text(lexical) && text_in_kind(lexical, kind) {
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
/// The value of a lexical form of the datatype of the kind, if it is in the
/// lexical space.
pub fn kind_value(kind: Kind, lexical: &Vec<u8>) -> Option<DataValue> {
    match kind {
        Kind::Integer => number_value(lexical, true),
        Kind::Decimal => number_value(lexical, false),
        Kind::String => string_value(kind, lexical),
        Kind::Plain => plain_value(lexical),
        Kind::Boolean => truth_value(lexical),
        Kind::Real => None,
        Kind::Rational => rational_value(lexical),
        Kind::AnyUri => {
            if xml_text(lexical) {
                Some(DataValue::Uri(copy_range(
                    lexical,
                    0,
                    lexical.len(),
                    Vec::new(),
                )))
            } else {
                None
            }
        }
        Kind::HexBinary => match hex_from(lexical, 0, Vec::new()) {
            Some(octets) => Some(DataValue::Hex(octets)),
            None => None,
        },
        Kind::Base64Binary => match base64_value(lexical) {
            Some(octets) => Some(DataValue::Base64(octets)),
            None => None,
        },
        Kind::NormalizedString => string_value(kind, lexical),
        Kind::Token => string_value(kind, lexical),
        Kind::Language => string_value(kind, lexical),
        Kind::NmToken => string_value(kind, lexical),
        Kind::Name => string_value(kind, lexical),
        Kind::NcName => string_value(kind, lexical),
        Kind::DateTime => moment_value(lexical, false),
        Kind::DateTimeStamp => moment_value(lexical, true),
        Kind::Double => match binary_value(lexical, true) {
            Some(value) => Some(DataValue::Double(value)),
            None => None,
        },
        Kind::Float => match binary_value(lexical, false) {
            Some(value) => Some(DataValue::Float(value)),
            None => None,
        },
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
        DataValue::Uri(a) => match right {
            DataValue::Uri(b) => same_bytes(a, b),
            _ => false,
        },
        DataValue::Hex(a) => match right {
            DataValue::Hex(b) => same_bytes(a, b),
            _ => false,
        },
        DataValue::Base64(a) => match right {
            DataValue::Base64(b) => same_bytes(a, b),
            _ => false,
        },
        DataValue::Moment(a) => match right {
            DataValue::Moment(b) => same_moment(a, b),
            _ => false,
        },
        DataValue::Double(a) => match right {
            DataValue::Double(b) => same_binary(a, b),
            _ => false,
        },
        DataValue::Float(a) => match right {
            DataValue::Float(b) => same_binary(a, b),
            _ => false,
        },
    }
}
/// Whether two values of `xsd:double` or of `xsd:float` are the same.
fn same_binary(left: &Binary, right: &Binary) -> bool {
    match left {
        Binary::Finite(a, b, c) => match right {
            Binary::Finite(d, e, f) => (*a == *d) & (*b == *e) & (*c == *f),
            _ => false,
        },
        Binary::Infinite(a) => match right {
            Binary::Infinite(b) => *a == *b,
            _ => false,
        },
        Binary::NotANumber => match right {
            Binary::NotANumber => true,
            _ => false,
        },
    }
}
/// Whether two time zones are the same.
#[allow(clippy::redundant_pattern_matching)] // Explicit branches match the source-linked proof.
fn same_zone(left: &Option<(bool, u8, u8)>, right: &Option<(bool, u8, u8)>) -> bool {
    match left {
        Some((west, hours, minutes)) => match right {
            Some((west2, hours2, minutes2)) => {
                (*west == *west2) & (*hours == *hours2) & (*minutes == *minutes2)
            }
            None => false,
        },
        None => match right {
            Some(_) => false,
            None => true,
        },
    }
}
/// Whether two moments are the same.
fn same_moment(left: &Moment, right: &Moment) -> bool {
    (left.negative == right.negative)
        & same_bytes(&left.year, &right.year)
        & (left.month == right.month)
        & (left.day == right.day)
        & (left.hour == right.hour)
        & (left.minute == right.minute)
        & (left.second == right.second)
        & same_bytes(&left.fraction, &right.fraction)
        & same_zone(&left.zone, &right.zone)
}
/// Whether the value is in the value space of the datatype of the kind.
#[allow(clippy::redundant_pattern_matching)] // Explicit branches match the source-linked proof.
pub fn in_kind(value: &DataValue, kind: Kind) -> bool {
    match value {
        DataValue::Number(_, _, fraction) => number_in_kind(value, fraction.len() == 0, kind),
        DataValue::Fraction(_, _, _) => match kind {
            Kind::Real => true,
            Kind::Rational => true,
            _ => false,
        },
        DataValue::Text(text) => text_in_kind(text, kind),
        DataValue::Tagged(_, _) => match kind {
            Kind::Plain => true,
            _ => false,
        },
        DataValue::Truth(_) => match kind {
            Kind::Boolean => true,
            _ => false,
        },
        DataValue::Uri(_) => match kind {
            Kind::AnyUri => true,
            _ => false,
        },
        DataValue::Hex(_) => match kind {
            Kind::HexBinary => true,
            _ => false,
        },
        DataValue::Base64(_) => match kind {
            Kind::Base64Binary => true,
            _ => false,
        },
        DataValue::Moment(moment) => match kind {
            Kind::DateTime => true,
            Kind::DateTimeStamp => match moment.zone {
                Some(_) => true,
                None => false,
            },
            _ => false,
        },
        DataValue::Double(_) => match kind {
            Kind::Double => true,
            _ => false,
        },
        DataValue::Float(_) => match kind {
            Kind::Float => true,
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
/// datatype: for `owl:real` and `owl:rational` every number, for the
/// numeric datatypes of XML Schema every number of their value space, and for
/// `xsd:double` and `xsd:float` every value of their own.
pub fn facet_applies(kind: Kind, bound: &DataValue) -> bool {
    match bound {
        DataValue::Double(_) => match kind {
            Kind::Double => true,
            _ => false,
        },
        DataValue::Float(_) => match kind {
            Kind::Float => true,
            _ => false,
        },
        _ => numeric_facet_applies(kind, bound),
    }
}
/// Whether the facet with a bound other than a floating-point value is in the
/// facet space of the kind's datatype.
fn numeric_facet_applies(kind: Kind, bound: &DataValue) -> bool {
    if numeric(bound) {
        match kind {
            Kind::Real => true,
            Kind::Rational => true,
            Kind::String => false,
            Kind::Plain => false,
            Kind::Boolean => false,
            Kind::AnyUri => false,
            Kind::HexBinary => false,
            Kind::Base64Binary => false,
            Kind::NormalizedString => false,
            Kind::Token => false,
            Kind::Language => false,
            Kind::NmToken => false,
            Kind::Name => false,
            Kind::NcName => false,
            Kind::DateTime => false,
            Kind::DateTimeStamp => false,
            Kind::Double => false,
            Kind::Float => false,
            _ => in_kind(bound, kind),
        }
    } else {
        false
    }
}
