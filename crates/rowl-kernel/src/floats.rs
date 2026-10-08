//! Floating-point numbers of `xsd:double` and `xsd:float` (XML Schema 1.1
//! Part 2 §3.3.4 and §3.3.5): the lexical forms
//! `(\+|-)?([0-9]+(\.[0-9]*)?|\.[0-9]+)([Ee](\+|-)?[0-9]+)?`, `(\+|-)?INF` and
//! `NaN`, read into their values as `floatingPointRound` (§E.1.1) rounds the
//! decimal number of a numeral: to the nearest value `m × 2^e` with
//! `m < 2^p` and `eMin <= e <= eMax`, ties to the even `m`, and to an
//! infinity past the greatest value (`p`, `eMin`, `eMax` are 53, -1074, 971
//! for `xsd:double` and 24, -149, 104 for `xsd:float`). A zero keeps the sign
//! of its numeral, and the two zeros are different values (OWL 2 Structural
//! Specification §4.2).
//!
//! The arithmetic is exact, on decimal digit strings (`numbers`). A value
//! keeps its sign, the digits of its odd significand and its exponent of 2
//! plus `BIAS`; a zero has no digits. A lexical form of `LIMIT` bytes or more
//! gets no value.
#![allow(
    clippy::ptr_arg,
    clippy::len_zero,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::manual_is_multiple_of,
    clippy::type_complexity,
    clippy::match_like_matches_macro
)] // Indexed operations and explicit branches for the pinned extraction subset.

use crate::datatypes::Binary;
use crate::moments::{copy_span, digits_end, trimmed_end};
use crate::numbers::{
    add_naturals, canonical, compare_naturals, divide_naturals, subtract_naturals, ten_power,
    times_power,
};

/// The bias of the binary exponents of values.
pub const BIAS: usize = 2048;
/// The bias of decimal orders.
const ORDER_BIAS: usize = 268_435_456;
/// The length from which lexical forms get no value.
pub const LIMIT: usize = 1024;
/// The exponent digits beyond which an exponent counts as this large.
const SATURATED: usize = 100_000_000;
/// The most steps that finding the exponent of 2 takes.
const STEPS: usize = 4096;

/// The digits of the significand: 53 for `xsd:double`, 24 for `xsd:float`.
fn precision(double: bool) -> usize {
    if double {
        53
    } else {
        24
    }
}
/// The least exponent of 2, plus `BIAS`.
fn least(double: bool) -> usize {
    if double {
        BIAS - 1074
    } else {
        BIAS - 149
    }
}
/// The greatest exponent of 2, plus `BIAS`.
fn most(double: bool) -> usize {
    if double {
        BIAS + 971
    } else {
        BIAS + 104
    }
}
/// The decimal order, plus `ORDER_BIAS`, from which every number is past the
/// greatest value.
fn over(double: bool) -> usize {
    if double {
        ORDER_BIAS + 310
    } else {
        ORDER_BIAS + 40
    }
}
/// The decimal order, plus `ORDER_BIAS`, up to which every number rounds to
/// zero.
fn under(double: bool) -> usize {
    if double {
        ORDER_BIAS - 324
    } else {
        ORDER_BIAS - 46
    }
}

/// The number one.
fn one() -> Vec<u8> {
    let mut digits = Vec::new();
    digits.push(49);
    digits
}
/// The ASCII digits of a number, without leading zeros.
fn digits_of(value: u128) -> Vec<u8> {
    if value == 0 {
        Vec::new()
    } else {
        let mut out = digits_of(value / 10);
        out.push(48 + (value % 10) as u8);
        out
    }
}
/// The number of the digits `digits[index..]` on top of `total`, natively.
fn native_value(digits: &Vec<u8>, index: usize, total: u128) -> u128 {
    if index < digits.len() {
        native_value(digits, index + 1, 10 * total + (digits[index] - 48) as u128)
    } else {
        total
    }
}
/// Two to the count, natively, for a count below 128.
fn native_two(count: usize) -> u128 {
    if 0 < count {
        2 * native_two(count - 1)
    } else {
        1
    }
}
/// Ten to the count, natively, for a count below 39.
fn native_ten(count: usize) -> u128 {
    if 0 < count {
        10 * native_ten(count - 1)
    } else {
        1
    }
}
/// Two to the precision: the least significand that is too large.
fn top(double: bool) -> u128 {
    native_two(precision(double))
}
/// A finite value `±m × 2^e`, canonical: an odd significand, or zero.
fn finite(negative: bool, m: u64, e: usize) -> Binary {
    if m == 0 {
        Binary::Finite(negative, 0, BIAS)
    } else {
        let (odd, scale) = odd_form(m, e, 64);
        Binary::Finite(negative, odd, scale)
    }
}
/// The significand halved while it is even, and its exponent with it.
fn odd_form(m: u64, e: usize, fuel: usize) -> (u64, usize) {
    if 0 < fuel && m % 2 == 0 {
        odd_form(m / 2, e + 1, fuel - 1)
    } else {
        (m, e)
    }
}

// ---------------------------------------------------------------------------
// The quotient of the number by a power of two, natively
// ---------------------------------------------------------------------------

/// The number `d × 10^scale` (`up`) or `d / 10^scale`, scaled by `2^-e` for
/// an exponent `e` plus `BIAS`, as an integer part, a remainder and a
/// denominator; `None` when a part would not fit.
fn native_state(d: u128, up: bool, scale: usize, e: usize) -> Option<(u128, u128, u128)> {
    let (numerator, denominator) = if up {
        (d * native_ten(scale), 1)
    } else {
        (d, native_ten(scale))
    };
    if BIAS <= e {
        if e - BIAS < 127 {
            let power = native_two(e - BIAS);
            if denominator <= u128::MAX / 2 / power {
                let scaled = denominator * power;
                Some((numerator / scaled, numerator % scaled, scaled))
            } else {
                None
            }
        } else {
            None
        }
    } else if BIAS - e < 127 {
        let power = native_two(BIAS - e);
        if numerator <= u128::MAX / power {
            let scaled = numerator * power;
            Some((scaled / denominator, scaled % denominator, denominator))
        } else {
            None
        }
    } else {
        None
    }
}
/// The exponent at which the integer part has `p` digits, or the least
/// exponent when it has fewer there, with the quotient there: the greatest
/// exponent plus one past it. Each step halves the quotient or doubles it.
fn native_settle(
    k: u128,
    rest: u128,
    denominator: u128,
    e: usize,
    double: bool,
    fuel: usize,
) -> Option<(u128, u128, u128, usize)> {
    if 0 < fuel {
        if top(double) <= k {
            if e < most(double) {
                if denominator <= u128::MAX / 2 {
                    native_settle(
                        k / 2,
                        (k % 2) * denominator + rest,
                        2 * denominator,
                        e + 1,
                        double,
                        fuel - 1,
                    )
                } else {
                    None
                }
            } else {
                Some((k, rest, denominator, e + 1))
            }
        } else if least(double) < e && 2 * k < top(double) {
            if rest <= u128::MAX / 2 {
                if 2 * rest < denominator {
                    native_settle(2 * k, 2 * rest, denominator, e - 1, double, fuel - 1)
                } else {
                    native_settle(
                        2 * k + 1,
                        2 * rest - denominator,
                        denominator,
                        e - 1,
                        double,
                        fuel - 1,
                    )
                }
            } else {
                None
            }
        } else {
            Some((k, rest, denominator, e))
        }
    } else {
        None
    }
}
/// The quotient rounded at its exponent: to the nearer integer, ties to the
/// even one, and past the greatest value to an infinity.
fn native_round(
    k: u128,
    rest: u128,
    denominator: u128,
    e: usize,
    negative: bool,
    double: bool,
) -> Option<Binary> {
    if rest <= u128::MAX / 2 {
        let up = if 2 * rest < denominator {
            false
        } else if denominator < 2 * rest {
            true
        } else {
            k % 2 != 0
        };
        let m = if up { k + 1 } else { k };
        if m == top(double) {
            if e < most(double) {
                Some(finite(negative, (top(double) / 2) as u64, e + 1))
            } else {
                Some(Binary::Infinite(negative))
            }
        } else {
            Some(finite(negative, m as u64, e))
        }
    } else {
        None
    }
}
/// The value of `d × 10^(±scale)` from the exponent `e` on, natively; `None`
/// when a part would not fit.
fn native(
    d: u128,
    up: bool,
    scale: usize,
    e: usize,
    negative: bool,
    double: bool,
) -> Option<Binary> {
    match native_state(d, up, scale, e) {
        Some((k, rest, denominator)) => match native_settle(k, rest, denominator, e, double, STEPS)
        {
            Some((k, rest, denominator, e)) => {
                if most(double) < e {
                    Some(Binary::Infinite(negative))
                } else {
                    native_round(k, rest, denominator, e, negative, double)
                }
            }
            None => None,
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The quotient of the number by a power of two, on decimal digits
// ---------------------------------------------------------------------------

/// The number doubled `count` times.
fn doubled(digits: Vec<u8>, count: usize) -> Vec<u8> {
    if 0 < count {
        doubled(add_naturals(&digits, &digits), count - 1)
    } else {
        digits
    }
}
/// The number of the digits, natively, for one below `2^64`.
fn small_number(digits: &Vec<u8>, index: usize, total: u64) -> u64 {
    if index < digits.len() {
        small_number(digits, index + 1, 10 * total + (digits[index] - 48) as u64)
    } else {
        total
    }
}
/// The number `n / q` scaled by `2^-e`, for an exponent `e` plus `BIAS`, as an
/// integer part, a remainder and a denominator.
fn wide_state(n: &Vec<u8>, q: &Vec<u8>, e: usize) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    if BIAS <= e {
        let denominator = doubled(canonical(q), e - BIAS);
        let (k, rest) = divide_naturals(n, &denominator);
        (k, rest, denominator)
    } else {
        let scaled = doubled(canonical(n), BIAS - e);
        let (k, rest) = divide_naturals(&scaled, q);
        (k, rest, canonical(q))
    }
}
/// `native_settle` on decimal digits.
fn wide_settle(
    k: Vec<u8>,
    rest: Vec<u8>,
    denominator: Vec<u8>,
    e: usize,
    double: bool,
    fuel: usize,
) -> Option<(Vec<u8>, Vec<u8>, Vec<u8>, usize)> {
    if 0 < fuel {
        if compare_naturals(&k, &digits_of(top(double))) != 0 {
            if e < most(double) {
                let mut two = Vec::new();
                two.push(50);
                let (half, low) = divide_naturals(&k, &two);
                let rest = if low.len() == 0 {
                    rest
                } else {
                    add_naturals(&denominator, &rest)
                };
                let twice = add_naturals(&denominator, &denominator);
                wide_settle(half, rest, twice, e + 1, double, fuel - 1)
            } else {
                Some((k, rest, denominator, e + 1))
            }
        } else if least(double) < e && compare_naturals(&k, &digits_of(top(double) / 2)) == 0 {
            let twice = add_naturals(&rest, &rest);
            let doubled_k = add_naturals(&k, &k);
            if compare_naturals(&twice, &denominator) == 0 {
                wide_settle(doubled_k, twice, denominator, e - 1, double, fuel - 1)
            } else {
                let rest = subtract_naturals(&twice, &denominator);
                wide_settle(
                    add_naturals(&doubled_k, &one()),
                    rest,
                    denominator,
                    e - 1,
                    double,
                    fuel - 1,
                )
            }
        } else {
            Some((k, rest, denominator, e))
        }
    } else {
        None
    }
}
/// `native_round` on decimal digits.
fn wide_round(
    k: Vec<u8>,
    rest: Vec<u8>,
    denominator: Vec<u8>,
    e: usize,
    negative: bool,
    double: bool,
) -> Binary {
    let twice = add_naturals(&rest, &rest);
    let up = match compare_naturals(&twice, &denominator) {
        0 => false,
        2 => true,
        _ => {
            let last = if 0 < k.len() { k[k.len() - 1] } else { 48 };
            (last == 49) | (last == 51) | (last == 53) | (last == 55) | (last == 57)
        }
    };
    let m = if up { add_naturals(&k, &one()) } else { k };
    if compare_naturals(&m, &digits_of(top(double))) == 1 {
        if e < most(double) {
            finite(negative, (top(double) / 2) as u64, e + 1)
        } else {
            Binary::Infinite(negative)
        }
    } else {
        finite(negative, small_number(&m, 0, 0), e)
    }
}
/// The value of `n / q` from the exponent `e` on, on decimal digits.
fn wide(n: &Vec<u8>, q: &Vec<u8>, e: usize, negative: bool, double: bool) -> Option<Binary> {
    let (k, rest, denominator) = wide_state(n, q, e);
    match wide_settle(k, rest, denominator, e, double, STEPS) {
        Some((k, rest, denominator, e)) => {
            if most(double) < e {
                Some(Binary::Infinite(negative))
            } else {
                Some(wide_round(k, rest, denominator, e, negative, double))
            }
        }
        None => None,
    }
}
/// A first guess of the exponent from the decimal order of the number:
/// `⌊(order − 1) · log₂ 10⌋ − p + 1`, roughly, within the exponents.
fn estimate(order: usize, double: bool) -> usize {
    let guess = if ORDER_BIAS < order {
        BIAS + 1 + (order - ORDER_BIAS - 1) * 3_321_928 / 1_000_000 - precision(double)
    } else {
        let down = (ORDER_BIAS + 1 - order) * 3_321_928 / 1_000_000;
        if precision(double) + down < BIAS + 1 {
            BIAS + 1 - precision(double) - down
        } else {
            0
        }
    };
    if guess < least(double) {
        least(double)
    } else if most(double) < guess {
        most(double)
    } else {
        guess
    }
}
/// The value of the positive number `digits × 10^(order − ORDER_BIAS −
/// digits.len())`, of decimal order `order`: natively when it fits, and on
/// decimal digits otherwise.
fn exact(digits: Vec<u8>, order: usize, negative: bool, double: bool) -> Option<Binary> {
    let length = digits.len();
    let up = ORDER_BIAS + length <= order;
    let scale = if up {
        order - ORDER_BIAS - length
    } else {
        ORDER_BIAS + length - order
    };
    let e = estimate(order, double);
    let quick = if length <= 17 && scale <= 21 {
        native(native_value(&digits, 0, 0), up, scale, e, negative, double)
    } else {
        None
    };
    match quick {
        Some(value) => Some(value),
        None => {
            if up {
                wide(&times_power(digits, scale), &one(), e, negative, double)
            } else {
                wide(&digits, &ten_power(scale), e, negative, double)
            }
        }
    }
}
/// Whether `bytes[index..]` is the word.
fn word_at(bytes: &Vec<u8>, index: usize, word: &[u8]) -> bool {
    if index <= bytes.len() && bytes.len() - index == word.len() {
        rest_is(bytes, index, word, 0)
    } else {
        false
    }
}
fn rest_is(bytes: &Vec<u8>, index: usize, word: &[u8], at: usize) -> bool {
    if at < word.len() && index + at < bytes.len() {
        bytes[index + at] == word[at] && rest_is(bytes, index, word, at + 1)
    } else {
        true
    }
}
/// The value of the digits `bytes[index..end]` on top of `total`, as large as
/// `SATURATED` when it is that large or larger.
fn small_value(bytes: &Vec<u8>, index: usize, end: usize, total: usize) -> usize {
    if index < end && end <= bytes.len() {
        if total < SATURATED {
            small_value(
                bytes,
                index + 1,
                end,
                10 * total + (bytes[index] - 48) as usize,
            )
        } else {
            SATURATED
        }
    } else if total < SATURATED {
        total
    } else {
        SATURATED
    }
}
/// The value of the numeral with the digits `whole` and `fraction` (by
/// position) and the exponent `±exponent`.
#[allow(clippy::too_many_arguments)] // The parts of the numeral, as positions.
fn numeral_value(
    lexical: &Vec<u8>,
    whole_start: usize,
    whole_end: usize,
    fraction_start: usize,
    fraction_end: usize,
    exponent_negative: bool,
    exponent: usize,
    negative: bool,
    double: bool,
) -> Option<Binary> {
    let written = copy_span(
        lexical,
        fraction_start,
        fraction_end,
        copy_span(lexical, whole_start, whole_end, Vec::new()),
    );
    let digits = canonical(&written);
    if digits.len() == 0 {
        Some(Binary::Finite(negative, 0, BIAS))
    } else {
        let fraction = fraction_end - fraction_start;
        let order = if exponent_negative {
            ORDER_BIAS + digits.len() - fraction - exponent
        } else {
            ORDER_BIAS + digits.len() + exponent - fraction
        };
        if over(double) <= order {
            Some(Binary::Infinite(negative))
        } else if order <= under(double) {
            Some(Binary::Finite(negative, 0, BIAS))
        } else {
            let end = trimmed_end(&digits, 0, digits.len());
            exact(
                copy_span(&digits, 0, end, Vec::new()),
                order,
                negative,
                double,
            )
        }
    }
}
/// The value of a numeral from `start` on, after its sign.
fn numeral(lexical: &Vec<u8>, start: usize, negative: bool, double: bool) -> Option<Binary> {
    let whole_end = digits_end(lexical, start);
    let point = whole_end < lexical.len() && lexical[whole_end] == 46;
    let fraction_start = if point { whole_end + 1 } else { whole_end };
    let fraction_end = digits_end(lexical, fraction_start);
    if start < whole_end || fraction_start < fraction_end {
        if fraction_end < lexical.len() {
            let mark = lexical[fraction_end];
            if (mark == 69) | (mark == 101) {
                let sign_at = fraction_end + 1;
                let signed = sign_at < lexical.len()
                    && ((lexical[sign_at] == 45) | (lexical[sign_at] == 43));
                let exponent_negative = sign_at < lexical.len() && lexical[sign_at] == 45;
                let exponent_start = if signed { sign_at + 1 } else { sign_at };
                let exponent_end = digits_end(lexical, exponent_start);
                if exponent_start < exponent_end && exponent_end == lexical.len() {
                    numeral_value(
                        lexical,
                        start,
                        whole_end,
                        fraction_start,
                        fraction_end,
                        exponent_negative,
                        small_value(lexical, exponent_start, exponent_end, 0),
                        negative,
                        double,
                    )
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            numeral_value(
                lexical,
                start,
                whole_end,
                fraction_start,
                fraction_end,
                false,
                0,
                negative,
                double,
            )
        }
    } else {
        None
    }
}
// ---------------------------------------------------------------------------
// The order of the values
// ---------------------------------------------------------------------------

/// The number of binary digits of `m`.
fn length(m: u64) -> usize {
    if m == 0 {
        0
    } else {
        1 + length(m / 2)
    }
}
/// The place of a positive value `m × 2^e` among the positive values of its
/// format, from 1, for a value of the format with the exponent `e` plus
/// `BIAS` (`scale`): its IEEE 754 encoding, the exponent where `m` has the
/// precision's digits, or the least one, above the significand there.
fn place(m: u64, scale: usize, double: bool) -> u128 {
    let p = precision(double);
    let low = least(double);
    if scale < usize::MAX - 64 {
        let high = scale + length(m);
        let exponent = if low + p <= high { high - p } else { low };
        if exponent <= scale {
            if scale - exponent < 64 {
                ((exponent - low) as u128) * native_two(p - 1)
                    + (m as u128) * native_two(scale - exponent)
            } else {
                0
            }
        } else {
            0
        }
    } else {
        0
    }
}
/// The place of positive infinity among the positive values: one more than
/// the greatest number's.
fn top_place(double: bool) -> u128 {
    ((most(double) - least(double) + 2) as u128) * native_two(precision(double) - 1)
}
/// The place of a value in the order of its format, from 0: NaN, negative
/// infinity, the negative numbers from the least, negative zero, positive
/// zero, the positive numbers and positive infinity, one place for each
/// value (XML Schema 1.1 Part 2 §3.3.4.1 and §3.3.5.1).
pub fn position(value: &Binary, double: bool) -> u128 {
    let top = top_place(double);
    match value {
        Binary::NotANumber => 0,
        Binary::Infinite(negative) => {
            if *negative {
                1
            } else {
                2 * top + 2
            }
        }
        Binary::Finite(negative, m, scale) => {
            if *m == 0 {
                if *negative {
                    top + 1
                } else {
                    top + 2
                }
            } else {
                let p = place(*m, *scale, double);
                if p < top {
                    if *negative {
                        top + 1 - p
                    } else {
                        top + 2 + p
                    }
                } else {
                    0
                }
            }
        }
    }
}
/// The number of the values of a format, NaN and the infinities included.
pub fn places(double: bool) -> u128 {
    2 * top_place(double) + 3
}
/// Whether a value is NaN.
pub fn is_nan(value: &Binary) -> bool {
    match value {
        Binary::NotANumber => true,
        _ => false,
    }
}
/// The first place of the values equal to a value: negative zero's for a
/// zero, which equals positive zero.
pub fn low_position(value: &Binary, double: bool) -> u128 {
    match value {
        Binary::Finite(_, 0, _) => top_place(double) + 1,
        _ => position(value, double),
    }
}
/// The last place of the values equal to a value: positive zero's for a
/// zero.
pub fn high_position(value: &Binary, double: bool) -> u128 {
    match value {
        Binary::Finite(_, 0, _) => top_place(double) + 2,
        _ => position(value, double),
    }
}

/// The value of a lexical form of `xsd:double` (`double`) or `xsd:float`, if
/// it is one.
pub fn binary_value(lexical: &Vec<u8>, double: bool) -> Option<Binary> {
    if lexical.len() < LIMIT {
        let negative = 0 < lexical.len() && lexical[0] == 45;
        let signed = 0 < lexical.len() && ((lexical[0] == 45) | (lexical[0] == 43));
        let start = if signed { 1 } else { 0 };
        if word_at(lexical, start, b"INF") {
            Some(Binary::Infinite(negative))
        } else if word_at(lexical, 0, b"NaN") {
            Some(Binary::NotANumber)
        } else {
            numeral(lexical, start, negative, double)
        }
    } else {
        None
    }
}
