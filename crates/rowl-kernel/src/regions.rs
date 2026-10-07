//! Numbers on the real line for the data encoding of `data_ontology`.
//!
//! A cut is a number with a side: the numbers at or above it (closed) or
//! above it (open). The encoding orders the cuts it uses, numbers first and a
//! closed cut before the open cut of the same number, by selection: each step
//! scans the cuts for the least one above the last one found, comparing
//! numbers exactly with `datatypes::compare_values`. Between two neighbouring
//! cuts of different numbers lie the integers that the first cut contains and
//! the second does not; they are counted from the floors and ceilings of the
//! numbers with the digit arithmetic of `numbers`, as signed integers, and the
//! count is turned into a `usize` only up to a cap.
#![allow(
    clippy::ptr_arg,
    clippy::len_zero,
    clippy::vec_init_then_push,
    clippy::manual_range_contains,
    clippy::redundant_pattern_matching
)]
// Indexed operations and explicit pushes for the pinned extraction subset.
use crate::datatypes::{compare_values, same_value, DataValue};
use crate::nnf::copy_bytes;
use crate::numbers::{
    add_naturals, canonical, compare_naturals, divide_naturals, subtract_naturals,
};

/// A cut: the numbers at or above `value` (closed), or above it (`open`).
pub struct Cut {
    pub value: DataValue,
    pub open: bool,
}

/// A copy of a value.
pub fn copy_value(value: &DataValue) -> DataValue {
    match value {
        DataValue::Number(negative, whole, fraction) => {
            DataValue::Number(*negative, copy_bytes(whole), copy_bytes(fraction))
        }
        DataValue::Fraction(negative, numerator, denominator) => {
            DataValue::Fraction(*negative, copy_bytes(numerator), copy_bytes(denominator))
        }
        DataValue::Text(text) => DataValue::Text(copy_bytes(text)),
        DataValue::Tagged(text, tag) => DataValue::Tagged(copy_bytes(text), copy_bytes(tag)),
        DataValue::Truth(truth) => DataValue::Truth(*truth),
    }
}
/// The index of the cut of `value` on the side `open` in `cuts[index..]`.
pub fn cut_index(cuts: &Vec<Cut>, value: &DataValue, open: bool, index: usize) -> Option<usize> {
    if index < cuts.len() {
        if same_value(&cuts[index].value, value) & (cuts[index].open == open) {
            Some(index)
        } else {
            cut_index(cuts, value, open, index + 1)
        }
    } else {
        None
    }
}
/// The cuts with the cut of `value` on the side `open` too, once.
pub fn add_cut(mut cuts: Vec<Cut>, value: &DataValue, open: bool) -> Vec<Cut> {
    match cut_index(&cuts, value, open, 0) {
        Some(_) => cuts,
        None => {
            if cuts.len() < usize::MAX {
                cuts.push(Cut {
                    value: copy_value(value),
                    open,
                });
            }
            cuts
        }
    }
}

// ---------------------------------------------------------------------------
// The order of the cuts
// ---------------------------------------------------------------------------

/// Whether `left` and `right` are numbers and `left` is the greater.
pub fn is_greater(left: &DataValue, right: &DataValue) -> bool {
    match compare_values(left, right) {
        Some(order) => order == 2,
        None => false,
    }
}
/// Whether the cut `left` comes after the cut `right`: its number is greater,
/// or it is the open cut of the same number.
fn after(left: &Cut, right: &Cut) -> bool {
    is_greater(&left.value, &right.value)
        | (same_value(&left.value, &right.value) & left.open & !right.open)
}
/// Whether `cut` comes after the cut at `bound`, or there is no bound.
fn after_bound(cuts: &Vec<Cut>, bound: Option<usize>, cut: &Cut) -> bool {
    match bound {
        Some(index) => {
            if index < cuts.len() {
                after(cut, &cuts[index])
            } else {
                false
            }
        }
        None => true,
    }
}
/// Whether `cut` comes before the cut at `best`, or there is no best yet.
fn before_best(cuts: &Vec<Cut>, best: Option<usize>, cut: &Cut) -> bool {
    match best {
        Some(index) => {
            if index < cuts.len() {
                after(&cuts[index], cut)
            } else {
                false
            }
        }
        None => true,
    }
}
/// Whether `cut` comes after the cut at `bound` and before the cut at `best`.
fn better(cuts: &Vec<Cut>, bound: Option<usize>, best: Option<usize>, cut: &Cut) -> bool {
    after_bound(cuts, bound, cut) & before_best(cuts, best, cut)
}
/// The index of the first cut of `cuts[index..]` after the cut at `bound`, or
/// `best` when that cut comes first.
fn least_after(
    cuts: &Vec<Cut>,
    bound: Option<usize>,
    index: usize,
    best: Option<usize>,
) -> Option<usize> {
    if index < cuts.len() {
        if better(cuts, bound, best, &cuts[index]) {
            least_after(cuts, bound, index + 1, Some(index))
        } else {
            least_after(cuts, bound, index + 1, best)
        }
    } else {
        best
    }
}
/// `out` followed by the indices of the cuts after the cut at `last`, in
/// order.
fn order_from(cuts: &Vec<Cut>, last: Option<usize>, mut out: Vec<usize>) -> Vec<usize> {
    if out.len() < cuts.len() {
        match least_after(cuts, last, 0, None) {
            Some(next) => {
                out.push(next);
                order_from(cuts, Some(next), out)
            }
            None => out,
        }
    } else {
        out
    }
}
/// The indices of the cuts in order.
pub fn cut_order(cuts: &Vec<Cut>) -> Vec<usize> {
    order_from(cuts, None, Vec::new())
}
/// Whether a value is a number short enough to compare.
fn fits(value: &DataValue) -> bool {
    match compare_values(value, value) {
        Some(_) => true,
        None => false,
    }
}
/// Whether every cut of `cuts[index..]` is of a number short enough to
/// compare.
pub fn cuts_fit(cuts: &Vec<Cut>, index: usize) -> bool {
    if index < cuts.len() {
        if fits(&cuts[index].value) {
            cuts_fit(cuts, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

// ---------------------------------------------------------------------------
// The integers between two cuts
// ---------------------------------------------------------------------------

/// A signed integer: whether it is negative, and the digits of its magnitude,
/// with zero not negative.
pub struct Signed {
    pub negative: bool,
    pub magnitude: Vec<u8>,
}

/// The digits of one.
fn one() -> Vec<u8> {
    let mut digits = Vec::new();
    digits.push(b'1');
    digits
}
/// Whether a number is negative.
fn below_zero(value: &DataValue) -> bool {
    match value {
        DataValue::Number(negative, _, _) => *negative,
        DataValue::Fraction(negative, _, _) => *negative,
        _ => false,
    }
}
/// The magnitude of a number rounded down.
fn floor_magnitude(value: &DataValue) -> Vec<u8> {
    match value {
        DataValue::Number(_, whole, _) => canonical(whole),
        DataValue::Fraction(_, numerator, denominator) => {
            let (quotient, _) = divide_naturals(numerator, denominator);
            quotient
        }
        _ => Vec::new(),
    }
}
/// The magnitude of a number rounded up.
fn ceil_magnitude(value: &DataValue) -> Vec<u8> {
    match value {
        DataValue::Number(_, whole, fraction) => {
            if fraction.len() == 0 {
                canonical(whole)
            } else {
                add_naturals(whole, &one())
            }
        }
        DataValue::Fraction(_, numerator, denominator) => {
            let (quotient, remainder) = divide_naturals(numerator, denominator);
            if remainder.len() == 0 {
                quotient
            } else {
                add_naturals(&quotient, &one())
            }
        }
        _ => Vec::new(),
    }
}
/// The signed integer of a sign and a magnitude, with zero not negative.
fn signed(negative: bool, magnitude: Vec<u8>) -> Signed {
    if magnitude.len() == 0 {
        Signed {
            negative: false,
            magnitude,
        }
    } else {
        Signed {
            negative,
            magnitude,
        }
    }
}
/// The greatest integer at most a number.
fn floor_of(value: &DataValue) -> Signed {
    if below_zero(value) {
        signed(true, ceil_magnitude(value))
    } else {
        signed(false, floor_magnitude(value))
    }
}
/// The least integer at least a number.
fn ceil_of(value: &DataValue) -> Signed {
    if below_zero(value) {
        signed(true, floor_magnitude(value))
    } else {
        signed(false, ceil_magnitude(value))
    }
}
/// An integer plus one.
fn plus_one(value: Signed) -> Signed {
    if value.negative {
        signed(true, subtract_naturals(&value.magnitude, &one()))
    } else {
        signed(false, add_naturals(&value.magnitude, &one()))
    }
}
/// An integer minus one.
fn minus_one(value: Signed) -> Signed {
    if value.negative {
        signed(true, add_naturals(&value.magnitude, &one()))
    } else if value.magnitude.len() == 0 {
        signed(true, one())
    } else {
        signed(false, subtract_naturals(&value.magnitude, &one()))
    }
}
/// `left - right` for magnitudes, as a signed integer.
fn magnitude_difference(left: &Vec<u8>, right: &Vec<u8>) -> Signed {
    if compare_naturals(left, right) == 0 {
        signed(true, subtract_naturals(right, left))
    } else {
        signed(false, subtract_naturals(left, right))
    }
}
/// `left - right` for integers.
fn difference(left: &Signed, right: &Signed) -> Signed {
    if left.negative {
        if right.negative {
            magnitude_difference(&right.magnitude, &left.magnitude)
        } else {
            signed(true, add_naturals(&left.magnitude, &right.magnitude))
        }
    } else if right.negative {
        signed(false, add_naturals(&left.magnitude, &right.magnitude))
    } else {
        magnitude_difference(&left.magnitude, &right.magnitude)
    }
}
/// The least integer in a cut.
fn first_in(cut: &Cut) -> Signed {
    if cut.open {
        plus_one(floor_of(&cut.value))
    } else {
        ceil_of(&cut.value)
    }
}
/// The greatest integer outside a cut.
fn last_outside(cut: &Cut) -> Signed {
    if cut.open {
        floor_of(&cut.value)
    } else {
        minus_one(ceil_of(&cut.value))
    }
}
/// The digits of the number of integers in the cut `low` and outside the cut
/// `high`.
pub fn between(low: &Cut, high: &Cut) -> Vec<u8> {
    let first = first_in(low);
    let last = last_outside(high);
    let gap = difference(&last, &first);
    if gap.negative {
        Vec::new()
    } else {
        add_naturals(&gap.magnitude, &one())
    }
}
/// The value of an ASCII digit.
fn digit(byte: u8) -> usize {
    if (48 <= byte) & (byte <= 57) {
        (byte - 48) as usize
    } else {
        0
    }
}
/// The least of `cap` and the number written by `digits`, after the digits
/// before `index` wrote `value < cap`.
fn capped_from(digits: &Vec<u8>, index: usize, value: usize, cap: usize) -> usize {
    if index < digits.len() {
        let next = value * 10 + digit(digits[index]);
        if next < cap {
            capped_from(digits, index + 1, next, cap)
        } else {
            cap
        }
    } else {
        value
    }
}
/// The least of `cap` and the number written by `digits`, for a cap of at
/// most a sixteenth of the largest `usize`.
pub fn capped(digits: &Vec<u8>, cap: usize) -> usize {
    if (0 < cap) & (cap <= usize::MAX / 16) {
        capped_from(digits, 0, 0, cap)
    } else {
        0
    }
}
/// The least of `cap` and the number of integers in the cut `low` and outside
/// the cut `high`.
pub fn run_size(low: &Cut, high: &Cut, cap: usize) -> usize {
    capped(&between(low, high), cap)
}
