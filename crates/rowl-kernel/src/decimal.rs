//! Exact nonnegative decimal values for OWL cardinality syntax.
//! Values use the existing unbounded research Natural representation. Physical
//! stack/memory control and OWL document parsing remain separate milestones.
#![allow(clippy::ptr_arg)]
use crate::probes::{add, decimal_digit, Natural};

pub enum ReadError {
    InvalidSpan { offset: usize },
    Empty { offset: usize },
    InvalidDigit { offset: usize },
}
fn small_value(count: u8) -> Natural {
    if count == 0 {
        Natural::Zero
    } else {
        Natural::Succ(Box::new(small_value(count - 1)))
    }
}
fn times_ten(value: &Natural) -> Natural {
    let total = add(value, Natural::Zero);
    let total = add(value, total);
    let total = add(value, total);
    let total = add(value, total);
    let total = add(value, total);
    let total = add(value, total);
    let total = add(value, total);
    let total = add(value, total);
    let total = add(value, total);
    add(value, total)
}
fn scan(
    bytes: &Vec<u8>,
    position: usize,
    end: usize,
    previous: Natural,
) -> Result<Natural, ReadError> {
    if position == end {
        return Ok(previous);
    }
    let digit = match decimal_digit(bytes[position]) {
        Some(digit) => digit,
        None => return Err(ReadError::InvalidDigit { offset: position }),
    };
    let value = add(&times_ten(&previous), small_value(digit));
    scan(bytes, position + 1, end, value)
}
/// Interpret a nonempty original source span of ASCII digits as its exact
/// mathematical natural value. Leading zeroes are accepted; there is no machine
/// integer value cap. Every error retains its original source byte position.
pub fn read_span(bytes: &Vec<u8>, start: usize, end: usize) -> Result<Natural, ReadError> {
    if start > end || end > bytes.len() {
        return Err(ReadError::InvalidSpan { offset: start });
    }
    if start == end {
        return Err(ReadError::Empty { offset: start });
    }
    scan(bytes, start, end, Natural::Zero)
}
/// Interpret a complete immutable byte string. No trimming, sign acceptance,
/// Unicode digit normalization or partial-value return occurs.
pub fn read(bytes: &Vec<u8>) -> Result<Natural, ReadError> {
    read_span(bytes, 0, bytes.len())
}
