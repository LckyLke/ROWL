//! Exact arithmetic on natural numbers written in decimal: a number is the
//! vector of the ASCII digits of its canonical spelling, most significant
//! first and without leading zeros, so zero has no digits.
//!
//! Comparison, addition, subtraction, multiplication, division with remainder
//! and the greatest common divisor work on numbers of any length; they are
//! what the kernel needs to read `owl:rational` literals in lowest terms and to
//! compare rational numbers exactly by cross-multiplication.
#![allow(
    clippy::ptr_arg,
    clippy::len_zero,
    clippy::manual_range_contains,
    clippy::vec_init_then_push
)] // Indexed operations and explicit pushes for the pinned extraction subset.

/// The value of an ASCII digit, and 0 for any other byte.
fn digit_value(byte: u8) -> u8 {
    if (48 <= byte) & (byte <= 57) {
        byte - 48
    } else {
        0
    }
}

/// The digit `index` places from the right of `digits`, and 0 beyond them.
fn digit_at(digits: &Vec<u8>, index: usize) -> u8 {
    if index < digits.len() {
        digit_value(digits[digits.len() - 1 - index])
    } else {
        0
    }
}

/// `out` followed by `digits[..end]` from the last byte to the first.
fn reverse_into(digits: &Vec<u8>, end: usize, mut out: Vec<u8>) -> Vec<u8> {
    if (0 < end) & (end <= digits.len()) {
        if out.len() < usize::MAX {
            out.push(digits[end - 1]);
        }
        reverse_into(digits, end - 1, out)
    } else {
        out
    }
}

/// The first index from `index` on whose byte is not `0`, or the length.
fn first_nonzero(digits: &Vec<u8>, index: usize) -> usize {
    if index < digits.len() {
        if digits[index] == 48 {
            first_nonzero(digits, index + 1)
        } else {
            index
        }
    } else {
        digits.len()
    }
}

/// `out` followed by `digits[index..]`.
fn copy_from(digits: &Vec<u8>, index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < digits.len() {
        if out.len() < usize::MAX {
            out.push(digits[index]);
        }
        copy_from(digits, index + 1, out)
    } else {
        out
    }
}

/// The digits without their leading zeros.
pub fn canonical(digits: &Vec<u8>) -> Vec<u8> {
    copy_from(digits, first_nonzero(digits, 0), Vec::new())
}

/// The digits in the opposite order, without the zeros that then lead.
fn canonical_reversed(digits: &Vec<u8>) -> Vec<u8> {
    canonical(&reverse_into(digits, digits.len(), Vec::new()))
}

/// The order of the digits from `index` on: 0 when `left`'s are smaller, 1 when
/// they are the same, 2 when they are greater, for vectors of one length.
fn compare_from(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> u8 {
    if index < left.len() {
        if index < right.len() {
            if left[index] < right[index] {
                0
            } else if right[index] < left[index] {
                2
            } else {
                compare_from(left, right, index + 1)
            }
        } else {
            1
        }
    } else {
        1
    }
}

/// The order of two canonical numbers: 0 when `left` is smaller, 1 when they
/// are equal and 2 when `left` is greater.
pub fn compare_naturals(left: &Vec<u8>, right: &Vec<u8>) -> u8 {
    if left.len() < right.len() {
        0
    } else if right.len() < left.len() {
        2
    } else {
        compare_from(left, right, 0)
    }
}

/// Whether `index` is a position of one of the numbers.
fn within_either(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> bool {
    (index < left.len()) | (index < right.len())
}

/// `out` followed by the digits of `left + right + carry` from the place
/// `index` on, least significant first.
fn add_from(left: &Vec<u8>, right: &Vec<u8>, index: usize, carry: u8, mut out: Vec<u8>) -> Vec<u8> {
    if within_either(left, right, index) {
        let sum = digit_at(left, index) + digit_at(right, index) + carry;
        if out.len() < usize::MAX {
            out.push(48 + sum % 10);
        }
        add_from(left, right, index + 1, sum / 10, out)
    } else if 0 < carry {
        if out.len() < usize::MAX {
            out.push(48 + carry);
        }
        out
    } else {
        out
    }
}

/// The sum of two numbers.
pub fn add_naturals(left: &Vec<u8>, right: &Vec<u8>) -> Vec<u8> {
    canonical_reversed(&add_from(left, right, 0, 0, Vec::new()))
}

/// `out` followed by the digits of `left - right - borrow` from the place
/// `index` on, least significant first.
fn subtract_from(
    left: &Vec<u8>,
    right: &Vec<u8>,
    index: usize,
    borrow: u8,
    mut out: Vec<u8>,
) -> Vec<u8> {
    if index < left.len() {
        let top = digit_at(left, index);
        let low = digit_at(right, index) + borrow;
        let (digit, next) = if low <= top {
            (top - low, 0)
        } else {
            (top + 10 - low, 1)
        };
        if out.len() < usize::MAX {
            out.push(48 + digit);
        }
        subtract_from(left, right, index + 1, next, out)
    } else {
        out
    }
}

/// The difference of two canonical numbers, the first not below the second.
pub fn subtract_naturals(left: &Vec<u8>, right: &Vec<u8>) -> Vec<u8> {
    canonical_reversed(&subtract_from(left, right, 0, 0, Vec::new()))
}

/// The number times ten.
fn shifted(mut digits: Vec<u8>) -> Vec<u8> {
    if 0 < digits.len() {
        if digits.len() < usize::MAX {
            digits.push(48);
        }
        digits
    } else {
        digits
    }
}

/// `total` plus `count` times `value`.
fn repeated(value: &Vec<u8>, count: u8, total: Vec<u8>) -> Vec<u8> {
    if 0 < count {
        let sum = add_naturals(&total, value);
        repeated(value, count - 1, sum)
    } else {
        total
    }
}

/// `total` times ten to the remaining places of `right`, plus `left` times the
/// number those places write.
fn multiply_from(left: &Vec<u8>, right: &Vec<u8>, index: usize, total: Vec<u8>) -> Vec<u8> {
    if index < right.len() {
        let partial = repeated(left, digit_value(right[index]), Vec::new());
        let next = add_naturals(&shifted(total), &partial);
        multiply_from(left, right, index + 1, next)
    } else {
        total
    }
}

/// The product of two canonical numbers.
pub fn multiply_naturals(left: &Vec<u8>, right: &Vec<u8>) -> Vec<u8> {
    multiply_from(left, right, 0, Vec::new())
}

/// The number times ten plus the digit, canonical when the number is.
fn append_digit(mut digits: Vec<u8>, digit: u8) -> Vec<u8> {
    if 0 < digits.len() {
        if digits.len() < usize::MAX {
            digits.push(digit);
        }
        digits
    } else if digit == 48 {
        digits
    } else {
        if digits.len() < usize::MAX {
            digits.push(digit);
        }
        digits
    }
}

/// `current` less `divisor` as often as it fits, at most nine more times, and
/// how often in all.
fn reduce(divisor: &Vec<u8>, current: Vec<u8>, count: u8) -> (u8, Vec<u8>) {
    if count < 9 {
        if compare_naturals(&current, divisor) == 0 {
            (count, current)
        } else {
            let rest = subtract_naturals(&current, divisor);
            reduce(divisor, rest, count + 1)
        }
    } else {
        (count, current)
    }
}

/// Long division from the digit `index` of the dividend on, with the quotient
/// and remainder of the digits before it.
fn divide_from(
    dividend: &Vec<u8>,
    divisor: &Vec<u8>,
    index: usize,
    quotient: Vec<u8>,
    remainder: Vec<u8>,
) -> (Vec<u8>, Vec<u8>) {
    if index < dividend.len() {
        let current = append_digit(remainder, dividend[index]);
        let (count, rest) = reduce(divisor, current, 0);
        let next = append_digit(quotient, 48 + count);
        divide_from(dividend, divisor, index + 1, next, rest)
    } else {
        (quotient, remainder)
    }
}

/// The quotient and the remainder of two canonical numbers, the divisor not
/// zero.
pub fn divide_naturals(dividend: &Vec<u8>, divisor: &Vec<u8>) -> (Vec<u8>, Vec<u8>) {
    divide_from(dividend, divisor, 0, Vec::new(), Vec::new())
}

/// The greatest common divisor by Euclid's algorithm.
fn gcd_of(left: Vec<u8>, right: Vec<u8>) -> Vec<u8> {
    if 0 < right.len() {
        let (_, rest) = divide_naturals(&left, &right);
        gcd_of(right, rest)
    } else {
        left
    }
}

/// The greatest common divisor of two canonical numbers.
pub fn gcd_naturals(left: &Vec<u8>, right: &Vec<u8>) -> Vec<u8> {
    gcd_of(
        copy_from(left, 0, Vec::new()),
        copy_from(right, 0, Vec::new()),
    )
}

/// The number times ten to the count, canonical when the number is.
pub fn times_power(digits: Vec<u8>, count: usize) -> Vec<u8> {
    if 0 < count {
        times_power(shifted(digits), count - 1)
    } else {
        digits
    }
}

/// Ten to the count.
pub fn ten_power(count: usize) -> Vec<u8> {
    let mut one = Vec::new();
    one.push(49);
    times_power(one, count)
}
