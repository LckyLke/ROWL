//! Owned regular-language recognizer for the verified lexical frontend.
//!
//! Derivatives consume exactly one Unicode code point. Smart constructors avoid
//! retaining dead alternatives; matching still scans the complete UTF-8 buffer
//! so a malformed suffix cannot be hidden by an earlier language mismatch.
//! This is the shared recognizer for lexical grammars, not an OWL/RDF parser.

use crate::unicode::{decode_next, Decoded, TextError};

pub enum Expression {
    Empty,
    Epsilon,
    Interval { lower: u32, upper: u32 },
    Alternative(Box<Expression>, Box<Expression>),
    Sequence(Box<Expression>, Box<Expression>),
    Repeat(Box<Expression>),
}

pub enum MatchResult {
    Matched(bool),
    MalformedUtf8(TextError),
}

/// Explicit structural copying stays within the supported extraction subset.
pub fn copy_expression(expression: &Expression) -> Expression {
    match expression {
        Expression::Empty => Expression::Empty,
        Expression::Epsilon => Expression::Epsilon,
        Expression::Interval { lower, upper } => Expression::Interval {
            lower: *lower,
            upper: *upper,
        },
        Expression::Alternative(left, right) => Expression::Alternative(
            Box::new(copy_expression(left)),
            Box::new(copy_expression(right)),
        ),
        Expression::Sequence(left, right) => Expression::Sequence(
            Box::new(copy_expression(left)),
            Box::new(copy_expression(right)),
        ),
        Expression::Repeat(inner) => Expression::Repeat(Box::new(copy_expression(inner))),
    }
}

pub fn nullable(expression: &Expression) -> bool {
    match expression {
        Expression::Empty | Expression::Interval { .. } => false,
        Expression::Epsilon | Expression::Repeat(_) => true,
        Expression::Alternative(left, right) => nullable(left) || nullable(right),
        Expression::Sequence(left, right) => nullable(left) && nullable(right),
    }
}

pub fn alternate(left: Expression, right: Expression) -> Expression {
    match (left, right) {
        (Expression::Empty, right) => right,
        (left, Expression::Empty) => left,
        (left, right) => Expression::Alternative(Box::new(left), Box::new(right)),
    }
}

pub fn sequence(left: Expression, right: Expression) -> Expression {
    match (left, right) {
        (Expression::Empty, _) | (_, Expression::Empty) => Expression::Empty,
        (Expression::Epsilon, right) => right,
        (left, Expression::Epsilon) => left,
        (left, right) => Expression::Sequence(Box::new(left), Box::new(right)),
    }
}

pub fn repeat(expression: Expression) -> Expression {
    match expression {
        Expression::Empty | Expression::Epsilon => Expression::Epsilon,
        other => Expression::Repeat(Box::new(other)),
    }
}

/// Brzozowski derivative, preserving the language of the unconsumed suffix.
#[allow(clippy::manual_range_contains)]
pub fn derivative(expression: Expression, codepoint: u32) -> Expression {
    match expression {
        Expression::Empty | Expression::Epsilon => Expression::Empty,
        Expression::Interval { lower, upper } => {
            if (lower <= codepoint) && (codepoint <= upper) {
                Expression::Epsilon
            } else {
                Expression::Empty
            }
        }
        Expression::Alternative(left, right) => {
            alternate(derivative(*left, codepoint), derivative(*right, codepoint))
        }
        Expression::Sequence(left, right) => {
            let accepts_empty = nullable(&left);
            let right_derivative = if accepts_empty {
                derivative(copy_expression(&right), codepoint)
            } else {
                Expression::Empty
            };
            let joined = sequence(derivative(*left, codepoint), *right);
            alternate(joined, right_derivative)
        }
        Expression::Repeat(inner) => {
            let original = copy_expression(&inner);
            sequence(derivative(*inner, codepoint), repeat(original))
        }
    }
}

fn match_from(expression: Expression, bytes: &Vec<u8>, offset: usize) -> MatchResult {
    match decode_next(bytes, offset) {
        Decoded::End => MatchResult::Matched(nullable(&expression)),
        Decoded::Error(error) => MatchResult::MalformedUtf8(error),
        Decoded::Scalar { codepoint, next } => {
            match_from(derivative(expression, codepoint), bytes, next)
        }
    }
}

/// Match the entire UTF-8 input. No XML-character restriction or normalization
/// is imposed here; the supplied lexical grammar determines its own alphabet.
#[allow(clippy::ptr_arg)]
pub fn matches_utf8(expression: Expression, bytes: &Vec<u8>) -> MatchResult {
    match_from(expression, bytes, 0)
}
