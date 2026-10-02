//! OWL 2 Functional Syntax names from the referenced SPARQL 2008 grammar.
//!
//! These whole-buffer recognizers cover PNAME_NS, PN_LOCAL, PNAME_LN and
//! BLANK_NODE_LABEL. They preserve strict UTF-8 diagnostics. They do not apply
//! the broader Turtle/SPARQL 1.1 local-name escape grammar or tokenize a document.
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

pub fn validate_prefix(bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(prefix_grammar(), bytes)
}
pub fn validate_local(bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(local_word(), bytes)
}
pub fn validate_abbreviated(bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(abbreviated_grammar(), bytes)
}
pub fn validate_node(bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(node_grammar(), bytes)
}
