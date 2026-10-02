//! RFC 5646 §2.1/§2.2.9 well-formed language tags, without registry validity.
//! Well-formedness is ABNF syntax; duplicate restrictions belong to validity.
//! Matching preserves the original bytes and uses ASCII case-insensitive tokens.
#![allow(clippy::ptr_arg, clippy::manual_range_contains)]
use crate::regular::{copy_expression, matches_utf8, Expression, MatchResult};

fn range(lower: u32, upper: u32) -> Expression {
    Expression::Interval { lower, upper }
}
fn ch(cp: u32) -> Expression {
    range(cp, cp)
}
fn alt(a: Expression, b: Expression) -> Expression {
    Expression::Alternative(Box::new(a), Box::new(b))
}
fn cat(a: Expression, b: Expression) -> Expression {
    Expression::Sequence(Box::new(a), Box::new(b))
}
fn opt(a: Expression) -> Expression {
    alt(Expression::Epsilon, a)
}
fn star(a: Expression) -> Expression {
    Expression::Repeat(Box::new(a))
}
fn plus(a: Expression) -> Expression {
    cat(copy_expression(&a), star(a))
}
fn exact(a: &Expression, n: u8) -> Expression {
    if n == 0 {
        Expression::Epsilon
    } else {
        cat(copy_expression(a), exact(a, n - 1))
    }
}
fn up_to(a: &Expression, n: u8) -> Expression {
    if n == 0 {
        Expression::Epsilon
    } else {
        opt(cat(copy_expression(a), up_to(a, n - 1)))
    }
}
fn between(a: Expression, lower: u8, extra: u8) -> Expression {
    cat(exact(&a, lower), up_to(&a, extra))
}
fn alpha() -> Expression {
    alt(range(65, 90), range(97, 122))
}
fn digit() -> Expression {
    range(48, 57)
}
fn alnum() -> Expression {
    alt(alpha(), digit())
}
fn singleton() -> Expression {
    alt(
        digit(),
        alt(
            alt(range(65, 87), range(89, 90)),
            alt(range(97, 119), range(121, 122)),
        ),
    )
}
fn dashed(a: Expression) -> Expression {
    cat(ch(45), a)
}
fn literal_from(bytes: &[u8], position: usize) -> Expression {
    if position == bytes.len() {
        Expression::Epsilon
    } else {
        let value = u32::from(bytes[position]);
        let token = if value >= 97 && value <= 122 {
            alt(ch(value), ch(value - 32))
        } else {
            ch(value)
        };
        cat(token, literal_from(bytes, position + 1))
    }
}
fn literal(bytes: &[u8]) -> Expression {
    literal_from(bytes, 0)
}
fn grandfathered() -> Expression {
    alt(literal(b"en-gb-oed"), alt(literal(b"i-ami"), alt(literal(b"i-bnn"),
    alt(literal(b"i-default"), alt(literal(b"i-enochian"), alt(literal(b"i-hak"),
    alt(literal(b"i-klingon"), alt(literal(b"i-lux"), alt(literal(b"i-mingo"),
    alt(literal(b"i-navajo"), alt(literal(b"i-pwn"), alt(literal(b"i-tao"),
    alt(literal(b"i-tay"), alt(literal(b"i-tsu"), alt(literal(b"sgn-be-fr"),
    alt(literal(b"sgn-be-nl"), alt(literal(b"sgn-ch-de"), alt(literal(b"art-lojban"),
    alt(literal(b"cel-gaulish"), alt(literal(b"no-bok"), alt(literal(b"no-nyn"),
    alt(literal(b"zh-guoyu"), alt(literal(b"zh-hakka"), alt(literal(b"zh-min"),
    alt(literal(b"zh-min-nan"), literal(b"zh-xiang"))))))))))))))))))))))))))
}
fn language() -> Expression {
    let extlang = cat(exact(&alpha(), 3), up_to(&dashed(exact(&alpha(), 3)), 2));
    alt(
        cat(between(alpha(), 2, 1), opt(dashed(extlang))),
        alt(exact(&alpha(), 4), between(alpha(), 5, 3)),
    )
}
fn variant() -> Expression {
    alt(between(alnum(), 5, 3), cat(digit(), exact(&alnum(), 3)))
}
fn extension() -> Expression {
    cat(singleton(), plus(dashed(between(alnum(), 2, 6))))
}
fn private_use() -> Expression {
    cat(alt(ch(120), ch(88)), plus(dashed(between(alnum(), 1, 7))))
}
fn langtag() -> Expression {
    cat(
        language(),
        cat(
            opt(dashed(exact(&alpha(), 4))),
            cat(
                opt(dashed(alt(exact(&alpha(), 2), exact(&digit(), 3)))),
                cat(
                    star(dashed(variant())),
                    cat(star(dashed(extension())), opt(dashed(private_use()))),
                ),
            ),
        ),
    )
}
/// Complete RFC 5646 well-formed ABNF, including all grandfathered tags.
/// Registered meaning, duplicate-subtag validity and canonicalization are separate.
pub fn grammar() -> Expression {
    alt(langtag(), alt(private_use(), grandfathered()))
}
/// The explicitly named RFC 5646 `langtag` production used by OWL Functional
/// Syntax. Standalone private-use and grandfathered alternatives belong to
/// the broader `Language-Tag` production returned by `grammar`.
pub fn normal_grammar() -> Expression {
    langtag()
}
pub fn well_formed(bytes: &Vec<u8>) -> bool {
    matches!(matches_utf8(grammar(), bytes), MatchResult::Matched(true))
}
