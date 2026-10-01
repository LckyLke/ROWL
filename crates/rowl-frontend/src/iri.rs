//! RFC 3987 section 2.2 IRI and IRI-reference lexical grammar.
//!
//! `iri` includes fragments (the RFC's differently named `absolute-IRI`
//! production does not). Identity remains exact bytes; no percent decoding,
//! case folding, host interpretation or scheme-specific policy is performed.

use crate::regular::{copy_expression, matches_utf8, Expression, MatchResult};

fn range(lower: u32, upper: u32) -> Expression {
    Expression::Interval { lower, upper }
}
fn chr(cp: u32) -> Expression {
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
fn exact(a: Expression, count: u8) -> Expression {
    if count == 0 {
        Expression::Epsilon
    } else {
        cat(copy_expression(&a), exact(a, count - 1))
    }
}
fn up_to(a: Expression, count: u8) -> Expression {
    if count == 0 {
        Expression::Epsilon
    } else {
        opt(cat(copy_expression(&a), up_to(a, count - 1)))
    }
}
fn alpha() -> Expression {
    alt(range(65, 90), range(97, 122))
}
fn digit() -> Expression {
    range(48, 57)
}
fn hex() -> Expression {
    alt(digit(), alt(range(65, 70), range(97, 102)))
}
fn unreserved() -> Expression {
    alt(
        alpha(),
        alt(digit(), alt(chr(45), alt(chr(46), alt(chr(95), chr(126))))),
    )
}
fn sub_delims() -> Expression {
    alt(
        chr(33),
        alt(
            chr(36),
            alt(
                chr(38),
                alt(
                    chr(39),
                    alt(
                        chr(40),
                        alt(
                            chr(41),
                            alt(chr(42), alt(chr(43), alt(chr(44), alt(chr(59), chr(61))))),
                        ),
                    ),
                ),
            ),
        ),
    )
}
fn pct_encoded() -> Expression {
    cat(chr(37), exact(hex(), 2))
}
fn ucschar() -> Expression {
    alt(
        range(0xa0, 0xd7ff),
        alt(
            range(0xf900, 0xfdcf),
            alt(
                range(0xfdf0, 0xffef),
                alt(
                    range(0x10000, 0x1fffd),
                    alt(
                        range(0x20000, 0x2fffd),
                        alt(
                            range(0x30000, 0x3fffd),
                            alt(
                                range(0x40000, 0x4fffd),
                                alt(
                                    range(0x50000, 0x5fffd),
                                    alt(
                                        range(0x60000, 0x6fffd),
                                        alt(
                                            range(0x70000, 0x7fffd),
                                            alt(
                                                range(0x80000, 0x8fffd),
                                                alt(
                                                    range(0x90000, 0x9fffd),
                                                    alt(
                                                        range(0xa0000, 0xafffd),
                                                        alt(
                                                            range(0xb0000, 0xbfffd),
                                                            alt(
                                                                range(0xc0000, 0xcfffd),
                                                                alt(
                                                                    range(0xd0000, 0xdfffd),
                                                                    range(0xe1000, 0xefffd),
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
                ),
            ),
        ),
    )
}
fn iprivate() -> Expression {
    alt(
        range(0xe000, 0xf8ff),
        alt(range(0xf0000, 0xffffd), range(0x100000, 0x10fffd)),
    )
}
fn iunreserved() -> Expression {
    alt(unreserved(), ucschar())
}
fn ipchar() -> Expression {
    alt(
        iunreserved(),
        alt(pct_encoded(), alt(sub_delims(), alt(chr(58), chr(64)))),
    )
}
fn segment() -> Expression {
    star(ipchar())
}
fn segment_nz() -> Expression {
    plus(ipchar())
}
fn segment_nz_nc() -> Expression {
    plus(alt(
        iunreserved(),
        alt(pct_encoded(), alt(sub_delims(), chr(64))),
    ))
}
fn path_tail() -> Expression {
    star(cat(chr(47), segment()))
}
fn path_absolute() -> Expression {
    cat(chr(47), opt(cat(segment_nz(), path_tail())))
}
fn path_rootless() -> Expression {
    cat(segment_nz(), path_tail())
}
fn path_noscheme() -> Expression {
    cat(segment_nz_nc(), path_tail())
}
fn query() -> Expression {
    star(alt(ipchar(), alt(iprivate(), alt(chr(47), chr(63)))))
}
fn fragment() -> Expression {
    star(alt(ipchar(), alt(chr(47), chr(63))))
}
fn scheme() -> Expression {
    cat(
        alpha(),
        star(alt(
            alpha(),
            alt(digit(), alt(chr(43), alt(chr(45), chr(46)))),
        )),
    )
}
fn userinfo() -> Expression {
    star(alt(
        iunreserved(),
        alt(pct_encoded(), alt(sub_delims(), chr(58))),
    ))
}
fn reg_name() -> Expression {
    star(alt(iunreserved(), alt(pct_encoded(), sub_delims())))
}
fn dec_octet() -> Expression {
    alt(
        digit(),
        alt(
            cat(range(49, 57), digit()),
            alt(
                cat(chr(49), exact(digit(), 2)),
                alt(
                    cat(chr(50), cat(range(48, 52), digit())),
                    cat(chr(50), cat(chr(53), range(48, 53))),
                ),
            ),
        ),
    )
}
fn ipv4() -> Expression {
    cat(exact(cat(dec_octet(), chr(46)), 3), dec_octet())
}
fn h16() -> Expression {
    cat(hex(), up_to(hex(), 3))
}
fn ls32() -> Expression {
    alt(cat(h16(), cat(chr(58), h16())), ipv4())
}
fn colon_pair() -> Expression {
    cat(chr(58), chr(58))
}
fn h16_colon() -> Expression {
    cat(h16(), chr(58))
}
fn compressed_prefix(max_colons: u8) -> Expression {
    opt(cat(up_to(h16_colon(), max_colons), h16()))
}
fn ipv6() -> Expression {
    alt(
        cat(exact(h16_colon(), 6), ls32()),
        alt(
            cat(colon_pair(), cat(exact(h16_colon(), 5), ls32())),
            alt(
                cat(
                    opt(h16()),
                    cat(colon_pair(), cat(exact(h16_colon(), 4), ls32())),
                ),
                alt(
                    cat(
                        compressed_prefix(1),
                        cat(colon_pair(), cat(exact(h16_colon(), 3), ls32())),
                    ),
                    alt(
                        cat(
                            compressed_prefix(2),
                            cat(colon_pair(), cat(exact(h16_colon(), 2), ls32())),
                        ),
                        alt(
                            cat(
                                compressed_prefix(3),
                                cat(colon_pair(), cat(h16_colon(), ls32())),
                            ),
                            alt(
                                cat(compressed_prefix(4), cat(colon_pair(), ls32())),
                                alt(
                                    cat(compressed_prefix(5), cat(colon_pair(), h16())),
                                    cat(compressed_prefix(6), colon_pair()),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}
fn ipv_future() -> Expression {
    cat(
        alt(chr(118), chr(86)),
        cat(
            plus(hex()),
            cat(chr(46), plus(alt(unreserved(), alt(sub_delims(), chr(58))))),
        ),
    )
}
fn ip_literal() -> Expression {
    cat(chr(91), cat(alt(ipv6(), ipv_future()), chr(93)))
}
fn host() -> Expression {
    alt(ip_literal(), alt(ipv4(), reg_name()))
}
fn authority() -> Expression {
    cat(
        opt(cat(userinfo(), chr(64))),
        cat(host(), opt(cat(chr(58), star(digit())))),
    )
}
fn authority_path() -> Expression {
    cat(double_slash(), cat(authority(), path_tail()))
}
fn double_slash() -> Expression {
    cat(chr(47), chr(47))
}
fn hier_part() -> Expression {
    alt(
        authority_path(),
        alt(path_absolute(), alt(path_rootless(), Expression::Epsilon)),
    )
}
fn relative_part() -> Expression {
    alt(
        authority_path(),
        alt(path_absolute(), alt(path_noscheme(), Expression::Epsilon)),
    )
}
fn suffix() -> Expression {
    cat(opt(cat(chr(63), query())), opt(cat(chr(35), fragment())))
}

/// The `IRI` production; fragments are permitted for OWL/RDF absolute IRIs.
pub fn iri() -> Expression {
    cat(scheme(), cat(chr(58), cat(hier_part(), suffix())))
}
/// A complete relative reference, including optional query and fragment.
fn relative_ref() -> Expression {
    cat(relative_part(), suffix())
}
/// The complete `IRI-reference` production, also used before base resolution.
pub fn iri_reference() -> Expression {
    alt(iri(), relative_ref())
}

/// Validate exact bytes against the `IRI` production and strict UTF-8.
#[allow(clippy::ptr_arg)]
pub fn validate_iri(bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(iri(), bytes)
}
/// Validate exact bytes against `IRI-reference`; this does not resolve a base.
#[allow(clippy::ptr_arg)]
pub fn validate_reference(bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(iri_reference(), bytes)
}
