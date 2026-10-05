//! Functional Syntax data ranges: datatypes, `DataIntersectionOf`,
//! `DataUnionOf`, `DataComplementOf`, `DataOneOf` and `DatatypeRestriction`.
//!
//! Datatype and facet IRIs resolve their original spans through the checked
//! prefix table, and literals are read by the proved literal reader. Records
//! keep the original keyword tokens.
#![allow(clippy::ptr_arg, clippy::question_mark, clippy::len_zero)] // Vec::is_empty lacks a model in the pinned extraction.
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_header::{iri_kind, HeaderIri};
use crate::functional_iris::{resolve_span, SourceIriError};
use crate::functional_lexer::Tokens;
use crate::functional_literals::{read_literal, SourceLiteral, SourceLiteralError};
use crate::prefixes::PrefixTable;

/// A constraining facet of a datatype restriction and its value.
pub struct SourceFacet {
    pub facet: HeaderIri,
    pub value: SourceLiteral,
}
/// A data range. Intersections and unions keep their members, at least two,
/// enumerations their literals, at least one, and datatype restrictions their
/// facets, at least one, in source order.
pub enum SourceDataRange {
    Datatype(HeaderIri),
    IntersectionOf {
        keyword: Token,
        members: Vec<SourceDataRange>,
    },
    UnionOf {
        keyword: Token,
        members: Vec<SourceDataRange>,
    },
    ComplementOf {
        keyword: Token,
        operand: Box<SourceDataRange>,
    },
    OneOf {
        keyword: Token,
        members: Vec<SourceLiteral>,
    },
    Restriction {
        keyword: Token,
        datatype: HeaderIri,
        facets: Vec<SourceFacet>,
    },
}
#[derive(Clone, Copy)]
pub enum RangeExpected {
    Range,
    Open,
    Iri,
    Literal,
    Close,
}
pub enum RangeError {
    Expected {
        expected: RangeExpected,
        offset: usize,
    },
    Iri(SourceIriError),
    Literal(SourceLiteralError),
    DepthLimit {
        offset: usize,
    },
    CountLimit {
        offset: usize,
    },
}
/// A data range connective: an intersection (`true`) or union (`false`), a
/// complement, an enumeration of literals or a datatype restriction.
#[derive(Clone, Copy)]
enum RangeForm {
    Junction(bool),
    Complement,
    OneOf,
    Restriction,
}
fn range_form(terminal: Terminal) -> Option<RangeForm> {
    match terminal {
        Terminal::Keyword(Keyword::DataIntersectionOf) => Some(RangeForm::Junction(true)),
        Terminal::Keyword(Keyword::DataUnionOf) => Some(RangeForm::Junction(false)),
        Terminal::Keyword(Keyword::DataComplementOf) => Some(RangeForm::Complement),
        Terminal::Keyword(Keyword::DataOneOf) => Some(RangeForm::OneOf),
        Terminal::Keyword(Keyword::DatatypeRestriction) => Some(RangeForm::Restriction),
        _ => None,
    }
}
fn closes(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Close)
}
fn expected_terminal(expected: RangeExpected, terminal: Terminal) -> bool {
    match expected {
        RangeExpected::Range => range_form(terminal).is_some() || iri_kind(terminal).is_some(),
        RangeExpected::Open => matches!(terminal, Terminal::Open),
        RangeExpected::Iri => iri_kind(terminal).is_some(),
        RangeExpected::Literal => matches!(terminal, Terminal::QuotedString),
        RangeExpected::Close => closes(terminal),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: RangeExpected,
    eof: usize,
) -> Result<(Token, Tokens), RangeError> {
    match tokens {
        Tokens::Empty => Err(RangeError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(RangeError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
/// The offset of the next token, or the source length at the end.
fn offset_of(tokens: &Tokens, eof: usize) -> usize {
    match tokens {
        Tokens::Empty => eof,
        Tokens::Cons { token, .. } => token.start,
    }
}
/// Resolve an IRI token through the prefix table; any other token is reported
/// as missing the `expected` syntax.
fn resolve(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    token: Token,
    expected: RangeExpected,
    limit: usize,
) -> Result<HeaderIri, RangeError> {
    match iri_kind(token.terminal) {
        Some(family) => match resolve_span(table, family, bytes, token.start, token.end, limit) {
            Ok(value) => Ok(HeaderIri { token, value }),
            Err(error) => Err(RangeError::Iri(error)),
        },
        None => Err(RangeError::Expected {
            expected,
            offset: token.start,
        }),
    }
}
fn read_range(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    depth: usize,
    count: usize,
    limit: usize,
) -> Result<(SourceDataRange, Tokens), RangeError> {
    match tokens {
        Tokens::Empty => Err(RangeError::Expected {
            expected: RangeExpected::Range,
            offset: bytes.len(),
        }),
        Tokens::Cons { token, next } => match range_form(token.terminal) {
            None => match resolve(table, bytes, token, RangeExpected::Range, limit) {
                Ok(datatype) => Ok((SourceDataRange::Datatype(datatype), *next)),
                Err(error) => Err(error),
            },
            Some(form) => {
                if depth == 0 {
                    return Err(RangeError::DepthLimit {
                        offset: token.start,
                    });
                }
                let (_, inner) = match take_expected(*next, RangeExpected::Open, bytes.len()) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                read_body(table, bytes, token, form, inner, depth - 1, count, limit)
            }
        },
    }
}
/// The body of a data range connective after its `(`, ending with its `)`.
#[allow(clippy::too_many_arguments)]
fn read_body(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    keyword: Token,
    form: RangeForm,
    tokens: Tokens,
    depth: usize,
    count: usize,
    limit: usize,
) -> Result<(SourceDataRange, Tokens), RangeError> {
    match form {
        RangeForm::Junction(conjunctive) => {
            let (members, tokens) =
                match read_members(table, bytes, tokens, Vec::new(), depth, count, limit) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
            if members.len() < 2 {
                return Err(RangeError::Expected {
                    expected: RangeExpected::Range,
                    offset: offset_of(&tokens, bytes.len()),
                });
            }
            let (_, remaining) = match take_expected(tokens, RangeExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if conjunctive {
                Ok((
                    SourceDataRange::IntersectionOf { keyword, members },
                    remaining,
                ))
            } else {
                Ok((SourceDataRange::UnionOf { keyword, members }, remaining))
            }
        }
        RangeForm::Complement => {
            let (operand, tokens) = match read_range(table, bytes, tokens, depth, count, limit) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (_, remaining) = match take_expected(tokens, RangeExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceDataRange::ComplementOf {
                    keyword,
                    operand: Box::new(operand),
                },
                remaining,
            ))
        }
        RangeForm::OneOf => {
            let (members, tokens) =
                match read_literals(table, bytes, tokens, Vec::new(), count, limit) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
            if members.len() < 1 {
                return Err(RangeError::Expected {
                    expected: RangeExpected::Literal,
                    offset: offset_of(&tokens, bytes.len()),
                });
            }
            let (_, remaining) = match take_expected(tokens, RangeExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((SourceDataRange::OneOf { keyword, members }, remaining))
        }
        RangeForm::Restriction => {
            let (named, tokens) = match take_expected(tokens, RangeExpected::Iri, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let datatype = match resolve(table, bytes, named, RangeExpected::Iri, limit) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (facets, tokens) = match read_facets(table, bytes, tokens, Vec::new(), count, limit)
            {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if facets.len() < 1 {
                return Err(RangeError::Expected {
                    expected: RangeExpected::Iri,
                    offset: offset_of(&tokens, bytes.len()),
                });
            }
            let (_, remaining) = match take_expected(tokens, RangeExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceDataRange::Restriction {
                    keyword,
                    datatype,
                    facets,
                },
                remaining,
            ))
        }
    }
}
/// The maximal member sequence, stopping before `)` or at the end.
fn read_members(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut members: Vec<SourceDataRange>,
    depth: usize,
    count: usize,
    limit: usize,
) -> Result<(Vec<SourceDataRange>, Tokens), RangeError> {
    match tokens {
        Tokens::Empty => Ok((members, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((members, Tokens::Cons { token, next }));
            }
            if members.len() >= count {
                return Err(RangeError::CountLimit {
                    offset: token.start,
                });
            }
            let (member, remaining) = match read_range(
                table,
                bytes,
                Tokens::Cons { token, next },
                depth,
                count,
                limit,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            members.push(member);
            read_members(table, bytes, remaining, members, depth, count, limit)
        }
    }
}
/// The maximal literal sequence of an enumeration, stopping before `)` or at
/// the end.
fn read_literals(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut members: Vec<SourceLiteral>,
    count: usize,
    limit: usize,
) -> Result<(Vec<SourceLiteral>, Tokens), RangeError> {
    match tokens {
        Tokens::Empty => Ok((members, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((members, Tokens::Cons { token, next }));
            }
            if members.len() >= count {
                return Err(RangeError::CountLimit {
                    offset: token.start,
                });
            }
            let (member, remaining) =
                match read_literal(table, bytes, Tokens::Cons { token, next }, limit, limit) {
                    Ok(value) => value,
                    Err(error) => return Err(RangeError::Literal(error)),
                };
            members.push(member);
            read_literals(table, bytes, remaining, members, count, limit)
        }
    }
}
/// The maximal sequence of facets and their values, stopping before `)` or at
/// the end.
fn read_facets(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut facets: Vec<SourceFacet>,
    count: usize,
    limit: usize,
) -> Result<(Vec<SourceFacet>, Tokens), RangeError> {
    match tokens {
        Tokens::Empty => Ok((facets, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((facets, Tokens::Cons { token, next }));
            }
            if facets.len() >= count {
                return Err(RangeError::CountLimit {
                    offset: token.start,
                });
            }
            let facet = match resolve(table, bytes, token, RangeExpected::Iri, limit) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (value, remaining) = match read_literal(table, bytes, *next, limit, limit) {
                Ok(value) => value,
                Err(error) => return Err(RangeError::Literal(error)),
            };
            facets.push(SourceFacet { facet, value });
            read_facets(table, bytes, remaining, facets, count, limit)
        }
    }
}
/// Read exactly one data range. Datatype and facet IRIs resolve their original
/// spans through the checked prefix table with the `limit`, which also bounds
/// every literal's lexical form and datatype IRI. `depth` bounds connective
/// nesting and `count` the members of each list. Errors report the first
/// failing step in source order with original offsets (EOF errors use the
/// source length): at a connective keyword the nesting depth, then `(`, the
/// operands in order (each member, literal or facet after checking the count),
/// then the two-member minimum of an intersection or union, the one-literal
/// minimum of an enumeration or the one-facet minimum of a restriction, then
/// `)`. The unchanged suffix after the range is returned.
pub fn read_data_range(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    depth: usize,
    count: usize,
    limit: usize,
) -> Result<(SourceDataRange, Tokens), RangeError> {
    read_range(table, bytes, tokens, depth, count, limit)
}
/// The optional data range of a data number restriction: none before `)` or at
/// the end, and otherwise one data range.
pub fn read_optional_range(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    depth: usize,
    count: usize,
    limit: usize,
) -> Result<(Option<SourceDataRange>, Tokens), RangeError> {
    match tokens {
        Tokens::Empty => Ok((None, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((None, Tokens::Cons { token, next }));
            }
            match read_range(
                table,
                bytes,
                Tokens::Cons { token, next },
                depth,
                count,
                limit,
            ) {
                Ok((range, remaining)) => Ok((Some(range), remaining)),
                Err(error) => Err(error),
            }
        }
    }
}
