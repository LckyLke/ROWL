//! Functional Syntax class expressions of the reasoner's fragment.
//!
//! Reads named classes, `ObjectIntersectionOf`, `ObjectUnionOf`,
//! `ObjectComplementOf`, `ObjectOneOf`, `ObjectSomeValuesFrom`,
//! `ObjectAllValuesFrom` and `ObjectHasValue`, with object property expressions
//! `IRI` or `ObjectInverseOf( IRI )` and individuals read by the proved
//! individual reader. The other ten class-expression forms are reported as
//! unsupported at their keyword; later stages read them. Records keep the
//! original keyword and IRI tokens and the IRIs resolved through the checked
//! prefix table.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_header::{iri_kind, HeaderIri};
use crate::functional_individuals::{
    read_individual, read_individual_list, IndividualError, SourceIndividual,
};
use crate::functional_iris::{resolve_span, SourceIriError};
use crate::functional_lexer::Tokens;
use crate::prefixes::PrefixTable;

/// An object property expression: a property IRI or its inverse.
pub enum SourceObjectProperty {
    Named(HeaderIri),
    Inverse { keyword: Token, property: HeaderIri },
}
/// A class expression of the supported forms. Intersections and unions keep
/// their members, at least two, in source order; enumerations keep their
/// individuals, at least one, in source order.
pub enum SourceClass {
    Named(HeaderIri),
    IntersectionOf {
        keyword: Token,
        members: Vec<SourceClass>,
    },
    UnionOf {
        keyword: Token,
        members: Vec<SourceClass>,
    },
    ComplementOf {
        keyword: Token,
        operand: Box<SourceClass>,
    },
    SomeValuesFrom {
        keyword: Token,
        property: SourceObjectProperty,
        filler: Box<SourceClass>,
    },
    AllValuesFrom {
        keyword: Token,
        property: SourceObjectProperty,
        filler: Box<SourceClass>,
    },
    OneOf {
        keyword: Token,
        members: Vec<SourceIndividual>,
    },
    HasValue {
        keyword: Token,
        property: SourceObjectProperty,
        individual: SourceIndividual,
    },
}
/// `depth` bounds connective nesting: 0 permits only named classes, because
/// each level uses the physical stack. `count` bounds the members of each
/// intersection, union and enumeration. `iri` bounds every final IRI and node
/// ID.
pub struct ClassLimits {
    pub depth: usize,
    pub count: usize,
    pub iri: usize,
}
#[derive(Clone, Copy)]
pub enum ClassExpected {
    Class,
    Open,
    Property,
    Iri,
    Close,
}
pub enum ClassError {
    Expected {
        expected: ClassExpected,
        offset: usize,
    },
    Iri(SourceIriError),
    Individual(IndividualError),
    /// A class-expression form that this stage does not read yet.
    Unsupported {
        offset: usize,
    },
    DepthLimit {
        offset: usize,
    },
    CountLimit {
        offset: usize,
    },
}
/// A supported connective: an intersection (`true`) or union (`false`), a
/// complement, an existential (`true`) or universal (`false`) restriction, an
/// enumeration of individuals, or a restriction to one individual value.
#[derive(Clone, Copy)]
enum ClassForm {
    Junction(bool),
    Complement,
    Restriction(bool),
    OneOf,
    HasValue,
}
enum ClassKeyword {
    Connective(ClassForm),
    Unsupported,
    Other,
}
fn class_keyword(terminal: Terminal) -> ClassKeyword {
    match terminal {
        Terminal::Keyword(Keyword::ObjectIntersectionOf) => {
            ClassKeyword::Connective(ClassForm::Junction(true))
        }
        Terminal::Keyword(Keyword::ObjectUnionOf) => {
            ClassKeyword::Connective(ClassForm::Junction(false))
        }
        Terminal::Keyword(Keyword::ObjectComplementOf) => {
            ClassKeyword::Connective(ClassForm::Complement)
        }
        Terminal::Keyword(Keyword::ObjectSomeValuesFrom) => {
            ClassKeyword::Connective(ClassForm::Restriction(true))
        }
        Terminal::Keyword(Keyword::ObjectAllValuesFrom) => {
            ClassKeyword::Connective(ClassForm::Restriction(false))
        }
        Terminal::Keyword(Keyword::ObjectOneOf) => ClassKeyword::Connective(ClassForm::OneOf),
        Terminal::Keyword(Keyword::ObjectHasValue) => ClassKeyword::Connective(ClassForm::HasValue),
        Terminal::Keyword(Keyword::ObjectHasSelf) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::ObjectMinCardinality) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::ObjectMaxCardinality) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::ObjectExactCardinality) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::DataSomeValuesFrom) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::DataAllValuesFrom) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::DataHasValue) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::DataMinCardinality) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::DataMaxCardinality) => ClassKeyword::Unsupported,
        Terminal::Keyword(Keyword::DataExactCardinality) => ClassKeyword::Unsupported,
        _ => ClassKeyword::Other,
    }
}
fn inverse_keyword(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Keyword(Keyword::ObjectInverseOf))
}
fn closes(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Close)
}
fn expected_terminal(expected: ClassExpected, terminal: Terminal) -> bool {
    match expected {
        ClassExpected::Class => match class_keyword(terminal) {
            ClassKeyword::Other => iri_kind(terminal).is_some(),
            _ => true,
        },
        ClassExpected::Open => matches!(terminal, Terminal::Open),
        ClassExpected::Property => inverse_keyword(terminal) || iri_kind(terminal).is_some(),
        ClassExpected::Iri => iri_kind(terminal).is_some(),
        ClassExpected::Close => closes(terminal),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: ClassExpected,
    eof: usize,
) -> Result<(Token, Tokens), ClassError> {
    match tokens {
        Tokens::Empty => Err(ClassError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(ClassError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
/// The offset of the next token, or the source length at the end.
pub(crate) fn offset_of(tokens: &Tokens, eof: usize) -> usize {
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
    expected: ClassExpected,
    limit: usize,
) -> Result<HeaderIri, ClassError> {
    match iri_kind(token.terminal) {
        Some(family) => match resolve_span(table, family, bytes, token.start, token.end, limit) {
            Ok(value) => Ok(HeaderIri { token, value }),
            Err(error) => Err(ClassError::Iri(error)),
        },
        None => Err(ClassError::Expected {
            expected,
            offset: token.start,
        }),
    }
}
/// Read one object property expression: an IRI, or `ObjectInverseOf( IRI )`.
/// Errors report the first failing step in source order with original offsets.
pub fn read_object_property(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceObjectProperty, Tokens), ClassError> {
    match tokens {
        Tokens::Empty => Err(ClassError::Expected {
            expected: ClassExpected::Property,
            offset: bytes.len(),
        }),
        Tokens::Cons { token, next } => {
            if inverse_keyword(token.terminal) {
                let (_, tokens) = match take_expected(*next, ClassExpected::Open, bytes.len()) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                let (named, tokens) = match take_expected(tokens, ClassExpected::Iri, bytes.len()) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                let property = match resolve(table, bytes, named, ClassExpected::Iri, limit) {
                    Ok(property) => property,
                    Err(error) => return Err(error),
                };
                let (_, remaining) = match take_expected(tokens, ClassExpected::Close, bytes.len())
                {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                Ok((
                    SourceObjectProperty::Inverse {
                        keyword: token,
                        property,
                    },
                    remaining,
                ))
            } else {
                match resolve(table, bytes, token, ClassExpected::Property, limit) {
                    Ok(property) => Ok((SourceObjectProperty::Named(property), *next)),
                    Err(error) => Err(error),
                }
            }
        }
    }
}
fn read_class(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    depth: usize,
    limits: &ClassLimits,
) -> Result<(SourceClass, Tokens), ClassError> {
    match tokens {
        Tokens::Empty => Err(ClassError::Expected {
            expected: ClassExpected::Class,
            offset: bytes.len(),
        }),
        Tokens::Cons { token, next } => match class_keyword(token.terminal) {
            ClassKeyword::Other => {
                match resolve(table, bytes, token, ClassExpected::Class, limits.iri) {
                    Ok(iri) => Ok((SourceClass::Named(iri), *next)),
                    Err(error) => Err(error),
                }
            }
            ClassKeyword::Unsupported => Err(ClassError::Unsupported {
                offset: token.start,
            }),
            ClassKeyword::Connective(form) => {
                if depth == 0 {
                    return Err(ClassError::DepthLimit {
                        offset: token.start,
                    });
                }
                let (_, inner) = match take_expected(*next, ClassExpected::Open, bytes.len()) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                read_connective(table, bytes, token, form, inner, depth - 1, limits)
            }
        },
    }
}
/// The body of a connective after its `(`, ending with its `)`.
fn read_connective(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    keyword: Token,
    form: ClassForm,
    tokens: Tokens,
    depth: usize,
    limits: &ClassLimits,
) -> Result<(SourceClass, Tokens), ClassError> {
    match form {
        ClassForm::Junction(conjunctive) => {
            let (members, tokens) =
                match read_members(table, bytes, tokens, Vec::new(), depth, limits) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
            if members.len() < 2 {
                return Err(ClassError::Expected {
                    expected: ClassExpected::Class,
                    offset: offset_of(&tokens, bytes.len()),
                });
            }
            let (_, remaining) = match take_expected(tokens, ClassExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if conjunctive {
                Ok((SourceClass::IntersectionOf { keyword, members }, remaining))
            } else {
                Ok((SourceClass::UnionOf { keyword, members }, remaining))
            }
        }
        ClassForm::Complement => {
            let (operand, tokens) = match read_class(table, bytes, tokens, depth, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (_, remaining) = match take_expected(tokens, ClassExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceClass::ComplementOf {
                    keyword,
                    operand: Box::new(operand),
                },
                remaining,
            ))
        }
        ClassForm::Restriction(existential) => {
            let (property, tokens) = match read_object_property(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (filler, tokens) = match read_class(table, bytes, tokens, depth, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (_, remaining) = match take_expected(tokens, ClassExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if existential {
                Ok((
                    SourceClass::SomeValuesFrom {
                        keyword,
                        property,
                        filler: Box::new(filler),
                    },
                    remaining,
                ))
            } else {
                Ok((
                    SourceClass::AllValuesFrom {
                        keyword,
                        property,
                        filler: Box::new(filler),
                    },
                    remaining,
                ))
            }
        }
        ClassForm::OneOf => {
            let (members, tokens) =
                match read_individual_list(table, bytes, tokens, 1, limits.count, limits.iri) {
                    Ok(value) => value,
                    Err(error) => return Err(ClassError::Individual(error)),
                };
            let (_, remaining) = match take_expected(tokens, ClassExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((SourceClass::OneOf { keyword, members }, remaining))
        }
        ClassForm::HasValue => {
            let (property, tokens) = match read_object_property(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (individual, tokens) = match read_individual(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(ClassError::Individual(error)),
            };
            let (_, remaining) = match take_expected(tokens, ClassExpected::Close, bytes.len()) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceClass::HasValue {
                    keyword,
                    property,
                    individual,
                },
                remaining,
            ))
        }
    }
}
/// The maximal member sequence, stopping before `)` or at the end.
pub(crate) fn read_members(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut members: Vec<SourceClass>,
    depth: usize,
    limits: &ClassLimits,
) -> Result<(Vec<SourceClass>, Tokens), ClassError> {
    match tokens {
        Tokens::Empty => Ok((members, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((members, Tokens::Cons { token, next }));
            }
            if members.len() >= limits.count {
                return Err(ClassError::CountLimit {
                    offset: token.start,
                });
            }
            let (member, remaining) =
                match read_class(table, bytes, Tokens::Cons { token, next }, depth, limits) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
            members.push(member);
            read_members(table, bytes, remaining, members, depth, limits)
        }
    }
}
/// Read exactly one class expression of the supported forms. Named classes,
/// object properties and individuals resolve their original spans through the
/// checked prefix table with the `iri` limit. Errors report the first failing
/// step in source order with original offsets (EOF errors use the source
/// length): at a connective keyword the nesting depth, then `(`, the operands in
/// order (each member of an intersection, union or enumeration after checking
/// the member count), then the two-member minimum of an intersection or union or
/// the one-member minimum of an enumeration, then `)`. The unchanged suffix
/// after the expression is returned. The other class-expression forms are
/// reported as unsupported.
pub fn read_class_expression(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceClass, Tokens), ClassError> {
    read_class(table, bytes, tokens, limits.depth, limits)
}
