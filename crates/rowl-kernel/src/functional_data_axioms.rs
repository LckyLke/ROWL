//! Functional Syntax data property axioms, datatype definitions and keys, with
//! their axiom annotations.
//!
//! Reads `SubDataPropertyOf`, `EquivalentDataProperties`,
//! `DisjointDataProperties`, `DataPropertyDomain`, `DataPropertyRange`,
//! `FunctionalDataProperty`, `DatatypeDefinition` and `HasKey` at a
//! caller-supplied axiom position. Axiom annotations, class expressions, object
//! property expressions and data ranges use the proved readers; data
//! properties and datatypes are IRIs resolved through the checked prefix table.
#![allow(clippy::ptr_arg, clippy::question_mark, clippy::len_zero)] // Vec::is_empty lacks a model in the pinned extraction.
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation,
};
use crate::functional_classes::{
    offset_of, read_class_expression, read_object_property, ClassError, ClassLimits, SourceClass,
    SourceObjectProperty,
};
use crate::functional_header::{iri_kind, HeaderIri};
use crate::functional_iris::{resolve_span, SourceIriError};
use crate::functional_lexer::Tokens;
use crate::functional_ranges::{read_data_range, RangeError, SourceDataRange};
use crate::prefixes::PrefixTable;

/// The body of a data property axiom, datatype definition or key. Member lists
/// keep their properties, at least two, in source order; a key keeps its object
/// and data properties, either list possibly empty, in source order.
pub enum SourceDataAxiomBody {
    SubDataPropertyOf {
        sub: HeaderIri,
        sup: HeaderIri,
    },
    EquivalentDataProperties(Vec<HeaderIri>),
    DisjointDataProperties(Vec<HeaderIri>),
    DataPropertyDomain {
        property: HeaderIri,
        domain: SourceClass,
    },
    DataPropertyRange {
        property: HeaderIri,
        range: SourceDataRange,
    },
    FunctionalDataProperty(HeaderIri),
    DatatypeDefinition {
        datatype: HeaderIri,
        range: SourceDataRange,
    },
    HasKey {
        class: SourceClass,
        objects: Vec<SourceObjectProperty>,
        data: Vec<HeaderIri>,
    },
}
pub struct SourceDataAxiom {
    pub keyword: Token,
    pub annotations: Vec<SourceAnnotation>,
    pub body: SourceDataAxiomBody,
}
#[derive(Clone, Copy)]
pub enum DataAxiomExpected {
    Axiom,
    Open,
    Iri,
    Close,
}
pub enum DataAxiomError {
    Expected {
        expected: DataAxiomExpected,
        offset: usize,
    },
    /// A property list longer than the class limits' count.
    CountLimit {
        offset: usize,
    },
    Iri(SourceIriError),
    Annotation(AnnotationError),
    Class(ClassError),
    Range(RangeError),
}
#[derive(Clone, Copy)]
enum AxiomForm {
    Sub,
    Equivalent,
    Disjoint,
    Domain,
    Range,
    Functional,
    Definition,
    Key,
}
fn axiom_form(terminal: Terminal) -> Option<AxiomForm> {
    match terminal {
        Terminal::Keyword(Keyword::SubDataPropertyOf) => Some(AxiomForm::Sub),
        Terminal::Keyword(Keyword::EquivalentDataProperties) => Some(AxiomForm::Equivalent),
        Terminal::Keyword(Keyword::DisjointDataProperties) => Some(AxiomForm::Disjoint),
        Terminal::Keyword(Keyword::DataPropertyDomain) => Some(AxiomForm::Domain),
        Terminal::Keyword(Keyword::DataPropertyRange) => Some(AxiomForm::Range),
        Terminal::Keyword(Keyword::FunctionalDataProperty) => Some(AxiomForm::Functional),
        Terminal::Keyword(Keyword::DatatypeDefinition) => Some(AxiomForm::Definition),
        Terminal::Keyword(Keyword::HasKey) => Some(AxiomForm::Key),
        _ => None,
    }
}
fn closes(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Close)
}
fn expected_terminal(expected: DataAxiomExpected, terminal: Terminal) -> bool {
    match expected {
        DataAxiomExpected::Axiom => axiom_form(terminal).is_some(),
        DataAxiomExpected::Open => matches!(terminal, Terminal::Open),
        DataAxiomExpected::Iri => iri_kind(terminal).is_some(),
        DataAxiomExpected::Close => closes(terminal),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: DataAxiomExpected,
    eof: usize,
) -> Result<(Token, Tokens), DataAxiomError> {
    match tokens {
        Tokens::Empty => Err(DataAxiomError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(DataAxiomError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
/// One IRI: a data property or datatype resolved through the prefix table.
fn read_iri(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(HeaderIri, Tokens), DataAxiomError> {
    match tokens {
        Tokens::Empty => Err(DataAxiomError::Expected {
            expected: DataAxiomExpected::Iri,
            offset: bytes.len(),
        }),
        Tokens::Cons { token, next } => match iri_kind(token.terminal) {
            Some(family) => {
                match resolve_span(table, family, bytes, token.start, token.end, limit) {
                    Ok(value) => Ok((HeaderIri { token, value }, *next)),
                    Err(error) => Err(DataAxiomError::Iri(error)),
                }
            }
            None => Err(DataAxiomError::Expected {
                expected: DataAxiomExpected::Iri,
                offset: token.start,
            }),
        },
    }
}
/// Data properties up to the next `)` or the end, after `members`; a list may
/// hold at most the class limits' count.
fn read_iris(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut members: Vec<HeaderIri>,
    limits: &ClassLimits,
) -> Result<(Vec<HeaderIri>, Tokens), DataAxiomError> {
    match tokens {
        Tokens::Empty => Ok((members, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((members, Tokens::Cons { token, next }));
            }
            if members.len() >= limits.count {
                return Err(DataAxiomError::CountLimit {
                    offset: token.start,
                });
            }
            let (member, remaining) =
                match read_iri(table, bytes, Tokens::Cons { token, next }, limits.iri) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
            members.push(member);
            read_iris(table, bytes, remaining, members, limits)
        }
    }
}
/// Object property expressions up to the next `)` or the end, after `members`.
fn read_objects(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut members: Vec<SourceObjectProperty>,
    limits: &ClassLimits,
) -> Result<(Vec<SourceObjectProperty>, Tokens), DataAxiomError> {
    match tokens {
        Tokens::Empty => Ok((members, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((members, Tokens::Cons { token, next }));
            }
            if members.len() >= limits.count {
                return Err(DataAxiomError::CountLimit {
                    offset: token.start,
                });
            }
            let (member, remaining) = match read_object_property(
                table,
                bytes,
                Tokens::Cons { token, next },
                limits.iri,
            ) {
                Ok(value) => value,
                Err(error) => return Err(DataAxiomError::Class(error)),
            };
            members.push(member);
            read_objects(table, bytes, remaining, members, limits)
        }
    }
}
/// At least two data properties, up to the next `)` or the end.
fn read_list(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(Vec<HeaderIri>, Tokens), DataAxiomError> {
    let (members, rest) = match read_iris(table, bytes, tokens, Vec::new(), limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if members.len() < 2 {
        return Err(DataAxiomError::Expected {
            expected: DataAxiomExpected::Iri,
            offset: offset_of(&rest, bytes.len()),
        });
    }
    Ok((members, rest))
}
fn read_class(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceClass, Tokens), DataAxiomError> {
    match read_class_expression(table, bytes, tokens, limits) {
        Ok(value) => Ok(value),
        Err(error) => Err(DataAxiomError::Class(error)),
    }
}
fn read_range(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceDataRange, Tokens), DataAxiomError> {
    match read_data_range(table, bytes, tokens, limits.depth, limits.count, limits.iri) {
        Ok(value) => Ok(value),
        Err(error) => Err(DataAxiomError::Range(error)),
    }
}
/// A parenthesized list of a key: `(`, the members, `)`.
fn read_key_objects(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(Vec<SourceObjectProperty>, Tokens), DataAxiomError> {
    let (_, tokens) = match take_expected(tokens, DataAxiomExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (members, tokens) = match read_objects(table, bytes, tokens, Vec::new(), limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match take_expected(tokens, DataAxiomExpected::Close, bytes.len()) {
        Ok((_, remaining)) => Ok((members, remaining)),
        Err(error) => Err(error),
    }
}
fn read_key_data(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(Vec<HeaderIri>, Tokens), DataAxiomError> {
    let (_, tokens) = match take_expected(tokens, DataAxiomExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (members, tokens) = match read_iris(table, bytes, tokens, Vec::new(), limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match take_expected(tokens, DataAxiomExpected::Close, bytes.len()) {
        Ok((_, remaining)) => Ok((members, remaining)),
        Err(error) => Err(error),
    }
}
fn read_body(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    form: AxiomForm,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceDataAxiomBody, Tokens), DataAxiomError> {
    match form {
        AxiomForm::Sub => {
            let (sub, tokens) = match read_iri(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_iri(table, bytes, tokens, limits.iri) {
                Ok((sup, remaining)) => Ok((
                    SourceDataAxiomBody::SubDataPropertyOf { sub, sup },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AxiomForm::Equivalent => match read_list(table, bytes, tokens, limits) {
            Ok((members, remaining)) => Ok((
                SourceDataAxiomBody::EquivalentDataProperties(members),
                remaining,
            )),
            Err(error) => Err(error),
        },
        AxiomForm::Disjoint => match read_list(table, bytes, tokens, limits) {
            Ok((members, remaining)) => Ok((
                SourceDataAxiomBody::DisjointDataProperties(members),
                remaining,
            )),
            Err(error) => Err(error),
        },
        AxiomForm::Domain => {
            let (property, tokens) = match read_iri(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_class(table, bytes, tokens, limits) {
                Ok((domain, remaining)) => Ok((
                    SourceDataAxiomBody::DataPropertyDomain { property, domain },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AxiomForm::Range => {
            let (property, tokens) = match read_iri(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_range(table, bytes, tokens, limits) {
                Ok((range, remaining)) => Ok((
                    SourceDataAxiomBody::DataPropertyRange { property, range },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AxiomForm::Functional => match read_iri(table, bytes, tokens, limits.iri) {
            Ok((property, remaining)) => Ok((
                SourceDataAxiomBody::FunctionalDataProperty(property),
                remaining,
            )),
            Err(error) => Err(error),
        },
        AxiomForm::Definition => {
            let (datatype, tokens) = match read_iri(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_range(table, bytes, tokens, limits) {
                Ok((range, remaining)) => Ok((
                    SourceDataAxiomBody::DatatypeDefinition { datatype, range },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AxiomForm::Key => {
            let (class, tokens) = match read_class(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (objects, tokens) = match read_key_objects(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_key_data(table, bytes, tokens, limits) {
                Ok((data, remaining)) => Ok((
                    SourceDataAxiomBody::HasKey {
                        class,
                        objects,
                        data,
                    },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
    }
}
/// Read exactly one data property axiom, datatype definition or key:
/// `SubDataPropertyOf( {Annotation} DP DP )`, `EquivalentDataProperties` and
/// `DisjointDataProperties` with at least two data properties,
/// `DataPropertyDomain( {Annotation} DP ClassExpression )`,
/// `DataPropertyRange( {Annotation} DP DataRange )`,
/// `FunctionalDataProperty( {Annotation} DP )`,
/// `DatatypeDefinition( {Annotation} Datatype DataRange )` or
/// `HasKey( {Annotation} ClassExpression ( {OPE} ) ( {DP} ) )`. Axiom
/// annotations use the proved annotation reader with `annotations`; class
/// expressions, object property expressions and data ranges use the proved
/// readers with `classes`, whose `iri` limit also bounds data properties and
/// datatypes and whose `count` bounds every property list. Errors report the
/// first failing step in source order with original offsets (EOF errors use
/// the source length): the keyword, `(`, the annotations, the body in order
/// (member lists after their two-member minimum), then `)`. The unchanged
/// suffix after the axiom is returned.
pub fn read_data_axiom(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    annotations: &AnnotationLimits,
    classes: &ClassLimits,
) -> Result<(SourceDataAxiom, Tokens), DataAxiomError> {
    let (keyword, tokens) = match take_expected(tokens, DataAxiomExpected::Axiom, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let form = match axiom_form(keyword.terminal) {
        Some(form) => form,
        None => {
            return Err(DataAxiomError::Expected {
                expected: DataAxiomExpected::Axiom,
                offset: keyword.start,
            })
        }
    };
    let (_, tokens) = match take_expected(tokens, DataAxiomExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let annotated = match read_annotations(table, bytes, tokens, annotations) {
        Ok(value) => value,
        Err(error) => return Err(DataAxiomError::Annotation(error)),
    };
    let (body, tokens) = match read_body(table, bytes, form, annotated.remaining, classes) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, DataAxiomExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((
        SourceDataAxiom {
            keyword,
            annotations: annotated.annotations,
            body,
        },
        remaining,
    ))
}
