//! Functional Syntax annotation axioms with their axiom annotations.
//! The caller supplies the axiom position; the axiom loop, the logical axiom
//! forms and the ontology closing token remain separate stages.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_annotations::{
    read_annotations, read_value, AnnotationError, AnnotationLimits, SourceAnnotation,
    SourceAnnotationValue,
};
use crate::functional_header::{iri_kind, HeaderIri};
use crate::functional_iris::{resolve_span, SourceIriError, SourceIriKind};
use crate::functional_lexer::Tokens;
use crate::functional_names::{read_span, NameError, NameKind};
use crate::prefixes::PrefixTable;

/// The four standard annotation axioms, in the order of the structural model.
#[derive(Clone, Copy)]
pub enum AnnotationAxiomKind {
    Assertion,
    SubProperty,
    Domain,
    Range,
}
/// An annotation subject is an IRI or an anonymous individual; node labels
/// exclude `_:`, and their scopes belong to the later import assembler.
pub enum SourceAnnotationSubject {
    Iri(HeaderIri),
    Anonymous { token: Token, label: Vec<u8> },
}
pub enum SourceAnnotationAxiomBody {
    Assertion {
        property: HeaderIri,
        subject: SourceAnnotationSubject,
        value: SourceAnnotationValue,
    },
    SubProperty {
        sub_property: HeaderIri,
        super_property: HeaderIri,
    },
    Domain {
        property: HeaderIri,
        domain: HeaderIri,
    },
    Range {
        property: HeaderIri,
        range: HeaderIri,
    },
}
pub struct SourceAnnotationAxiom {
    pub keyword: Token,
    pub annotations: Vec<SourceAnnotation>,
    pub body: SourceAnnotationAxiomBody,
}
#[derive(Clone, Copy)]
pub enum AnnotationAxiomExpected {
    Keyword,
    Open,
    Property,
    Subject,
    Iri,
    Close,
}
pub enum AnnotationAxiomError {
    Expected {
        expected: AnnotationAxiomExpected,
        offset: usize,
    },
    Annotation(AnnotationError),
    Iri(SourceIriError),
    Anonymous(NameError),
    Value(AnnotationError),
}
enum AnnotationSubjectKind {
    Iri(SourceIriKind),
    Anonymous,
}
fn axiom_kind(terminal: Terminal) -> Option<AnnotationAxiomKind> {
    match terminal {
        Terminal::Keyword(Keyword::AnnotationAssertion) => Some(AnnotationAxiomKind::Assertion),
        Terminal::Keyword(Keyword::SubAnnotationPropertyOf) => {
            Some(AnnotationAxiomKind::SubProperty)
        }
        Terminal::Keyword(Keyword::AnnotationPropertyDomain) => Some(AnnotationAxiomKind::Domain),
        Terminal::Keyword(Keyword::AnnotationPropertyRange) => Some(AnnotationAxiomKind::Range),
        _ => None,
    }
}
fn subject_kind(terminal: Terminal) -> Option<AnnotationSubjectKind> {
    match terminal {
        Terminal::FullIri => Some(AnnotationSubjectKind::Iri(SourceIriKind::Full)),
        Terminal::AbbreviatedIri => Some(AnnotationSubjectKind::Iri(SourceIriKind::Abbreviated)),
        Terminal::NodeId => Some(AnnotationSubjectKind::Anonymous),
        _ => None,
    }
}
fn expected_terminal(expected: AnnotationAxiomExpected, terminal: Terminal) -> bool {
    match expected {
        AnnotationAxiomExpected::Keyword => axiom_kind(terminal).is_some(),
        AnnotationAxiomExpected::Open => matches!(terminal, Terminal::Open),
        AnnotationAxiomExpected::Property | AnnotationAxiomExpected::Iri => {
            iri_kind(terminal).is_some()
        }
        AnnotationAxiomExpected::Subject => subject_kind(terminal).is_some(),
        AnnotationAxiomExpected::Close => matches!(terminal, Terminal::Close),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: AnnotationAxiomExpected,
    eof: usize,
) -> Result<(Token, Tokens), AnnotationAxiomError> {
    match tokens {
        Tokens::Empty => Err(AnnotationAxiomError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(AnnotationAxiomError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
/// Read one full or abbreviated IRI at a property or IRI position.
fn read_iri(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    expected: AnnotationAxiomExpected,
    limit: usize,
) -> Result<(HeaderIri, Tokens), AnnotationAxiomError> {
    let (token, remaining) = match take_expected(tokens, expected, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let kind = match iri_kind(token.terminal) {
        Some(kind) => kind,
        None => {
            return Err(AnnotationAxiomError::Expected {
                expected,
                offset: token.start,
            })
        }
    };
    match resolve_span(table, kind, bytes, token.start, token.end, limit) {
        Ok(value) => Ok((HeaderIri { token, value }, remaining)),
        Err(error) => Err(AnnotationAxiomError::Iri(error)),
    }
}
fn read_subject(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceAnnotationSubject, Tokens), AnnotationAxiomError> {
    let (token, remaining) =
        match take_expected(tokens, AnnotationAxiomExpected::Subject, bytes.len()) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
    match subject_kind(token.terminal) {
        Some(AnnotationSubjectKind::Iri(kind)) => {
            match resolve_span(table, kind, bytes, token.start, token.end, limit) {
                Ok(value) => Ok((
                    SourceAnnotationSubject::Iri(HeaderIri { token, value }),
                    remaining,
                )),
                Err(error) => Err(AnnotationAxiomError::Iri(error)),
            }
        }
        Some(AnnotationSubjectKind::Anonymous) => {
            match read_span(NameKind::NodeId, bytes, token.start, token.end, limit) {
                Ok(label) => Ok((
                    SourceAnnotationSubject::Anonymous { token, label },
                    remaining,
                )),
                Err(error) => Err(AnnotationAxiomError::Anonymous(error)),
            }
        }
        None => Err(AnnotationAxiomError::Expected {
            expected: AnnotationAxiomExpected::Subject,
            offset: token.start,
        }),
    }
}
fn read_body(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    kind: AnnotationAxiomKind,
    tokens: Tokens,
    limits: &AnnotationLimits,
) -> Result<(SourceAnnotationAxiomBody, Tokens), AnnotationAxiomError> {
    let (property, tokens) = match read_iri(
        table,
        bytes,
        tokens,
        AnnotationAxiomExpected::Property,
        limits.iri,
    ) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match kind {
        AnnotationAxiomKind::Assertion => {
            let (subject, tokens) = match read_subject(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_value(table, bytes, tokens, limits) {
                Ok((value, remaining)) => Ok((
                    SourceAnnotationAxiomBody::Assertion {
                        property,
                        subject,
                        value,
                    },
                    remaining,
                )),
                Err(error) => Err(AnnotationAxiomError::Value(error)),
            }
        }
        AnnotationAxiomKind::SubProperty => {
            match read_iri(
                table,
                bytes,
                tokens,
                AnnotationAxiomExpected::Property,
                limits.iri,
            ) {
                Ok((super_property, remaining)) => Ok((
                    SourceAnnotationAxiomBody::SubProperty {
                        sub_property: property,
                        super_property,
                    },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AnnotationAxiomKind::Domain => {
            match read_iri(
                table,
                bytes,
                tokens,
                AnnotationAxiomExpected::Iri,
                limits.iri,
            ) {
                Ok((domain, remaining)) => Ok((
                    SourceAnnotationAxiomBody::Domain { property, domain },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AnnotationAxiomKind::Range => {
            match read_iri(
                table,
                bytes,
                tokens,
                AnnotationAxiomExpected::Iri,
                limits.iri,
            ) {
                Ok((range, remaining)) => Ok((
                    SourceAnnotationAxiomBody::Range { property, range },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
    }
}
/// Read exactly one annotation axiom: `AnnotationAssertion( {Annotation}
/// property subject value )`, `SubAnnotationPropertyOf( {Annotation} sub super )`,
/// `AnnotationPropertyDomain( {Annotation} property IRI )` or
/// `AnnotationPropertyRange( {Annotation} property IRI )`. Axiom annotations use
/// the proved annotation reader and its limits; every IRI resolves its original
/// span through the checked prefix table under the `iri` limit; subjects may be
/// node IDs; values use the annotation value reader. Errors report the first
/// failing step in source order with original offsets (EOF errors use the source
/// length). Original tokens and the unchanged suffix are kept.
pub fn read_annotation_axiom(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &AnnotationLimits,
) -> Result<(SourceAnnotationAxiom, Tokens), AnnotationAxiomError> {
    let (keyword, tokens) =
        match take_expected(tokens, AnnotationAxiomExpected::Keyword, bytes.len()) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
    let kind = match axiom_kind(keyword.terminal) {
        Some(kind) => kind,
        None => {
            return Err(AnnotationAxiomError::Expected {
                expected: AnnotationAxiomExpected::Keyword,
                offset: keyword.start,
            })
        }
    };
    let (_, tokens) = match take_expected(tokens, AnnotationAxiomExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let annotations = match read_annotations(table, bytes, tokens, limits) {
        Ok(value) => value,
        Err(error) => return Err(AnnotationAxiomError::Annotation(error)),
    };
    let (body, tokens) = match read_body(table, bytes, kind, annotations.remaining, limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, AnnotationAxiomExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((
        SourceAnnotationAxiom {
            keyword,
            annotations: annotations.annotations,
            body,
        },
        remaining,
    ))
}
