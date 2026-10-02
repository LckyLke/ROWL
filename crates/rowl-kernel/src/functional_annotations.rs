//! Functional Syntax annotations, including recursively nested annotations.
//! Feed the untouched suffix from `read_header_tail` to read ontology
//! annotations. Axioms, the closing token and anonymous scopes remain pending.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_header::{iri_kind, HeaderIri};
use crate::functional_iris::{resolve_span, SourceIriError, SourceIriKind};
use crate::functional_lexer::Tokens;
use crate::functional_literals::{read_literal, SourceLiteral, SourceLiteralError};
use crate::functional_names::{read_span, NameError, NameKind};
use crate::prefixes::PrefixTable;

/// The three standard annotation-value families. Anonymous labels exclude
/// the `_:` marker; scope assignment belongs to the later import assembler.
pub enum SourceAnnotationValue {
    Iri(HeaderIri),
    Anonymous { token: Token, label: Vec<u8> },
    Literal(SourceLiteral),
}
pub struct SourceAnnotation {
    pub keyword: Token,
    pub annotations: Vec<SourceAnnotation>,
    pub property: HeaderIri,
    pub value: SourceAnnotationValue,
}
pub struct SourceAnnotations {
    pub annotations: Vec<SourceAnnotation>,
    pub remaining: Tokens,
}
/// `depth` bounds annotation nesting: 0 permits no annotation, 1 permits only
/// unannotated annotations. `count` bounds each sequence, nested or not. `iri`
/// bounds every final IRI, node label and literal datatype; `lexical` bounds
/// final literal lexical forms.
pub struct AnnotationLimits {
    pub depth: usize,
    pub count: usize,
    pub iri: usize,
    pub lexical: usize,
}
#[derive(Clone, Copy)]
pub enum AnnotationExpected {
    Open,
    Property,
    Value,
    Close,
}
pub enum AnnotationError {
    Expected {
        expected: AnnotationExpected,
        offset: usize,
    },
    Property(SourceIriError),
    Iri(SourceIriError),
    Anonymous(NameError),
    Literal(SourceLiteralError),
    DepthLimit {
        offset: usize,
    },
    CountLimit {
        offset: usize,
    },
}
enum AnnotationValueKind {
    Iri(SourceIriKind),
    Anonymous,
    Literal,
}
fn value_kind(terminal: Terminal) -> Option<AnnotationValueKind> {
    match terminal {
        Terminal::FullIri => Some(AnnotationValueKind::Iri(SourceIriKind::Full)),
        Terminal::AbbreviatedIri => Some(AnnotationValueKind::Iri(SourceIriKind::Abbreviated)),
        Terminal::NodeId => Some(AnnotationValueKind::Anonymous),
        Terminal::QuotedString => Some(AnnotationValueKind::Literal),
        _ => None,
    }
}
fn expected_terminal(expected: AnnotationExpected, terminal: Terminal) -> bool {
    match expected {
        AnnotationExpected::Open => matches!(terminal, Terminal::Open),
        AnnotationExpected::Property => iri_kind(terminal).is_some(),
        AnnotationExpected::Value => value_kind(terminal).is_some(),
        AnnotationExpected::Close => matches!(terminal, Terminal::Close),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: AnnotationExpected,
    eof: usize,
) -> Result<(Token, Tokens), AnnotationError> {
    match tokens {
        Tokens::Empty => Err(AnnotationError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(AnnotationError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
fn read_property(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(HeaderIri, Tokens), AnnotationError> {
    let (token, remaining) = match take_expected(tokens, AnnotationExpected::Property, bytes.len())
    {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let kind = match iri_kind(token.terminal) {
        Some(kind) => kind,
        None => {
            return Err(AnnotationError::Expected {
                expected: AnnotationExpected::Property,
                offset: token.start,
            })
        }
    };
    match resolve_span(table, kind, bytes, token.start, token.end, limit) {
        Ok(value) => Ok((HeaderIri { token, value }, remaining)),
        Err(error) => Err(AnnotationError::Property(error)),
    }
}
pub(crate) fn read_value(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &AnnotationLimits,
) -> Result<(SourceAnnotationValue, Tokens), AnnotationError> {
    let (token, next) = match take_expected(tokens, AnnotationExpected::Value, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match value_kind(token.terminal) {
        Some(AnnotationValueKind::Iri(kind)) => {
            match resolve_span(table, kind, bytes, token.start, token.end, limits.iri) {
                Ok(value) => Ok((SourceAnnotationValue::Iri(HeaderIri { token, value }), next)),
                Err(error) => Err(AnnotationError::Iri(error)),
            }
        }
        Some(AnnotationValueKind::Anonymous) => {
            match read_span(NameKind::NodeId, bytes, token.start, token.end, limits.iri) {
                Ok(label) => Ok((SourceAnnotationValue::Anonymous { token, label }, next)),
                Err(error) => Err(AnnotationError::Anonymous(error)),
            }
        }
        Some(AnnotationValueKind::Literal) => {
            let tokens = Tokens::Cons {
                token,
                next: Box::new(next),
            };
            match read_literal(table, bytes, tokens, limits.lexical, limits.iri) {
                Ok((literal, remaining)) => {
                    Ok((SourceAnnotationValue::Literal(literal), remaining))
                }
                Err(error) => Err(AnnotationError::Literal(error)),
            }
        }
        None => Err(AnnotationError::Expected {
            expected: AnnotationExpected::Value,
            offset: token.start,
        }),
    }
}
struct AnnotationTail {
    property: HeaderIri,
    value: SourceAnnotationValue,
    remaining: Tokens,
}
fn finish_annotation(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &AnnotationLimits,
) -> Result<AnnotationTail, AnnotationError> {
    let (property, tokens) = match read_property(table, bytes, tokens, limits.iri) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (value, tokens) = match read_value(table, bytes, tokens, limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, AnnotationExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(AnnotationTail {
        property,
        value,
        remaining,
    })
}
fn scan_annotations(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut annotations: Vec<SourceAnnotation>,
    depth: usize,
    limits: &AnnotationLimits,
) -> Result<SourceAnnotations, AnnotationError> {
    let (keyword, next) = match tokens {
        Tokens::Empty => {
            return Ok(SourceAnnotations {
                annotations,
                remaining: Tokens::Empty,
            })
        }
        Tokens::Cons { token, next } => match token.terminal {
            Terminal::Keyword(Keyword::Annotation) => (token, next),
            _ => {
                return Ok(SourceAnnotations {
                    annotations,
                    remaining: Tokens::Cons { token, next },
                })
            }
        },
    };
    if depth == 0 {
        return Err(AnnotationError::DepthLimit {
            offset: keyword.start,
        });
    }
    if annotations.len() >= limits.count {
        return Err(AnnotationError::CountLimit {
            offset: keyword.start,
        });
    }
    let (_, tokens) = match take_expected(*next, AnnotationExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let nested = match scan_annotations(table, bytes, tokens, Vec::new(), depth - 1, limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let tail = match finish_annotation(table, bytes, nested.remaining, limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    annotations.push(SourceAnnotation {
        keyword,
        annotations: nested.annotations,
        property: tail.property,
        value: tail.value,
    });
    scan_annotations(table, bytes, tail.remaining, annotations, depth, limits)
}
/// Read the maximal leading `{ Annotation }` sequence, including each nested
/// `Annotation( {Annotation} property value )`, in source order. Properties and
/// IRI values resolve their original spans through the checked prefix table;
/// node IDs retain their exact label; literals use the proved literal reader.
/// Errors report the first failing stage in source order: nesting depth, the
/// sequence count, `(`, nested annotations, property, value, then `)`. The
/// first non-`Annotation` token and its suffix remain unchanged. This partial
/// stage reads no axioms and assigns no anonymous-individual scopes.
pub fn read_annotations(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &AnnotationLimits,
) -> Result<SourceAnnotations, AnnotationError> {
    scan_annotations(table, bytes, tokens, Vec::new(), limits.depth, limits)
}
