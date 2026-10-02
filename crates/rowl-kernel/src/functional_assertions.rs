//! Functional Syntax assertions about individuals, with their axiom annotations.
//!
//! Reads `ClassAssertion`, `ObjectPropertyAssertion` and
//! `NegativeObjectPropertyAssertion` at a caller-supplied axiom position, using
//! the proved annotation, class-expression and object-property readers. An
//! individual is a named individual's IRI, resolved through the checked prefix
//! table, or a node ID with its exact label. The other assertion forms remain
//! separate stages.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation,
};
use crate::functional_classes::{
    read_class_expression, read_object_property, ClassError, ClassLimits, SourceClass,
    SourceObjectProperty,
};
use crate::functional_header::HeaderIri;
use crate::functional_iris::{resolve_span, SourceIriError, SourceIriKind};
use crate::functional_lexer::Tokens;
use crate::functional_names::{read_span, NameError, NameKind};
use crate::prefixes::PrefixTable;

/// A named individual's IRI or an anonymous individual's node ID. Node labels
/// exclude `_:`; their scopes are assigned when the document is mapped.
pub enum SourceIndividual {
    Named(HeaderIri),
    Anonymous { token: Token, label: Vec<u8> },
}
pub enum SourceAssertionBody {
    ClassAssertion {
        class: SourceClass,
        individual: SourceIndividual,
    },
    ObjectPropertyAssertion {
        property: SourceObjectProperty,
        source: SourceIndividual,
        target: SourceIndividual,
    },
    NegativeObjectPropertyAssertion {
        property: SourceObjectProperty,
        source: SourceIndividual,
        target: SourceIndividual,
    },
}
pub struct SourceAssertion {
    pub keyword: Token,
    pub annotations: Vec<SourceAnnotation>,
    pub body: SourceAssertionBody,
}
#[derive(Clone, Copy)]
pub enum AssertionExpected {
    Axiom,
    Open,
    Individual,
    Close,
}
pub enum AssertionError {
    Expected {
        expected: AssertionExpected,
        offset: usize,
    },
    Annotation(AnnotationError),
    Class(ClassError),
    Iri(SourceIriError),
    Anonymous(NameError),
}
#[derive(Clone, Copy)]
enum AssertionForm {
    Class,
    Property,
    NegativeProperty,
}
enum IndividualKind {
    Named(SourceIriKind),
    Anonymous,
}
fn assertion_form(terminal: Terminal) -> Option<AssertionForm> {
    match terminal {
        Terminal::Keyword(Keyword::ClassAssertion) => Some(AssertionForm::Class),
        Terminal::Keyword(Keyword::ObjectPropertyAssertion) => Some(AssertionForm::Property),
        Terminal::Keyword(Keyword::NegativeObjectPropertyAssertion) => {
            Some(AssertionForm::NegativeProperty)
        }
        _ => None,
    }
}
fn individual_kind(terminal: Terminal) -> Option<IndividualKind> {
    match terminal {
        Terminal::FullIri => Some(IndividualKind::Named(SourceIriKind::Full)),
        Terminal::AbbreviatedIri => Some(IndividualKind::Named(SourceIriKind::Abbreviated)),
        Terminal::NodeId => Some(IndividualKind::Anonymous),
        _ => None,
    }
}
fn expected_terminal(expected: AssertionExpected, terminal: Terminal) -> bool {
    match expected {
        AssertionExpected::Axiom => assertion_form(terminal).is_some(),
        AssertionExpected::Open => matches!(terminal, Terminal::Open),
        AssertionExpected::Individual => individual_kind(terminal).is_some(),
        AssertionExpected::Close => matches!(terminal, Terminal::Close),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: AssertionExpected,
    eof: usize,
) -> Result<(Token, Tokens), AssertionError> {
    match tokens {
        Tokens::Empty => Err(AssertionError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(AssertionError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
fn read_class(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceClass, Tokens), AssertionError> {
    match read_class_expression(table, bytes, tokens, limits) {
        Ok(value) => Ok(value),
        Err(error) => Err(AssertionError::Class(error)),
    }
}
fn read_property(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceObjectProperty, Tokens), AssertionError> {
    match read_object_property(table, bytes, tokens, limit) {
        Ok(value) => Ok(value),
        Err(error) => Err(AssertionError::Class(error)),
    }
}
/// One individual: an IRI resolved through the checked prefix table, or a node
/// ID with its exact label; both are bounded by `limit`.
fn read_individual(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceIndividual, Tokens), AssertionError> {
    let (token, remaining) = match take_expected(tokens, AssertionExpected::Individual, bytes.len())
    {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match individual_kind(token.terminal) {
        Some(IndividualKind::Named(kind)) => {
            match resolve_span(table, kind, bytes, token.start, token.end, limit) {
                Ok(value) => Ok((
                    SourceIndividual::Named(HeaderIri { token, value }),
                    remaining,
                )),
                Err(error) => Err(AssertionError::Iri(error)),
            }
        }
        Some(IndividualKind::Anonymous) => {
            match read_span(NameKind::NodeId, bytes, token.start, token.end, limit) {
                Ok(label) => Ok((SourceIndividual::Anonymous { token, label }, remaining)),
                Err(error) => Err(AssertionError::Anonymous(error)),
            }
        }
        None => Err(AssertionError::Expected {
            expected: AssertionExpected::Individual,
            offset: token.start,
        }),
    }
}
/// An object property expression and its source and target individuals.
fn read_edge(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<
    (
        (SourceObjectProperty, SourceIndividual, SourceIndividual),
        Tokens,
    ),
    AssertionError,
> {
    let (property, tokens) = match read_property(table, bytes, tokens, limits.iri) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (source, tokens) = match read_individual(table, bytes, tokens, limits.iri) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match read_individual(table, bytes, tokens, limits.iri) {
        Ok((target, remaining)) => Ok(((property, source, target), remaining)),
        Err(error) => Err(error),
    }
}
fn read_body(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    form: AssertionForm,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceAssertionBody, Tokens), AssertionError> {
    match form {
        AssertionForm::Class => {
            let (class, tokens) = match read_class(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_individual(table, bytes, tokens, limits.iri) {
                Ok((individual, remaining)) => Ok((
                    SourceAssertionBody::ClassAssertion { class, individual },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AssertionForm::Property => match read_edge(table, bytes, tokens, limits) {
            Ok(((property, source, target), remaining)) => Ok((
                SourceAssertionBody::ObjectPropertyAssertion {
                    property,
                    source,
                    target,
                },
                remaining,
            )),
            Err(error) => Err(error),
        },
        AssertionForm::NegativeProperty => match read_edge(table, bytes, tokens, limits) {
            Ok(((property, source, target), remaining)) => Ok((
                SourceAssertionBody::NegativeObjectPropertyAssertion {
                    property,
                    source,
                    target,
                },
                remaining,
            )),
            Err(error) => Err(error),
        },
    }
}
/// Read exactly one assertion: `ClassAssertion( {Annotation} ClassExpression
/// Individual )`, `ObjectPropertyAssertion( {Annotation} ObjectPropertyExpression
/// Individual Individual )` or the negative object property assertion of the
/// same shape. Axiom annotations use the proved annotation reader with
/// `annotations`; class expressions and object properties use the proved readers
/// with `classes`, and individuals use its `iri` limit. Errors report the first
/// failing step in source order with original offsets (EOF errors use the source
/// length): the keyword, `(`, the annotations, the body in order, then `)`. The
/// unchanged suffix after the assertion is returned.
pub fn read_assertion(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    annotations: &AnnotationLimits,
    classes: &ClassLimits,
) -> Result<(SourceAssertion, Tokens), AssertionError> {
    let (keyword, tokens) = match take_expected(tokens, AssertionExpected::Axiom, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let form = match assertion_form(keyword.terminal) {
        Some(form) => form,
        None => {
            return Err(AssertionError::Expected {
                expected: AssertionExpected::Axiom,
                offset: keyword.start,
            })
        }
    };
    let (_, tokens) = match take_expected(tokens, AssertionExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let annotated = match read_annotations(table, bytes, tokens, annotations) {
        Ok(value) => value,
        Err(error) => return Err(AssertionError::Annotation(error)),
    };
    let (body, tokens) = match read_body(table, bytes, form, annotated.remaining, classes) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, AssertionExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((
        SourceAssertion {
            keyword,
            annotations: annotated.annotations,
            body,
        },
        remaining,
    ))
}
