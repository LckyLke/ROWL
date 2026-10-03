//! Functional Syntax assertions about individuals, with their axiom annotations.
//!
//! Reads `SameIndividual`, `DifferentIndividuals`, `ClassAssertion`,
//! `ObjectPropertyAssertion` and `NegativeObjectPropertyAssertion` at a
//! caller-supplied axiom position, using the proved annotation,
//! class-expression, object-property and individual readers. The data property
//! assertions remain a separate stage.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation,
};
use crate::functional_classes::{
    read_class_expression, read_object_property, ClassError, ClassLimits, SourceClass,
    SourceObjectProperty,
};
use crate::functional_individuals::{
    read_individual, read_individual_list, IndividualError, SourceIndividual,
};
use crate::functional_lexer::Tokens;
use crate::prefixes::PrefixTable;

/// An assertion body. Individual equalities and inequalities keep their
/// individuals, at least two, in source order.
pub enum SourceAssertionBody {
    SameIndividual(Vec<SourceIndividual>),
    DifferentIndividuals(Vec<SourceIndividual>),
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
    Close,
}
pub enum AssertionError {
    Expected {
        expected: AssertionExpected,
        offset: usize,
    },
    Annotation(AnnotationError),
    Class(ClassError),
    Individual(IndividualError),
}
#[derive(Clone, Copy)]
enum AssertionForm {
    Same,
    Different,
    Class,
    Property,
    NegativeProperty,
}
fn assertion_form(terminal: Terminal) -> Option<AssertionForm> {
    match terminal {
        Terminal::Keyword(Keyword::SameIndividual) => Some(AssertionForm::Same),
        Terminal::Keyword(Keyword::DifferentIndividuals) => Some(AssertionForm::Different),
        Terminal::Keyword(Keyword::ClassAssertion) => Some(AssertionForm::Class),
        Terminal::Keyword(Keyword::ObjectPropertyAssertion) => Some(AssertionForm::Property),
        Terminal::Keyword(Keyword::NegativeObjectPropertyAssertion) => {
            Some(AssertionForm::NegativeProperty)
        }
        _ => None,
    }
}
fn expected_terminal(expected: AssertionExpected, terminal: Terminal) -> bool {
    match expected {
        AssertionExpected::Axiom => assertion_form(terminal).is_some(),
        AssertionExpected::Open => matches!(terminal, Terminal::Open),
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
/// One individual, bounded by `limit`, with its errors wrapped.
fn read_member(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceIndividual, Tokens), AssertionError> {
    match read_individual(table, bytes, tokens, limit) {
        Ok(value) => Ok(value),
        Err(error) => Err(AssertionError::Individual(error)),
    }
}
/// At least two and at most `count` individuals before `)`, with their errors
/// wrapped.
fn read_members(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(Vec<SourceIndividual>, Tokens), AssertionError> {
    match read_individual_list(table, bytes, tokens, 2, limits.count, limits.iri) {
        Ok(value) => Ok(value),
        Err(error) => Err(AssertionError::Individual(error)),
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
    let (source, tokens) = match read_member(table, bytes, tokens, limits.iri) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match read_member(table, bytes, tokens, limits.iri) {
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
        AssertionForm::Same => match read_members(table, bytes, tokens, limits) {
            Ok((members, remaining)) => {
                Ok((SourceAssertionBody::SameIndividual(members), remaining))
            }
            Err(error) => Err(error),
        },
        AssertionForm::Different => match read_members(table, bytes, tokens, limits) {
            Ok((members, remaining)) => Ok((
                SourceAssertionBody::DifferentIndividuals(members),
                remaining,
            )),
            Err(error) => Err(error),
        },
        AssertionForm::Class => {
            let (class, tokens) = match read_class(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_member(table, bytes, tokens, limits.iri) {
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
/// Read exactly one assertion: `SameIndividual( {Annotation} Individual
/// Individual {Individual} )`, `DifferentIndividuals` of the same shape,
/// `ClassAssertion( {Annotation} ClassExpression Individual )`,
/// `ObjectPropertyAssertion( {Annotation} ObjectPropertyExpression Individual
/// Individual )` or the negative object property assertion of the same shape.
/// Axiom annotations use the proved annotation reader with `annotations`; class
/// expressions and object properties use the proved readers with `classes`,
/// individuals its `iri` limit and individual lists its `count` limit. Errors
/// report the first failing step in source order with original offsets (EOF
/// errors use the source length): the keyword, `(`, the annotations, the body in
/// order (an individual list before its two-member minimum), then `)`. The
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
