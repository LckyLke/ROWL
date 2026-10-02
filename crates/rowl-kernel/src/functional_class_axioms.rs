//! Functional Syntax class axioms and object property domain and range axioms,
//! with their axiom annotations.
//!
//! Reads `SubClassOf`, `EquivalentClasses`, `DisjointClasses`, `DisjointUnion`,
//! `ObjectPropertyDomain` and `ObjectPropertyRange` at a caller-supplied axiom
//! position, using the proved annotation, class-expression and object-property
//! readers. The axiom loop and the other axiom forms remain separate stages.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation,
};
use crate::functional_classes::{
    offset_of, read_class_expression, read_members, read_object_property, ClassError,
    ClassExpected, ClassLimits, SourceClass, SourceObjectProperty,
};
use crate::functional_header::{iri_kind, HeaderIri};
use crate::functional_iris::{resolve_span, SourceIriError};
use crate::functional_lexer::Tokens;
use crate::prefixes::PrefixTable;

/// The body of a class axiom. Member lists keep their occurrences, at least
/// two, in source order.
pub enum SourceClassAxiomBody {
    SubClassOf {
        sub: SourceClass,
        sup: SourceClass,
    },
    EquivalentClasses(Vec<SourceClass>),
    DisjointClasses(Vec<SourceClass>),
    DisjointUnion {
        class: HeaderIri,
        members: Vec<SourceClass>,
    },
    ObjectPropertyDomain {
        property: SourceObjectProperty,
        domain: SourceClass,
    },
    ObjectPropertyRange {
        property: SourceObjectProperty,
        range: SourceClass,
    },
}
pub struct SourceClassAxiom {
    pub keyword: Token,
    pub annotations: Vec<SourceAnnotation>,
    pub body: SourceClassAxiomBody,
}
#[derive(Clone, Copy)]
pub enum ClassAxiomExpected {
    Axiom,
    Open,
    Iri,
    Close,
}
pub enum ClassAxiomError {
    Expected {
        expected: ClassAxiomExpected,
        offset: usize,
    },
    Annotation(AnnotationError),
    Class(ClassError),
    Iri(SourceIriError),
}
#[derive(Clone, Copy)]
enum AxiomForm {
    SubClassOf,
    EquivalentClasses,
    DisjointClasses,
    DisjointUnion,
    ObjectPropertyDomain,
    ObjectPropertyRange,
}
fn axiom_form(terminal: Terminal) -> Option<AxiomForm> {
    match terminal {
        Terminal::Keyword(Keyword::SubClassOf) => Some(AxiomForm::SubClassOf),
        Terminal::Keyword(Keyword::EquivalentClasses) => Some(AxiomForm::EquivalentClasses),
        Terminal::Keyword(Keyword::DisjointClasses) => Some(AxiomForm::DisjointClasses),
        Terminal::Keyword(Keyword::DisjointUnion) => Some(AxiomForm::DisjointUnion),
        Terminal::Keyword(Keyword::ObjectPropertyDomain) => Some(AxiomForm::ObjectPropertyDomain),
        Terminal::Keyword(Keyword::ObjectPropertyRange) => Some(AxiomForm::ObjectPropertyRange),
        _ => None,
    }
}
fn expected_terminal(expected: ClassAxiomExpected, terminal: Terminal) -> bool {
    match expected {
        ClassAxiomExpected::Axiom => axiom_form(terminal).is_some(),
        ClassAxiomExpected::Open => matches!(terminal, Terminal::Open),
        ClassAxiomExpected::Iri => iri_kind(terminal).is_some(),
        ClassAxiomExpected::Close => matches!(terminal, Terminal::Close),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: ClassAxiomExpected,
    eof: usize,
) -> Result<(Token, Tokens), ClassAxiomError> {
    match tokens {
        Tokens::Empty => Err(ClassAxiomError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(ClassAxiomError::Expected {
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
) -> Result<(SourceClass, Tokens), ClassAxiomError> {
    match read_class_expression(table, bytes, tokens, limits) {
        Ok(value) => Ok(value),
        Err(error) => Err(ClassAxiomError::Class(error)),
    }
}
/// At least two class expressions, up to the next `)` or the end.
fn read_list(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(Vec<SourceClass>, Tokens), ClassAxiomError> {
    let (members, rest) = match read_members(table, bytes, tokens, Vec::new(), limits.depth, limits)
    {
        Ok(value) => value,
        Err(error) => return Err(ClassAxiomError::Class(error)),
    };
    if members.len() < 2 {
        return Err(ClassAxiomError::Class(ClassError::Expected {
            expected: ClassExpected::Class,
            offset: offset_of(&rest, bytes.len()),
        }));
    }
    Ok((members, rest))
}
/// The class IRI of a disjoint union.
fn read_named(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(HeaderIri, Tokens), ClassAxiomError> {
    let (token, rest) = match take_expected(tokens, ClassAxiomExpected::Iri, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let family = match iri_kind(token.terminal) {
        Some(family) => family,
        None => {
            return Err(ClassAxiomError::Expected {
                expected: ClassAxiomExpected::Iri,
                offset: token.start,
            })
        }
    };
    match resolve_span(table, family, bytes, token.start, token.end, limit) {
        Ok(value) => Ok((HeaderIri { token, value }, rest)),
        Err(error) => Err(ClassAxiomError::Iri(error)),
    }
}
fn read_body(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    form: AxiomForm,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceClassAxiomBody, Tokens), ClassAxiomError> {
    match form {
        AxiomForm::SubClassOf => {
            let (sub, tokens) = match read_class(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let (sup, remaining) = match read_class(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((SourceClassAxiomBody::SubClassOf { sub, sup }, remaining))
        }
        AxiomForm::EquivalentClasses => match read_list(table, bytes, tokens, limits) {
            Ok((members, remaining)) => {
                Ok((SourceClassAxiomBody::EquivalentClasses(members), remaining))
            }
            Err(error) => Err(error),
        },
        AxiomForm::DisjointClasses => match read_list(table, bytes, tokens, limits) {
            Ok((members, remaining)) => {
                Ok((SourceClassAxiomBody::DisjointClasses(members), remaining))
            }
            Err(error) => Err(error),
        },
        AxiomForm::DisjointUnion => {
            let (class, tokens) = match read_named(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_list(table, bytes, tokens, limits) {
                Ok((members, remaining)) => Ok((
                    SourceClassAxiomBody::DisjointUnion { class, members },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AxiomForm::ObjectPropertyDomain => {
            let (property, tokens) = match read_object_property(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(ClassAxiomError::Class(error)),
            };
            let (domain, remaining) = match read_class(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceClassAxiomBody::ObjectPropertyDomain { property, domain },
                remaining,
            ))
        }
        AxiomForm::ObjectPropertyRange => {
            let (property, tokens) = match read_object_property(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(ClassAxiomError::Class(error)),
            };
            let (range, remaining) = match read_class(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceClassAxiomBody::ObjectPropertyRange { property, range },
                remaining,
            ))
        }
    }
}
/// Read exactly one class axiom: `SubClassOf`, `EquivalentClasses`,
/// `DisjointClasses`, `DisjointUnion`, `ObjectPropertyDomain` or
/// `ObjectPropertyRange`, each `Keyword( {Annotation} ... )`. Axiom annotations
/// use the proved annotation reader with `annotations`; class expressions and
/// object properties use the proved readers with `classes`, starting at its full
/// nesting allowance; the disjoint union's class IRI uses the same `iri` limit.
/// Errors report the first failing step in source order with original offsets
/// (EOF errors use the source length): the keyword, `(`, the annotations, the
/// body in order (member lists after their two-member minimum), then `)`. The
/// unchanged suffix after the axiom is returned.
pub fn read_class_axiom(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    annotations: &AnnotationLimits,
    classes: &ClassLimits,
) -> Result<(SourceClassAxiom, Tokens), ClassAxiomError> {
    let (keyword, tokens) = match take_expected(tokens, ClassAxiomExpected::Axiom, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let form = match axiom_form(keyword.terminal) {
        Some(form) => form,
        None => {
            return Err(ClassAxiomError::Expected {
                expected: ClassAxiomExpected::Axiom,
                offset: keyword.start,
            })
        }
    };
    let (_, tokens) = match take_expected(tokens, ClassAxiomExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let annotated = match read_annotations(table, bytes, tokens, annotations) {
        Ok(value) => value,
        Err(error) => return Err(ClassAxiomError::Annotation(error)),
    };
    let (body, tokens) = match read_body(table, bytes, form, annotated.remaining, classes) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, ClassAxiomExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((
        SourceClassAxiom {
            keyword,
            annotations: annotated.annotations,
            body,
        },
        remaining,
    ))
}
