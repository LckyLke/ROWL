//! Functional Syntax object property axioms, with their axiom annotations.
//!
//! Reads `SubObjectPropertyOf` (whose sub-property may be an
//! `ObjectPropertyChain`), `EquivalentObjectProperties`,
//! `DisjointObjectProperties`, `InverseObjectProperties` and the seven property
//! characteristics, from `FunctionalObjectProperty` to
//! `TransitiveObjectProperty`, at a caller-supplied axiom position. Axiom
//! annotations and object property expressions use the proved readers.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation,
};
use crate::functional_classes::{
    offset_of, read_object_property, ClassError, ClassLimits, SourceObjectProperty,
};
use crate::functional_lexer::Tokens;
use crate::prefixes::PrefixTable;

/// The sub-property of `SubObjectPropertyOf`: one object property expression,
/// or a chain of at least two in source order.
pub enum SourceSubProperty {
    Single(SourceObjectProperty),
    Chain {
        keyword: Token,
        members: Vec<SourceObjectProperty>,
    },
}
/// The seven property characteristics, each stated of one property.
#[derive(Clone, Copy)]
pub enum PropertyCharacteristic {
    Functional,
    InverseFunctional,
    Reflexive,
    Irreflexive,
    Symmetric,
    Asymmetric,
    Transitive,
}
/// The body of an object property axiom. Member lists keep their occurrences, at
/// least two, in source order.
pub enum SourcePropertyAxiomBody {
    SubObjectPropertyOf {
        sub: SourceSubProperty,
        sup: SourceObjectProperty,
    },
    EquivalentObjectProperties(Vec<SourceObjectProperty>),
    DisjointObjectProperties(Vec<SourceObjectProperty>),
    InverseObjectProperties {
        first: SourceObjectProperty,
        second: SourceObjectProperty,
    },
    Characteristic {
        characteristic: PropertyCharacteristic,
        property: SourceObjectProperty,
    },
}
pub struct SourcePropertyAxiom {
    pub keyword: Token,
    pub annotations: Vec<SourceAnnotation>,
    pub body: SourcePropertyAxiomBody,
}
#[derive(Clone, Copy)]
pub enum PropertyAxiomExpected {
    Axiom,
    Open,
    Property,
    Close,
}
pub enum PropertyAxiomError {
    Expected {
        expected: PropertyAxiomExpected,
        offset: usize,
    },
    /// A member list longer than the class limits' count.
    CountLimit {
        offset: usize,
    },
    Annotation(AnnotationError),
    Class(ClassError),
}
#[derive(Clone, Copy)]
enum AxiomForm {
    SubObjectPropertyOf,
    EquivalentObjectProperties,
    DisjointObjectProperties,
    InverseObjectProperties,
    Characteristic(PropertyCharacteristic),
}
fn axiom_form(terminal: Terminal) -> Option<AxiomForm> {
    match terminal {
        Terminal::Keyword(Keyword::SubObjectPropertyOf) => Some(AxiomForm::SubObjectPropertyOf),
        Terminal::Keyword(Keyword::EquivalentObjectProperties) => {
            Some(AxiomForm::EquivalentObjectProperties)
        }
        Terminal::Keyword(Keyword::DisjointObjectProperties) => {
            Some(AxiomForm::DisjointObjectProperties)
        }
        Terminal::Keyword(Keyword::InverseObjectProperties) => {
            Some(AxiomForm::InverseObjectProperties)
        }
        Terminal::Keyword(Keyword::FunctionalObjectProperty) => Some(AxiomForm::Characteristic(
            PropertyCharacteristic::Functional,
        )),
        Terminal::Keyword(Keyword::InverseFunctionalObjectProperty) => Some(
            AxiomForm::Characteristic(PropertyCharacteristic::InverseFunctional),
        ),
        Terminal::Keyword(Keyword::ReflexiveObjectProperty) => {
            Some(AxiomForm::Characteristic(PropertyCharacteristic::Reflexive))
        }
        Terminal::Keyword(Keyword::IrreflexiveObjectProperty) => Some(AxiomForm::Characteristic(
            PropertyCharacteristic::Irreflexive,
        )),
        Terminal::Keyword(Keyword::SymmetricObjectProperty) => {
            Some(AxiomForm::Characteristic(PropertyCharacteristic::Symmetric))
        }
        Terminal::Keyword(Keyword::AsymmetricObjectProperty) => Some(AxiomForm::Characteristic(
            PropertyCharacteristic::Asymmetric,
        )),
        Terminal::Keyword(Keyword::TransitiveObjectProperty) => Some(AxiomForm::Characteristic(
            PropertyCharacteristic::Transitive,
        )),
        _ => None,
    }
}
fn closes(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Close)
}
fn starts_chain(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Keyword(Keyword::ObjectPropertyChain))
}
fn expected_terminal(expected: PropertyAxiomExpected, terminal: Terminal) -> bool {
    match expected {
        PropertyAxiomExpected::Axiom => axiom_form(terminal).is_some(),
        PropertyAxiomExpected::Open => matches!(terminal, Terminal::Open),
        PropertyAxiomExpected::Property => false,
        PropertyAxiomExpected::Close => closes(terminal),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: PropertyAxiomExpected,
    eof: usize,
) -> Result<(Token, Tokens), PropertyAxiomError> {
    match tokens {
        Tokens::Empty => Err(PropertyAxiomError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(PropertyAxiomError::Expected {
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
) -> Result<(SourceObjectProperty, Tokens), PropertyAxiomError> {
    match read_object_property(table, bytes, tokens, limit) {
        Ok(value) => Ok(value),
        Err(error) => Err(PropertyAxiomError::Class(error)),
    }
}
/// Object property expressions up to the next `)` or the end, after `members`;
/// a list may hold at most the class limits' count.
fn read_properties(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut members: Vec<SourceObjectProperty>,
    limits: &ClassLimits,
) -> Result<(Vec<SourceObjectProperty>, Tokens), PropertyAxiomError> {
    match tokens {
        Tokens::Empty => Ok((members, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((members, Tokens::Cons { token, next }));
            }
            if members.len() >= limits.count {
                return Err(PropertyAxiomError::CountLimit {
                    offset: token.start,
                });
            }
            let (member, remaining) =
                match read_property(table, bytes, Tokens::Cons { token, next }, limits.iri) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
            members.push(member);
            read_properties(table, bytes, remaining, members, limits)
        }
    }
}
/// At least two object property expressions, up to the next `)` or the end.
fn read_list(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(Vec<SourceObjectProperty>, Tokens), PropertyAxiomError> {
    let (members, rest) = match read_properties(table, bytes, tokens, Vec::new(), limits) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if members.len() < 2 {
        return Err(PropertyAxiomError::Expected {
            expected: PropertyAxiomExpected::Property,
            offset: offset_of(&rest, bytes.len()),
        });
    }
    Ok((members, rest))
}
fn single(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceSubProperty, Tokens), PropertyAxiomError> {
    match read_property(table, bytes, tokens, limit) {
        Ok((property, rest)) => Ok((SourceSubProperty::Single(property), rest)),
        Err(error) => Err(error),
    }
}
/// The sub-property of `SubObjectPropertyOf`: `ObjectPropertyChain( P1 P2 ... )`
/// or one object property expression.
fn read_sub(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourceSubProperty, Tokens), PropertyAxiomError> {
    match tokens {
        Tokens::Empty => single(table, bytes, Tokens::Empty, limits.iri),
        Tokens::Cons { token, next } => {
            if starts_chain(token.terminal) {
                let (_, inner) =
                    match take_expected(*next, PropertyAxiomExpected::Open, bytes.len()) {
                        Ok(value) => value,
                        Err(error) => return Err(error),
                    };
                let (members, rest) = match read_list(table, bytes, inner, limits) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                let (_, remaining) =
                    match take_expected(rest, PropertyAxiomExpected::Close, bytes.len()) {
                        Ok(value) => value,
                        Err(error) => return Err(error),
                    };
                Ok((
                    SourceSubProperty::Chain {
                        keyword: token,
                        members,
                    },
                    remaining,
                ))
            } else {
                single(table, bytes, Tokens::Cons { token, next }, limits.iri)
            }
        }
    }
}
fn read_body(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    form: AxiomForm,
    tokens: Tokens,
    limits: &ClassLimits,
) -> Result<(SourcePropertyAxiomBody, Tokens), PropertyAxiomError> {
    match form {
        AxiomForm::SubObjectPropertyOf => {
            let (sub, tokens) = match read_sub(table, bytes, tokens, limits) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_property(table, bytes, tokens, limits.iri) {
                Ok((sup, remaining)) => Ok((
                    SourcePropertyAxiomBody::SubObjectPropertyOf { sub, sup },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AxiomForm::EquivalentObjectProperties => match read_list(table, bytes, tokens, limits) {
            Ok((members, remaining)) => Ok((
                SourcePropertyAxiomBody::EquivalentObjectProperties(members),
                remaining,
            )),
            Err(error) => Err(error),
        },
        AxiomForm::DisjointObjectProperties => match read_list(table, bytes, tokens, limits) {
            Ok((members, remaining)) => Ok((
                SourcePropertyAxiomBody::DisjointObjectProperties(members),
                remaining,
            )),
            Err(error) => Err(error),
        },
        AxiomForm::InverseObjectProperties => {
            let (first, tokens) = match read_property(table, bytes, tokens, limits.iri) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            match read_property(table, bytes, tokens, limits.iri) {
                Ok((second, remaining)) => Ok((
                    SourcePropertyAxiomBody::InverseObjectProperties { first, second },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
        AxiomForm::Characteristic(characteristic) => {
            match read_property(table, bytes, tokens, limits.iri) {
                Ok((property, remaining)) => Ok((
                    SourcePropertyAxiomBody::Characteristic {
                        characteristic,
                        property,
                    },
                    remaining,
                )),
                Err(error) => Err(error),
            }
        }
    }
}
/// Read exactly one object property axiom: `SubObjectPropertyOf( {Annotation}
/// SubObjectPropertyExpression ObjectPropertyExpression )`, where the
/// sub-property is an object property expression or `ObjectPropertyChain( ... )`;
/// `EquivalentObjectProperties` and `DisjointObjectProperties` with at least two
/// object property expressions; `InverseObjectProperties` with two; or one of
/// the seven characteristics with one. Axiom annotations use the proved
/// annotation reader with `annotations`; object property expressions use the
/// proved reader with the `iri` limit of `classes`, and member lists its
/// `count`. Errors report the first failing step in source order with original
/// offsets (EOF errors use the source length): the keyword, `(`, the
/// annotations, the body in order (member lists after their two-member minimum),
/// then `)`. The unchanged suffix after the axiom is returned.
pub fn read_property_axiom(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    annotations: &AnnotationLimits,
    classes: &ClassLimits,
) -> Result<(SourcePropertyAxiom, Tokens), PropertyAxiomError> {
    let (keyword, tokens) = match take_expected(tokens, PropertyAxiomExpected::Axiom, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let form = match axiom_form(keyword.terminal) {
        Some(form) => form,
        None => {
            return Err(PropertyAxiomError::Expected {
                expected: PropertyAxiomExpected::Axiom,
                offset: keyword.start,
            })
        }
    };
    let (_, tokens) = match take_expected(tokens, PropertyAxiomExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let annotated = match read_annotations(table, bytes, tokens, annotations) {
        Ok(value) => value,
        Err(error) => return Err(PropertyAxiomError::Annotation(error)),
    };
    let (body, tokens) = match read_body(table, bytes, form, annotated.remaining, classes) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, PropertyAxiomExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((
        SourcePropertyAxiom {
            keyword,
            annotations: annotated.annotations,
            body,
        },
        remaining,
    ))
}
