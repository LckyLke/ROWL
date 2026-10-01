//! Functional Syntax entity declarations with their axiom annotations.
//! The caller supplies the axiom position; the axiom loop, the other axiom
//! forms and the ontology closing token remain separate stages.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation,
};
use crate::functional_header::{iri_kind, HeaderIri};
use crate::functional_iris::{resolve_span, SourceIriError};
use crate::functional_lexer::Tokens;
use crate::prefixes::PrefixTable;

/// The six standard entity kinds, in the order of the structural model.
#[derive(Clone, Copy)]
pub enum SourceEntityKind {
    Class,
    Datatype,
    ObjectProperty,
    DataProperty,
    AnnotationProperty,
    NamedIndividual,
}
pub struct SourceEntity {
    pub kind: SourceEntityKind,
    pub keyword: Token,
    pub iri: HeaderIri,
}
pub struct SourceDeclaration {
    pub keyword: Token,
    pub annotations: Vec<SourceAnnotation>,
    pub entity: SourceEntity,
}
#[derive(Clone, Copy)]
pub enum DeclarationExpected {
    Declaration,
    Open,
    Entity,
    Iri,
    Close,
}
pub enum DeclarationError {
    Expected {
        expected: DeclarationExpected,
        offset: usize,
    },
    Annotation(AnnotationError),
    Iri(SourceIriError),
}
fn entity_kind(terminal: Terminal) -> Option<SourceEntityKind> {
    match terminal {
        Terminal::Keyword(Keyword::Class) => Some(SourceEntityKind::Class),
        Terminal::Keyword(Keyword::Datatype) => Some(SourceEntityKind::Datatype),
        Terminal::Keyword(Keyword::ObjectProperty) => Some(SourceEntityKind::ObjectProperty),
        Terminal::Keyword(Keyword::DataProperty) => Some(SourceEntityKind::DataProperty),
        Terminal::Keyword(Keyword::AnnotationProperty) => {
            Some(SourceEntityKind::AnnotationProperty)
        }
        Terminal::Keyword(Keyword::NamedIndividual) => Some(SourceEntityKind::NamedIndividual),
        _ => None,
    }
}
fn expected_terminal(expected: DeclarationExpected, terminal: Terminal) -> bool {
    match expected {
        DeclarationExpected::Declaration => {
            matches!(terminal, Terminal::Keyword(Keyword::Declaration))
        }
        DeclarationExpected::Open => matches!(terminal, Terminal::Open),
        DeclarationExpected::Entity => entity_kind(terminal).is_some(),
        DeclarationExpected::Iri => iri_kind(terminal).is_some(),
        DeclarationExpected::Close => matches!(terminal, Terminal::Close),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: DeclarationExpected,
    eof: usize,
) -> Result<(Token, Tokens), DeclarationError> {
    match tokens {
        Tokens::Empty => Err(DeclarationError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(DeclarationError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
fn read_entity(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceEntity, Tokens), DeclarationError> {
    let (keyword, tokens) = match take_expected(tokens, DeclarationExpected::Entity, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let kind = match entity_kind(keyword.terminal) {
        Some(kind) => kind,
        None => {
            return Err(DeclarationError::Expected {
                expected: DeclarationExpected::Entity,
                offset: keyword.start,
            })
        }
    };
    let (_, tokens) = match take_expected(tokens, DeclarationExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (token, tokens) = match take_expected(tokens, DeclarationExpected::Iri, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let family = match iri_kind(token.terminal) {
        Some(family) => family,
        None => {
            return Err(DeclarationError::Expected {
                expected: DeclarationExpected::Iri,
                offset: token.start,
            })
        }
    };
    let value = match resolve_span(table, family, bytes, token.start, token.end, limit) {
        Ok(value) => value,
        Err(error) => return Err(DeclarationError::Iri(error)),
    };
    let (_, remaining) = match take_expected(tokens, DeclarationExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((
        SourceEntity {
            kind,
            keyword,
            iri: HeaderIri { token, value },
        },
        remaining,
    ))
}
/// Read exactly one `Declaration( {Annotation} Entity )` axiom, where an entity
/// is `Class(IRI)`, `Datatype(IRI)`, `ObjectProperty(IRI)`, `DataProperty(IRI)`,
/// `AnnotationProperty(IRI)` or `NamedIndividual(IRI)`. Axiom annotations use
/// the proved annotation reader and its limits; the entity IRI resolves through
/// the checked prefix table with the same `iri` limit. Errors report the first
/// failing step in source order with original offsets (EOF errors use the source
/// length). Original keyword and IRI tokens and the unchanged suffix are kept.
/// Declaration typing, punning and DL validity are separate checks.
pub fn read_declaration(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limits: &AnnotationLimits,
) -> Result<(SourceDeclaration, Tokens), DeclarationError> {
    let (keyword, tokens) =
        match take_expected(tokens, DeclarationExpected::Declaration, bytes.len()) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
    let (_, tokens) = match take_expected(tokens, DeclarationExpected::Open, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let annotations = match read_annotations(table, bytes, tokens, limits) {
        Ok(value) => value,
        Err(error) => return Err(DeclarationError::Annotation(error)),
    };
    let (entity, tokens) = match read_entity(table, bytes, annotations.remaining, limits.iri) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, DeclarationExpected::Close, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok((
        SourceDeclaration {
            keyword,
            annotations: annotations.annotations,
            entity,
        },
        remaining,
    ))
}
