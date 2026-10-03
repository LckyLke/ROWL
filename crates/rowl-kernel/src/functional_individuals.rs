//! Functional Syntax individuals and individual lists.
//!
//! An individual is a named individual's IRI, resolved through the checked
//! prefix table, or a node ID with its exact label. Lists read the maximal
//! individual sequence before the closing parenthesis, which is left in place,
//! and then require their minimum length. Class expressions and assertions read
//! their individuals here.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Terminal, Token};
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
pub enum IndividualError {
    /// An individual was expected at `offset`: a missing or wrong token, or a
    /// list shorter than its minimum, reported where it stops.
    Expected {
        offset: usize,
    },
    Iri(SourceIriError),
    Anonymous(NameError),
    /// A list member beyond the caller's bound, at its first token.
    CountLimit {
        offset: usize,
    },
}
enum IndividualKind {
    Named(SourceIriKind),
    Anonymous,
}
fn individual_kind(terminal: Terminal) -> Option<IndividualKind> {
    match terminal {
        Terminal::FullIri => Some(IndividualKind::Named(SourceIriKind::Full)),
        Terminal::AbbreviatedIri => Some(IndividualKind::Named(SourceIriKind::Abbreviated)),
        Terminal::NodeId => Some(IndividualKind::Anonymous),
        _ => None,
    }
}
fn closes(terminal: Terminal) -> bool {
    matches!(terminal, Terminal::Close)
}
/// The offset of the next token, or the source length at the end.
fn position(tokens: &Tokens, eof: usize) -> usize {
    match tokens {
        Tokens::Empty => eof,
        Tokens::Cons { token, .. } => token.start,
    }
}
/// Read one individual: an IRI resolved through the checked prefix table, or a
/// node ID with its exact label; both are bounded by `limit`. A missing token
/// reports the source length, any other token its start.
pub fn read_individual(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceIndividual, Tokens), IndividualError> {
    match tokens {
        Tokens::Empty => Err(IndividualError::Expected {
            offset: bytes.len(),
        }),
        Tokens::Cons { token, next } => match individual_kind(token.terminal) {
            Some(IndividualKind::Named(kind)) => {
                match resolve_span(table, kind, bytes, token.start, token.end, limit) {
                    Ok(value) => Ok((SourceIndividual::Named(HeaderIri { token, value }), *next)),
                    Err(error) => Err(IndividualError::Iri(error)),
                }
            }
            Some(IndividualKind::Anonymous) => {
                match read_span(NameKind::NodeId, bytes, token.start, token.end, limit) {
                    Ok(label) => Ok((SourceIndividual::Anonymous { token, label }, *next)),
                    Err(error) => Err(IndividualError::Anonymous(error)),
                }
            }
            None => Err(IndividualError::Expected {
                offset: token.start,
            }),
        },
    }
}
/// The maximal individual sequence after `members`, stopping before `)` or at
/// the end; before each further member the `count` bound is checked.
pub fn read_individuals(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut members: Vec<SourceIndividual>,
    count: usize,
    limit: usize,
) -> Result<(Vec<SourceIndividual>, Tokens), IndividualError> {
    match tokens {
        Tokens::Empty => Ok((members, Tokens::Empty)),
        Tokens::Cons { token, next } => {
            if closes(token.terminal) {
                return Ok((members, Tokens::Cons { token, next }));
            }
            if members.len() >= count {
                return Err(IndividualError::CountLimit {
                    offset: token.start,
                });
            }
            let (member, remaining) =
                match read_individual(table, bytes, Tokens::Cons { token, next }, limit) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
            members.push(member);
            read_individuals(table, bytes, remaining, members, count, limit)
        }
    }
}
/// Read at least `least` and at most `count` individuals in source order, up to
/// the closing parenthesis, which is left in place. A shorter list reports an
/// expected individual where it stops.
pub fn read_individual_list(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    least: usize,
    count: usize,
    limit: usize,
) -> Result<(Vec<SourceIndividual>, Tokens), IndividualError> {
    let (members, rest) = match read_individuals(table, bytes, tokens, Vec::new(), count, limit) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    if members.len() < least {
        return Err(IndividualError::Expected {
            offset: position(&rest, bytes.len()),
        });
    }
    Ok((members, rest))
}
