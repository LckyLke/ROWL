//! Functional Syntax IRI values and source-derived prefix macro expansion.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional_names::{read_span, NameError, NameKind};
use crate::ntriples::copy_term;
use crate::prefixes::{expand_parts, Expansion, PrefixTable};
use crate::unicode::{decode_next, Decoded};

#[derive(Clone, Copy)]
pub enum SourceIriKind {
    Full,
    Abbreviated,
}
pub struct AbbreviatedParts {
    pub prefix: Vec<u8>,
    pub local: Vec<u8>,
}
pub enum SourceIriError {
    Name(NameError),
    InvalidParts { offset: usize },
    UndeclaredPrefix { offset: usize },
    ResourceLimit { offset: usize },
    InvalidExpandedIri { offset: usize },
}
fn colon_from(bytes: &Vec<u8>, position: usize) -> Option<usize> {
    match decode_next(bytes, position) {
        Decoded::Scalar { codepoint, next } => {
            if codepoint == 58 {
                Some(next)
            } else {
                colon_from(bytes, next)
            }
        }
        _ => None,
    }
}
/// Derive prefix/local bytes from a revalidated original abbreviated-IRI span.
/// The prefix retains its colon. No caller-supplied separator or string split is
/// trusted. The token is copied with its source-size bound; this operation does
/// not impose the final expanded-IRI output budget.
pub fn split_abbreviated(
    bytes: &Vec<u8>,
    start: usize,
    end: usize,
) -> Result<AbbreviatedParts, SourceIriError> {
    if start > end || end > bytes.len() {
        return Err(SourceIriError::Name(NameError::InvalidSpan {
            offset: start,
        }));
    }
    let token = match read_span(NameKind::AbbreviatedIri, bytes, start, end, end - start) {
        Ok(token) => token,
        Err(error) => return Err(SourceIriError::Name(error)),
    };
    let separator = match colon_from(&token, 0) {
        Some(separator) => separator,
        None => return Err(SourceIriError::InvalidParts { offset: start }),
    };
    let prefix = match copy_term(&token, 0, separator, token.len()) {
        Ok(prefix) => prefix,
        Err(_) => return Err(SourceIriError::InvalidParts { offset: start }),
    };
    let local = match copy_term(&token, separator, token.len(), token.len()) {
        Ok(local) => local,
        Err(_) => return Err(SourceIriError::InvalidParts { offset: start }),
    };
    Ok(AbbreviatedParts { prefix, local })
}
/// Resolve a full or abbreviated original IRI span to exact absolute IRI bytes.
/// Abbreviations concatenate the selected namespace and original local bytes,
/// then revalidate the resulting IRI. Limits count only the final returned IRI,
/// even when a prefix spelling is longer than the corresponding namespace.
/// Prefix declarations are supplied through the existing checked immutable table;
/// parsing their source declarations remains a separate document-parser stage.
pub fn resolve_span(
    table: &PrefixTable<'_>,
    kind: SourceIriKind,
    bytes: &Vec<u8>,
    start: usize,
    end: usize,
    limit: usize,
) -> Result<Vec<u8>, SourceIriError> {
    match kind {
        SourceIriKind::Full => match read_span(NameKind::FullIri, bytes, start, end, limit) {
            Ok(value) => Ok(value),
            Err(error) => Err(SourceIriError::Name(error)),
        },
        SourceIriKind::Abbreviated => {
            let parts = match split_abbreviated(bytes, start, end) {
                Ok(parts) => parts,
                Err(error) => return Err(error),
            };
            match expand_parts(table, &parts.prefix, &parts.local, limit) {
                Expansion::Expanded(value) => Ok(value),
                Expansion::UndeclaredPrefix => {
                    Err(SourceIriError::UndeclaredPrefix { offset: start })
                }
                Expansion::ResourceLimit => Err(SourceIriError::ResourceLimit { offset: start }),
                Expansion::InvalidExpandedIri => {
                    Err(SourceIriError::InvalidExpandedIri { offset: start })
                }
                Expansion::InvalidPrefix | Expansion::InvalidLocal => {
                    Err(SourceIriError::InvalidParts { offset: start })
                }
            }
        }
    }
}
