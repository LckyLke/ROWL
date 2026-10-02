//! Exact nonquoted Functional Syntax name payloads from original source spans.
//! The complete lexer validates bytes outside the selected span separately.
#![allow(clippy::ptr_arg)]
use crate::functional::{recognize, Terminal};
use crate::ntriples::copy_term;
use crate::regular::MatchResult;

#[derive(Clone, Copy)]
pub enum NameKind {
    FullIri,
    PrefixName,
    AbbreviatedIri,
    NodeId,
    LanguageTag,
}
pub enum NameError {
    InvalidSpan { offset: usize },
    InvalidToken { offset: usize },
    ResourceLimit { offset: usize },
}
fn terminal(kind: NameKind) -> Terminal {
    match kind {
        NameKind::FullIri => Terminal::FullIri,
        NameKind::PrefixName => Terminal::PrefixName,
        NameKind::AbbreviatedIri => Terminal::AbbreviatedIri,
        NameKind::NodeId => Terminal::NodeId,
        NameKind::LanguageTag => Terminal::LanguageTag,
    }
}
fn leading(kind: NameKind) -> usize {
    match kind {
        NameKind::FullIri | NameKind::LanguageTag => 1,
        NameKind::NodeId => 2,
        NameKind::PrefixName | NameKind::AbbreviatedIri => 0,
    }
}
fn trailing(kind: NameKind) -> usize {
    match kind {
        NameKind::FullIri => 1,
        _ => 0,
    }
}
/// Revalidate one whole original terminal span and copy its exact payload.
/// Full IRIs lose `<`/`>`; node IDs lose `_:`; language tags lose `@`.
/// Prefix/abbreviated names retain the colon and their exact source spelling.
/// No case/percent/Unicode normalization or escape decoding takes place.
/// The byte budget counts the returned payload, excluding stripped markers.
/// Invalid tokens identify the original span start; budget failures identify
/// the original payload start. No successful partial value is returned.
pub fn read_span(
    kind: NameKind,
    bytes: &Vec<u8>,
    start: usize,
    end: usize,
    limit: usize,
) -> Result<Vec<u8>, NameError> {
    if start > end || end > bytes.len() {
        return Err(NameError::InvalidSpan { offset: start });
    }
    let count = end - start;
    let head = leading(kind);
    let tail = trailing(kind);
    if count < head || count - head < tail {
        return Err(NameError::InvalidToken { offset: start });
    }
    let token = match copy_term(bytes, start, end, count) {
        Ok(token) => token,
        Err(error) => {
            return Err(NameError::ResourceLimit {
                offset: error.offset,
            });
        }
    };
    if !matches!(
        recognize(terminal(kind), &token),
        MatchResult::Matched(true)
    ) {
        return Err(NameError::InvalidToken { offset: start });
    }
    match copy_term(bytes, start + head, end - tail, limit) {
        Ok(value) => Ok(value),
        Err(error) => Err(NameError::ResourceLimit {
            offset: error.offset,
        }),
    }
}
