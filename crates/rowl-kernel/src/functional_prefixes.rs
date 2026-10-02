//! Source-derived Functional Syntax prefix declarations and ontology opening.
//! The whole source is lexed first. Ontology contents remain unparsed, and the
//! raw declaration records must pass `prefixes::check` before being used as a table.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_lexer::{lex, LexResult, Tokens};
use crate::functional_names::{read_span, NameError, NameKind};
use crate::prefixes::Declaration;
use crate::unicode::TextError;

#[derive(Clone, Copy)]
pub enum PrefixExpected {
    Ontology,
    Open,
    Name,
    Equals,
    Namespace,
    Close,
}
pub enum PrefixSyntaxError {
    Expected {
        expected: PrefixExpected,
        offset: usize,
    },
    Name(NameError),
    DeclarationLimit {
        offset: usize,
    },
}
pub enum PrefixReadError {
    Syntax(PrefixSyntaxError),
    InvalidText(TextError),
    NoToken { offset: usize },
    MissingSeparator { offset: usize },
    TokenLimit { offset: usize },
    InvalidSpan { offset: usize },
}
pub struct PrefixHeader {
    pub declarations: Vec<Declaration>,
    pub ontology: Token,
    pub opening: Token,
    pub remaining: Tokens,
}
fn expected_terminal(expected: PrefixExpected, terminal: Terminal) -> bool {
    matches!(
        (expected, terminal),
        (
            PrefixExpected::Ontology,
            Terminal::Keyword(Keyword::Ontology)
        ) | (PrefixExpected::Open, Terminal::Open)
            | (PrefixExpected::Name, Terminal::PrefixName)
            | (PrefixExpected::Equals, Terminal::Equals)
            | (PrefixExpected::Namespace, Terminal::FullIri)
            | (PrefixExpected::Close, Terminal::Close)
    )
}
fn take_expected(
    tokens: Tokens,
    expected: PrefixExpected,
    eof: usize,
) -> Result<(Token, Tokens), PrefixSyntaxError> {
    match tokens {
        Tokens::Empty => Err(PrefixSyntaxError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(PrefixSyntaxError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
struct DeclarationShape {
    name: Token,
    namespace: Token,
    remaining: Tokens,
}
fn read_shape(tokens: Tokens, eof: usize) -> Result<DeclarationShape, PrefixSyntaxError> {
    let (_, tokens) = match take_expected(tokens, PrefixExpected::Open, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (name_token, tokens) = match take_expected(tokens, PrefixExpected::Name, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, tokens) = match take_expected(tokens, PrefixExpected::Equals, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (namespace_token, tokens) = match take_expected(tokens, PrefixExpected::Namespace, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, tokens) = match take_expected(tokens, PrefixExpected::Close, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(DeclarationShape {
        name: name_token,
        namespace: namespace_token,
        remaining: tokens,
    })
}
fn read_declaration(
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(Declaration, Tokens), PrefixSyntaxError> {
    let shape = match read_shape(tokens, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let name = match read_span(
        NameKind::PrefixName,
        bytes,
        shape.name.start,
        shape.name.end,
        limit,
    ) {
        Ok(value) => value,
        Err(error) => return Err(PrefixSyntaxError::Name(error)),
    };
    let namespace = match read_span(
        NameKind::FullIri,
        bytes,
        shape.namespace.start,
        shape.namespace.end,
        limit,
    ) {
        Ok(value) => value,
        Err(error) => return Err(PrefixSyntaxError::Name(error)),
    };
    Ok((Declaration { name, namespace }, shape.remaining))
}
fn scan_prefixes(
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut declarations: Vec<Declaration>,
    count_limit: usize,
    value_limit: usize,
) -> Result<PrefixHeader, PrefixSyntaxError> {
    match tokens {
        Tokens::Empty => Err(PrefixSyntaxError::Expected {
            expected: PrefixExpected::Ontology,
            offset: bytes.len(),
        }),
        Tokens::Cons { token, next } => match token.terminal {
            Terminal::Keyword(Keyword::Prefix) => {
                if declarations.len() >= count_limit {
                    return Err(PrefixSyntaxError::DeclarationLimit {
                        offset: token.start,
                    });
                }
                let (declaration, tokens) = match read_declaration(bytes, *next, value_limit) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                declarations.push(declaration);
                scan_prefixes(bytes, tokens, declarations, count_limit, value_limit)
            }
            Terminal::Keyword(Keyword::Ontology) => {
                let (opening, remaining) =
                    match take_expected(*next, PrefixExpected::Open, bytes.len()) {
                        Ok(value) => value,
                        Err(error) => return Err(error),
                    };
                Ok(PrefixHeader {
                    declarations,
                    ontology: token,
                    opening,
                    remaining,
                })
            }
            _ => Err(PrefixSyntaxError::Expected {
                expected: PrefixExpected::Ontology,
                offset: token.start,
            }),
        },
    }
}
/// Read all leading Prefix declarations and the exact Ontology opening from
/// original bytes. A later lexical error rejects the entire source before syntax
/// reading. Remaining tokens are returned intact for the full document parser.
/// All rows, including duplicate/reserved declarations, retain original order and
/// spelling; `prefixes::check` enforces the normative table rules separately.
/// Syntax precedes payload limits within a declaration. Count limits are checked
/// at each Prefix keyword before its body; each name/namespace has a byte limit.
pub fn read_prefix_header(
    bytes: &Vec<u8>,
    token_limit: usize,
    declaration_limit: usize,
    value_limit: usize,
) -> Result<PrefixHeader, PrefixReadError> {
    let tokens = match lex(bytes, token_limit) {
        LexResult::Tokens(tokens) => tokens,
        LexResult::InvalidText(error) => return Err(PrefixReadError::InvalidText(error)),
        LexResult::NoToken { offset } => return Err(PrefixReadError::NoToken { offset }),
        LexResult::MissingSeparator { offset } => {
            return Err(PrefixReadError::MissingSeparator { offset })
        }
        LexResult::TokenLimit { offset } => return Err(PrefixReadError::TokenLimit { offset }),
        LexResult::InvalidSpan { offset } => return Err(PrefixReadError::InvalidSpan { offset }),
    };
    match scan_prefixes(bytes, tokens, Vec::new(), declaration_limit, value_limit) {
        Ok(header) => Ok(header),
        Err(error) => Err(PrefixReadError::Syntax(error)),
    }
}
