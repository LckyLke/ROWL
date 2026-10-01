//! Exact OWL 2 Functional Syntax literals and required plain-literal expansion.
//! Datatype lexical/value spaces and complete document parsing remain separate.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Terminal, Token};
use crate::functional_header::iri_kind;
use crate::functional_iris::{resolve_span, SourceIriError};
use crate::functional_lexer::Tokens;
use crate::functional_names::{read_span, NameError, NameKind};
use crate::functional_payload::read_quoted;
use crate::ntriples::ReadError;
use crate::prefixes::{copy, join, PrefixTable};

pub enum SourceLiteralForm {
    Plain,
    Language(Token),
    Typed { indicator: Token, datatype: Token },
}
pub struct SourceLiteral {
    pub quoted: Token,
    pub form: SourceLiteralForm,
    pub lexical: Vec<u8>,
    pub datatype: Vec<u8>,
}
#[derive(Clone, Copy)]
pub enum LiteralExpected {
    Quoted,
    Datatype,
}
pub enum SourceLiteralError {
    Expected {
        expected: LiteralExpected,
        offset: usize,
    },
    InvalidSpan {
        offset: usize,
    },
    Quoted(ReadError),
    Language(NameError),
    Datatype(SourceIriError),
    LexicalLimit {
        offset: usize,
    },
    DatatypeLimit {
        offset: usize,
    },
}
struct LiteralShape {
    quoted: Token,
    form: SourceLiteralForm,
    remaining: Tokens,
}
fn read_shape(tokens: Tokens, eof: usize) -> Result<LiteralShape, SourceLiteralError> {
    let (quoted, remaining) = match tokens {
        Tokens::Empty => {
            return Err(SourceLiteralError::Expected {
                expected: LiteralExpected::Quoted,
                offset: eof,
            })
        }
        Tokens::Cons { token, next } => {
            if !matches!(token.terminal, Terminal::QuotedString) {
                return Err(SourceLiteralError::Expected {
                    expected: LiteralExpected::Quoted,
                    offset: token.start,
                });
            }
            (token, *next)
        }
    };
    match remaining {
        Tokens::Empty => Ok(LiteralShape {
            quoted,
            form: SourceLiteralForm::Plain,
            remaining: Tokens::Empty,
        }),
        Tokens::Cons { token, next } => match token.terminal {
            Terminal::DatatypeIndicator => match *next {
                Tokens::Empty => Err(SourceLiteralError::Expected {
                    expected: LiteralExpected::Datatype,
                    offset: eof,
                }),
                Tokens::Cons {
                    token: datatype,
                    next: remaining,
                } => {
                    if iri_kind(datatype.terminal).is_some() {
                        Ok(LiteralShape {
                            quoted,
                            form: SourceLiteralForm::Typed {
                                indicator: token,
                                datatype,
                            },
                            remaining: *remaining,
                        })
                    } else {
                        Err(SourceLiteralError::Expected {
                            expected: LiteralExpected::Datatype,
                            offset: datatype.start,
                        })
                    }
                }
            },
            Terminal::LanguageTag => Ok(LiteralShape {
                quoted,
                form: SourceLiteralForm::Language(token),
                remaining: *next,
            }),
            _ => Ok(LiteralShape {
                quoted,
                form: SourceLiteralForm::Plain,
                remaining: Tokens::Cons { token, next },
            }),
        },
    }
}
fn string_span(
    bytes: &Vec<u8>,
    token: &Token,
    limit: usize,
) -> Result<Vec<u8>, SourceLiteralError> {
    if token.start > token.end || token.end > bytes.len() {
        return Err(SourceLiteralError::InvalidSpan {
            offset: token.start,
        });
    }
    let (value, end) = match read_quoted(bytes, token.start, limit) {
        Ok(value) => value,
        Err(error) => return Err(SourceLiteralError::Quoted(error)),
    };
    if end == token.end {
        Ok(value)
    } else {
        Err(SourceLiteralError::InvalidSpan {
            offset: token.start,
        })
    }
}
fn plain_lexical(payload: &Vec<u8>, language: &Vec<u8>, limit: usize) -> Option<Vec<u8>> {
    let separator = copy(b"@");
    match join(payload, &separator, limit) {
        Some(value) => join(&value, language, limit),
        None => None,
    }
}
fn plain_datatype(limit: usize, offset: usize) -> Result<Vec<u8>, SourceLiteralError> {
    let value = copy(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral");
    if value.len() > limit {
        Err(SourceLiteralError::DatatypeLimit { offset })
    } else {
        Ok(value)
    }
}
/// Read exactly one literal and preserve the original source tokens and suffix.
/// All written syntax is checked before payload decoding. Typed literals retain
/// their decoded lexical spelling and resolve their original datatype IRI.
/// Plain/string-language shortcuts expand to rdf:PlainLiteral with lexical
/// payload + '@' + unchanged language spelling (empty for an untagged string).
/// Limits count the final structural lexical/datatype fields, including the
/// added '@'. Datatype lexical/value validity remains a separate M5 obligation.
pub fn read_literal(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    lexical_limit: usize,
    datatype_limit: usize,
) -> Result<(SourceLiteral, Tokens), SourceLiteralError> {
    let shape = match read_shape(tokens, bytes.len()) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let payload = match string_span(bytes, &shape.quoted, lexical_limit) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match shape.form {
        SourceLiteralForm::Typed {
            indicator,
            datatype,
        } => {
            let kind = match iri_kind(datatype.terminal) {
                Some(kind) => kind,
                None => {
                    return Err(SourceLiteralError::Expected {
                        expected: LiteralExpected::Datatype,
                        offset: datatype.start,
                    })
                }
            };
            let value = match resolve_span(
                table,
                kind,
                bytes,
                datatype.start,
                datatype.end,
                datatype_limit,
            ) {
                Ok(value) => value,
                Err(error) => return Err(SourceLiteralError::Datatype(error)),
            };
            Ok((
                SourceLiteral {
                    quoted: shape.quoted,
                    form: SourceLiteralForm::Typed {
                        indicator,
                        datatype,
                    },
                    lexical: payload,
                    datatype: value,
                },
                shape.remaining,
            ))
        }
        SourceLiteralForm::Plain => {
            let lexical = match plain_lexical(&payload, &Vec::new(), lexical_limit) {
                Some(value) => value,
                None => {
                    return Err(SourceLiteralError::LexicalLimit {
                        offset: shape.quoted.start,
                    })
                }
            };
            let datatype = match plain_datatype(datatype_limit, shape.quoted.start) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceLiteral {
                    quoted: shape.quoted,
                    form: SourceLiteralForm::Plain,
                    lexical,
                    datatype,
                },
                shape.remaining,
            ))
        }
        SourceLiteralForm::Language(token) => {
            let language = match read_span(
                NameKind::LanguageTag,
                bytes,
                token.start,
                token.end,
                lexical_limit,
            ) {
                Ok(value) => value,
                Err(error) => return Err(SourceLiteralError::Language(error)),
            };
            let lexical = match plain_lexical(&payload, &language, lexical_limit) {
                Some(value) => value,
                None => {
                    return Err(SourceLiteralError::LexicalLimit {
                        offset: shape.quoted.start,
                    })
                }
            };
            let datatype = match plain_datatype(datatype_limit, shape.quoted.start) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((
                SourceLiteral {
                    quoted: shape.quoted,
                    form: SourceLiteralForm::Language(token),
                    lexical,
                    datatype,
                },
                shape.remaining,
            ))
        }
    }
}
