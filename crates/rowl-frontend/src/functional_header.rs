//! Functional Syntax ontology identity and leading import references.
//! Feed the untouched suffix from `read_prefix_header` and its checked table.
//! Annotations, axioms and the ontology closing token remain unparsed.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional::{Keyword, Terminal, Token};
use crate::functional_iris::{resolve_span, SourceIriError, SourceIriKind};
use crate::functional_lexer::Tokens;
use crate::prefixes::PrefixTable;

pub struct HeaderIri {
    pub token: Token,
    pub value: Vec<u8>,
}
pub enum SourceOntologyIdentity {
    Anonymous,
    Named {
        ontology: HeaderIri,
        version: Option<HeaderIri>,
    },
}
pub struct ImportReference {
    pub keyword: Token,
    pub target: HeaderIri,
}
pub struct HeaderTail {
    pub identity: SourceOntologyIdentity,
    pub imports: Vec<ImportReference>,
    pub remaining: Tokens,
}
#[derive(Clone, Copy)]
pub enum HeaderExpected {
    Open,
    Iri,
    Close,
}
pub enum HeaderError {
    Expected {
        expected: HeaderExpected,
        offset: usize,
    },
    Iri(SourceIriError),
    ImportLimit {
        offset: usize,
    },
}
pub(crate) fn iri_kind(terminal: Terminal) -> Option<SourceIriKind> {
    match terminal {
        Terminal::FullIri => Some(SourceIriKind::Full),
        Terminal::AbbreviatedIri => Some(SourceIriKind::Abbreviated),
        _ => None,
    }
}
fn read_optional_iri(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(Option<HeaderIri>, Tokens), HeaderError> {
    match tokens {
        Tokens::Empty => Ok((None, Tokens::Empty)),
        Tokens::Cons { token, next } => match iri_kind(token.terminal) {
            None => Ok((None, Tokens::Cons { token, next })),
            Some(kind) => match resolve_span(table, kind, bytes, token.start, token.end, limit) {
                Ok(value) => Ok((Some(HeaderIri { token, value }), *next)),
                Err(error) => Err(HeaderError::Iri(error)),
            },
        },
    }
}
fn read_identity(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(SourceOntologyIdentity, Tokens), HeaderError> {
    let (ontology, tokens) = match read_optional_iri(table, bytes, tokens, limit) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    match ontology {
        None => Ok((SourceOntologyIdentity::Anonymous, tokens)),
        Some(ontology) => {
            let (version, tokens) = match read_optional_iri(table, bytes, tokens, limit) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            Ok((SourceOntologyIdentity::Named { ontology, version }, tokens))
        }
    }
}
fn expected_terminal(expected: HeaderExpected, terminal: Terminal) -> bool {
    match expected {
        HeaderExpected::Open => matches!(terminal, Terminal::Open),
        HeaderExpected::Iri => matches!(terminal, Terminal::FullIri | Terminal::AbbreviatedIri),
        HeaderExpected::Close => matches!(terminal, Terminal::Close),
    }
}
fn take_expected(
    tokens: Tokens,
    expected: HeaderExpected,
    eof: usize,
) -> Result<(Token, Tokens), HeaderError> {
    match tokens {
        Tokens::Empty => Err(HeaderError::Expected {
            expected,
            offset: eof,
        }),
        Tokens::Cons { token, next } => {
            if expected_terminal(expected, token.terminal) {
                Ok((token, *next))
            } else {
                Err(HeaderError::Expected {
                    expected,
                    offset: token.start,
                })
            }
        }
    }
}
struct ImportShape {
    target: Token,
    remaining: Tokens,
}
fn read_import_shape(tokens: Tokens, eof: usize) -> Result<ImportShape, HeaderError> {
    let (_, tokens) = match take_expected(tokens, HeaderExpected::Open, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (target, tokens) = match take_expected(tokens, HeaderExpected::Iri, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let (_, remaining) = match take_expected(tokens, HeaderExpected::Close, eof) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(ImportShape { target, remaining })
}
fn read_import(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    limit: usize,
) -> Result<(HeaderIri, Tokens), HeaderError> {
    let shape = match read_import_shape(tokens, bytes.len()) {
        Ok(shape) => shape,
        Err(error) => return Err(error),
    };
    let kind = match iri_kind(shape.target.terminal) {
        Some(kind) => kind,
        None => {
            return Err(HeaderError::Expected {
                expected: HeaderExpected::Iri,
                offset: shape.target.start,
            })
        }
    };
    let value = match resolve_span(
        table,
        kind,
        bytes,
        shape.target.start,
        shape.target.end,
        limit,
    ) {
        Ok(value) => value,
        Err(error) => return Err(HeaderError::Iri(error)),
    };
    Ok((
        HeaderIri {
            token: shape.target,
            value,
        },
        shape.remaining,
    ))
}
struct HeaderImports {
    references: Vec<ImportReference>,
    remaining: Tokens,
}
fn scan_imports(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    mut references: Vec<ImportReference>,
    count_limit: usize,
    value_limit: usize,
) -> Result<HeaderImports, HeaderError> {
    match tokens {
        Tokens::Cons { token, next } => match token.terminal {
            Terminal::Keyword(Keyword::Import) => {
                if references.len() >= count_limit {
                    return Err(HeaderError::ImportLimit {
                        offset: token.start,
                    });
                }
                let (target, remaining) = match read_import(table, bytes, *next, value_limit) {
                    Ok(value) => value,
                    Err(error) => return Err(error),
                };
                references.push(ImportReference {
                    keyword: token,
                    target,
                });
                scan_imports(
                    table,
                    bytes,
                    remaining,
                    references,
                    count_limit,
                    value_limit,
                )
            }
            _ => Ok(HeaderImports {
                references,
                remaining: Tokens::Cons { token, next },
            }),
        },
        Tokens::Empty => Ok(HeaderImports {
            references,
            remaining: Tokens::Empty,
        }),
    }
}
/// Read `[ontologyIRI [versionIRI]]` and every leading `Import(IRI)` after the
/// ontology opening. All IRI values are resolved from their original spans; the
/// caller supplies the checked prefix table derived by `read_prefix_header`.
/// Import rows retain order, repetitions and original keyword/IRI tokens.
/// Count limits precede each import body; complete body syntax precedes its IRI
/// resolution. Annotations, axioms, closing syntax and any unexpected trailing
/// token are left unchanged for full document parsing. This partial stage alone
/// cannot establish a complete ontology or a complete canonical import closure.
pub fn read_header_tail(
    table: &PrefixTable<'_>,
    bytes: &Vec<u8>,
    tokens: Tokens,
    import_limit: usize,
    iri_limit: usize,
) -> Result<HeaderTail, HeaderError> {
    let (identity, tokens) = match read_identity(table, bytes, tokens, iri_limit) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    let imports = match scan_imports(table, bytes, tokens, Vec::new(), import_limit, iri_limit) {
        Ok(value) => value,
        Err(error) => return Err(error),
    };
    Ok(HeaderTail {
        identity,
        imports: imports.references,
        remaining: imports.remaining,
    })
}
