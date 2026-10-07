//! Functional Syntax prefix declarations and exact IRI macro expansion.
//!
//! The immutable table borrows supplied declaration records; parsing the Prefix
//! punctuation and source locations is a separate lexer/parser obligation.
//! Expanded names are concatenated verbatim and rechecked as absolute IRIs.
#![allow(clippy::ptr_arg)] // Vec indexing in the supported extraction subset.
use crate::iri::validate_iri;
use crate::names::{validate_local, validate_prefix};
use crate::regular::MatchResult;

pub struct Declaration {
    pub name: Vec<u8>,
    pub namespace: Vec<u8>,
}
pub enum Standard {
    Rdf,
    Rdfs,
    Xsd,
    Owl,
}
pub struct PrefixTable<'a> {
    declarations: &'a Vec<Declaration>,
}
pub enum Check<'a> {
    Ready(PrefixTable<'a>),
    InvalidName(&'a Declaration),
    ReservedName(&'a Declaration),
    InvalidNamespace(&'a Declaration),
    Duplicate {
        first: &'a Declaration,
        second: &'a Declaration,
    },
}
pub enum Expansion {
    Expanded(Vec<u8>),
    InvalidPrefix,
    InvalidLocal,
    UndeclaredPrefix,
    ResourceLimit,
    InvalidExpandedIri,
}
fn accepted(result: MatchResult) -> bool {
    matches!(result, MatchResult::Matched(true))
}
fn same_from(left: &[u8], right: &[u8], index: usize) -> bool {
    if index < left.len() {
        left[index] == right[index] && same_from(left, right, index + 1)
    } else {
        true
    }
}
fn same(left: &[u8], right: &[u8]) -> bool {
    left.len() == right.len() && same_from(left, right, 0)
}
fn copy_from(bytes: &[u8], index: usize, mut output: Vec<u8>) -> Vec<u8> {
    if index < bytes.len() {
        output.push(bytes[index]);
        copy_from(bytes, index + 1, output)
    } else {
        output
    }
}
pub(crate) fn copy(bytes: &[u8]) -> Vec<u8> {
    copy_from(bytes, 0, Vec::new())
}
/// These four exact lower-case prefix names are implicit. OWL 2 forbids
/// declaring them (Structural Specification, section 3.7); a declaration that
/// gives one exactly its own namespace changes no expansion and is accepted,
/// since tools built on the OWL API write one for each.
pub fn standard(name: &Vec<u8>) -> Option<Standard> {
    if same(name, b"rdf:") {
        Some(Standard::Rdf)
    } else if same(name, b"rdfs:") {
        Some(Standard::Rdfs)
    } else if same(name, b"xsd:") {
        Some(Standard::Xsd)
    } else if same(name, b"owl:") {
        Some(Standard::Owl)
    } else {
        None
    }
}
pub fn namespace(standard: Standard) -> Vec<u8> {
    match standard {
        Standard::Rdf => copy(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
        Standard::Rdfs => copy(b"http://www.w3.org/2000/01/rdf-schema#"),
        Standard::Xsd => copy(b"http://www.w3.org/2001/XMLSchema#"),
        Standard::Owl => copy(b"http://www.w3.org/2002/07/owl#"),
    }
}
/// Whether a declaration gives one of the four implicit prefix names a
/// namespace other than its own.
fn reserved(declaration: &Declaration) -> bool {
    match standard(&declaration.name) {
        Some(key) => !same(&declaration.namespace, &namespace(key)),
        None => false,
    }
}
fn find_from<'a>(
    declarations: &'a Vec<Declaration>,
    name: &Vec<u8>,
    stop: usize,
    index: usize,
) -> Option<&'a Declaration> {
    if index < stop {
        if same(&declarations[index].name, name) {
            Some(&declarations[index])
        } else {
            find_from(declarations, name, stop, index + 1)
        }
    } else {
        None
    }
}
fn check_from(declarations: &Vec<Declaration>, index: usize) -> Check<'_> {
    if index < declarations.len() {
        let declaration = &declarations[index];
        if !accepted(validate_prefix(&declaration.name)) {
            Check::InvalidName(declaration)
        } else if reserved(declaration) {
            Check::ReservedName(declaration)
        } else if !accepted(validate_iri(&declaration.namespace)) {
            Check::InvalidNamespace(declaration)
        } else {
            match find_from(declarations, &declaration.name, index, 0) {
                Some(first) => Check::Duplicate {
                    first,
                    second: declaration,
                },
                None => check_from(declarations, index + 1),
            }
        }
    } else {
        Check::Ready(PrefixTable { declarations })
    }
}
/// Check every supplied declaration, including unused ones, before expansion.
pub fn check(declarations: &Vec<Declaration>) -> Check<'_> {
    check_from(declarations, 0)
}
/// Borrow all original declaration bytes unchanged, in their original order.
pub fn declarations<'a>(table: &PrefixTable<'a>) -> &'a Vec<Declaration> {
    table.declarations
}
/// Exact owned namespace bytes for an implicit standard or declared prefix.
#[allow(clippy::manual_map)] // Explicit first-order branches match the source-linked proof.
pub fn lookup(table: &PrefixTable<'_>, name: &Vec<u8>) -> Option<Vec<u8>> {
    match standard(name) {
        Some(key) => Some(namespace(key)),
        None => match find_from(table.declarations, name, table.declarations.len(), 0) {
            Some(declaration) => Some(copy(&declaration.namespace)),
            None => None,
        },
    }
}
fn append_from(bytes: &[u8], index: usize, mut output: Vec<u8>, limit: usize) -> Option<Vec<u8>> {
    if index < bytes.len() {
        if output.len() >= limit {
            None
        } else {
            output.push(bytes[index]);
            append_from(bytes, index + 1, output, limit)
        }
    } else {
        Some(output)
    }
}
pub(crate) fn join(namespace: &Vec<u8>, local: &Vec<u8>, limit: usize) -> Option<Vec<u8>> {
    match append_from(namespace, 0, Vec::new(), limit) {
        None => None,
        Some(output) => append_from(local, 0, output, limit),
    }
}
/// Expand parsed prefix/local parts. Both byte grammars are checked here; no
/// unchecked token metadata can justify success. Output preserves exact spelling.
/// The byte limit is explicit and checked without overflowing a summed length.
pub fn expand_parts(
    table: &PrefixTable<'_>,
    prefix: &Vec<u8>,
    local: &Vec<u8>,
    limit: usize,
) -> Expansion {
    if !accepted(validate_prefix(prefix)) {
        Expansion::InvalidPrefix
    } else if !accepted(validate_local(local)) {
        Expansion::InvalidLocal
    } else {
        match lookup(table, prefix) {
            None => Expansion::UndeclaredPrefix,
            Some(namespace) => match join(&namespace, local, limit) {
                None => Expansion::ResourceLimit,
                Some(value) => {
                    if accepted(validate_iri(&value)) {
                        Expansion::Expanded(value)
                    } else {
                        Expansion::InvalidExpandedIri
                    }
                }
            },
        }
    }
}
