//! Canonical serialization of raw RDF graphs, shared by the N-Triples and
//! Turtle writers.
//!
//! A writer first looks for the first term its syntax cannot carry and reports
//! it; only a graph with none is written, within a byte budget. Every triple is
//! one line `subject predicate object .` followed by a line feed. IRIs are
//! IRIREFs whose characters stay raw unless an IRIREF cannot hold them raw, in
//! which case they become `\U` escapes; string characters stay raw except `"`,
//! `\`, line feed and carriage return, which become ECHARs; every literal
//! carries its datatype or language tag; a blank node is `_:b` followed by the
//! hexadecimal digits of the bytes of its scope, `_` and those of its label,
//! which encodes the pair injectively.
#![allow(
    clippy::ptr_arg,
    clippy::manual_range_contains,
    clippy::if_same_then_else
)]

use crate::iri::validate_iri;
use crate::langtag::well_formed;
use crate::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfIri, RdfLiteral, Subject, Triple};
use crate::references::resolve;
use crate::regular::MatchResult;
use crate::unicode::{decode_next, Decoded};

/// Why a writer cannot write a graph.
pub enum WriteError {
    /// An IRI is not an absolute RFC 3987 IRI.
    InvalidIri,
    /// The lexical form of a literal is not UTF-8.
    MalformedLiteralUtf8,
    /// A language tag is not a well-formed BCP 47 tag of the LANGTAG form.
    InvalidLanguageTag,
    /// A literal has the datatype rdf:langString without a language tag.
    InvalidLiteralKind,
    /// The IRI is one that RFC 3986 resolution, which a Turtle reader applies
    /// to every IRIREF, would change: its path has dot segments.
    IriChangedByResolution,
    /// The output would exceed the byte budget.
    ResourceLimit,
}

/// The bytes written, or why they could not be.
pub enum WriteResult {
    Bytes(Vec<u8>),
    Error(WriteError),
}

/// `output` and `byte`, within `limit` bytes.
fn put(mut output: Vec<u8>, byte: u8, limit: usize) -> Result<Vec<u8>, WriteError> {
    if output.len() < limit {
        output.push(byte);
        Ok(output)
    } else {
        Err(WriteError::ResourceLimit)
    }
}

/// `output` and `bytes[index..]`.
fn put_from(
    output: Vec<u8>,
    bytes: &[u8],
    index: usize,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    if index < bytes.len() {
        let output = put(output, bytes[index], limit)?;
        put_from(output, bytes, index + 1, limit)
    } else {
        Ok(output)
    }
}

/// `output` and `bytes[index..end]`.
fn put_span(
    output: Vec<u8>,
    bytes: &Vec<u8>,
    index: usize,
    end: usize,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    if index < end {
        let output = put(output, bytes[index], limit)?;
        put_span(output, bytes, index + 1, end, limit)
    } else {
        Ok(output)
    }
}

/// The lowercase hexadecimal digit of `n`, which is below 16.
fn hex_lower(n: u8) -> u8 {
    if n < 10 {
        48 + n
    } else {
        87 + n
    }
}

/// `output` and the two hexadecimal digits of each byte of `key[index..]`.
fn put_key(
    output: Vec<u8>,
    key: &Vec<u8>,
    index: usize,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    if index < key.len() {
        let output = put(output, hex_lower(key[index] / 16), limit)?;
        let output = put(output, hex_lower(key[index] % 16), limit)?;
        put_key(output, key, index + 1, limit)
    } else {
        Ok(output)
    }
}

/// `output` and the blank node label of `node`.
fn put_blank(output: Vec<u8>, node: &BlankNode, limit: usize) -> Result<Vec<u8>, WriteError> {
    let output = put_from(output, b"_:b", 0, limit)?;
    let output = put_key(output, &node.scope, 0, limit)?;
    let output = put(output, 95, limit)?;
    put_key(output, &node.label, 0, limit)
}

/// The uppercase hexadecimal digit of `n`, which is below 16.
fn hex_upper(n: u32) -> u8 {
    let digit = if n < 10 { 48 + n } else { 55 + n };
    digit as u8
}

/// `output` and the last `count` hexadecimal digits of `value`, the most
/// significant first.
fn put_hex(output: Vec<u8>, value: u32, count: u32, limit: usize) -> Result<Vec<u8>, WriteError> {
    if count == 0 {
        Ok(output)
    } else {
        let output = put_hex(output, value / 16, count - 1, limit)?;
        put(output, hex_upper(value % 16), limit)
    }
}

/// `output` and the UCHAR `\U` with the eight hexadecimal digits of `cp`.
fn put_uchar(output: Vec<u8>, cp: u32, limit: usize) -> Result<Vec<u8>, WriteError> {
    let output = put(output, 92, limit)?;
    let output = put(output, 85, limit)?;
    put_hex(output, cp, 8, limit)
}

/// A character that an IRIREF may hold raw.
fn iri_raw(cp: u32) -> bool {
    cp > 32
        && cp != 60
        && cp != 62
        && cp != 34
        && cp != 123
        && cp != 125
        && cp != 124
        && cp != 94
        && cp != 96
        && cp != 92
}

/// `output` and the character `cp` of `spelling[index..next]` in an IRIREF.
fn put_iri_character(
    output: Vec<u8>,
    spelling: &Vec<u8>,
    index: usize,
    next: usize,
    cp: u32,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    if iri_raw(cp) {
        put_span(output, spelling, index, next, limit)
    } else {
        put_uchar(output, cp, limit)
    }
}

/// `output` and the IRIREF characters of `spelling[index..]`.
fn put_iri_from(
    output: Vec<u8>,
    spelling: &Vec<u8>,
    index: usize,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    match decode_next(spelling, index) {
        Decoded::Scalar { codepoint, next } => {
            let output = put_iri_character(output, spelling, index, next, codepoint, limit)?;
            put_iri_from(output, spelling, next, limit)
        }
        Decoded::End => Ok(output),
        Decoded::Error(_) => Err(WriteError::InvalidIri),
    }
}

/// `output` and the IRIREF of `iri`.
fn put_iri(output: Vec<u8>, iri: &RdfIri, limit: usize) -> Result<Vec<u8>, WriteError> {
    let output = put(output, 60, limit)?;
    let output = put_iri_from(output, &iri.spelling, 0, limit)?;
    put(output, 62, limit)
}

/// The ECHAR letter of a character that a string must escape, or 0.
fn string_escape(cp: u32) -> u8 {
    if cp == 34 {
        34
    } else if cp == 92 {
        92
    } else if cp == 10 {
        110
    } else if cp == 13 {
        114
    } else {
        0
    }
}

/// `output` and the character `cp` of `lexical[index..next]` in a string.
fn put_string_character(
    output: Vec<u8>,
    lexical: &Vec<u8>,
    index: usize,
    next: usize,
    cp: u32,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    let marker = string_escape(cp);
    if marker == 0 {
        put_span(output, lexical, index, next, limit)
    } else {
        let output = put(output, 92, limit)?;
        put(output, marker, limit)
    }
}

/// `output` and the string characters of `lexical[index..]`.
fn put_string_from(
    output: Vec<u8>,
    lexical: &Vec<u8>,
    index: usize,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    match decode_next(lexical, index) {
        Decoded::Scalar { codepoint, next } => {
            let output = put_string_character(output, lexical, index, next, codepoint, limit)?;
            put_string_from(output, lexical, next, limit)
        }
        Decoded::End => Ok(output),
        Decoded::Error(_) => Err(WriteError::MalformedLiteralUtf8),
    }
}

/// `output` and `literal` with its datatype or language tag.
fn put_literal(output: Vec<u8>, literal: &RdfLiteral, limit: usize) -> Result<Vec<u8>, WriteError> {
    let output = put(output, 34, limit)?;
    let output = put_string_from(output, &literal.lexical, 0, limit)?;
    let output = put(output, 34, limit)?;
    match &literal.kind {
        LiteralKind::Datatype(iri) => {
            let output = put_from(output, b"^^", 0, limit)?;
            put_iri(output, iri, limit)
        }
        LiteralKind::Language(tag) => {
            let output = put(output, 64, limit)?;
            put_span(output, tag, 0, tag.len(), limit)
        }
    }
}

fn put_subject(output: Vec<u8>, subject: &Subject, limit: usize) -> Result<Vec<u8>, WriteError> {
    match subject {
        Subject::Iri(iri) => put_iri(output, iri, limit),
        Subject::Blank(node) => put_blank(output, node, limit),
    }
}

fn put_object(output: Vec<u8>, object: &Object, limit: usize) -> Result<Vec<u8>, WriteError> {
    match object {
        Object::Iri(iri) => put_iri(output, iri, limit),
        Object::Blank(node) => put_blank(output, node, limit),
        Object::Literal(literal) => put_literal(output, literal, limit),
    }
}

/// `output` and `subject predicate object` of `triple`.
fn put_triple(output: Vec<u8>, triple: &Triple, limit: usize) -> Result<Vec<u8>, WriteError> {
    let output = put_subject(output, &triple.subject, limit)?;
    let output = put(output, 32, limit)?;
    let output = put_iri(output, &triple.predicate, limit)?;
    let output = put(output, 32, limit)?;
    put_object(output, &triple.object, limit)
}

/// `output` and the lines of `triples[index..]`.
fn put_lines(
    output: Vec<u8>,
    triples: &Vec<Triple>,
    index: usize,
    limit: usize,
) -> Result<Vec<u8>, WriteError> {
    if index < triples.len() {
        let output = put_triple(output, &triples[index], limit)?;
        let output = put_from(output, b" .\n", 0, limit)?;
        put_lines(output, triples, index + 1, limit)
    } else {
        Ok(output)
    }
}

/// Whether `bytes[index..]` is UTF-8.
fn utf8_from(bytes: &Vec<u8>, index: usize) -> bool {
    match decode_next(bytes, index) {
        Decoded::Scalar { next, .. } => utf8_from(bytes, next),
        Decoded::End => true,
        Decoded::Error(_) => false,
    }
}

/// Whether `a[index..]` and `b[index..]` are equal, for `a` and `b` of the
/// same length.
fn equal_from(a: &Vec<u8>, b: &[u8], index: usize) -> bool {
    if index < a.len() {
        if a[index] == b[index] {
            equal_from(a, b, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether `a` and `b` are the same bytes.
fn equal(a: &Vec<u8>, b: &[u8]) -> bool {
    if a.len() == b.len() {
        equal_from(a, b, 0)
    } else {
        false
    }
}

/// Whether `spelling` is an absolute RFC 3987 IRI.
fn absolute(spelling: &Vec<u8>) -> bool {
    matches!(validate_iri(spelling), MatchResult::Matched(true))
}

/// Whether RFC 3986 resolution leaves the IRI `spelling` as it is.
fn resolution_keeps(spelling: &Vec<u8>) -> bool {
    match resolve(&Vec::new(), spelling) {
        Some(target) => equal(&target, spelling),
        None => false,
    }
}

/// The fault of `iri`; `resolved` for a syntax that resolves its IRIREFs.
fn iri_fault(iri: &RdfIri, resolved: bool) -> Option<WriteError> {
    if !absolute(&iri.spelling) {
        Some(WriteError::InvalidIri)
    } else if !resolved {
        None
    } else if resolution_keeps(&iri.spelling) {
        None
    } else {
        Some(WriteError::IriChangedByResolution)
    }
}

fn ascii_letter(byte: u8) -> bool {
    (65 <= byte && byte <= 90) || (97 <= byte && byte <= 122)
}

fn ascii_alphanumeric(byte: u8) -> bool {
    ascii_letter(byte) || (48 <= byte && byte <= 57)
}

/// A letter, or with `letters` false also a digit.
fn tag_class(byte: u8, letters: bool) -> bool {
    if letters {
        ascii_letter(byte)
    } else {
        ascii_alphanumeric(byte)
    }
}

/// Whether `bytes[index]` exists and is of the class.
fn tag_byte_at(bytes: &Vec<u8>, index: usize, letters: bool) -> bool {
    index < bytes.len() && tag_class(bytes[index], letters)
}

/// The end of the bytes of the class from `index`.
fn word_end(bytes: &Vec<u8>, index: usize, letters: bool) -> usize {
    if tag_byte_at(bytes, index, letters) {
        word_end(bytes, index + 1, letters)
    } else {
        index
    }
}

/// Whether `bytes[index..]` is a sequence of `-` and letters or digits.
fn subtags_from(bytes: &Vec<u8>, index: usize) -> bool {
    if bytes.len() <= index {
        true
    } else if bytes[index] != 45 {
        false
    } else {
        let end = word_end(bytes, index + 1, false);
        if end == index + 1 {
            false
        } else {
            subtags_from(bytes, end)
        }
    }
}

/// Whether `tag` has the LANGTAG form: letters, then subtags of `-` and
/// letters or digits.
fn tag_form(tag: &Vec<u8>) -> bool {
    let head = word_end(tag, 0, true);
    if head == 0 {
        false
    } else {
        subtags_from(tag, head)
    }
}

/// The fault of a language tag.
fn tag_fault(tag: &Vec<u8>) -> Option<WriteError> {
    if !tag_form(tag) {
        Some(WriteError::InvalidLanguageTag)
    } else if well_formed(tag) {
        None
    } else {
        Some(WriteError::InvalidLanguageTag)
    }
}

/// The fault of a datatype IRI.
fn datatype_fault(iri: &RdfIri, resolved: bool) -> Option<WriteError> {
    if equal(
        &iri.spelling,
        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString",
    ) {
        Some(WriteError::InvalidLiteralKind)
    } else {
        iri_fault(iri, resolved)
    }
}

/// The fault of a literal: its lexical form, then its datatype or tag.
fn literal_fault(literal: &RdfLiteral, resolved: bool) -> Option<WriteError> {
    if !utf8_from(&literal.lexical, 0) {
        Some(WriteError::MalformedLiteralUtf8)
    } else {
        match &literal.kind {
            LiteralKind::Datatype(iri) => datatype_fault(iri, resolved),
            LiteralKind::Language(tag) => tag_fault(tag),
        }
    }
}

fn subject_fault(subject: &Subject, resolved: bool) -> Option<WriteError> {
    match subject {
        Subject::Iri(iri) => iri_fault(iri, resolved),
        Subject::Blank(_) => None,
    }
}

fn object_fault(object: &Object, resolved: bool) -> Option<WriteError> {
    match object {
        Object::Iri(iri) => iri_fault(iri, resolved),
        Object::Blank(_) => None,
        Object::Literal(literal) => literal_fault(literal, resolved),
    }
}

/// The first fault of `triple`: its subject, predicate, then object.
fn triple_fault(triple: &Triple, resolved: bool) -> Option<WriteError> {
    match subject_fault(&triple.subject, resolved) {
        Some(error) => Some(error),
        None => match iri_fault(&triple.predicate, resolved) {
            Some(error) => Some(error),
            None => object_fault(&triple.object, resolved),
        },
    }
}

/// The first fault of `triples[index..]`.
fn graph_fault(triples: &Vec<Triple>, index: usize, resolved: bool) -> Option<WriteError> {
    if index < triples.len() {
        match triple_fault(&triples[index], resolved) {
            Some(error) => Some(error),
            None => graph_fault(triples, index + 1, resolved),
        }
    } else {
        None
    }
}

/// Write `graph` in lines of triples within `limit` bytes, or report its first
/// fault; `resolved` for a syntax that resolves its IRIREFs.
pub(crate) fn write_graph(graph: &RawGraph, resolved: bool, limit: usize) -> WriteResult {
    match graph_fault(&graph.triples, 0, resolved) {
        Some(error) => WriteResult::Error(error),
        None => match put_lines(Vec::new(), &graph.triples, 0, limit) {
            Ok(bytes) => WriteResult::Bytes(bytes),
            Err(error) => WriteResult::Error(error),
        },
    }
}
