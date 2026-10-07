//! Experimental complete N-Triples read/export implementation.
//!
//! The byte-to-graph and serializer composition proofs remain in progress. The
//! complete quoted/IRI/blank/language tokens and subject construction are proved.
//! Literal kinds, full-document construction and export laws need composition.
//! No OWL structural mapping or ontology reasoning is performed here.
#![allow(clippy::ptr_arg, clippy::manual_range_contains)]

use crate::encoding::{encode, Encoded};
use crate::iri::validate_iri;
use crate::langtag::well_formed;
use crate::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfIri, RdfLiteral, Subject, Triple};
use crate::regular::MatchResult;
use crate::unicode::{decode_next, Decoded};

pub enum ErrorKind {
    MalformedUtf8,
    UnexpectedEnd,
    ExpectedIri,
    ExpectedSubject,
    ExpectedObject,
    ExpectedPeriod,
    ExpectedLineEnd,
    InvalidCharacter,
    InvalidEscape,
    InvalidIri,
    InvalidBlankLabel,
    InvalidLanguageTag,
    InvalidLiteralKind,
    ResourceLimit,
}
pub struct ReadError {
    pub kind: ErrorKind,
    pub offset: usize,
}
pub enum ReadResult {
    Graph(RawGraph),
    Error(ReadError),
}
pub struct Limits {
    pub max_term_bytes: usize,
    pub max_triples: usize,
}

type Step<T> = Result<(T, usize), ReadError>;
fn error(kind: ErrorKind, offset: usize) -> ReadError {
    ReadError { kind, offset }
}
pub(crate) fn at(bytes: &Vec<u8>, position: usize) -> Result<Option<(u32, usize)>, ReadError> {
    match decode_next(bytes, position) {
        Decoded::End => Ok(None),
        Decoded::Scalar { codepoint, next } => Ok(Some((codepoint, next))),
        Decoded::Error(_) => Err(error(ErrorKind::MalformedUtf8, position)),
    }
}
pub(crate) fn required(bytes: &Vec<u8>, position: usize) -> Result<(u32, usize), ReadError> {
    match at(bytes, position)? {
        Some(unit) => Ok(unit),
        None => Err(error(ErrorKind::UnexpectedEnd, position)),
    }
}
pub(crate) fn expect(
    bytes: &Vec<u8>,
    position: usize,
    wanted: u32,
    kind: ErrorKind,
) -> Result<usize, ReadError> {
    let (cp, next) = required(bytes, position)?;
    if cp == wanted {
        Ok(next)
    } else {
        Err(error(kind, position))
    }
}
fn push(bytes: &mut Vec<u8>, byte: u8, limit: usize) -> bool {
    if bytes.len() >= limit {
        false
    } else {
        bytes.push(byte);
        true
    }
}
pub(crate) fn append_encoded(output: &mut Vec<u8>, value: Encoded, limit: usize) -> bool {
    match value {
        Encoded::One(a) => push(output, a, limit),
        Encoded::Two(a, b) => push(output, a, limit) && push(output, b, limit),
        Encoded::Three(a, b, c) => {
            push(output, a, limit) && push(output, b, limit) && push(output, c, limit)
        }
        Encoded::Four(a, b, c, d) => {
            push(output, a, limit)
                && push(output, b, limit)
                && push(output, c, limit)
                && push(output, d, limit)
        }
    }
}
fn copy(values: &[u8]) -> Vec<u8> {
    let mut output = Vec::new();
    let mut i = 0;
    while i < values.len() {
        output.push(values[i]);
        i += 1;
    }
    output
}
fn copy_vec(values: &Vec<u8>) -> Vec<u8> {
    let mut output = Vec::new();
    let mut i = 0;
    while i < values.len() {
        output.push(values[i]);
        i += 1;
    }
    output
}
fn horizontal(cp: u32) -> bool {
    cp == 9 || cp == 32
}
fn eol(cp: u32) -> bool {
    cp == 10 || cp == 13
}
fn skip_comment(bytes: &Vec<u8>, position: usize) -> Result<usize, ReadError> {
    match at(bytes, position)? {
        Some((cp, next)) if !eol(cp) => skip_comment(bytes, next),
        _ => Ok(position),
    }
}
pub(crate) fn skip(bytes: &Vec<u8>, position: usize, lines: bool) -> Result<usize, ReadError> {
    match at(bytes, position)? {
        Some((cp, next)) => {
            if horizontal(cp) || (lines && eol(cp)) {
                skip(bytes, next, lines)
            } else if cp == 35 {
                let end = skip_comment(bytes, next)?;
                if lines {
                    skip(bytes, end, lines)
                } else {
                    Ok(end)
                }
            } else {
                Ok(position)
            }
        }
        None => Ok(position),
    }
}
pub(crate) fn hex(cp: u32) -> Option<u32> {
    if (cp >= 48) && (cp <= 57) {
        Some(cp - 48)
    } else if (cp >= 65) && (cp <= 70) {
        Some(cp - 55)
    } else if (cp >= 97) && (cp <= 102) {
        Some(cp - 87)
    } else {
        None
    }
}
// One shared UCHAR decoder keeps the four/eight-digit cases on the same
// arithmetic and diagnostic path. Callers select exactly four or eight digits.
fn unicode_escape(bytes: &Vec<u8>, slash: usize, mut next: usize, count: usize) -> Step<u32> {
    let mut value: u64 = 0;
    let mut i = 0;
    while i < count {
        let (cp, end) = required(bytes, next)?;
        let digit = match hex(cp) {
            Some(d) => d,
            None => return Err(error(ErrorKind::InvalidEscape, slash)),
        };
        value = value * 16 + u64::from(digit);
        next = end;
        i += 1;
    }
    if value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff) {
        return Err(error(ErrorKind::InvalidEscape, slash));
    }
    Ok((value as u32, next))
}
pub(crate) fn escape(bytes: &Vec<u8>, slash: usize, after_slash: usize, iri: bool) -> Step<u32> {
    let (marker, next) = required(bytes, after_slash)?;
    if marker == 117 {
        return unicode_escape(bytes, slash, next, 4);
    }
    if marker == 85 {
        return unicode_escape(bytes, slash, next, 8);
    }
    if iri {
        return Err(error(ErrorKind::InvalidEscape, slash));
    }
    let value = match marker {
        116 => 9,
        98 => 8,
        110 => 10,
        114 => 13,
        102 => 12,
        34 => 34,
        39 => 39,
        92 => 92,
        _ => return Err(error(ErrorKind::InvalidEscape, slash)),
    };
    Ok((value, next))
}
fn iri_character(cp: u32) -> bool {
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
// The caller handles the closing delimiter first. This stage returns exactly
// one decoded raw/escaped character or its original source diagnostic.
pub(crate) fn quoted_item(
    bytes: &Vec<u8>,
    position: usize,
    cp: u32,
    next: usize,
    iri: bool,
) -> Step<u32> {
    if cp == 92 {
        escape(bytes, position, next, iri)
    } else {
        if (iri && !iri_character(cp)) || (!iri && eol(cp)) {
            return Err(error(ErrorKind::InvalidCharacter, position));
        }
        Ok((cp, next))
    }
}
pub(crate) fn quoted(bytes: &Vec<u8>, start: usize, iri: bool, limit: usize) -> Step<Vec<u8>> {
    let opening = if iri { 60 } else { 34 };
    let closing = if iri { 62 } else { 34 };
    let mut position = expect(
        bytes,
        start,
        opening,
        if iri {
            ErrorKind::ExpectedIri
        } else {
            ErrorKind::ExpectedObject
        },
    )?;
    let mut output = Vec::new();
    loop {
        let (cp, next) = required(bytes, position)?;
        if cp == closing {
            return Ok((output, next));
        }
        let (value, end) = quoted_item(bytes, position, cp, next, iri)?;
        let encoded = match encode(value) {
            Some(value) => value,
            None => return Err(error(ErrorKind::InvalidEscape, position)),
        };
        if !append_encoded(&mut output, encoded, limit) {
            return Err(error(ErrorKind::ResourceLimit, position));
        }
        position = end;
    }
}
fn read_iri(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<RdfIri> {
    let (spelling, next) = quoted(bytes, start, true, limit)?;
    if matches!(validate_iri(&spelling), MatchResult::Matched(true)) {
        Ok((RdfIri { spelling }, next))
    } else {
        Err(error(ErrorKind::InvalidIri, start))
    }
}
pub(crate) fn in_range(cp: u32, lower: u32, upper: u32) -> bool {
    (cp >= lower) && (cp <= upper)
}
pub(crate) fn pn_base(cp: u32) -> bool {
    in_range(cp, 65, 90)
        || in_range(cp, 97, 122)
        || in_range(cp, 0xc0, 0xd6)
        || in_range(cp, 0xd8, 0xf6)
        || in_range(cp, 0xf8, 0x2ff)
        || in_range(cp, 0x370, 0x37d)
        || in_range(cp, 0x37f, 0x1fff)
        || in_range(cp, 0x200c, 0x200d)
        || in_range(cp, 0x2070, 0x218f)
        || in_range(cp, 0x2c00, 0x2fef)
        || in_range(cp, 0x3001, 0xd7ff)
        || in_range(cp, 0xf900, 0xfdcf)
        || in_range(cp, 0xfdf0, 0xfffd)
        || in_range(cp, 0x10000, 0xeffff)
}
fn pn_u(cp: u32) -> bool {
    pn_base(cp) || cp == 95 || cp == 58
}
pub(crate) fn ascii_digit(cp: u32) -> bool {
    cp >= 48 && cp <= 57
}
fn pn(cp: u32) -> bool {
    pn_u(cp)
        || cp == 45
        || ascii_digit(cp)
        || cp == 0xb7
        || (cp >= 0x300 && cp <= 0x36f)
        || (cp >= 0x203f && cp <= 0x2040)
}
fn blank_end(bytes: &Vec<u8>, position: usize, accepted: usize) -> Result<usize, ReadError> {
    match at(bytes, position)? {
        Some((cp, next)) => {
            if pn(cp) {
                blank_end(bytes, next, next)
            } else if cp == 46 {
                blank_end(bytes, next, accepted)
            } else {
                Ok(accepted)
            }
        }
        None => Ok(accepted),
    }
}
pub(crate) fn copy_term(
    bytes: &Vec<u8>,
    start: usize,
    end: usize,
    limit: usize,
) -> Result<Vec<u8>, ReadError> {
    if end - start > limit {
        return Err(error(ErrorKind::ResourceLimit, start));
    }
    let mut value = Vec::new();
    let mut i = start;
    while i < end {
        value.push(bytes[i]);
        i += 1;
    }
    Ok(value)
}
fn blank(bytes: &Vec<u8>, start: usize, scope: &Vec<u8>, limit: usize) -> Step<BlankNode> {
    let colon = expect(bytes, start, 95, ErrorKind::InvalidBlankLabel)?;
    let label_start = expect(bytes, colon, 58, ErrorKind::InvalidBlankLabel)?;
    let (first, position) = required(bytes, label_start)?;
    if !pn_u(first) && !ascii_digit(first) {
        return Err(error(ErrorKind::InvalidBlankLabel, label_start));
    }
    let accepted = blank_end(bytes, position, position)?;
    let label = copy_term(bytes, label_start, accepted, limit)?;
    Ok((
        BlankNode {
            scope: copy_vec(scope),
            label,
        },
        accepted,
    ))
}
fn ascii_alpha(cp: u32) -> bool {
    (cp >= 65 && cp <= 90) || (cp >= 97 && cp <= 122)
}
fn tag_word(bytes: &Vec<u8>, position: usize, letters: bool) -> Result<usize, ReadError> {
    match at(bytes, position)? {
        Some((cp, next)) => {
            if ascii_alpha(cp) || (!letters && ascii_digit(cp)) {
                tag_word(bytes, next, letters)
            } else {
                Ok(position)
            }
        }
        None => Ok(position),
    }
}
fn tag_tail(bytes: &Vec<u8>, position: usize, start: usize) -> Result<usize, ReadError> {
    match at(bytes, position)? {
        Some((45, next)) => {
            let end = tag_word(bytes, next, false)?;
            if end == next {
                Err(error(ErrorKind::InvalidLanguageTag, start))
            } else {
                tag_tail(bytes, end, start)
            }
        }
        _ => Ok(position),
    }
}
fn tag(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<Vec<u8>> {
    let begin = expect(bytes, start, 64, ErrorKind::InvalidLanguageTag)?;
    let head = tag_word(bytes, begin, true)?;
    if begin == head {
        return Err(error(ErrorKind::InvalidLanguageTag, start));
    }
    let position = tag_tail(bytes, head, start)?;
    let output = copy_term(bytes, begin, position, limit)?;
    if !well_formed(&output) {
        return Err(error(ErrorKind::InvalidLanguageTag, start));
    }
    Ok((output, position))
}
fn literal_kind(bytes: &Vec<u8>, position: usize, limit: usize) -> Step<LiteralKind> {
    let (kind, next) = match at(bytes, position)? {
        Some((64, _)) => {
            let (value, next) = tag(bytes, position, limit)?;
            (LiteralKind::Language(value), next)
        }
        Some((94, next)) => {
            let end = expect(bytes, next, 94, ErrorKind::InvalidLiteralKind)?;
            let end = skip(bytes, end, false)?;
            let (datatype, next) = read_iri(bytes, end, limit)?;
            if same_literal_bytes(
                &datatype.spelling,
                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString",
            ) {
                return Err(error(ErrorKind::InvalidLiteralKind, position));
            }
            (LiteralKind::Datatype(datatype), next)
        }
        _ => (
            LiteralKind::Datatype(RdfIri {
                spelling: copy(b"http://www.w3.org/2001/XMLSchema#string"),
            }),
            position,
        ),
    };
    Ok((kind, next))
}
fn literal(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<RdfLiteral> {
    let (lexical, end) = quoted(bytes, start, false, limit)?;
    let position = skip(bytes, end, false)?;
    let (kind, next) = literal_kind(bytes, position, limit)?;
    Ok((RdfLiteral { lexical, kind }, next))
}
fn same_literal_bytes(a: &Vec<u8>, b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}
fn subject(bytes: &Vec<u8>, start: usize, scope: &Vec<u8>, limit: usize) -> Step<Subject> {
    match required(bytes, start)?.0 {
        60 => {
            let (value, next) = read_iri(bytes, start, limit)?;
            Ok((Subject::Iri(value), next))
        }
        95 => {
            let (value, next) = blank(bytes, start, scope, limit)?;
            Ok((Subject::Blank(value), next))
        }
        _ => Err(error(ErrorKind::ExpectedSubject, start)),
    }
}
fn object(bytes: &Vec<u8>, start: usize, scope: &Vec<u8>, limit: usize) -> Step<Object> {
    match required(bytes, start)?.0 {
        60 => {
            let (value, next) = read_iri(bytes, start, limit)?;
            Ok((Object::Iri(value), next))
        }
        95 => {
            let (value, next) = blank(bytes, start, scope, limit)?;
            Ok((Object::Blank(value), next))
        }
        34 => {
            let (value, next) = literal(bytes, start, limit)?;
            Ok((Object::Literal(value), next))
        }
        _ => Err(error(ErrorKind::ExpectedObject, start)),
    }
}
fn line_end(bytes: &Vec<u8>, position: usize) -> Result<(), ReadError> {
    if let Some((cp, _)) = at(bytes, position)? {
        if !eol(cp) {
            return Err(error(ErrorKind::ExpectedLineEnd, position));
        }
    }
    Ok(())
}
fn read_triple(bytes: &Vec<u8>, position: usize, scope: &Vec<u8>, limit: usize) -> Step<Triple> {
    let (subject, next) = subject(bytes, position, scope, limit)?;
    let next = skip(bytes, next, false)?;
    let (predicate, next) = read_iri(bytes, next, limit)?;
    let next = skip(bytes, next, false)?;
    let (object, next) = object(bytes, next, scope, limit)?;
    let next = skip(bytes, next, false)?;
    let next = expect(bytes, next, 46, ErrorKind::ExpectedPeriod)?;
    let next = skip(bytes, next, false)?;
    line_end(bytes, next)?;
    Ok((
        Triple {
            subject,
            predicate,
            object,
        },
        next,
    ))
}
fn read_from(
    bytes: &Vec<u8>,
    scope: &Vec<u8>,
    limits: &Limits,
    position: usize,
    mut triples: Vec<Triple>,
) -> Result<RawGraph, ReadError> {
    if position < bytes.len() {
        let (triple, next) = read_triple(bytes, position, scope, limits.max_term_bytes)?;
        if triples.len() >= limits.max_triples {
            return Err(error(ErrorKind::ResourceLimit, position));
        }
        triples.push(triple);
        let position = skip(bytes, next, true)?;
        read_from(bytes, scope, limits, position, triples)
    } else {
        Ok(RawGraph { triples })
    }
}
fn read_impl(bytes: &Vec<u8>, scope: &Vec<u8>, limits: &Limits) -> Result<RawGraph, ReadError> {
    let position = skip(bytes, 0, true)?;
    read_from(bytes, scope, limits, position, Vec::new())
}
/// Parse a whole N-Triples source. A caller-supplied immutable document scope
/// gives equal labels one identity and must differ across independent documents.
/// The import assembler will assign these scopes; this low-level API does not.
pub fn read_with_limits(bytes: &Vec<u8>, scope: &Vec<u8>, limits: &Limits) -> ReadResult {
    match read_impl(bytes, scope, limits) {
        Ok(graph) => ReadResult::Graph(graph),
        Err(error) => ReadResult::Error(error),
    }
}
/// Input-sized term/triple bounds suffice for document content; physical
/// allocation failure is not handled by these logical count limits.
pub fn read(bytes: &Vec<u8>, scope: &Vec<u8>) -> ReadResult {
    read_with_limits(
        bytes,
        scope,
        &Limits {
            max_term_bytes: bytes.len(),
            max_triples: bytes.len(),
        },
    )
}

pub enum WriteError {
    InvalidIri,
    MalformedLiteralUtf8,
    InvalidLanguageTag,
    InvalidLiteralKind,
    ResourceLimit,
}
pub enum WriteResult {
    Bytes(Vec<u8>),
    Error(WriteError),
}
fn put(output: &mut Vec<u8>, byte: u8, limit: usize) -> Result<(), WriteError> {
    if push(output, byte, limit) {
        Ok(())
    } else {
        Err(WriteError::ResourceLimit)
    }
}
fn put_bytes(output: &mut Vec<u8>, bytes: &[u8], limit: usize) -> Result<(), WriteError> {
    let mut i = 0;
    while i < bytes.len() {
        put(output, bytes[i], limit)?;
        i += 1;
    }
    Ok(())
}
fn write_iri(output: &mut Vec<u8>, value: &RdfIri, limit: usize) -> Result<(), WriteError> {
    if !matches!(validate_iri(&value.spelling), MatchResult::Matched(true)) {
        return Err(WriteError::InvalidIri);
    }
    put(output, 60, limit)?;
    put_span(output, &value.spelling, 0, value.spelling.len(), limit)?;
    put(output, 62, limit)
}
fn put_span(
    output: &mut Vec<u8>,
    bytes: &Vec<u8>,
    start: usize,
    end: usize,
    limit: usize,
) -> Result<(), WriteError> {
    let mut p = start;
    while p < end {
        put(output, bytes[p], limit)?;
        p += 1;
    }
    Ok(())
}
fn write_units(
    output: &mut Vec<u8>,
    lexical: &Vec<u8>,
    i: usize,
    limit: usize,
) -> Result<(), WriteError> {
    match decode_next(lexical, i) {
        Decoded::End => Ok(()),
        Decoded::Error(_) => Err(WriteError::MalformedLiteralUtf8),
        Decoded::Scalar { codepoint, next } => {
            let escape = match codepoint {
                34 => Some(34),
                92 => Some(92),
                10 => Some(110),
                13 => Some(114),
                _ => None,
            };
            match escape {
                Some(byte) => {
                    put(output, 92, limit)?;
                    put(output, byte, limit)?;
                }
                None => {
                    put_span(output, lexical, i, next, limit)?;
                }
            }
            write_units(output, lexical, next, limit)
        }
    }
}
fn write_lexical(output: &mut Vec<u8>, lexical: &Vec<u8>, limit: usize) -> Result<(), WriteError> {
    put(output, 34, limit)?;
    write_units(output, lexical, 0, limit)?;
    put(output, 34, limit)
}
// Scope/label are encoded injectively into a legal blank label. Raw blank keys
// may be empty or non-UTF-8; separators make component boundaries unambiguous.
fn hex_digit(n: u8) -> u8 {
    if n < 10 {
        48 + n
    } else {
        87 + n
    }
}
fn write_key(output: &mut Vec<u8>, key: &Vec<u8>, limit: usize) -> Result<(), WriteError> {
    let mut i = 0;
    while i < key.len() {
        put(output, hex_digit(key[i] / 16), limit)?;
        put(output, hex_digit(key[i] % 16), limit)?;
        i += 1;
    }
    Ok(())
}
fn write_blank(output: &mut Vec<u8>, node: &BlankNode, limit: usize) -> Result<(), WriteError> {
    put_bytes(output, b"_:b", limit)?;
    write_key(output, &node.scope, limit)?;
    put(output, 95, limit)?;
    write_key(output, &node.label, limit)
}
fn write_subject(output: &mut Vec<u8>, value: &Subject, limit: usize) -> Result<(), WriteError> {
    match value {
        Subject::Iri(i) => write_iri(output, i, limit),
        Subject::Blank(b) => write_blank(output, b, limit),
    }
}
fn write_object(output: &mut Vec<u8>, value: &Object, limit: usize) -> Result<(), WriteError> {
    match value {
        Object::Iri(i) => write_iri(output, i, limit),
        Object::Blank(b) => write_blank(output, b, limit),
        Object::Literal(literal) => {
            write_lexical(output, &literal.lexical, limit)?;
            match &literal.kind {
                LiteralKind::Datatype(iri) => {
                    if same_literal_bytes(
                        &iri.spelling,
                        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString",
                    ) {
                        return Err(WriteError::InvalidLiteralKind);
                    }
                    put_bytes(output, b"^^", limit)?;
                    write_iri(output, iri, limit)
                }
                LiteralKind::Language(tag) => {
                    if !well_formed(tag) {
                        return Err(WriteError::InvalidLanguageTag);
                    }
                    put(output, 64, limit)?;
                    put_span(output, tag, 0, tag.len(), limit)
                }
            }
        }
    }
}
fn write_impl(graph: &RawGraph, limit: usize) -> Result<Vec<u8>, WriteError> {
    let mut output = Vec::new();
    let mut i = 0;
    while i < graph.triples.len() {
        let triple = &graph.triples[i];
        write_subject(&mut output, &triple.subject, limit)?;
        put(&mut output, 32, limit)?;
        write_iri(&mut output, &triple.predicate, limit)?;
        put(&mut output, 32, limit)?;
        write_object(&mut output, &triple.object, limit)?;
        put_bytes(&mut output, b" .\n", limit)?;
        i += 1;
    }
    Ok(output)
}
/// Export one graph with an explicit byte budget. Blank identity is preserved
/// up to the required graph isomorphism, including distinct scope/label pairs.
/// Errors never expose partially serialized bytes as a successful result.
pub fn write(graph: &RawGraph, max_output_bytes: usize) -> WriteResult {
    match write_impl(graph, max_output_bytes) {
        Ok(bytes) => WriteResult::Bytes(bytes),
        Err(error) => WriteResult::Error(error),
    }
}
