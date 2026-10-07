//! RDF 1.1 Turtle reading (W3C Recommendation, 25 February 2014).
//!
//! `read_with_limits` turns the UTF-8 bytes of a Turtle document into the
//! triples it denotes. Statements are read in order. An object's triple
//! `curSubject curPredicate object` (section 7) follows the triples inside the
//! object, so the triples of a blank node property list or a collection come
//! before the triple that uses its node; in a collection the triple
//! `node rdf:rest next` comes before the triples of the next member.
//!
//! IRIREFs are resolved by `references::resolve` (RFC 3986 section 5.2)
//! against the base, which `@base` and `BASE` change; the reference must be an
//! RFC 3987 IRI reference and every resulting IRI an RFC 3987 IRI. A prefixed
//! name denotes its namespace followed by its local name without the `\` of its
//! escapes. Labelled blank nodes carry the caller's scope and their label. The
//! blank node of a `[` at byte offset `n` has the label `0xFF` followed by the
//! decimal digits of `n`, and the list node of a collection member starting at
//! byte offset `n` has the label `0xFE` followed by those digits; no document
//! label contains these bytes, which never occur in UTF-8. Comments count as
//! white space everywhere outside IRIs and strings, also inside `[ ]`.
//!
//! The tokens Turtle shares with N-Triples (IRIREF, STRING_LITERAL_QUOTE,
//! ECHAR, UCHAR, LANGTAG, white space and comments) are read by the N-Triples
//! readers. Every condition below is a single comparison or call, and ranges
//! and vectors are written out because `RangeInclusive::contains` and `vec!`
//! lack a model in the pinned extraction.
#![allow(
    clippy::ptr_arg,
    clippy::manual_range_contains,
    clippy::vec_init_then_push
)]

use crate::encoding::encode;
use crate::iri::validate_iri;
use crate::langtag::well_formed;
use crate::ntriples;
use crate::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfIri, RdfLiteral, Subject, Triple};
use crate::references::{is_reference, resolve};
use crate::regular::MatchResult;

pub enum ErrorKind {
    /// The bytes at the offset are no UTF-8 encoded character.
    MalformedUtf8,
    /// The document ends inside a token or statement.
    UnexpectedEnd,
    /// A character that is not allowed raw in an IRI or a string.
    InvalidCharacter,
    /// An escape that is not ECHAR or UCHAR, or not allowed here.
    InvalidEscape,
    /// An IRI reference that is not an RFC 3987 IRI reference, or an IRI that
    /// is not an RFC 3987 IRI.
    InvalidIri,
    /// A blank node label that does not follow BLANK_NODE_LABEL.
    InvalidBlankLabel,
    /// A language tag that is not a well-formed BCP 47 tag.
    InvalidLanguageTag,
    /// `^^` not followed by a second `^`, or the datatype rdf:langString.
    InvalidLiteralKind,
    /// A prefixed name whose prefix is not declared.
    UndefinedPrefix,
    /// A prefix declaration without `PN_PREFIX? ':'`.
    ExpectedPrefix,
    /// A position that needs an IRI.
    ExpectedIri,
    /// A position that needs a subject.
    ExpectedSubject,
    /// A position that needs a predicate.
    ExpectedVerb,
    /// A position that needs an object.
    ExpectedObject,
    /// A statement that does not end with `.`.
    ExpectedPeriod,
    /// A blank node property list that does not end with `]`.
    ExpectedBracket,
    /// A term longer than the term limit, or more triples than the limit.
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

/// A prefix declaration: the prefix name and its namespace IRI.
pub struct Prefix {
    pub name: Vec<u8>,
    pub iri: Vec<u8>,
}

type Step<T> = Result<(T, usize), ReadError>;
type Grown<T> = Result<(T, usize, Vec<Triple>), ReadError>;
type Emitted = Result<(usize, Vec<Triple>), ReadError>;

fn error(kind: ErrorKind, offset: usize) -> ReadError {
    ReadError { kind, offset }
}

/// The Turtle error kind of an N-Triples error kind: the kind of the same
/// name, and `ExpectedPeriod` for the line end that Turtle does not have.
fn kind_of(kind: ntriples::ErrorKind) -> ErrorKind {
    match kind {
        ntriples::ErrorKind::MalformedUtf8 => ErrorKind::MalformedUtf8,
        ntriples::ErrorKind::UnexpectedEnd => ErrorKind::UnexpectedEnd,
        ntriples::ErrorKind::ExpectedIri => ErrorKind::ExpectedIri,
        ntriples::ErrorKind::ExpectedSubject => ErrorKind::ExpectedSubject,
        ntriples::ErrorKind::ExpectedObject => ErrorKind::ExpectedObject,
        ntriples::ErrorKind::ExpectedPeriod => ErrorKind::ExpectedPeriod,
        ntriples::ErrorKind::ExpectedLineEnd => ErrorKind::ExpectedPeriod,
        ntriples::ErrorKind::InvalidCharacter => ErrorKind::InvalidCharacter,
        ntriples::ErrorKind::InvalidEscape => ErrorKind::InvalidEscape,
        ntriples::ErrorKind::InvalidIri => ErrorKind::InvalidIri,
        ntriples::ErrorKind::InvalidBlankLabel => ErrorKind::InvalidBlankLabel,
        ntriples::ErrorKind::InvalidLanguageTag => ErrorKind::InvalidLanguageTag,
        ntriples::ErrorKind::InvalidLiteralKind => ErrorKind::InvalidLiteralKind,
        ntriples::ErrorKind::ResourceLimit => ErrorKind::ResourceLimit,
    }
}

fn from_ntriples(e: ntriples::ReadError) -> ReadError {
    ReadError {
        kind: kind_of(e.kind),
        offset: e.offset,
    }
}

/// The unit at `position`, or `None` at the end.
fn unit(bytes: &Vec<u8>, position: usize) -> Result<Option<(u32, usize)>, ReadError> {
    match ntriples::at(bytes, position) {
        Ok(found) => Ok(found),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// The unit at `position`, which must exist.
fn needed(bytes: &Vec<u8>, position: usize) -> Result<(u32, usize), ReadError> {
    match ntriples::required(bytes, position) {
        Ok(found) => Ok(found),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// The position after the white space and comments at `position`.
fn space(bytes: &Vec<u8>, position: usize) -> Result<usize, ReadError> {
    match ntriples::skip(bytes, position, true) {
        Ok(next) => Ok(next),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// The bytes `start..end`, within the term limit.
fn copied(bytes: &Vec<u8>, start: usize, end: usize, limit: usize) -> Result<Vec<u8>, ReadError> {
    match ntriples::copy_term(bytes, start, end, limit) {
        Ok(value) => Ok(value),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// The IRIREF token at `start`: its characters after unescaping.
fn quoted_iri(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<Vec<u8>> {
    match ntriples::quoted(bytes, start, true, limit) {
        Ok(found) => Ok(found),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// The STRING_LITERAL_QUOTE token at `start`: its characters after unescaping.
fn quoted_string(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<Vec<u8>> {
    match ntriples::quoted(bytes, start, false, limit) {
        Ok(found) => Ok(found),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// One raw or escaped character of a short string, whose first unit `cp`
/// ends at `next`.
fn string_item(bytes: &Vec<u8>, position: usize, cp: u32, next: usize) -> Step<u32> {
    match ntriples::quoted_item(bytes, position, cp, next, false) {
        Ok(found) => Ok(found),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// The ECHAR or UCHAR whose `\` at `slash` ends at `next`.
fn string_escape(bytes: &Vec<u8>, slash: usize, next: usize) -> Step<u32> {
    match ntriples::escape(bytes, slash, next, false) {
        Ok(found) => Ok(found),
        Err(e) => Err(from_ntriples(e)),
    }
}

/// Whether `bytes[index]` exists and is `value`.
fn byte_is(bytes: &Vec<u8>, index: usize, value: u8) -> bool {
    index < bytes.len() && bytes[index] == value
}

/// A copy of a byte vector.
fn copy_bytes(values: &Vec<u8>) -> Vec<u8> {
    copy_from(values, 0, Vec::new())
}

fn copy_from(values: &Vec<u8>, index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < values.len() {
        out.push(values[index]);
        copy_from(values, index + 1, out)
    } else {
        out
    }
}

/// A vector of the bytes of a constant.
fn constant(values: &[u8]) -> Vec<u8> {
    constant_from(values, 0, Vec::new())
}

fn constant_from(values: &[u8], index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < values.len() {
        out.push(values[index]);
        constant_from(values, index + 1, out)
    } else {
        out
    }
}

fn copy_iri(iri: &RdfIri) -> RdfIri {
    RdfIri {
        spelling: copy_bytes(&iri.spelling),
    }
}

fn copy_subject(subject: &Subject) -> Subject {
    match subject {
        Subject::Iri(iri) => Subject::Iri(copy_iri(iri)),
        Subject::Blank(node) => Subject::Blank(BlankNode {
            scope: copy_bytes(&node.scope),
            label: copy_bytes(&node.label),
        }),
    }
}

/// The object that is the node `subject`.
fn object_of(subject: Subject) -> Object {
    match subject {
        Subject::Iri(iri) => Object::Iri(iri),
        Subject::Blank(node) => Object::Blank(node),
    }
}

fn rdf_iri(spelling: &[u8]) -> RdfIri {
    RdfIri {
        spelling: constant(spelling),
    }
}

fn rdf_type() -> RdfIri {
    rdf_iri(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type")
}

fn rdf_first() -> RdfIri {
    rdf_iri(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#first")
}

fn rdf_rest() -> RdfIri {
    rdf_iri(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest")
}

fn rdf_nil() -> RdfIri {
    rdf_iri(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil")
}

fn xsd(kind: &[u8]) -> LiteralKind {
    LiteralKind::Datatype(rdf_iri(kind))
}

/// Whether the bytes are exactly the IRI of rdf:langString.
fn lang_string(spelling: &Vec<u8>) -> bool {
    same_constant(
        spelling,
        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString",
    )
}

fn same_constant(value: &Vec<u8>, pattern: &[u8]) -> bool {
    value.len() == pattern.len() && same_constant_from(value, pattern, 0)
}

fn same_constant_from(value: &Vec<u8>, pattern: &[u8], index: usize) -> bool {
    if index < value.len() {
        if value[index] == pattern[index] {
            same_constant_from(value, pattern, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// `out` followed by the decimal digits of `number`.
fn digits(number: usize, out: Vec<u8>) -> Vec<u8> {
    let mut out = if number < 10 {
        out
    } else {
        digits(number / 10, out)
    };
    out.push(48 + (number % 10) as u8);
    out
}

/// The byte `marker` followed by the decimal digits of `number`.
fn marked(marker: u8, number: usize) -> Vec<u8> {
    let mut label = Vec::new();
    label.push(marker);
    digits(number, label)
}

/// The blank node of the `[` at byte offset `start`.
fn bracket_node(scope: &Vec<u8>, start: usize) -> BlankNode {
    BlankNode {
        scope: copy_bytes(scope),
        label: marked(255, start),
    }
}

/// The list node of the collection member at byte offset `start`.
fn list_node(scope: &Vec<u8>, start: usize) -> BlankNode {
    BlankNode {
        scope: copy_bytes(scope),
        label: marked(254, start),
    }
}

/// The triples with one more, within the triple limit.
fn emit(
    mut triples: Vec<Triple>,
    triple: Triple,
    limits: &Limits,
    position: usize,
) -> Result<Vec<Triple>, ReadError> {
    if triples.len() < limits.max_triples {
        triples.push(triple);
        Ok(triples)
    } else {
        Err(error(ErrorKind::ResourceLimit, position))
    }
}

// Character classes of section 6.5.

/// PN_CHARS_U: PN_CHARS_BASE or `_`; Turtle's class has no `:`.
fn pn_u(cp: u32) -> bool {
    ntriples::pn_base(cp) || cp == 95
}

/// PN_CHARS of Turtle.
fn pn_chars(cp: u32) -> bool {
    pn_u(cp)
        || cp == 45
        || ntriples::ascii_digit(cp)
        || cp == 0xb7
        || ntriples::in_range(cp, 0x300, 0x36f)
        || ntriples::in_range(cp, 0x203f, 0x2040)
}

/// The first character of a blank node label: PN_CHARS_U or a digit.
fn label_first(cp: u32) -> bool {
    pn_u(cp) || ntriples::ascii_digit(cp)
}

/// The first character of a local name other than PLX: PN_CHARS_U, `:` or a
/// digit.
fn local_first_char(cp: u32) -> bool {
    pn_u(cp) || cp == 58 || ntriples::ascii_digit(cp)
}

/// A later character of a local name other than PLX and `.`: PN_CHARS or `:`.
fn local_char(cp: u32) -> bool {
    pn_chars(cp) || cp == 58
}

/// The characters that PN_LOCAL_ESC escapes: `!`, `#` to `/`, `;`, `=`, `?`,
/// `@`, `_` and `~`.
fn local_escape(cp: u32) -> bool {
    cp == 33
        || ntriples::in_range(cp, 35, 47)
        || cp == 59
        || cp == 61
        || cp == 63
        || cp == 64
        || cp == 95
        || cp == 126
}

/// `%` or `\`, the first character of PLX.
fn plx_start(cp: u32) -> bool {
    cp == 37 || cp == 92
}

/// The end of the maximal run of PN_CHARS and `.` from `position` that ends
/// with PN_CHARS, or `accepted` when the run is empty or only dots.
fn name_end(bytes: &Vec<u8>, position: usize, accepted: usize) -> Result<usize, ReadError> {
    match unit(bytes, position)? {
        Some((cp, next)) => {
            if pn_chars(cp) {
                name_end(bytes, next, next)
            } else if cp == 46 {
                name_end(bytes, next, accepted)
            } else {
                Ok(accepted)
            }
        }
        None => Ok(accepted),
    }
}

/// The position of the `:` after the rest of a PN_PREFIX from `next`.
fn prefix_end(bytes: &Vec<u8>, next: usize) -> Result<Option<usize>, ReadError> {
    let end = name_end(bytes, next, next)?;
    if byte_is(bytes, end, 58) {
        Ok(Some(end))
    } else {
        Ok(None)
    }
}

/// The position of the `:` of a PNAME_NS `PN_PREFIX? ':'` at `start`.
fn prefix_colon(bytes: &Vec<u8>, start: usize) -> Result<Option<usize>, ReadError> {
    match unit(bytes, start)? {
        Some((cp, next)) => {
            if cp == 58 {
                Ok(Some(start))
            } else if ntriples::pn_base(cp) {
                prefix_end(bytes, next)
            } else {
                Ok(None)
            }
        }
        None => Ok(None),
    }
}

/// The end of the hex digit at `position`, if there is one.
fn hex_at(bytes: &Vec<u8>, position: usize) -> Result<Option<usize>, ReadError> {
    match unit(bytes, position)? {
        Some((cp, next)) => {
            if ntriples::hex(cp).is_some() {
                Ok(Some(next))
            } else {
                Ok(None)
            }
        }
        None => Ok(None),
    }
}

/// The end of the PERCENT whose `%` ends at `next`.
fn percent(bytes: &Vec<u8>, next: usize) -> Result<Option<usize>, ReadError> {
    match hex_at(bytes, next)? {
        Some(second) => hex_at(bytes, second),
        None => Ok(None),
    }
}

/// The end of the PN_LOCAL_ESC whose `\` ends at `next`.
fn local_escaped(bytes: &Vec<u8>, next: usize) -> Result<Option<usize>, ReadError> {
    match unit(bytes, next)? {
        Some((cp, after)) => {
            if local_escape(cp) {
                Ok(Some(after))
            } else {
                Ok(None)
            }
        }
        None => Ok(None),
    }
}

/// The end of the PLX whose first character `cp` ends at `next`.
fn plx(bytes: &Vec<u8>, cp: u32, next: usize) -> Result<Option<usize>, ReadError> {
    if cp == 37 {
        percent(bytes, next)
    } else {
        local_escaped(bytes, next)
    }
}

/// The end of the first unit of a local name at `position`, if one begins.
fn local_first(bytes: &Vec<u8>, position: usize) -> Result<Option<usize>, ReadError> {
    match unit(bytes, position)? {
        Some((cp, next)) => {
            if plx_start(cp) {
                plx(bytes, cp, next)
            } else if local_first_char(cp) {
                Ok(Some(next))
            } else {
                Ok(None)
            }
        }
        None => Ok(None),
    }
}

/// A later unit of a local name: a name unit, a dot, or the end of the name.
enum Local {
    Name(usize),
    Dot(usize),
    End,
}

/// The PLX at a later position of a local name, or its end.
fn local_plx(bytes: &Vec<u8>, cp: u32, next: usize) -> Result<Local, ReadError> {
    match plx(bytes, cp, next)? {
        Some(after) => Ok(Local::Name(after)),
        None => Ok(Local::End),
    }
}

fn local_next(bytes: &Vec<u8>, position: usize) -> Result<Local, ReadError> {
    match unit(bytes, position)? {
        Some((cp, next)) => {
            if plx_start(cp) {
                local_plx(bytes, cp, next)
            } else if local_char(cp) {
                Ok(Local::Name(next))
            } else if cp == 46 {
                Ok(Local::Dot(next))
            } else {
                Ok(Local::End)
            }
        }
        None => Ok(Local::End),
    }
}

/// The end of the local name from `position`, after its last unit that is
/// not a dot.
fn local_rest(bytes: &Vec<u8>, position: usize, accepted: usize) -> Result<usize, ReadError> {
    match local_next(bytes, position)? {
        Local::Name(next) => local_rest(bytes, next, next),
        Local::Dot(next) => local_rest(bytes, next, accepted),
        Local::End => Ok(accepted),
    }
}

/// The end of the PN_LOCAL from `start`, or `start` when none begins.
fn local_end(bytes: &Vec<u8>, start: usize) -> Result<usize, ReadError> {
    match local_first(bytes, start)? {
        Some(next) => local_rest(bytes, next, next),
        None => Ok(start),
    }
}

/// Whether `index` lies before `end` and inside `bytes`.
fn before(bytes: &Vec<u8>, index: usize, end: usize) -> bool {
    index < end && index < bytes.len()
}

/// `out` with `byte`, if it is shorter than `limit`.
fn push_limited(mut out: Vec<u8>, byte: u8, limit: usize) -> Option<Vec<u8>> {
    if out.len() < limit {
        out.push(byte);
        Some(out)
    } else {
        None
    }
}

/// The byte at `index` after a `\`, or the `\` itself at the end.
fn escaped_byte(bytes: &Vec<u8>, index: usize, end: usize) -> (u8, usize) {
    if before(bytes, index, end) {
        (bytes[index], index + 1)
    } else {
        (92, index)
    }
}

/// The byte at `index` of a local name and the index after it: the byte after
/// a `\`, any other byte as it is.
fn local_byte(bytes: &Vec<u8>, index: usize, end: usize) -> (u8, usize) {
    if bytes[index] == 92 {
        escaped_byte(bytes, index + 1, end)
    } else {
        (bytes[index], index + 1)
    }
}

/// `out` followed by the local name `bytes[index..end]` without the `\` of
/// its escapes, if that stays within `limit` bytes.
fn unescape(
    bytes: &Vec<u8>,
    index: usize,
    end: usize,
    out: Vec<u8>,
    limit: usize,
) -> Option<Vec<u8>> {
    if before(bytes, index, end) {
        let (byte, next) = local_byte(bytes, index, end);
        match push_limited(out, byte, limit) {
            Some(out) => unescape(bytes, next, end, out, limit),
            None => None,
        }
    } else {
        Some(out)
    }
}

/// Whether `name` is the bytes `start..end`.
fn same_span(name: &Vec<u8>, bytes: &Vec<u8>, start: usize, end: usize) -> bool {
    name.len() == end - start && same_span_from(name, bytes, start, 0)
}

fn same_span_from(name: &Vec<u8>, bytes: &Vec<u8>, start: usize, index: usize) -> bool {
    if index < name.len() {
        if name[index] == bytes[start + index] {
            same_span_from(name, bytes, start, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// The last declaration among the first `count` whose name is `start..end`.
fn lookup(
    prefixes: &Vec<Prefix>,
    bytes: &Vec<u8>,
    start: usize,
    end: usize,
    count: usize,
) -> Option<usize> {
    if 0 < count {
        if same_span(&prefixes[count - 1].name, bytes, start, end) {
            Some(count - 1)
        } else {
            lookup(prefixes, bytes, start, end, count - 1)
        }
    } else {
        None
    }
}

/// Whether the bytes are an RFC 3987 IRI.
fn valid_iri(bytes: &Vec<u8>) -> bool {
    matches!(validate_iri(bytes), MatchResult::Matched(true))
}

/// The IRI `spelling` of the term at `start`, which must be an IRI.
fn checked_iri(spelling: Vec<u8>, start: usize, next: usize) -> Step<RdfIri> {
    if valid_iri(&spelling) {
        Ok((RdfIri { spelling }, next))
    } else {
        Err(error(ErrorKind::InvalidIri, start))
    }
}

/// The IRI `spelling` of the term at `start`, within the term limit.
fn bounded_iri(spelling: Vec<u8>, start: usize, next: usize, limit: usize) -> Step<RdfIri> {
    if limit < spelling.len() {
        Err(error(ErrorKind::ResourceLimit, start))
    } else {
        checked_iri(spelling, start, next)
    }
}

/// The IRI of the prefixed name at `start`, whose PNAME_NS ends with the `:`
/// at `colon`: the namespace followed by the unescaped local name.
fn prefixed(
    bytes: &Vec<u8>,
    start: usize,
    colon: usize,
    prefixes: &Vec<Prefix>,
    limit: usize,
) -> Step<RdfIri> {
    match lookup(prefixes, bytes, start, colon, prefixes.len()) {
        Some(entry) => {
            let end = local_end(bytes, colon + 1)?;
            let namespace = copy_bytes(&prefixes[entry].iri);
            match unescape(bytes, colon + 1, end, namespace, limit) {
                Some(spelling) => bounded_iri(spelling, start, end, limit),
                None => Err(error(ErrorKind::ResourceLimit, start)),
            }
        }
        None => Err(error(ErrorKind::UndefinedPrefix, start)),
    }
}

/// The IRIREF at `start`, resolved against `base`.
fn iri_ref(bytes: &Vec<u8>, start: usize, base: &Vec<u8>, limit: usize) -> Step<RdfIri> {
    let (reference, next) = quoted_iri(bytes, start, limit)?;
    if is_reference(&reference) {
        match resolve(base, &reference) {
            Some(spelling) => bounded_iri(spelling, start, next, limit),
            None => Err(error(ErrorKind::InvalidIri, start)),
        }
    } else {
        Err(error(ErrorKind::InvalidIri, start))
    }
}

/// The iri at `start`: an IRIREF or a prefixed name.
fn iri(
    bytes: &Vec<u8>,
    start: usize,
    base: &Vec<u8>,
    prefixes: &Vec<Prefix>,
    limit: usize,
) -> Step<RdfIri> {
    if byte_is(bytes, start, 60) {
        iri_ref(bytes, start, base, limit)
    } else {
        match prefix_colon(bytes, start)? {
            Some(colon) => prefixed(bytes, start, colon, prefixes, limit),
            None => Err(error(ErrorKind::ExpectedIri, start)),
        }
    }
}

/// The blank node of the BLANK_NODE_LABEL at `start`, which begins with `_`.
fn blank_label(bytes: &Vec<u8>, start: usize, scope: &Vec<u8>, limit: usize) -> Step<BlankNode> {
    if byte_is(bytes, start + 1, 58) {
        let (first, next) = needed(bytes, start + 2)?;
        if label_first(first) {
            let end = name_end(bytes, next, next)?;
            let label = copied(bytes, start + 2, end, limit)?;
            Ok((
                BlankNode {
                    scope: copy_bytes(scope),
                    label,
                },
                end,
            ))
        } else {
            Err(error(ErrorKind::InvalidBlankLabel, start + 2))
        }
    } else {
        Err(error(ErrorKind::InvalidBlankLabel, start))
    }
}

/// `output` followed by the UTF-8 encoding of `value`, within the limit.
fn add(
    mut output: Vec<u8>,
    value: u32,
    limit: usize,
    position: usize,
) -> Result<Vec<u8>, ReadError> {
    match encode(value) {
        Some(encoded) => {
            if ntriples::append_encoded(&mut output, encoded, limit) {
                Ok(output)
            } else {
                Err(error(ErrorKind::ResourceLimit, position))
            }
        }
        None => Err(error(ErrorKind::InvalidEscape, position)),
    }
}

/// The body of a STRING_LITERAL_SINGLE_QUOTE from `position` to its `'`.
fn single_body(bytes: &Vec<u8>, position: usize, output: Vec<u8>, limit: usize) -> Step<Vec<u8>> {
    let (cp, next) = needed(bytes, position)?;
    if cp == 39 {
        Ok((output, next))
    } else {
        let (value, end) = string_item(bytes, position, cp, next)?;
        let output = add(output, value, limit, position)?;
        single_body(bytes, end, output, limit)
    }
}

/// Whether three quotes `quote` begin at `position`.
fn triple_quote(bytes: &Vec<u8>, position: usize, quote: u8) -> bool {
    byte_is(bytes, position, quote)
        && byte_is(bytes, position + 1, quote)
        && byte_is(bytes, position + 2, quote)
}

/// One character of a long string at `position`: raw, or an escape.
fn long_item(bytes: &Vec<u8>, position: usize) -> Step<u32> {
    let (cp, next) = needed(bytes, position)?;
    if cp == 92 {
        string_escape(bytes, position, next)
    } else {
        Ok((cp, next))
    }
}

/// The body of a long string from `position` to its closing three quotes.
/// Its value is never longer than the bytes it is read from, so the output
/// needs no limit of its own.
fn long_body(bytes: &Vec<u8>, position: usize, quote: u8, output: Vec<u8>) -> Step<Vec<u8>> {
    if triple_quote(bytes, position, quote) {
        Ok((output, position + 3))
    } else {
        let (value, end) = long_item(bytes, position)?;
        let output = add(output, value, usize::MAX, position)?;
        long_body(bytes, end, quote, output)
    }
}

/// The value of the string at `start` and the position after it, within the
/// term limit.
fn bounded_string(value: Vec<u8>, start: usize, end: usize, limit: usize) -> Step<Vec<u8>> {
    if limit < value.len() {
        Err(error(ErrorKind::ResourceLimit, start))
    } else {
        Ok((value, end))
    }
}

/// The long string whose three quotes `quote` are at `start` or, when no long
/// string is there, the longest match: the empty short string of two quotes.
fn long_string(bytes: &Vec<u8>, start: usize, quote: u8, limit: usize) -> Step<Vec<u8>> {
    match long_body(bytes, start + 3, quote, Vec::new()) {
        Ok((value, end)) => bounded_string(value, start, end, limit),
        Err(_) => Ok((Vec::new(), start + 2)),
    }
}

/// The characters of the String at `start`, which begins with a quote.
fn string(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<Vec<u8>> {
    if triple_quote(bytes, start, 34) {
        long_string(bytes, start, 34, limit)
    } else if triple_quote(bytes, start, 39) {
        long_string(bytes, start, 39, limit)
    } else if byte_is(bytes, start, 34) {
        quoted_string(bytes, start, limit)
    } else {
        single_body(bytes, start + 1, Vec::new(), limit)
    }
}

/// The end of the ASCII letters from `index`.
fn letters_end(bytes: &Vec<u8>, index: usize) -> usize {
    if index < bytes.len() {
        if letter_byte(bytes[index]) {
            letters_end(bytes, index + 1)
        } else {
            index
        }
    } else {
        index
    }
}

/// Whether `byte` is an ASCII letter or digit.
fn alnum_byte(byte: u8) -> bool {
    letter_byte(byte) || digit_byte(byte)
}

/// The end of the ASCII letters and digits from `index`.
fn alnums_end(bytes: &Vec<u8>, index: usize) -> usize {
    if index < bytes.len() {
        if alnum_byte(bytes[index]) {
            alnums_end(bytes, index + 1)
        } else {
            index
        }
    } else {
        index
    }
}

/// The end of the subtags `('-' [a-zA-Z0-9]+)*` from `index`; a `-` that no
/// letter or digit follows ends the LANGTAG before it.
fn subtags_end(bytes: &Vec<u8>, index: usize) -> usize {
    if byte_is(bytes, index, 45) {
        let end = alnums_end(bytes, index + 1);
        if index + 1 < end {
            subtags_end(bytes, end)
        } else {
            index
        }
    } else {
        index
    }
}

/// The LANGTAG at `start`, which begins with `@`; its tag must be a
/// well-formed BCP 47 language tag.
fn language(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<Vec<u8>> {
    let head = letters_end(bytes, start + 1);
    if start + 1 < head {
        let end = subtags_end(bytes, head);
        let tag = copied(bytes, start + 1, end, limit)?;
        if well_formed(&tag) {
            Ok((tag, end))
        } else {
            Err(error(ErrorKind::InvalidLanguageTag, start))
        }
    } else {
        Err(error(ErrorKind::InvalidLanguageTag, start))
    }
}

/// The datatype after the `^` at `position`.
fn datatype(
    bytes: &Vec<u8>,
    position: usize,
    base: &Vec<u8>,
    prefixes: &Vec<Prefix>,
    limit: usize,
) -> Step<LiteralKind> {
    if byte_is(bytes, position + 1, 94) {
        let start = space(bytes, position + 2)?;
        let (datatype, next) = iri(bytes, start, base, prefixes, limit)?;
        if lang_string(&datatype.spelling) {
            Err(error(ErrorKind::InvalidLiteralKind, position))
        } else {
            Ok((LiteralKind::Datatype(datatype), next))
        }
    } else {
        Err(error(ErrorKind::InvalidLiteralKind, position))
    }
}

/// The language tag or datatype after a String ending at `end`, and the end
/// of the literal.
fn literal_kind(
    bytes: &Vec<u8>,
    end: usize,
    base: &Vec<u8>,
    prefixes: &Vec<Prefix>,
    limit: usize,
) -> Step<LiteralKind> {
    let position = space(bytes, end)?;
    if byte_is(bytes, position, 64) {
        let (tag, next) = language(bytes, position, limit)?;
        Ok((LiteralKind::Language(tag), next))
    } else if byte_is(bytes, position, 94) {
        datatype(bytes, position, base, prefixes, limit)
    } else {
        Ok((xsd(b"http://www.w3.org/2001/XMLSchema#string"), end))
    }
}

/// The RDFLiteral at `start`, which begins with a quote.
fn literal(
    bytes: &Vec<u8>,
    start: usize,
    base: &Vec<u8>,
    prefixes: &Vec<Prefix>,
    limit: usize,
) -> Step<RdfLiteral> {
    let (lexical, end) = string(bytes, start, limit)?;
    let (kind, next) = literal_kind(bytes, end, base, prefixes, limit)?;
    Ok((RdfLiteral { lexical, kind }, next))
}

/// Whether `byte` is an ASCII digit.
fn digit_byte(byte: u8) -> bool {
    48 <= byte && byte <= 57
}

/// The end of the ASCII digits from `index`.
fn digits_end(bytes: &Vec<u8>, index: usize) -> usize {
    if index < bytes.len() {
        if digit_byte(bytes[index]) {
            digits_end(bytes, index + 1)
        } else {
            index
        }
    } else {
        index
    }
}

/// Whether `bytes[index]` is `+` or `-`.
fn sign_at(bytes: &Vec<u8>, index: usize) -> bool {
    byte_is(bytes, index, 43) || byte_is(bytes, index, 45)
}

/// Whether `bytes[index]` is `e` or `E`.
fn exponent_at(bytes: &Vec<u8>, index: usize) -> bool {
    byte_is(bytes, index, 101) || byte_is(bytes, index, 69)
}

/// The position after the optional sign at `index`.
fn unsigned(bytes: &Vec<u8>, index: usize) -> usize {
    if sign_at(bytes, index) {
        index + 1
    } else {
        index
    }
}

/// The end of the digits of an EXPONENT whose `e` is at `index`.
fn exponent_digits(bytes: &Vec<u8>, index: usize) -> Option<usize> {
    let digits = unsigned(bytes, index + 1);
    let end = digits_end(bytes, digits);
    if digits < end {
        Some(end)
    } else {
        None
    }
}

/// The end of the EXPONENT `[eE] [+-]? [0-9]+` at `index`, if one is there.
fn exponent_end(bytes: &Vec<u8>, index: usize) -> Option<usize> {
    if exponent_at(bytes, index) {
        exponent_digits(bytes, index)
    } else {
        None
    }
}

/// INTEGER, DECIMAL or DOUBLE.
enum Number {
    Integer,
    Decimal,
    Double,
}

/// The number `plain` ending at `end`, or the DOUBLE with an EXPONENT at `end`.
fn with_exponent(bytes: &Vec<u8>, end: usize, plain: Number) -> (usize, Number) {
    match exponent_end(bytes, end) {
        Some(after) => (after, Number::Double),
        None => (end, plain),
    }
}

/// The longest number whose integer digits are `digits..point`, where
/// `bytes[point]` is `.`.
fn fraction(bytes: &Vec<u8>, digits: usize, point: usize) -> Option<(usize, Number)> {
    let end = digits_end(bytes, point + 1);
    if point + 1 < end {
        Some(with_exponent(bytes, end, Number::Decimal))
    } else if digits < point {
        match exponent_end(bytes, point + 1) {
            Some(after) => Some((after, Number::Double)),
            None => Some((point, Number::Integer)),
        }
    } else {
        None
    }
}

/// The longest INTEGER, DECIMAL or DOUBLE at `start`, if any.
fn number_end(bytes: &Vec<u8>, start: usize) -> Option<(usize, Number)> {
    let digits = unsigned(bytes, start);
    let point = digits_end(bytes, digits);
    if byte_is(bytes, point, 46) {
        fraction(bytes, digits, point)
    } else if digits < point {
        Some(with_exponent(bytes, point, Number::Integer))
    } else {
        None
    }
}

/// The NumericLiteral at `start`, with its lexical form as written.
fn number(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<RdfLiteral> {
    match number_end(bytes, start) {
        Some((end, kind)) => {
            let lexical = copied(bytes, start, end, limit)?;
            let kind = match kind {
                Number::Integer => xsd(b"http://www.w3.org/2001/XMLSchema#integer"),
                Number::Decimal => xsd(b"http://www.w3.org/2001/XMLSchema#decimal"),
                Number::Double => xsd(b"http://www.w3.org/2001/XMLSchema#double"),
            };
            Ok((RdfLiteral { lexical, kind }, end))
        }
        None => Err(error(ErrorKind::ExpectedObject, start)),
    }
}

/// Whether the bytes at `start` are `word`.
fn word_at(bytes: &Vec<u8>, start: usize, word: &[u8]) -> bool {
    start <= bytes.len() && word.len() <= bytes.len() - start && word_from(bytes, start, word, 0)
}

fn word_from(bytes: &Vec<u8>, start: usize, word: &[u8], index: usize) -> bool {
    if index < word.len() {
        if bytes[start + index] == word[index] {
            word_from(bytes, start, word, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether `bytes[index]` is `upper` or `lower`.
fn either(bytes: &Vec<u8>, index: usize, upper: u8, lower: u8) -> bool {
    byte_is(bytes, index, upper) || byte_is(bytes, index, lower)
}

/// Whether `PREFIX` in any case is at `start`.
fn prefix_word(bytes: &Vec<u8>, start: usize) -> bool {
    either(bytes, start, 80, 112)
        && either(bytes, start + 1, 82, 114)
        && either(bytes, start + 2, 69, 101)
        && either(bytes, start + 3, 70, 102)
        && either(bytes, start + 4, 73, 105)
        && either(bytes, start + 5, 88, 120)
}

/// Whether `BASE` in any case is at `start`.
fn base_word(bytes: &Vec<u8>, start: usize) -> bool {
    either(bytes, start, 66, 98)
        && either(bytes, start + 1, 65, 97)
        && either(bytes, start + 2, 83, 115)
        && either(bytes, start + 3, 69, 101)
}

/// Whether `byte` is an ASCII letter.
fn letter_byte(byte: u8) -> bool {
    (65 <= byte && byte <= 90) || (97 <= byte && byte <= 122)
}

/// Whether `byte` continues a LANGTAG: an ASCII letter, digit or `-`.
fn tag_byte(byte: u8) -> bool {
    letter_byte(byte) || digit_byte(byte) || byte == 45
}

/// Whether a LANGTAG continues at `index`.
fn tag_continues(bytes: &Vec<u8>, index: usize) -> bool {
    index < bytes.len() && tag_byte(bytes[index])
}

/// Whether the keyword `@` followed by `word` is at `start` and no longer
/// LANGTAG begins there.
fn at_keyword(bytes: &Vec<u8>, start: usize, word: &[u8]) -> bool {
    byte_is(bytes, start, 64)
        && word_at(bytes, start + 1, word)
        && !tag_continues(bytes, start + 1 + word.len())
}

/// `"` or `'`.
fn quote(cp: u32) -> bool {
    cp == 34 || cp == 39
}

/// A digit, `+`, `-` or `.`.
fn number_start(cp: u32) -> bool {
    ntriples::ascii_digit(cp) || cp == 43 || cp == 45 || cp == 46
}

/// PN_CHARS_BASE or `:`, which begin a prefixed name or a keyword.
fn word_start(cp: u32) -> bool {
    ntriples::pn_base(cp) || cp == 58
}

/// The term a node position begins with.
enum Start {
    Iri,
    Blank,
    Bracket,
    Paren,
    Quote,
    Number,
    Word,
    Other,
}

fn start_of(cp: u32) -> Start {
    if cp == 60 {
        Start::Iri
    } else if cp == 95 {
        Start::Blank
    } else if cp == 91 {
        Start::Bracket
    } else if cp == 40 {
        Start::Paren
    } else if quote(cp) {
        Start::Quote
    } else if number_start(cp) {
        Start::Number
    } else if word_start(cp) {
        Start::Word
    } else {
        Start::Other
    }
}

/// A boolean literal.
fn boolean(lexical: &[u8]) -> RdfLiteral {
    RdfLiteral {
        lexical: constant(lexical),
        kind: xsd(b"http://www.w3.org/2001/XMLSchema#boolean"),
    }
}

/// The keyword `true` or `false` at `start`.
fn boolean_at(bytes: &Vec<u8>, start: usize) -> Step<Object> {
    if word_at(bytes, start, b"true") {
        Ok((Object::Literal(boolean(b"true")), start + 4))
    } else if word_at(bytes, start, b"false") {
        Ok((Object::Literal(boolean(b"false")), start + 5))
    } else {
        Err(error(ErrorKind::ExpectedObject, start))
    }
}

/// The prefixed name, `true` or `false` at `start`.
fn word_object(
    bytes: &Vec<u8>,
    start: usize,
    prefixes: &Vec<Prefix>,
    limit: usize,
) -> Step<Object> {
    match prefix_colon(bytes, start)? {
        Some(colon) => {
            let (iri, next) = prefixed(bytes, start, colon, prefixes, limit)?;
            Ok((Object::Iri(iri), next))
        }
        None => boolean_at(bytes, start),
    }
}

/// The read context: the bytes, the blank node scope, the base, the prefix
/// declarations and the limits.
struct Context<'a> {
    bytes: &'a Vec<u8>,
    scope: &'a Vec<u8>,
    base: &'a Vec<u8>,
    prefixes: &'a Vec<Prefix>,
    limits: &'a Limits,
}

/// The node at `start` that needs no triples: an IRI, a labelled blank node
/// or a literal.
fn term(cx: &Context, start: usize, kind: Start) -> Step<Object> {
    let limit = cx.limits.max_term_bytes;
    match kind {
        Start::Iri => {
            let (iri, next) = iri_ref(cx.bytes, start, cx.base, limit)?;
            Ok((Object::Iri(iri), next))
        }
        Start::Blank => {
            let (node, next) = blank_label(cx.bytes, start, cx.scope, limit)?;
            Ok((Object::Blank(node), next))
        }
        Start::Quote => {
            let (literal, next) = literal(cx.bytes, start, cx.base, cx.prefixes, limit)?;
            Ok((Object::Literal(literal), next))
        }
        Start::Number => {
            let (literal, next) = number(cx.bytes, start, limit)?;
            Ok((Object::Literal(literal), next))
        }
        Start::Word => word_object(cx.bytes, start, cx.prefixes, limit),
        Start::Bracket => Err(error(ErrorKind::ExpectedObject, start)),
        Start::Paren => Err(error(ErrorKind::ExpectedObject, start)),
        Start::Other => Err(error(ErrorKind::ExpectedObject, start)),
    }
}

/// The object node at `start`, after the triples of a property list or
/// collection that it is.
fn node(cx: &Context, start: usize, out: Vec<Triple>) -> Grown<Object> {
    let (cp, _) = needed(cx.bytes, start)?;
    match start_of(cp) {
        Start::Bracket => {
            let (node, next, out, _) = bracket(cx, start, out)?;
            Ok((Object::Blank(node), next, out))
        }
        Start::Paren => {
            let (head, next, out) = collection(cx, start, out)?;
            Ok((object_of(head), next, out))
        }
        other => {
            let (value, next) = term(cx, start, other)?;
            Ok((value, next, out))
        }
    }
}

/// The `[` at `start`: ANON, or a blank node property list whose triples are
/// emitted. Also tells whether there was a property list.
fn bracket(
    cx: &Context,
    start: usize,
    out: Vec<Triple>,
) -> Result<(BlankNode, usize, Vec<Triple>, bool), ReadError> {
    let inside = space(cx.bytes, start + 1)?;
    if byte_is(cx.bytes, inside, 93) {
        Ok((bracket_node(cx.scope, start), inside + 1, out, false))
    } else {
        let subject = Subject::Blank(bracket_node(cx.scope, start));
        let (after, out) = predicate_object_list(cx, inside, &subject, out)?;
        let close = space(cx.bytes, after)?;
        if byte_is(cx.bytes, close, 93) {
            Ok((bracket_node(cx.scope, start), close + 1, out, true))
        } else {
            Err(error(ErrorKind::ExpectedBracket, close))
        }
    }
}

/// The collection at `start`: rdf:nil when empty, and otherwise the list node
/// of its first member, after the triples of every member.
fn collection(cx: &Context, start: usize, out: Vec<Triple>) -> Grown<Subject> {
    let inside = space(cx.bytes, start + 1)?;
    if byte_is(cx.bytes, inside, 41) {
        Ok((Subject::Iri(rdf_nil()), inside + 1, out))
    } else {
        let (after, out) = member(cx, inside, out)?;
        let (end, out) = members(cx, after, inside, out)?;
        Ok((Subject::Blank(list_node(cx.scope, inside)), end, out))
    }
}

/// The collection member at `start`: its object and the triple
/// `node rdf:first object` of the list node of `start`.
fn member(cx: &Context, start: usize, out: Vec<Triple>) -> Emitted {
    let subject = Subject::Blank(list_node(cx.scope, start));
    let predicate = rdf_first();
    object(cx, start, &subject, &predicate, out)
}

/// The members after the one at `last`, up to `)`, each linked by `rdf:rest`
/// to the one before.
fn members(cx: &Context, position: usize, last: usize, out: Vec<Triple>) -> Emitted {
    let next = space(cx.bytes, position)?;
    let link = Subject::Blank(list_node(cx.scope, last));
    if byte_is(cx.bytes, next, 41) {
        let triple = Triple {
            subject: link,
            predicate: rdf_rest(),
            object: Object::Iri(rdf_nil()),
        };
        let out = emit(out, triple, cx.limits, next)?;
        Ok((next + 1, out))
    } else {
        let triple = Triple {
            subject: link,
            predicate: rdf_rest(),
            object: Object::Blank(list_node(cx.scope, next)),
        };
        let out = emit(out, triple, cx.limits, next)?;
        let (after, out) = member(cx, next, out)?;
        members(cx, after, next, out)
    }
}

/// An object at `position`: its node and the triple `subject predicate node`.
fn object(
    cx: &Context,
    position: usize,
    subject: &Subject,
    predicate: &RdfIri,
    out: Vec<Triple>,
) -> Emitted {
    let start = space(cx.bytes, position)?;
    let (value, next, out) = node(cx, start, out)?;
    let triple = Triple {
        subject: copy_subject(subject),
        predicate: copy_iri(predicate),
        object: value,
    };
    let out = emit(out, triple, cx.limits, start)?;
    Ok((next, out))
}

/// An objectList: objects separated by `,`.
fn object_list(
    cx: &Context,
    position: usize,
    subject: &Subject,
    predicate: &RdfIri,
    out: Vec<Triple>,
) -> Emitted {
    let (next, out) = object(cx, position, subject, predicate, out)?;
    more_objects(cx, next, subject, predicate, out)
}

fn more_objects(
    cx: &Context,
    position: usize,
    subject: &Subject,
    predicate: &RdfIri,
    out: Vec<Triple>,
) -> Emitted {
    let next = space(cx.bytes, position)?;
    if byte_is(cx.bytes, next, 44) {
        let (after, out) = object(cx, next + 1, subject, predicate, out)?;
        more_objects(cx, after, subject, predicate, out)
    } else {
        Ok((next, out))
    }
}

/// The keyword `a` whose unit `cp` at `start` ends at `next`.
fn keyword_a(cp: u32, start: usize, next: usize) -> Step<RdfIri> {
    if cp == 97 {
        Ok((rdf_type(), next))
    } else {
        Err(error(ErrorKind::ExpectedVerb, start))
    }
}

/// The verb at `position`: an iri, or `a` for rdf:type.
fn verb(cx: &Context, position: usize) -> Step<RdfIri> {
    let start = space(cx.bytes, position)?;
    let (cp, next) = needed(cx.bytes, start)?;
    if cp == 60 {
        iri_ref(cx.bytes, start, cx.base, cx.limits.max_term_bytes)
    } else if word_start(cp) {
        match prefix_colon(cx.bytes, start)? {
            Some(colon) => prefixed(
                cx.bytes,
                start,
                colon,
                cx.prefixes,
                cx.limits.max_term_bytes,
            ),
            None => keyword_a(cp, start, next),
        }
    } else {
        Err(error(ErrorKind::ExpectedVerb, start))
    }
}

/// Whether a verb must follow `;` at `index`: anything but the end, `;`, `.`
/// and `]`.
fn verb_follows(bytes: &Vec<u8>, index: usize) -> bool {
    index < bytes.len() && bytes[index] != 59 && bytes[index] != 46 && bytes[index] != 93
}

/// A predicateObjectList with the subject `subject`.
fn predicate_object_list(
    cx: &Context,
    position: usize,
    subject: &Subject,
    out: Vec<Triple>,
) -> Emitted {
    let (predicate, next) = verb(cx, position)?;
    let (after, out) = object_list(cx, next, subject, &predicate, out)?;
    more_predicates(cx, after, subject, out)
}

fn more_predicates(cx: &Context, position: usize, subject: &Subject, out: Vec<Triple>) -> Emitted {
    let next = space(cx.bytes, position)?;
    if byte_is(cx.bytes, next, 59) {
        let after = space(cx.bytes, next + 1)?;
        if verb_follows(cx.bytes, after) {
            let (predicate, objects) = verb(cx, after)?;
            let (end, out) = object_list(cx, objects, subject, &predicate, out)?;
            more_predicates(cx, end, subject, out)
        } else {
            more_predicates(cx, after, subject, out)
        }
    } else {
        Ok((next, out))
    }
}

/// The subject at `start` of a triples statement that does not begin with `[`.
fn subject(cx: &Context, start: usize, out: Vec<Triple>) -> Grown<Subject> {
    let (cp, _) = needed(cx.bytes, start)?;
    let limit = cx.limits.max_term_bytes;
    match start_of(cp) {
        Start::Iri => {
            let (iri, next) = iri_ref(cx.bytes, start, cx.base, limit)?;
            Ok((Subject::Iri(iri), next, out))
        }
        Start::Blank => {
            let (node, next) = blank_label(cx.bytes, start, cx.scope, limit)?;
            Ok((Subject::Blank(node), next, out))
        }
        Start::Paren => collection(cx, start, out),
        Start::Word => match prefix_colon(cx.bytes, start)? {
            Some(colon) => {
                let (iri, next) = prefixed(cx.bytes, start, colon, cx.prefixes, limit)?;
                Ok((Subject::Iri(iri), next, out))
            }
            None => Err(error(ErrorKind::ExpectedSubject, start)),
        },
        _ => Err(error(ErrorKind::ExpectedSubject, start)),
    }
}

/// The predicateObjectList that may follow a blank node property list
/// subject: none when `.` follows.
fn optional_list(cx: &Context, position: usize, subject: &Subject, out: Vec<Triple>) -> Emitted {
    let next = space(cx.bytes, position)?;
    if byte_is(cx.bytes, next, 46) {
        Ok((next, out))
    } else {
        predicate_object_list(cx, next, subject, out)
    }
}

/// The triples statement at `start`, before its `.`.
fn triples(cx: &Context, start: usize, out: Vec<Triple>) -> Emitted {
    if byte_is(cx.bytes, start, 91) {
        let (node, next, out, listed) = bracket(cx, start, out)?;
        let subject = Subject::Blank(node);
        if listed {
            optional_list(cx, next, &subject, out)
        } else {
            predicate_object_list(cx, next, &subject, out)
        }
    } else {
        let (subject, next, out) = subject(cx, start, out)?;
        predicate_object_list(cx, next, &subject, out)
    }
}

/// The position after the `.` that ends a statement, after white space.
fn period(bytes: &Vec<u8>, position: usize) -> Result<usize, ReadError> {
    let next = space(bytes, position)?;
    if byte_is(bytes, next, 46) {
        Ok(next + 1)
    } else {
        Err(error(ErrorKind::ExpectedPeriod, next))
    }
}

/// How a statement begins, with the position after its keyword.
enum Statement {
    AtPrefix(usize),
    AtBase(usize),
    Prefix(usize),
    Base(usize),
    Triples,
}

/// The SPARQL keyword `keyword` at `start`, unless a longer PNAME_NS begins
/// there.
fn sparql(bytes: &Vec<u8>, start: usize, keyword: Statement) -> Result<Statement, ReadError> {
    match prefix_colon(bytes, start)? {
        Some(_) => Ok(Statement::Triples),
        None => Ok(keyword),
    }
}

fn statement_start(bytes: &Vec<u8>, start: usize) -> Result<Statement, ReadError> {
    if at_keyword(bytes, start, b"prefix") {
        Ok(Statement::AtPrefix(start + 7))
    } else if at_keyword(bytes, start, b"base") {
        Ok(Statement::AtBase(start + 5))
    } else if prefix_word(bytes, start) {
        sparql(bytes, start, Statement::Prefix(start + 6))
    } else if base_word(bytes, start) {
        sparql(bytes, start, Statement::Base(start + 4))
    } else {
        Ok(Statement::Triples)
    }
}

/// The PNAME_NS after white space at `position`: the prefix name and the
/// position after its `:`.
fn prefix_name(bytes: &Vec<u8>, position: usize, limit: usize) -> Step<Vec<u8>> {
    let start = space(bytes, position)?;
    match prefix_colon(bytes, start)? {
        Some(colon) => {
            let name = copied(bytes, start, colon, limit)?;
            Ok((name, colon + 1))
        }
        None => Err(error(ErrorKind::ExpectedPrefix, start)),
    }
}

/// The prefix declaration whose name follows its keyword at `position`.
fn prefix_declaration(
    bytes: &Vec<u8>,
    position: usize,
    base: &Vec<u8>,
    limit: usize,
) -> Step<Prefix> {
    let (name, after) = prefix_name(bytes, position, limit)?;
    let start = space(bytes, after)?;
    let (namespace, next) = iri_ref(bytes, start, base, limit)?;
    Ok((
        Prefix {
            name,
            iri: namespace.spelling,
        },
        next,
    ))
}

/// The base declaration whose IRIREF follows its keyword at `position`.
fn base_declaration(
    bytes: &Vec<u8>,
    position: usize,
    base: &Vec<u8>,
    limit: usize,
) -> Step<Vec<u8>> {
    let start = space(bytes, position)?;
    let (iri, next) = iri_ref(bytes, start, base, limit)?;
    Ok((iri.spelling, next))
}

/// The base, the prefix declarations and the triples read so far.
struct State {
    base: Vec<u8>,
    prefixes: Vec<Prefix>,
    triples: Vec<Triple>,
}

fn declare(mut prefixes: Vec<Prefix>, prefix: Prefix) -> Vec<Prefix> {
    prefixes.push(prefix);
    prefixes
}

/// The statement at `start` and the position after it.
fn statement(
    bytes: &Vec<u8>,
    scope: &Vec<u8>,
    limits: &Limits,
    start: usize,
    state: State,
) -> Result<(usize, State), ReadError> {
    let State {
        base,
        prefixes,
        triples: out,
    } = state;
    let limit = limits.max_term_bytes;
    match statement_start(bytes, start)? {
        Statement::AtPrefix(after) => {
            let (prefix, next) = prefix_declaration(bytes, after, &base, limit)?;
            let end = period(bytes, next)?;
            let prefixes = declare(prefixes, prefix);
            Ok((
                end,
                State {
                    base,
                    prefixes,
                    triples: out,
                },
            ))
        }
        Statement::AtBase(after) => {
            let (base, next) = base_declaration(bytes, after, &base, limit)?;
            let end = period(bytes, next)?;
            Ok((
                end,
                State {
                    base,
                    prefixes,
                    triples: out,
                },
            ))
        }
        Statement::Prefix(after) => {
            let (prefix, end) = prefix_declaration(bytes, after, &base, limit)?;
            let prefixes = declare(prefixes, prefix);
            Ok((
                end,
                State {
                    base,
                    prefixes,
                    triples: out,
                },
            ))
        }
        Statement::Base(after) => {
            let (base, end) = base_declaration(bytes, after, &base, limit)?;
            Ok((
                end,
                State {
                    base,
                    prefixes,
                    triples: out,
                },
            ))
        }
        Statement::Triples => {
            let cx = Context {
                bytes,
                scope,
                base: &base,
                prefixes: &prefixes,
                limits,
            };
            let (after, out) = triples(&cx, start, out)?;
            let end = period(bytes, after)?;
            Ok((
                end,
                State {
                    base,
                    prefixes,
                    triples: out,
                },
            ))
        }
    }
}

/// The statements from `position` to the end of the document.
fn statements(
    bytes: &Vec<u8>,
    scope: &Vec<u8>,
    limits: &Limits,
    position: usize,
    state: State,
) -> Result<Vec<Triple>, ReadError> {
    let start = space(bytes, position)?;
    if start < bytes.len() {
        let (end, state) = statement(bytes, scope, limits, start, state)?;
        statements(bytes, scope, limits, end, state)
    } else {
        Ok(state.triples)
    }
}

/// Read a whole Turtle document against the base IRI `base` within explicit
/// limits. A caller-supplied immutable scope gives equal labels one identity
/// and must differ across independent documents; the blank nodes without a
/// label get the same scope.
pub fn read_with_limits(
    bytes: &Vec<u8>,
    scope: &Vec<u8>,
    base: &Vec<u8>,
    limits: &Limits,
) -> ReadResult {
    let state = State {
        base: copy_bytes(base),
        prefixes: Vec::new(),
        triples: Vec::new(),
    };
    match statements(bytes, scope, limits, 0, state) {
        Ok(triples) => ReadResult::Graph(RawGraph { triples }),
        Err(e) => ReadResult::Error(e),
    }
}

/// Read a whole Turtle document with no limits beyond the input itself.
pub fn read(bytes: &Vec<u8>, scope: &Vec<u8>, base: &Vec<u8>) -> ReadResult {
    read_with_limits(
        bytes,
        scope,
        base,
        &Limits {
            max_term_bytes: usize::MAX,
            max_triples: usize::MAX,
        },
    )
}

pub use crate::rdf_write::{WriteError, WriteResult};

/// Write `graph` as Turtle within `max_output_bytes` bytes: every triple on a
/// line of its own, IRIs as IRIREFs and blank nodes with labels that encode
/// their scope and label (see `rdf_write`). A graph with a term this form
/// cannot carry, such as an IRI that the resolution of IRIREFs would change,
/// is reported with its first such term.
pub fn write(graph: &RawGraph, max_output_bytes: usize) -> WriteResult {
    crate::rdf_write::write_graph(graph, true, max_output_bytes)
}
