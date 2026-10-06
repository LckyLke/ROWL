//! RFC 3986 section 5.2 reference resolution on UTF-8 IRI bytes.
//!
//! A reference and its base are split into scheme, authority, path, query and
//! fragment by the regular expression of RFC 3986 Appendix B, which inspects
//! only the ASCII delimiters `:`, `/`, `?` and `#`. The reference is then
//! transformed by the strict algorithm of section 5.2.2, merging paths as in
//! section 5.2.3, removing dot segments as in section 5.2.4 and recomposing the
//! components as in section 5.3. No normalization is performed. The algorithm
//! looks only at ASCII characters, so it applies unchanged to the UTF-8 bytes
//! of IRIs (RFC 3987 section 6.5); `References.lean` proves that it commutes
//! with UTF-8 encoding.
//!
//! Every condition below is a single comparison or call: a chain of `&&` or
//! `||` lives in its own small helper, which keeps the extraction small. The
//! step classifier keeps one rule per RFC case even where two cases act alike,
//! and options are matched explicitly rather than through `Option::map`.
#![allow(clippy::ptr_arg, clippy::if_same_then_else, clippy::manual_map)]

use crate::iri::{validate_iri, validate_reference};
use crate::regular::MatchResult;

/// The bytes `start..end` of a buffer.
#[derive(Clone, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// The five components of RFC 3986 Appendix B, without their delimiters; an
/// undefined component is `None`. The path is always defined, possibly empty.
#[derive(Clone, Copy)]
pub struct Parts {
    pub scheme: Option<Span>,
    pub authority: Option<Span>,
    pub path: Span,
    pub query: Option<Span>,
    pub fragment: Option<Span>,
}

/// Whether `byte` ends a component at `level`: `#` ends a query (level 0),
/// `?` or `#` a path (1), `/`, `?` or `#` an authority (2) and `:`, `/`, `?`
/// or `#` a scheme (3).
fn stops(level: u8, byte: u8) -> bool {
    byte == 35
        || (0 < level && byte == 63)
        || (1 < level && byte == 47)
        || (2 < level && byte == 58)
}

/// The first index from `index` whose byte ends a component at `level`, or
/// the length.
fn scan(bytes: &Vec<u8>, index: usize, level: u8) -> usize {
    if index < bytes.len() {
        if stops(level, bytes[index]) {
            index
        } else {
            scan(bytes, index + 1, level)
        }
    } else {
        index
    }
}

/// Whether `bytes[index]` exists and is `value`.
fn byte_is(bytes: &Vec<u8>, index: usize, value: u8) -> bool {
    index < bytes.len() && bytes[index] == value
}

/// Whether a scheme of at least one byte ends at `colon`.
fn scheme_ends(bytes: &Vec<u8>, colon: usize) -> bool {
    0 < colon && byte_is(bytes, colon, 58)
}

/// Whether `bytes[index..]` begins with `//`.
fn double_slash(bytes: &Vec<u8>, index: usize) -> bool {
    byte_is(bytes, index, 47) && byte_is(bytes, index + 1, 47)
}

/// The components of `bytes` by the regular expression of RFC 3986 Appendix B,
/// `^(([^:/?#]+):)?(//([^/?#]*))?([^?#]*)(\?([^#]*))?(#(.*))?`.
pub fn split(bytes: &Vec<u8>) -> Parts {
    let colon = scan(bytes, 0, 3);
    let has_scheme = scheme_ends(bytes, colon);
    let start = if has_scheme { colon + 1 } else { 0 };
    let has_authority = double_slash(bytes, start);
    let path_start = if has_authority {
        scan(bytes, start + 2, 2)
    } else {
        start
    };
    let path_end = scan(bytes, path_start, 1);
    let has_query = byte_is(bytes, path_end, 63);
    let query_end = if has_query {
        scan(bytes, path_end + 1, 0)
    } else {
        path_end
    };
    let has_fragment = query_end < bytes.len();
    Parts {
        scheme: if has_scheme {
            Some(Span {
                start: 0,
                end: colon,
            })
        } else {
            None
        },
        authority: if has_authority {
            Some(Span {
                start: start + 2,
                end: path_start,
            })
        } else {
            None
        },
        path: Span {
            start: path_start,
            end: path_end,
        },
        query: if has_query {
            Some(Span {
                start: path_end + 1,
                end: query_end,
            })
        } else {
            None
        },
        fragment: if has_fragment {
            Some(Span {
                start: query_end + 1,
                end: bytes.len(),
            })
        } else {
            None
        },
    }
}

/// Whether `index` lies before `end` and inside `bytes`.
fn before(bytes: &Vec<u8>, index: usize, end: usize) -> bool {
    index < end && index < bytes.len()
}

/// `out` followed by `bytes[index..end]`.
fn append(bytes: &Vec<u8>, index: usize, end: usize, mut out: Vec<u8>) -> Vec<u8> {
    if before(bytes, index, end) {
        out.push(bytes[index]);
        append(bytes, index + 1, end, out)
    } else {
        out
    }
}

/// `out` followed by `byte`.
fn put(mut out: Vec<u8>, byte: u8) -> Vec<u8> {
    out.push(byte);
    out
}

/// Whether `bytes[index]` lies before `end` and is `value`.
fn at(bytes: &Vec<u8>, index: usize, end: usize, value: u8) -> bool {
    index < end && byte_is(bytes, index, value)
}

/// Whether `bytes[index..end]` begins with the two bytes `a`, `b`.
fn starts2(bytes: &Vec<u8>, index: usize, end: usize, a: u8, b: u8) -> bool {
    at(bytes, index, end, a) && at(bytes, index + 1, end, b)
}

/// Whether `bytes[index..end]` begins with the three bytes `a`, `b`, `c`.
fn starts3(bytes: &Vec<u8>, index: usize, end: usize, a: u8, b: u8, c: u8) -> bool {
    starts2(bytes, index, end, a, b) && at(bytes, index + 2, end, c)
}

/// Whether `bytes[index..end]` begins with the four bytes `a`, `b`, `c`, `d`.
fn starts4(bytes: &Vec<u8>, index: usize, end: usize, a: u8, b: u8, c: u8, d: u8) -> bool {
    starts3(bytes, index, end, a, b, c) && at(bytes, index + 3, end, d)
}

/// Whether `bytes[index..end]` is the byte `a`.
fn is1(bytes: &Vec<u8>, index: usize, end: usize, a: u8) -> bool {
    at(bytes, index, end, a) && index + 1 == end
}

/// Whether `bytes[index..end]` is the two bytes `a`, `b`.
fn is2(bytes: &Vec<u8>, index: usize, end: usize, a: u8, b: u8) -> bool {
    starts2(bytes, index, end, a, b) && index + 2 == end
}

/// Whether `bytes[index..end]` is the three bytes `a`, `b`, `c`.
fn is3(bytes: &Vec<u8>, index: usize, end: usize, a: u8, b: u8, c: u8) -> bool {
    starts3(bytes, index, end, a, b, c) && index + 3 == end
}

/// Whether the input buffer `bytes[index..end]` is empty.
fn exhausted(bytes: &Vec<u8>, index: usize, end: usize) -> bool {
    end <= index || bytes.len() < end
}

/// Whether `bytes[index]` lies before `end` and is not `/`.
fn inside_segment(bytes: &Vec<u8>, index: usize, end: usize) -> bool {
    before(bytes, index, end) && bytes[index] != 47
}

/// The first index from `index` before `end` whose byte is `/`, or `end`.
fn segment_end(bytes: &Vec<u8>, index: usize, end: usize) -> usize {
    if inside_segment(bytes, index, end) {
        segment_end(bytes, index + 1, end)
    } else {
        index
    }
}

/// Whether `bytes[start..index]` is nonempty and inside `bytes`.
fn searching(bytes: &Vec<u8>, start: usize, index: usize) -> bool {
    start < index && index <= bytes.len()
}

/// The position of the last `/` in `bytes[start..index]`.
fn last_slash(bytes: &Vec<u8>, start: usize, index: usize) -> Option<usize> {
    if searching(bytes, start, index) {
        if bytes[index - 1] == 47 {
            Some(index - 1)
        } else {
            last_slash(bytes, start, index - 1)
        }
    } else {
        None
    }
}

/// The output buffer without its last segment and the `/` before it, as rule
/// 2C of RFC 3986 section 5.2.4 removes them.
fn pop_segment(out: &Vec<u8>) -> Vec<u8> {
    match last_slash(out, 0, out.len()) {
        Some(slash) => append(out, 0, slash, Vec::new()),
        None => Vec::new(),
    }
}

/// The step of RFC 3986 section 5.2.4 that applies to an input buffer.
enum Step {
    /// The input buffer is empty: the output buffer is the result.
    Finish,
    /// 2A: remove a leading `../`.
    RemoveParent,
    /// 2A: remove a leading `./`.
    RemoveCurrent,
    /// 2B: replace a leading `/./` by `/`.
    SkipCurrent,
    /// 2B: replace a final `/.` by `/`.
    FinalCurrent,
    /// 2C: replace a leading `/../` by `/` and remove the last output segment.
    SkipParent,
    /// 2C: replace a final `/..` by `/` and remove the last output segment.
    FinalParent,
    /// 2D: the input buffer is `.` or `..`.
    DropDots,
    /// 2E: move the first segment, with its leading `/` if any.
    MoveSegment,
}

/// The step that applies to the input buffer `bytes[index..end]`.
fn step(bytes: &Vec<u8>, index: usize, end: usize) -> Step {
    if exhausted(bytes, index, end) {
        Step::Finish
    } else if starts3(bytes, index, end, 46, 46, 47) {
        Step::RemoveParent
    } else if starts2(bytes, index, end, 46, 47) {
        Step::RemoveCurrent
    } else if starts3(bytes, index, end, 47, 46, 47) {
        Step::SkipCurrent
    } else if is2(bytes, index, end, 47, 46) {
        Step::FinalCurrent
    } else if starts4(bytes, index, end, 47, 46, 46, 47) {
        Step::SkipParent
    } else if is3(bytes, index, end, 47, 46, 46) {
        Step::FinalParent
    } else if is1(bytes, index, end, 46) {
        Step::DropDots
    } else if is2(bytes, index, end, 46, 46) {
        Step::DropDots
    } else {
        Step::MoveSegment
    }
}

/// RFC 3986 section 5.2.4: removes the dot segments of the input buffer
/// `bytes[index..end]`, moving the remaining segments to the output buffer.
/// A replacement of a leading `/./` or `/../` by `/` moves `index` onto the
/// final `/` of the prefix; a final `/.` or `/..` becomes `/`, which step 2E
/// then moves to the output buffer.
fn remove_dots(bytes: &Vec<u8>, index: usize, end: usize, out: Vec<u8>) -> Vec<u8> {
    match step(bytes, index, end) {
        Step::Finish => out,
        Step::RemoveParent => remove_dots(bytes, index + 3, end, out),
        Step::RemoveCurrent => remove_dots(bytes, index + 2, end, out),
        Step::SkipCurrent => remove_dots(bytes, index + 2, end, out),
        Step::FinalCurrent => put(out, 47),
        Step::SkipParent => remove_dots(bytes, index + 3, end, pop_segment(&out)),
        Step::FinalParent => put(pop_segment(&out), 47),
        Step::DropDots => out,
        Step::MoveSegment => {
            let stop = segment_end(bytes, index + 1, end);
            remove_dots(bytes, stop, end, append(bytes, index, stop, out))
        }
    }
}

/// `out` followed by `before` and `bytes[span]` when the component is defined.
fn component(bytes: &Vec<u8>, span: Option<Span>, before: u8, out: Vec<u8>) -> Vec<u8> {
    match span {
        Some(span) => append(bytes, span.start, span.end, put(out, before)),
        None => out,
    }
}

/// `out` followed by `//` and the authority when it is defined.
fn authority(bytes: &Vec<u8>, span: Option<Span>, out: Vec<u8>) -> Vec<u8> {
    match span {
        Some(span) => append(bytes, span.start, span.end, put(put(out, 47), 47)),
        None => out,
    }
}

/// Whether the base has an authority and an empty path.
fn bare_authority(b: Parts) -> bool {
    b.authority.is_some() && b.path.end <= b.path.start
}

/// RFC 3986 section 5.2.3: the reference path appended to all but the last
/// segment of the base path, or to `/` when the base has an authority and an
/// empty path.
fn merge(base: &Vec<u8>, b: Parts, reference: &Vec<u8>, path: Span) -> Vec<u8> {
    let directory = if bare_authority(b) {
        put(Vec::new(), 47)
    } else {
        match last_slash(base, b.path.start, b.path.end) {
            Some(slash) => append(base, b.path.start, slash + 1, Vec::new()),
            None => Vec::new(),
        }
    };
    append(reference, path.start, path.end, directory)
}

/// `out` followed by the path `bytes[span]` with its dot segments removed.
fn clean_path(bytes: &Vec<u8>, span: Span, out: Vec<u8>) -> Vec<u8> {
    let path = remove_dots(bytes, span.start, span.end, Vec::new());
    append(&path, 0, path.len(), out)
}

/// The target of RFC 3986 section 5.2.2 for a reference without a scheme or
/// authority, from the base authority on.
fn relative_path(base: &Vec<u8>, b: Parts, reference: &Vec<u8>, r: Parts, out: Vec<u8>) -> Vec<u8> {
    let out = authority(base, b.authority, out);
    if r.path.end <= r.path.start {
        let out = append(base, b.path.start, b.path.end, out);
        if r.query.is_some() {
            component(reference, r.query, 63, out)
        } else {
            component(base, b.query, 63, out)
        }
    } else if byte_is(reference, r.path.start, 47) {
        let out = clean_path(reference, r.path, out);
        component(reference, r.query, 63, out)
    } else {
        let merged = merge(base, b, reference, r.path);
        let out = clean_path(
            &merged,
            Span {
                start: 0,
                end: merged.len(),
            },
            out,
        );
        component(reference, r.query, 63, out)
    }
}

/// The target of RFC 3986 section 5.2.2 for a reference with a scheme, which
/// does not depend on the base, recomposed as in section 5.3.
fn absolute(reference: &Vec<u8>, own: Span, r: Parts) -> Vec<u8> {
    let out = put(append(reference, own.start, own.end, Vec::new()), 58);
    let out = authority(reference, r.authority, out);
    let out = clean_path(reference, r.path, out);
    let out = component(reference, r.query, 63, out);
    component(reference, r.fragment, 35, out)
}

/// The target of RFC 3986 section 5.2.2 for a reference without a scheme
/// against a base with a scheme, recomposed as in section 5.3.
fn relative(base: &Vec<u8>, b: Parts, scheme: Span, reference: &Vec<u8>, r: Parts) -> Vec<u8> {
    let out = put(append(base, scheme.start, scheme.end, Vec::new()), 58);
    let out = if r.authority.is_some() {
        let out = authority(reference, r.authority, out);
        let out = clean_path(reference, r.path, out);
        component(reference, r.query, 63, out)
    } else {
        relative_path(base, b, reference, r, out)
    };
    component(reference, r.fragment, 35, out)
}

/// Whether both inputs have fewer than `usize::MAX / 8` bytes, so that every
/// buffer the resolution builds fits.
fn small(base: &Vec<u8>, reference: &Vec<u8>) -> bool {
    base.len() < usize::MAX / 8 && reference.len() < usize::MAX / 8
}

/// Resolve `reference` against `base` by RFC 3986 section 5.2. A reference
/// with a scheme needs no base; `None` when neither has a scheme, or when
/// either input has `usize::MAX / 8` bytes or more.
pub fn resolve(base: &Vec<u8>, reference: &Vec<u8>) -> Option<Vec<u8>> {
    if small(base, reference) {
        let r = split(reference);
        match r.scheme {
            Some(own) => Some(absolute(reference, own, r)),
            None => {
                let b = split(base);
                match b.scheme {
                    Some(scheme) => Some(relative(base, b, scheme, reference, r)),
                    None => None,
                }
            }
        }
    } else {
        None
    }
}

/// An ASCII letter, digit, `-`, `.`, `_` or `~`.
#[allow(clippy::manual_range_contains)] // RangeInclusive::contains lacks a model in the pinned extraction.
fn plain(byte: u8) -> bool {
    (65 <= byte && byte <= 90)
        || (97 <= byte && byte <= 122)
        || (48 <= byte && byte <= 57)
        || byte == 45
        || byte == 46
        || byte == 95
        || byte == 126
}

/// Whether `bytes[index]` exists and is plain or `/`.
fn path_byte(bytes: &Vec<u8>, index: usize) -> bool {
    index < bytes.len() && (plain(bytes[index]) || bytes[index] == 47)
}

/// The end of the plain bytes and slashes from `index`.
fn plain_end(bytes: &Vec<u8>, index: usize) -> usize {
    if path_byte(bytes, index) {
        plain_end(bytes, index + 1)
    } else {
        index
    }
}

/// Whether `bytes` are plain bytes and slashes, optionally followed by `#` and
/// plain bytes and slashes; such bytes always spell a relative reference.
fn plain_relative(bytes: &Vec<u8>) -> bool {
    let end = plain_end(bytes, 0);
    if end < bytes.len() {
        bytes[end] == 35 && plain_end(bytes, end + 1) == bytes.len()
    } else {
        true
    }
}

/// Whether `bytes` are the UTF-8 spelling of an RFC 3987 IRI reference. Plain
/// relative references and plain IRIs are recognized without the grammar.
pub fn is_reference(bytes: &Vec<u8>) -> bool {
    plain_relative(bytes)
        || matches!(validate_iri(bytes), MatchResult::Matched(true))
        || matches!(validate_reference(bytes), MatchResult::Matched(true))
}
