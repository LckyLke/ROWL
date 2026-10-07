//! XML 1.0 (Fifth Edition) and Namespaces in XML 1.0 (Third Edition) reading,
//! as far as RDF/XML needs it: UTF-8 bytes to the element tree of a document.
//!
//! The bytes are decoded strictly as UTF-8, every character must match `Char`,
//! a leading byte order mark is dropped and line ends are normalized (§2.11).
//! The parser then follows the grammar of the document entity: the XML
//! declaration (its encoding, when given, must be UTF-8), comments, processing
//! instructions, a document type declaration whose internal subset declares
//! entities, elements with attributes, character data, CDATA sections,
//! character references, the predefined entities and internal general
//! entities, whose replacement text is read as content or, in attribute
//! values, normalized as §3.3.3 prescribes. Namespace declarations resolve
//! element and attribute names under every namespace constraint.
//!
//! Declined with a typed error: encodings other than UTF-8, element type,
//! attribute-list and notation declarations and parameter-entity references in
//! the internal subset (an attribute-list declaration would change attribute
//! values), and references to undeclared, external or unparsed entities. Each
//! entity expansion costs one plus the length of its replacement text from a
//! caller-supplied budget, so a document cannot expand without bound.
//!
//! The result keeps what RDF/XML reads (RDF/XML §6): elements with their
//! prefixes, namespace names and local names, attributes with their normalized
//! values, the element's namespace declarations, and children, where every
//! maximal run of characters is one text node; comments and processing
//! instructions give nothing. `Xml.lean` proves that `read` returns the element
//! tree of the unique parse of a document in this grammar, and an error when
//! there is none.
//!
//! Every condition below is a single comparison or call, multi-way decisions
//! go through a classifier and one `match`, and loops are recursive helpers,
//! which keeps the extraction small.
#![allow(clippy::ptr_arg, clippy::manual_range_contains, clippy::len_zero)]
#![allow(clippy::too_many_arguments, clippy::type_complexity)]

use crate::unicode::{decode_next, xml_character, Decoded};

/// Why a document was not read.
#[derive(Clone, Copy)]
pub enum ErrorKind {
    /// The bytes are not UTF-8.
    MalformedUtf8,
    /// A code point outside the XML `Char` production.
    NonXmlCharacter,
    /// The XML declaration names an encoding other than UTF-8.
    UnsupportedEncoding,
    /// The text ends inside a construct.
    UnexpectedEnd,
    /// The text does not match the grammar here.
    Syntax,
    /// No Name, NCName or QName where one is required.
    InvalidName,
    /// An end tag does not match its start tag.
    MismatchedEndTag,
    /// An attribute name or expanded name occurs twice in one tag.
    DuplicateAttribute,
    /// A namespace prefix without a declaration in scope.
    UndeclaredPrefix,
    /// A declaration or use of a reserved prefix or namespace name.
    ReservedNamespace,
    /// A character reference to a code point outside `Char`.
    InvalidCharacterReference,
    /// A reference to an undeclared, external or unparsed entity.
    UndeclaredEntity,
    /// An entity that refers to itself, directly or through others.
    RecursiveEntity,
    /// The content of an entity does not end inside the entity.
    EntityBoundary,
    /// An element type, attribute-list or notation declaration, or a
    /// parameter-entity reference, in the internal subset.
    UnsupportedDeclaration,
    /// The expansion budget or a length limit was exhausted.
    ResourceLimit,
}

/// An error and its offset: a byte offset into the input of `read`.
pub struct XmlError {
    pub kind: ErrorKind,
    pub offset: usize,
}

/// An attribute: its prefix, its namespace name (`None` when it has none),
/// its local name and its normalized value, all as code points.
pub struct Attribute {
    pub ns_prefix: Option<Vec<u32>>,
    pub ns_name: Option<Vec<u32>>,
    pub local_name: Vec<u32>,
    pub value: Vec<u32>,
}

/// A namespace declaration: `xmlns` (no prefix) or `xmlns:prefix`, with the
/// normalized attribute value.
pub struct Binding {
    pub ns_prefix: Option<Vec<u32>>,
    pub value: Vec<u32>,
}

/// A child of an element: an element or a maximal run of characters.
pub enum Node {
    Element(Element),
    Text(Vec<u32>),
}

/// An element: its prefix, namespace name and local name, its attributes in
/// document order (namespace declarations excluded), its own namespace
/// declarations and its children.
pub struct Element {
    pub ns_prefix: Option<Vec<u32>>,
    pub ns_name: Option<Vec<u32>>,
    pub local_name: Vec<u32>,
    pub attributes: Vec<Attribute>,
    pub declarations: Vec<Binding>,
    pub children: Vec<Node>,
}

/// A document: its root element.
pub struct Document {
    pub root: Element,
}

pub enum ReadResult {
    Document(Document),
    Error(XmlError),
}

/// The budget of entity expansions: each costs one plus the length of the
/// entity's replacement text.
pub struct Limits {
    pub expansion: usize,
}

/// The kind of a declared general entity.
#[derive(Clone, Copy)]
pub enum EntityKind {
    Internal,
    External,
    Unparsed,
}

/// A general entity declaration; `text` is the replacement text of an
/// internal entity and empty otherwise.
pub struct Entity {
    pub name: Vec<u32>,
    pub kind: EntityKind,
    pub text: Vec<u32>,
}

fn fail(kind: ErrorKind, offset: usize) -> XmlError {
    XmlError { kind, offset }
}

// ---------------------------------------------------------------------------
// Decoding: strict UTF-8, Char, byte order mark and line ends.

/// Whether the code point at `offset` is a byte order mark to drop.
fn order_mark(offset: usize, codepoint: u32) -> bool {
    (offset == 0) & (codepoint == 0xFEFF)
}

/// Whether a line feed follows a carriage return, which became a line feed.
fn crlf(codepoint: u32, cr: bool) -> bool {
    (codepoint == 10) & cr
}

fn push_char(mut text: Vec<u32>, codepoint: u32, offset: usize) -> Result<Vec<u32>, XmlError> {
    if text.len() < usize::MAX {
        text.push(codepoint);
        Ok(text)
    } else {
        Err(fail(ErrorKind::ResourceLimit, offset))
    }
}

/// Adds one decoded code point, as §2.11 and the byte order mark require.
fn take(chars: Vec<u32>, codepoint: u32, offset: usize, cr: bool) -> Result<Vec<u32>, XmlError> {
    if order_mark(offset, codepoint) {
        Ok(chars)
    } else if codepoint == 13 {
        push_char(chars, 10, offset)
    } else if crlf(codepoint, cr) {
        Ok(chars)
    } else {
        push_char(chars, codepoint, offset)
    }
}

fn decode_from(
    bytes: &Vec<u8>,
    offset: usize,
    chars: Vec<u32>,
    cr: bool,
) -> Result<Vec<u32>, XmlError> {
    match decode_next(bytes, offset) {
        Decoded::End => Ok(chars),
        Decoded::Error(_) => Err(fail(ErrorKind::MalformedUtf8, offset)),
        Decoded::Scalar { codepoint, next } => {
            if xml_character(codepoint) {
                let chars = take(chars, codepoint, offset, cr)?;
                decode_from(bytes, next, chars, codepoint == 13)
            } else {
                Err(fail(ErrorKind::NonXmlCharacter, offset))
            }
        }
    }
}

/// The characters of a UTF-8 document entity, without a leading byte order
/// mark and with every line end normalized to a line feed.
pub fn decode(bytes: &Vec<u8>) -> Result<Vec<u32>, XmlError> {
    decode_from(bytes, 0, Vec::new(), false)
}

/// Whether the code point at `offset` gives a character of the decoded text.
fn emitted(offset: usize, codepoint: u32, cr: bool) -> bool {
    !(order_mark(offset, codepoint) | crlf(codepoint, cr))
}

fn offset_from(bytes: &Vec<u8>, offset: usize, count: usize, index: usize, cr: bool) -> usize {
    match decode_next(bytes, offset) {
        Decoded::Scalar { codepoint, next } => {
            if emitted(offset, codepoint, cr) {
                if count == index {
                    offset
                } else {
                    offset_from(bytes, next, count + 1, index, codepoint == 13)
                }
            } else {
                offset_from(bytes, next, count, index, codepoint == 13)
            }
        }
        _ => offset,
    }
}

/// The byte offset of the decoded character at `index`, for diagnostics.
pub fn byte_offset(bytes: &Vec<u8>, index: usize) -> usize {
    offset_from(bytes, 0, 0, index, false)
}

// ---------------------------------------------------------------------------
// Characters and names.

/// The code point at `i`, or 0, which is no `Char`, past the end.
fn at(cs: &Vec<u32>, i: usize) -> u32 {
    if i < cs.len() {
        cs[i]
    } else {
        0
    }
}

/// [3] S: space, tab, carriage return or line feed.
fn space(c: u32) -> bool {
    (c == 32) | (c == 9) | (c == 13) | (c == 10)
}

/// [4] NameStartChar.
fn name_start(c: u32) -> bool {
    (c == 58)
        | ((c >= 65) & (c <= 90))
        | (c == 95)
        | ((c >= 97) & (c <= 122))
        | ((c >= 0xC0) & (c <= 0xD6))
        | ((c >= 0xD8) & (c <= 0xF6))
        | ((c >= 0xF8) & (c <= 0x2FF))
        | ((c >= 0x370) & (c <= 0x37D))
        | ((c >= 0x37F) & (c <= 0x1FFF))
        | ((c >= 0x200C) & (c <= 0x200D))
        | ((c >= 0x2070) & (c <= 0x218F))
        | ((c >= 0x2C00) & (c <= 0x2FEF))
        | ((c >= 0x3001) & (c <= 0xD7FF))
        | ((c >= 0xF900) & (c <= 0xFDCF))
        | ((c >= 0xFDF0) & (c <= 0xFFFD))
        | ((c >= 0x10000) & (c <= 0xEFFFF))
}

/// [4a] NameChar.
fn name_char(c: u32) -> bool {
    name_start(c)
        | (c == 45)
        | (c == 46)
        | ((c >= 48) & (c <= 57))
        | (c == 0xB7)
        | ((c >= 0x300) & (c <= 0x36F))
        | ((c >= 0x203F) & (c <= 0x2040))
}

/// The first position from `i` that is not white space.
fn skip_spaces(cs: &Vec<u32>, i: usize) -> usize {
    if space(at(cs, i)) {
        skip_spaces(cs, i + 1)
    } else {
        i
    }
}

/// S: at least one white space character; the position after the run.
fn spaces(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    if space(at(cs, i)) {
        Ok(skip_spaces(cs, i + 1))
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

/// The first position from `i` that holds no name character.
fn names_end(cs: &Vec<u32>, i: usize) -> usize {
    if name_char(at(cs, i)) {
        names_end(cs, i + 1)
    } else {
        i
    }
}

/// [5] Name at `i`: its end.
fn name(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    if name_start(at(cs, i)) {
        Ok(names_end(cs, i + 1))
    } else {
        Err(fail(ErrorKind::InvalidName, i))
    }
}

/// The first colon in `cs[i..end]`, or `end`.
fn colon(cs: &Vec<u32>, i: usize, end: usize) -> usize {
    if i < end {
        if at(cs, i) == 58 {
            i
        } else {
            colon(cs, i + 1, end)
        }
    } else {
        end
    }
}

/// Whether the Name `cs[start..end]` with its first colon at `mark` is a
/// PrefixedName: two NCNames around that colon.
fn prefixed(cs: &Vec<u32>, start: usize, mark: usize, end: usize) -> bool {
    (start < mark)
        & (mark + 1 < end)
        & name_start(at(cs, mark + 1))
        & (colon(cs, mark + 1, end) == end)
}

/// A QName at `i`: its end and the position of its colon, which is the end
/// for an unprefixed name.
fn qname(cs: &Vec<u32>, i: usize) -> Result<(usize, usize), XmlError> {
    let end = name(cs, i)?;
    let mark = colon(cs, i, end);
    if mark == end {
        Ok((end, end))
    } else if prefixed(cs, i, mark, end) {
        Ok((end, mark))
    } else {
        Err(fail(ErrorKind::InvalidName, i))
    }
}

/// An NCName at `i`: its end.
fn ncname(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let end = name(cs, i)?;
    if colon(cs, i, end) == end {
        Ok(end)
    } else {
        Err(fail(ErrorKind::InvalidName, i))
    }
}

/// Whether `cs[i..]` begins with `word[k..]`.
fn starts_from(cs: &Vec<u32>, i: usize, word: &[u8], k: usize) -> bool {
    if k < word.len() {
        if i < cs.len() {
            if cs[i] == u32::from(word[k]) {
                starts_from(cs, i + 1, word, k + 1)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether `cs[i..]` begins with the ASCII `word`.
fn starts(cs: &Vec<u32>, i: usize, word: &[u8]) -> bool {
    starts_from(cs, i, word, 0)
}

/// Whether `cs[start..end]` is the ASCII `word`.
fn span_is(cs: &Vec<u32>, start: usize, end: usize, word: &[u8]) -> bool {
    (end - start == word.len()) & starts(cs, start, word)
}

/// Whether the ASCII lower-case letter `lower` is `c` in either case.
fn caseless(c: u32, lower: u32) -> bool {
    (c == lower) | (c == lower - 32)
}

/// Whether the three characters from `start` are `x`, `m`, `l` in any case.
fn xml_letters(cs: &Vec<u32>, start: usize) -> bool {
    caseless(at(cs, start), 120)
        & caseless(at(cs, start + 1), 109)
        & caseless(at(cs, start + 2), 108)
}

/// Whether `cs[start..end]` is `xml` in any case, a reserved PI target.
fn reserved_target(cs: &Vec<u32>, start: usize, end: usize) -> bool {
    if end - start == 3 {
        xml_letters(cs, start)
    } else {
        false
    }
}

/// Whether `cs[a..a+n]` and `cs[b..b+n]` agree from offset `k`.
fn same_from(cs: &Vec<u32>, a: usize, b: usize, n: usize, k: usize) -> bool {
    if k < n {
        if at(cs, a + k) == at(cs, b + k) {
            same_from(cs, a, b, n, k + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether the spans `cs[a..a_end]` and `cs[b..b_end]` are equal.
fn same_span(cs: &Vec<u32>, a: usize, a_end: usize, b: usize, b_end: usize) -> bool {
    if a_end - a == b_end - b {
        same_from(cs, a, b, a_end - a, 0)
    } else {
        false
    }
}

/// Whether `word[k..]` equals `cs[start+k..start+word.len()]`.
fn word_from(word: &Vec<u32>, cs: &Vec<u32>, start: usize, k: usize) -> bool {
    if k < word.len() {
        if word[k] == at(cs, start + k) {
            word_from(word, cs, start, k + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether `word` equals `cs[start..end]`.
fn word_is(word: &Vec<u32>, cs: &Vec<u32>, start: usize, end: usize) -> bool {
    if word.len() == end - start {
        word_from(word, cs, start, 0)
    } else {
        false
    }
}

/// `out` followed by `cs[i..end]`.
fn copy_from(cs: &Vec<u32>, i: usize, end: usize, out: Vec<u32>) -> Result<Vec<u32>, XmlError> {
    if i < end {
        let out = push_char(out, at(cs, i), i)?;
        copy_from(cs, i + 1, end, out)
    } else {
        Ok(out)
    }
}

/// A copy of `cs[start..end]`.
fn copy_span(cs: &Vec<u32>, start: usize, end: usize) -> Result<Vec<u32>, XmlError> {
    copy_from(cs, start, end, Vec::new())
}

/// A copy of a whole buffer.
fn copy_all(word: &Vec<u32>) -> Result<Vec<u32>, XmlError> {
    copy_from(word, 0, word.len(), Vec::new())
}

// ---------------------------------------------------------------------------
// Comments, processing instructions, CDATA sections and character data.

fn comment_body(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let c = at(cs, i);
    if c == 0 {
        Err(fail(ErrorKind::UnexpectedEnd, i))
    } else if c == 45 {
        comment_dash(cs, i)
    } else {
        comment_body(cs, i + 1)
    }
}

/// A `-` at `i` inside a comment: `-->` ends it, another `--` is an error.
fn comment_dash(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    if at(cs, i + 1) == 45 {
        if at(cs, i + 2) == 62 {
            Ok(i + 3)
        } else {
            Err(fail(ErrorKind::Syntax, i))
        }
    } else {
        comment_body(cs, i + 1)
    }
}

/// [15] Comment at `i` (which begins with `<!--`): its end.
fn comment(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    comment_body(cs, i + 4)
}

/// Whether `cs[i..]` begins with `?>`.
fn pi_end(cs: &Vec<u32>, i: usize) -> bool {
    starts(cs, i, b"?>")
}

fn pi_body(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    if at(cs, i) == 0 {
        Err(fail(ErrorKind::UnexpectedEnd, i))
    } else if pi_end(cs, i) {
        Ok(i + 2)
    } else {
        pi_body(cs, i + 1)
    }
}

/// After a PI target ending at `end`: `?>`, or white space and the data.
fn pi_rest(cs: &Vec<u32>, end: usize) -> Result<usize, XmlError> {
    if pi_end(cs, end) {
        Ok(end + 2)
    } else if space(at(cs, end)) {
        pi_body(cs, end + 1)
    } else {
        Err(fail(ErrorKind::Syntax, end))
    }
}

/// [16] PI at `i` (which begins with `<?`): its end. The target is an NCName
/// other than `xml` in any case.
fn pi(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let end = ncname(cs, i + 2)?;
    if reserved_target(cs, i + 2, end) {
        Err(fail(ErrorKind::Syntax, i))
    } else {
        pi_rest(cs, end)
    }
}

/// Whether `cs[i..]` begins with `]]>`.
fn cdata_end(cs: &Vec<u32>, i: usize) -> bool {
    starts(cs, i, b"]]>")
}

fn cdata_body(cs: &Vec<u32>, i: usize, text: Vec<u32>) -> Result<(Vec<u32>, usize), XmlError> {
    if at(cs, i) == 0 {
        Err(fail(ErrorKind::UnexpectedEnd, i))
    } else if cdata_end(cs, i) {
        Ok((text, i + 3))
    } else {
        let text = push_char(text, at(cs, i), i)?;
        cdata_body(cs, i + 1, text)
    }
}

/// [18] CDSect at `i` (which begins with `<![CDATA[`): its characters
/// appended to `text`, and its end.
fn cdata(cs: &Vec<u32>, i: usize, text: Vec<u32>) -> Result<(Vec<u32>, usize), XmlError> {
    cdata_body(cs, i + 9, text)
}

/// Whether `c` ends character data: the end, `<` or `&`.
fn data_stop(c: u32) -> bool {
    (c == 0) | (c == 60) | (c == 38)
}

/// [14] CharData from `i`, which must not contain `]]>`: its characters
/// appended to `text`, and the first position after it.
fn char_data(cs: &Vec<u32>, i: usize, text: Vec<u32>) -> Result<(Vec<u32>, usize), XmlError> {
    if data_stop(at(cs, i)) {
        Ok((text, i))
    } else if cdata_end(cs, i) {
        Err(fail(ErrorKind::Syntax, i))
    } else {
        let text = push_char(text, at(cs, i), i)?;
        char_data(cs, i + 1, text)
    }
}

// ---------------------------------------------------------------------------
// References.

/// A reference: a character (from a character reference or a predefined
/// entity), or the name `cs[start..end]` of another entity.
pub enum Reference {
    Character(u32),
    Entity(usize, usize),
}

fn digit(c: u32) -> bool {
    (c >= 48) & (c <= 57)
}

/// The value of a hexadecimal digit, or 16.
fn hex_value(c: u32) -> u32 {
    if digit(c) {
        c - 48
    } else if (c >= 65) & (c <= 70) {
        c - 55
    } else if (c >= 97) & (c <= 102) {
        c - 87
    } else {
        16
    }
}

/// Decimal digits from `i`, accumulated onto `value`; values beyond U+10FFFF
/// are rejected at once. `start` is the first digit, `origin` the reference.
fn decimal(
    cs: &Vec<u32>,
    i: usize,
    start: usize,
    value: u32,
    origin: usize,
) -> Result<(u32, usize), XmlError> {
    let c = at(cs, i);
    if digit(c) {
        let next = value * 10 + (c - 48);
        if next > 0x10FFFF {
            Err(fail(ErrorKind::InvalidCharacterReference, origin))
        } else {
            decimal(cs, i + 1, start, next, origin)
        }
    } else if i == start {
        Err(fail(ErrorKind::Syntax, origin))
    } else {
        Ok((value, i))
    }
}

/// Hexadecimal digits from `i`, as `decimal`.
fn hexadecimal(
    cs: &Vec<u32>,
    i: usize,
    start: usize,
    value: u32,
    origin: usize,
) -> Result<(u32, usize), XmlError> {
    let d = hex_value(at(cs, i));
    if d < 16 {
        let next = value * 16 + d;
        if next > 0x10FFFF {
            Err(fail(ErrorKind::InvalidCharacterReference, origin))
        } else {
            hexadecimal(cs, i + 1, start, next, origin)
        }
    } else if i == start {
        Err(fail(ErrorKind::Syntax, origin))
    } else {
        Ok((value, i))
    }
}

/// The digits of a character reference at `i` (which begins with `&#`).
fn reference_digits(cs: &Vec<u32>, i: usize) -> Result<(u32, usize), XmlError> {
    if at(cs, i + 2) == 120 {
        hexadecimal(cs, i + 3, i + 3, 0, i)
    } else {
        decimal(cs, i + 2, i + 2, 0, i)
    }
}

/// [66] CharRef at `i`: its character, which must match `Char`, and its end.
fn char_reference(cs: &Vec<u32>, i: usize) -> Result<(u32, usize), XmlError> {
    let (value, j) = reference_digits(cs, i)?;
    if at(cs, j) != 59 {
        Err(fail(ErrorKind::Syntax, j))
    } else if xml_character(value) {
        Ok((value, j + 1))
    } else {
        Err(fail(ErrorKind::InvalidCharacterReference, i))
    }
}

/// The character of a predefined entity named `cs[start..end]`, or 0.
fn predefined(cs: &Vec<u32>, start: usize, end: usize) -> u32 {
    if span_is(cs, start, end, b"lt") {
        60
    } else if span_is(cs, start, end, b"gt") {
        62
    } else if span_is(cs, start, end, b"amp") {
        38
    } else if span_is(cs, start, end, b"apos") {
        39
    } else if span_is(cs, start, end, b"quot") {
        34
    } else {
        0
    }
}

/// [68] EntityRef at `i`: the entity's NCName and the reference's end.
fn entity_name(cs: &Vec<u32>, i: usize) -> Result<(usize, usize), XmlError> {
    let end = ncname(cs, i + 1)?;
    if at(cs, end) == 59 {
        Ok((end, end + 1))
    } else {
        Err(fail(ErrorKind::Syntax, end))
    }
}

/// [67] Reference at `i` (which begins with `&`), in content or in an
/// attribute value: a character or an entity name, and its end.
fn reference(cs: &Vec<u32>, i: usize) -> Result<(Reference, usize), XmlError> {
    if at(cs, i + 1) == 35 {
        let (c, j) = char_reference(cs, i)?;
        Ok((Reference::Character(c), j))
    } else {
        let (end, j) = entity_name(cs, i)?;
        let c = predefined(cs, i + 1, end);
        if c == 0 {
            Ok((Reference::Entity(i + 1, end), j))
        } else {
            Ok((Reference::Character(c), j))
        }
    }
}

// ---------------------------------------------------------------------------
// Entities.

/// The first declaration from `k` of the entity named `cs[start..end]`.
fn find_entity(
    env: &Vec<Entity>,
    cs: &Vec<u32>,
    start: usize,
    end: usize,
    k: usize,
) -> Option<usize> {
    if k < env.len() {
        if word_is(&env[k].name, cs, start, end) {
            Some(k)
        } else {
            find_entity(env, cs, start, end, k + 1)
        }
    } else {
        None
    }
}

/// Whether `k` occurs in `stack[i..]`.
fn on_stack(stack: &Vec<usize>, k: usize, i: usize) -> bool {
    if i < stack.len() {
        if stack[i] == k {
            true
        } else {
            on_stack(stack, k, i + 1)
        }
    } else {
        false
    }
}

/// Whether the declared entity `k` is internal.
fn internal(env: &Vec<Entity>, k: usize) -> bool {
    matches!(env[k].kind, EntityKind::Internal)
}

/// The internal entity named `cs[start..end]` that a reference at `origin`
/// may expand: declared, internal and not already being expanded.
fn expandable(
    cs: &Vec<u32>,
    start: usize,
    end: usize,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    origin: usize,
) -> Result<usize, XmlError> {
    match find_entity(env, cs, start, end, 0) {
        None => Err(fail(ErrorKind::UndeclaredEntity, origin)),
        Some(k) => {
            if !internal(env, k) {
                Err(fail(ErrorKind::UndeclaredEntity, origin))
            } else if on_stack(stack, k, 0) {
                Err(fail(ErrorKind::RecursiveEntity, origin))
            } else {
                Ok(k)
            }
        }
    }
}

/// `stack` followed by `k`.
fn pushed(stack: &Vec<usize>, k: usize, origin: usize) -> Result<Vec<usize>, XmlError> {
    let mut out = copy_stack(stack, 0, Vec::new())?;
    if out.len() < usize::MAX {
        out.push(k);
        Ok(out)
    } else {
        Err(fail(ErrorKind::ResourceLimit, origin))
    }
}

fn copy_stack(stack: &Vec<usize>, i: usize, mut out: Vec<usize>) -> Result<Vec<usize>, XmlError> {
    if i < stack.len() {
        if out.len() < usize::MAX {
            out.push(stack[i]);
            copy_stack(stack, i + 1, out)
        } else {
            Err(fail(ErrorKind::ResourceLimit, 0))
        }
    } else {
        Ok(out)
    }
}

/// The budget left after expanding entity `k`, or an error when it does not
/// cover the cost, one plus the length of the replacement text.
fn spend(env: &Vec<Entity>, k: usize, budget: usize, origin: usize) -> Result<usize, XmlError> {
    let length = env[k].text.len();
    if budget <= length {
        Err(fail(ErrorKind::ResourceLimit, origin))
    } else {
        Ok(budget - length - 1)
    }
}

// ---------------------------------------------------------------------------
// Attribute values (§3.3.3).

/// The normalized form of a literal character in an attribute value.
fn normalized(c: u32) -> u32 {
    if space(c) {
        32
    } else {
        c
    }
}

/// The normalized characters of attribute text from `i` up to the closing
/// `quote`, appended to `out`; a replacement text has `quote` 0 and ends at
/// its end. Returns the position of the quote and the budget left.
fn att_text(
    cs: &Vec<u32>,
    i: usize,
    quote: u32,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    budget: usize,
    out: Vec<u32>,
) -> Result<(Vec<u32>, usize, usize), XmlError> {
    let c = at(cs, i);
    if c == quote {
        Ok((out, i, budget))
    } else if c == 0 {
        Err(fail(ErrorKind::UnexpectedEnd, i))
    } else if c == 60 {
        Err(fail(ErrorKind::Syntax, i))
    } else if c == 38 {
        let (out, j, budget) = att_reference(cs, i, env, stack, budget, out)?;
        att_text(cs, j, quote, env, stack, budget, out)
    } else {
        let out = push_char(out, normalized(c), i)?;
        att_text(cs, i + 1, quote, env, stack, budget, out)
    }
}

/// A reference at `i` in attribute text: a character is appended as it is,
/// an entity's replacement text is normalized recursively.
fn att_reference(
    cs: &Vec<u32>,
    i: usize,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    budget: usize,
    out: Vec<u32>,
) -> Result<(Vec<u32>, usize, usize), XmlError> {
    let (r, j) = reference(cs, i)?;
    match r {
        Reference::Character(c) => {
            let out = push_char(out, c, i)?;
            Ok((out, j, budget))
        }
        Reference::Entity(start, end) => {
            let k = expandable(cs, start, end, env, stack, i)?;
            let left = spend(env, k, budget, i)?;
            let inner = pushed(stack, k, i)?;
            match att_text(&env[k].text, 0, 0, env, &inner, left, out) {
                Ok((out, _, left)) => Ok((out, j, left)),
                Err(e) => Err(fail(e.kind, i)),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Start tags and namespaces.

/// An attribute specification as written: its QName `cs[start..end]` with
/// its colon at `mark` (`end` when unprefixed) and its normalized value.
pub struct Raw {
    pub start: usize,
    pub mark: usize,
    pub stop: usize,
    pub value: Vec<u32>,
}

fn quote(c: u32) -> bool {
    (c == 34) | (c == 39)
}

/// [25] Eq at `i`: the position after it.
fn eq(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let j = skip_spaces(cs, i);
    if at(cs, j) == 61 {
        Ok(skip_spaces(cs, j + 1))
    } else {
        Err(fail(ErrorKind::Syntax, j))
    }
}

/// [41] Attribute at `i`, with its value normalized.
fn attribute(
    cs: &Vec<u32>,
    i: usize,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    budget: usize,
) -> Result<(Raw, usize, usize), XmlError> {
    let (end, mark) = qname(cs, i)?;
    let j = eq(cs, end)?;
    let q = at(cs, j);
    if quote(q) {
        let (value, k, budget) = att_text(cs, j + 1, q, env, stack, budget, Vec::new())?;
        Ok((
            Raw {
                start: i,
                mark,
                stop: end,
                value,
            },
            k + 1,
            budget,
        ))
    } else {
        Err(fail(ErrorKind::Syntax, j))
    }
}

/// Whether an attribute starts at `j` after white space from `i`.
fn attribute_follows(cs: &Vec<u32>, i: usize, j: usize) -> bool {
    (i < j) & name_start(at(cs, j))
}

fn push_raw(mut raws: Vec<Raw>, raw: Raw, offset: usize) -> Result<Vec<Raw>, XmlError> {
    if raws.len() < usize::MAX {
        raws.push(raw);
        Ok(raws)
    } else {
        Err(fail(ErrorKind::ResourceLimit, offset))
    }
}

/// `(S Attribute)*` from `i`: the attributes appended to `raws`, the position
/// after the last one and the budget left.
fn attributes(
    cs: &Vec<u32>,
    i: usize,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    budget: usize,
    raws: Vec<Raw>,
) -> Result<(Vec<Raw>, usize, usize), XmlError> {
    let j = skip_spaces(cs, i);
    if attribute_follows(cs, i, j) {
        let (raw, k, budget) = attribute(cs, j, env, stack, budget)?;
        let raws = push_raw(raws, raw, j)?;
        attributes(cs, k, env, stack, budget, raws)
    } else {
        Ok((raws, i, budget))
    }
}

/// Whether the attribute names of `raws[k]` and `raws[m..]` all differ.
fn distinct_from(cs: &Vec<u32>, raws: &Vec<Raw>, k: usize, m: usize) -> bool {
    if m < raws.len() {
        if same_span(cs, raws[k].start, raws[k].stop, raws[m].start, raws[m].stop) {
            false
        } else {
            distinct_from(cs, raws, k, m + 1)
        }
    } else {
        true
    }
}

/// [WFC: Unique Att Spec] for `raws[k..]`.
fn unique_names(cs: &Vec<u32>, raws: &Vec<Raw>, k: usize) -> Result<(), XmlError> {
    if k < raws.len() {
        if distinct_from(cs, raws, k, k + 1) {
            unique_names(cs, raws, k + 1)
        } else {
            Err(fail(ErrorKind::DuplicateAttribute, raws[k].start))
        }
    } else {
        Ok(())
    }
}

/// How an attribute specification declares a namespace.
enum NsKind {
    /// `xmlns`: the default namespace.
    Default,
    /// `xmlns:prefix`.
    Prefixed,
    /// Any other attribute.
    Plain,
}

fn ns_kind(cs: &Vec<u32>, raw: &Raw) -> NsKind {
    if raw.mark == raw.stop {
        if span_is(cs, raw.start, raw.stop, b"xmlns") {
            NsKind::Default
        } else {
            NsKind::Plain
        }
    } else if span_is(cs, raw.start, raw.mark, b"xmlns") {
        NsKind::Prefixed
    } else {
        NsKind::Plain
    }
}

/// The namespace name bound to `xml`.
const XML_NAMESPACE: &[u8] = b"http://www.w3.org/XML/1998/namespace";
/// The namespace name bound to `xmlns`.
const XMLNS_NAMESPACE: &[u8] = b"http://www.w3.org/2000/xmlns/";

/// Whether the code points of `word` are the ASCII `text`.
fn word_eq(word: &Vec<u32>, text: &[u8]) -> bool {
    (word.len() == text.len()) & word_eq_from(word, text, 0)
}

fn word_eq_from(word: &Vec<u32>, text: &[u8], k: usize) -> bool {
    if k < word.len() {
        if k < text.len() {
            if word[k] == u32::from(text[k]) {
                word_eq_from(word, text, k + 1)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether `value` is one of the two reserved namespace names.
fn reserved_value(value: &Vec<u32>) -> bool {
    word_eq(value, XML_NAMESPACE) | word_eq(value, XMLNS_NAMESPACE)
}

fn ascii_word(text: &[u8], k: usize, out: Vec<u32>) -> Result<Vec<u32>, XmlError> {
    if k < text.len() {
        let out = push_char(out, u32::from(text[k]), 0)?;
        ascii_word(text, k + 1, out)
    } else {
        Ok(out)
    }
}

fn push_binding(
    mut decls: Vec<Binding>,
    b: Binding,
    offset: usize,
) -> Result<Vec<Binding>, XmlError> {
    if decls.len() < usize::MAX {
        decls.push(b);
        Ok(decls)
    } else {
        Err(fail(ErrorKind::ResourceLimit, offset))
    }
}

/// A default namespace declaration: neither reserved namespace name.
fn default_declaration(raw: &Raw, decls: Vec<Binding>) -> Result<Vec<Binding>, XmlError> {
    if reserved_value(&raw.value) {
        Err(fail(ErrorKind::ReservedNamespace, raw.start))
    } else {
        let value = copy_all(&raw.value)?;
        push_binding(
            decls,
            Binding {
                ns_prefix: None,
                value,
            },
            raw.start,
        )
    }
}

/// Whether a declaration `xmlns:prefix="value"` keeps the constraints on
/// reserved prefixes and names and on undeclaring.
fn prefix_allowed(cs: &Vec<u32>, raw: &Raw) -> bool {
    if span_is(cs, raw.mark + 1, raw.stop, b"xmlns") {
        false
    } else if span_is(cs, raw.mark + 1, raw.stop, b"xml") {
        word_eq(&raw.value, XML_NAMESPACE)
    } else {
        (0 < raw.value.len()) & !reserved_value(&raw.value)
    }
}

/// A prefixed namespace declaration.
fn prefixed_declaration(
    cs: &Vec<u32>,
    raw: &Raw,
    decls: Vec<Binding>,
) -> Result<Vec<Binding>, XmlError> {
    if prefix_allowed(cs, raw) {
        let prefix = copy_span(cs, raw.mark + 1, raw.stop)?;
        let value = copy_all(&raw.value)?;
        push_binding(
            decls,
            Binding {
                ns_prefix: Some(prefix),
                value,
            },
            raw.start,
        )
    } else {
        Err(fail(ErrorKind::ReservedNamespace, raw.start))
    }
}

/// The namespace declarations among `raws[k..]`, appended to `decls`.
fn declarations(
    cs: &Vec<u32>,
    raws: &Vec<Raw>,
    k: usize,
    decls: Vec<Binding>,
) -> Result<Vec<Binding>, XmlError> {
    if k < raws.len() {
        let decls = match ns_kind(cs, &raws[k]) {
            NsKind::Default => default_declaration(&raws[k], decls)?,
            NsKind::Prefixed => prefixed_declaration(cs, &raws[k], decls)?,
            NsKind::Plain => decls,
        };
        declarations(cs, raws, k + 1, decls)
    } else {
        Ok(decls)
    }
}

fn copy_option(word: &Option<Vec<u32>>) -> Result<Option<Vec<u32>>, XmlError> {
    match word {
        Some(w) => {
            let w = copy_all(w)?;
            Ok(Some(w))
        }
        None => Ok(None),
    }
}

fn copy_bindings(
    ctx: &Vec<Binding>,
    i: usize,
    out: Vec<Binding>,
) -> Result<Vec<Binding>, XmlError> {
    if i < ctx.len() {
        let ns_prefix = copy_option(&ctx[i].ns_prefix)?;
        let value = copy_all(&ctx[i].value)?;
        let out = push_binding(out, Binding { ns_prefix, value }, 0)?;
        copy_bindings(ctx, i + 1, out)
    } else {
        Ok(out)
    }
}

/// The bindings in scope inside an element: `ctx`, then its declarations.
fn extend(ctx: &Vec<Binding>, decls: &Vec<Binding>) -> Result<Vec<Binding>, XmlError> {
    let out = copy_bindings(ctx, 0, Vec::new())?;
    copy_bindings(decls, 0, out)
}

/// Whether a binding declares the prefix `cs[start..end]`.
fn binds(b: &Binding, cs: &Vec<u32>, start: usize, end: usize) -> bool {
    match &b.ns_prefix {
        Some(p) => word_is(p, cs, start, end),
        None => false,
    }
}

/// The namespace name of the innermost binding of the prefix `cs[start..end]`
/// among `ctx[..k]`.
fn lookup_prefix(
    ctx: &Vec<Binding>,
    cs: &Vec<u32>,
    start: usize,
    end: usize,
    k: usize,
) -> Result<Option<Vec<u32>>, XmlError> {
    if 0 < k {
        if binds(&ctx[k - 1], cs, start, end) {
            let value = copy_all(&ctx[k - 1].value)?;
            Ok(Some(value))
        } else {
            lookup_prefix(ctx, cs, start, end, k - 1)
        }
    } else {
        Ok(None)
    }
}

/// Whether a binding declares the default namespace.
fn is_default(b: &Binding) -> bool {
    b.ns_prefix.is_none()
}

/// The default namespace among `ctx[..k]`: the innermost `xmlns`, where an
/// empty value means no default namespace.
fn lookup_default(ctx: &Vec<Binding>, k: usize) -> Result<Option<Vec<u32>>, XmlError> {
    if 0 < k {
        if is_default(&ctx[k - 1]) {
            if ctx[k - 1].value.len() == 0 {
                Ok(None)
            } else {
                let value = copy_all(&ctx[k - 1].value)?;
                Ok(Some(value))
            }
        } else {
            lookup_default(ctx, k - 1)
        }
    } else {
        Ok(None)
    }
}

/// The namespace name of a prefix `cs[start..end]` in scope `ctx`.
fn prefix_namespace(
    cs: &Vec<u32>,
    start: usize,
    end: usize,
    ctx: &Vec<Binding>,
) -> Result<Vec<u32>, XmlError> {
    if span_is(cs, start, end, b"xml") {
        ascii_word(XML_NAMESPACE, 0, Vec::new())
    } else {
        match lookup_prefix(ctx, cs, start, end, ctx.len())? {
            Some(value) => Ok(value),
            None => Err(fail(ErrorKind::UndeclaredPrefix, start)),
        }
    }
}

/// The prefix and namespace name of the element QName `cs[start..end]` with
/// its colon at `mark`.
fn element_namespace(
    cs: &Vec<u32>,
    start: usize,
    mark: usize,
    end: usize,
    ctx: &Vec<Binding>,
) -> Result<(Option<Vec<u32>>, Option<Vec<u32>>), XmlError> {
    if mark == end {
        let namespace = lookup_default(ctx, ctx.len())?;
        Ok((None, namespace))
    } else if span_is(cs, start, mark, b"xmlns") {
        Err(fail(ErrorKind::ReservedNamespace, start))
    } else {
        let namespace = prefix_namespace(cs, start, mark, ctx)?;
        let prefix = copy_span(cs, start, mark)?;
        Ok((Some(prefix), Some(namespace)))
    }
}

fn push_attribute(
    mut out: Vec<Attribute>,
    a: Attribute,
    offset: usize,
) -> Result<Vec<Attribute>, XmlError> {
    if out.len() < usize::MAX {
        out.push(a);
        Ok(out)
    } else {
        Err(fail(ErrorKind::ResourceLimit, offset))
    }
}

/// The attribute of a specification that is not a namespace declaration:
/// unprefixed names have no namespace.
fn resolved_attribute(cs: &Vec<u32>, raw: &Raw, ctx: &Vec<Binding>) -> Result<Attribute, XmlError> {
    let value = copy_all(&raw.value)?;
    if raw.mark == raw.stop {
        let local = copy_span(cs, raw.start, raw.stop)?;
        Ok(Attribute {
            ns_prefix: None,
            ns_name: None,
            local_name: local,
            value,
        })
    } else {
        let namespace = prefix_namespace(cs, raw.start, raw.mark, ctx)?;
        let prefix = copy_span(cs, raw.start, raw.mark)?;
        let local = copy_span(cs, raw.mark + 1, raw.stop)?;
        Ok(Attribute {
            ns_prefix: Some(prefix),
            ns_name: Some(namespace),
            local_name: local,
            value,
        })
    }
}

/// The attributes of `raws[k..]` other than namespace declarations,
/// appended to `out`.
fn resolve_attributes(
    cs: &Vec<u32>,
    raws: &Vec<Raw>,
    k: usize,
    ctx: &Vec<Binding>,
    out: Vec<Attribute>,
) -> Result<Vec<Attribute>, XmlError> {
    if k < raws.len() {
        let out = match ns_kind(cs, &raws[k]) {
            NsKind::Plain => {
                let a = resolved_attribute(cs, &raws[k], ctx)?;
                push_attribute(out, a, raws[k].start)?
            }
            _ => out,
        };
        resolve_attributes(cs, raws, k + 1, ctx, out)
    } else {
        Ok(out)
    }
}

/// Whether two optional words are equal.
fn same_option(a: &Option<Vec<u32>>, b: &Option<Vec<u32>>) -> bool {
    match (a, b) {
        (Some(x), Some(y)) => same_word(x, y),
        (None, None) => true,
        _ => false,
    }
}

fn same_word_from(a: &Vec<u32>, b: &Vec<u32>, k: usize) -> bool {
    if k < a.len() {
        if a[k] == b[k] {
            same_word_from(a, b, k + 1)
        } else {
            false
        }
    } else {
        true
    }
}

fn same_word(a: &Vec<u32>, b: &Vec<u32>) -> bool {
    if a.len() == b.len() {
        same_word_from(a, b, 0)
    } else {
        false
    }
}

/// Whether two attributes have the same expanded name.
fn same_expanded(a: &Attribute, b: &Attribute) -> bool {
    same_option(&a.ns_name, &b.ns_name) & same_word(&a.local_name, &b.local_name)
}

fn expanded_distinct_from(attrs: &Vec<Attribute>, k: usize, m: usize) -> bool {
    if m < attrs.len() {
        if same_expanded(&attrs[k], &attrs[m]) {
            false
        } else {
            expanded_distinct_from(attrs, k, m + 1)
        }
    } else {
        true
    }
}

/// [NSC: Attributes Unique] for `attrs[k..]`.
fn unique_expanded(attrs: &Vec<Attribute>, k: usize, origin: usize) -> Result<(), XmlError> {
    if k < attrs.len() {
        if expanded_distinct_from(attrs, k, k + 1) {
            unique_expanded(attrs, k + 1, origin)
        } else {
            Err(fail(ErrorKind::DuplicateAttribute, origin))
        }
    } else {
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Content and elements.

/// What begins at a position in content.
enum Rule {
    End,
    Stop,
    Chars,
    Comment,
    CData,
    Pi,
    Reference,
    Element,
    Invalid,
}

fn bang_rule(cs: &Vec<u32>, i: usize) -> Rule {
    if starts(cs, i, b"<!--") {
        Rule::Comment
    } else if starts(cs, i, b"<![CDATA[") {
        Rule::CData
    } else {
        Rule::Invalid
    }
}

fn markup_rule(cs: &Vec<u32>, i: usize) -> Rule {
    let c = at(cs, i + 1);
    if c == 47 {
        Rule::Stop
    } else if c == 33 {
        bang_rule(cs, i)
    } else if c == 63 {
        Rule::Pi
    } else {
        Rule::Element
    }
}

fn content_rule(cs: &Vec<u32>, i: usize) -> Rule {
    let c = at(cs, i);
    if c == 0 {
        Rule::End
    } else if c == 60 {
        markup_rule(cs, i)
    } else if c == 38 {
        Rule::Reference
    } else {
        Rule::Chars
    }
}

fn push_node(mut nodes: Vec<Node>, node: Node, offset: usize) -> Result<Vec<Node>, XmlError> {
    if nodes.len() < usize::MAX {
        nodes.push(node);
        Ok(nodes)
    } else {
        Err(fail(ErrorKind::ResourceLimit, offset))
    }
}

/// The children so far: `nodes`, then the pending characters as a text node.
fn flush(nodes: Vec<Node>, text: Vec<u32>, offset: usize) -> Result<Vec<Node>, XmlError> {
    if text.len() == 0 {
        Ok(nodes)
    } else {
        push_node(nodes, Node::Text(text), offset)
    }
}

/// [43] content from `i`, read into `nodes` and the pending characters
/// `text`, up to the end of `cs` or an end tag. Returns the children, the
/// pending characters, the stopping position and the budget left.
fn content(
    cs: &Vec<u32>,
    i: usize,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    ctx: &Vec<Binding>,
    budget: usize,
    nodes: Vec<Node>,
    text: Vec<u32>,
) -> Result<(Vec<Node>, Vec<u32>, usize, usize), XmlError> {
    match content_rule(cs, i) {
        Rule::End => Ok((nodes, text, i, budget)),
        Rule::Stop => Ok((nodes, text, i, budget)),
        Rule::Chars => {
            let (text, j) = char_data(cs, i, text)?;
            content(cs, j, env, stack, ctx, budget, nodes, text)
        }
        Rule::Comment => {
            let j = comment(cs, i)?;
            content(cs, j, env, stack, ctx, budget, nodes, text)
        }
        Rule::CData => {
            let (text, j) = cdata(cs, i, text)?;
            content(cs, j, env, stack, ctx, budget, nodes, text)
        }
        Rule::Pi => {
            let j = pi(cs, i)?;
            content(cs, j, env, stack, ctx, budget, nodes, text)
        }
        Rule::Reference => {
            let (nodes, text, j, budget) =
                content_reference(cs, i, env, stack, ctx, budget, nodes, text)?;
            content(cs, j, env, stack, ctx, budget, nodes, text)
        }
        Rule::Element => {
            let (e, j, budget) = element(cs, i, env, stack, ctx, budget)?;
            let nodes = flush(nodes, text, i)?;
            let nodes = push_node(nodes, Node::Element(e), i)?;
            content(cs, j, env, stack, ctx, budget, nodes, Vec::new())
        }
        Rule::Invalid => Err(fail(ErrorKind::Syntax, i)),
    }
}

/// A reference at `i` in content: a character joins the pending text; an
/// entity's replacement text is read as content, which must end with it.
fn content_reference(
    cs: &Vec<u32>,
    i: usize,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    ctx: &Vec<Binding>,
    budget: usize,
    nodes: Vec<Node>,
    text: Vec<u32>,
) -> Result<(Vec<Node>, Vec<u32>, usize, usize), XmlError> {
    let (r, j) = reference(cs, i)?;
    match r {
        Reference::Character(c) => {
            let text = push_char(text, c, i)?;
            Ok((nodes, text, j, budget))
        }
        Reference::Entity(start, end) => {
            let k = expandable(cs, start, end, env, stack, i)?;
            let left = spend(env, k, budget, i)?;
            let inner = pushed(stack, k, i)?;
            match content(&env[k].text, 0, env, &inner, ctx, left, nodes, text) {
                Ok((nodes, text, stop, left)) => {
                    if stop == env[k].text.len() {
                        Ok((nodes, text, j, left))
                    } else {
                        Err(fail(ErrorKind::EntityBoundary, i))
                    }
                }
                Err(e) => Err(fail(e.kind, i)),
            }
        }
    }
}

/// The end of a start tag at `j`: `>` (not empty) or `/>` (empty), and the
/// position after it.
fn tag_end(cs: &Vec<u32>, j: usize) -> Result<(bool, usize), XmlError> {
    let c = at(cs, j);
    if c == 62 {
        Ok((false, j + 1))
    } else if c == 47 {
        if at(cs, j + 1) == 62 {
            Ok((true, j + 2))
        } else {
            Err(fail(ErrorKind::Syntax, j))
        }
    } else {
        Err(fail(ErrorKind::Syntax, j))
    }
}

/// Whether `n` characters fit in `cs` from `i`, which is at most its length.
fn fits(cs: &Vec<u32>, i: usize, n: usize) -> bool {
    n <= cs.len() - i
}

/// The name of an end tag at `i`, copied from the start-tag name
/// `cs[start..end]` and ending at `stop`, then `S? '>'`.
fn end_name(
    cs: &Vec<u32>,
    i: usize,
    stop: usize,
    start: usize,
    end: usize,
) -> Result<usize, XmlError> {
    if same_from(cs, i + 2, start, end - start, 0) {
        let j = skip_spaces(cs, stop);
        if at(cs, j) == 62 {
            Ok(j + 1)
        } else {
            Err(fail(ErrorKind::MismatchedEndTag, i))
        }
    } else {
        Err(fail(ErrorKind::MismatchedEndTag, i))
    }
}

/// [42] ETag at `i` for the start-tag name `cs[start..end]`: its end.
fn end_tag(cs: &Vec<u32>, i: usize, start: usize, end: usize) -> Result<usize, XmlError> {
    if !starts(cs, i, b"</") {
        Err(fail(ErrorKind::UnexpectedEnd, i))
    } else if fits(cs, i + 2, end - start) {
        end_name(cs, i, i + 2 + (end - start), start, end)
    } else {
        Err(fail(ErrorKind::MismatchedEndTag, i))
    }
}

/// Where the local part of the QName `cs[start..end]` with its colon at
/// `mark` begins.
fn local_start(start: usize, mark: usize, end: usize) -> usize {
    if mark == end {
        start
    } else {
        mark + 1
    }
}

/// The rest of an element whose start tag at `i` has the QName
/// `cs[i+1..name_end]` (colon at `mark`), attributes `raws` and namespace
/// declarations `decls`, with the bindings `ctx` already extended by them.
fn element_in(
    cs: &Vec<u32>,
    i: usize,
    name_end: usize,
    mark: usize,
    after: usize,
    empty: bool,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    ctx: &Vec<Binding>,
    raws: &Vec<Raw>,
    decls: Vec<Binding>,
    budget: usize,
) -> Result<(Element, usize, usize), XmlError> {
    let (prefix, namespace) = element_namespace(cs, i + 1, mark, name_end, ctx)?;
    let local = copy_span(cs, local_start(i + 1, mark, name_end), name_end)?;
    let attributes = resolve_attributes(cs, raws, 0, ctx, Vec::new())?;
    unique_expanded(&attributes, 0, i)?;
    if empty {
        Ok((
            Element {
                ns_prefix: prefix,
                ns_name: namespace,
                local_name: local,
                attributes,
                declarations: decls,
                children: Vec::new(),
            },
            after,
            budget,
        ))
    } else {
        let (nodes, text, stop, budget) =
            content(cs, after, env, stack, ctx, budget, Vec::new(), Vec::new())?;
        let children = flush(nodes, text, stop)?;
        let end = end_tag(cs, stop, i + 1, name_end)?;
        Ok((
            Element {
                ns_prefix: prefix,
                ns_name: namespace,
                local_name: local,
                attributes,
                declarations: decls,
                children,
            },
            end,
            budget,
        ))
    }
}

/// [39] element at `i` (which begins with `<`): the element, its end and
/// the budget left.
fn element(
    cs: &Vec<u32>,
    i: usize,
    env: &Vec<Entity>,
    stack: &Vec<usize>,
    ctx: &Vec<Binding>,
    budget: usize,
) -> Result<(Element, usize, usize), XmlError> {
    let (name_end, mark) = qname(cs, i + 1)?;
    let (raws, j, budget) = attributes(cs, name_end, env, stack, budget, Vec::new())?;
    let (empty, after) = tag_end(cs, skip_spaces(cs, j))?;
    unique_names(cs, &raws, 0)?;
    let decls = declarations(cs, &raws, 0, Vec::new())?;
    if decls.len() == 0 {
        element_in(
            cs, i, name_end, mark, after, empty, env, stack, ctx, &raws, decls, budget,
        )
    } else {
        let inner = extend(ctx, &decls)?;
        element_in(
            cs, i, name_end, mark, after, empty, env, stack, &inner, &raws, decls, budget,
        )
    }
}

// ---------------------------------------------------------------------------
// The prolog: XML declaration, Misc and document type declaration.

/// [26] VersionNum digits after `1.`, then the closing quote `q`.
fn version_digits(cs: &Vec<u32>, i: usize, start: usize, q: u32) -> Result<usize, XmlError> {
    let c = at(cs, i);
    if digit(c) {
        version_digits(cs, i + 1, start, q)
    } else if i == start {
        Err(fail(ErrorKind::Syntax, i))
    } else if c == q {
        Ok(i + 1)
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

/// A quoted VersionNum `'1.' [0-9]+` at `i`.
fn version_value(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let q = at(cs, i);
    if !quote(q) {
        Err(fail(ErrorKind::Syntax, i))
    } else if starts(cs, i + 1, b"1.") {
        version_digits(cs, i + 3, i + 3, q)
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

fn ascii_letter(c: u32) -> bool {
    ((c >= 65) & (c <= 90)) | ((c >= 97) & (c <= 122))
}

/// [81] EncName characters after the first.
fn enc_char(c: u32) -> bool {
    ascii_letter(c) | digit(c) | (c == 46) | (c == 95) | (c == 45)
}

fn enc_end(cs: &Vec<u32>, i: usize) -> usize {
    if enc_char(at(cs, i)) {
        enc_end(cs, i + 1)
    } else {
        i
    }
}

/// Whether the five characters from `start` are `UTF-8` in any case.
fn utf8_letters(cs: &Vec<u32>, start: usize) -> bool {
    caseless(at(cs, start), 117)
        & caseless(at(cs, start + 1), 116)
        & caseless(at(cs, start + 2), 102)
        & (at(cs, start + 3) == 45)
        & (at(cs, start + 4) == 56)
}

/// Whether `cs[start..end]` is `UTF-8` in any case.
fn utf8_name(cs: &Vec<u32>, start: usize, end: usize) -> bool {
    if end - start == 5 {
        utf8_letters(cs, start)
    } else {
        false
    }
}

/// A quoted EncName at `i`, which must name UTF-8.
fn encoding_value(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let q = at(cs, i);
    if !quote(q) {
        Err(fail(ErrorKind::Syntax, i))
    } else if !ascii_letter(at(cs, i + 1)) {
        Err(fail(ErrorKind::Syntax, i + 1))
    } else {
        let end = enc_end(cs, i + 2);
        if at(cs, end) != q {
            Err(fail(ErrorKind::Syntax, end))
        } else if utf8_name(cs, i + 1, end) {
            Ok(end + 1)
        } else {
            Err(fail(ErrorKind::UnsupportedEncoding, i + 1))
        }
    }
}

/// The end of `yes` or `no` at `i`, or `i` when neither is there.
fn yes_no_end(cs: &Vec<u32>, i: usize) -> usize {
    if starts(cs, i, b"yes") {
        i + 3
    } else if starts(cs, i, b"no") {
        i + 2
    } else {
        i
    }
}

/// A quoted `yes` or `no` at `i`.
fn standalone_value(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let q = at(cs, i);
    if quote(q) {
        let end = yes_no_end(cs, i + 1);
        standalone_close(cs, i, end, q)
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

/// The closing quote `q` of a standalone value at `i` whose word ends at
/// `end`, which is `i + 1` when there is no word.
fn standalone_close(cs: &Vec<u32>, i: usize, end: usize, q: u32) -> Result<usize, XmlError> {
    if end == i + 1 {
        Err(fail(ErrorKind::Syntax, i))
    } else if at(cs, end) == q {
        Ok(end + 1)
    } else {
        Err(fail(ErrorKind::Syntax, end))
    }
}

/// Whether the keyword `word` follows white space from `i` to `j`.
fn keyword_follows(cs: &Vec<u32>, i: usize, j: usize, word: &[u8]) -> bool {
    (i < j) & starts(cs, j, word)
}

/// [80] EncodingDecl, when present after `i`.
fn encoding_part(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let j = skip_spaces(cs, i);
    if keyword_follows(cs, i, j, b"encoding") {
        let k = eq(cs, j + 8)?;
        encoding_value(cs, k)
    } else {
        Ok(i)
    }
}

/// [32] SDDecl, when present after `i`.
fn standalone_part(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let j = skip_spaces(cs, i);
    if keyword_follows(cs, i, j, b"standalone") {
        let k = eq(cs, j + 10)?;
        standalone_value(cs, k)
    } else {
        Ok(i)
    }
}

/// Whether the document begins with an XML declaration.
fn declaration_start(cs: &Vec<u32>) -> bool {
    starts(cs, 0, b"<?xml") & space(at(cs, 5))
}

/// [23] XMLDecl from its first white space at 5.
fn declaration_body(cs: &Vec<u32>) -> Result<usize, XmlError> {
    let i = skip_spaces(cs, 5);
    if !starts(cs, i, b"version") {
        Err(fail(ErrorKind::Syntax, i))
    } else {
        let i = eq(cs, i + 7)?;
        let i = version_value(cs, i)?;
        let i = encoding_part(cs, i)?;
        let i = standalone_part(cs, i)?;
        let j = skip_spaces(cs, i);
        if pi_end(cs, j) {
            Ok(j + 2)
        } else {
            Err(fail(ErrorKind::Syntax, j))
        }
    }
}

/// The XML declaration, when present: the position after it.
fn xml_declaration(cs: &Vec<u32>) -> Result<usize, XmlError> {
    if declaration_start(cs) {
        declaration_body(cs)
    } else {
        Ok(0)
    }
}

enum MiscRule {
    Comment,
    Pi,
    Other,
}

fn misc_rule(cs: &Vec<u32>, i: usize) -> MiscRule {
    if starts(cs, i, b"<!--") {
        MiscRule::Comment
    } else if starts(cs, i, b"<?") {
        MiscRule::Pi
    } else {
        MiscRule::Other
    }
}

/// [27] Misc* from `i`: the position after it.
fn misc(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let j = skip_spaces(cs, i);
    match misc_rule(cs, j) {
        MiscRule::Comment => {
            let k = comment(cs, j)?;
            misc(cs, k)
        }
        MiscRule::Pi => {
            let k = pi(cs, j)?;
            misc(cs, k)
        }
        MiscRule::Other => Ok(j),
    }
}

/// [11] SystemLiteral at `i`: its end.
fn system_literal(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let q = at(cs, i);
    if quote(q) {
        literal_end(cs, i + 1, q)
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

/// The position after the quote `q` that closes a literal from `i`.
fn literal_end(cs: &Vec<u32>, i: usize, q: u32) -> Result<usize, XmlError> {
    let c = at(cs, i);
    if c == q {
        Ok(i + 1)
    } else if c == 0 {
        Err(fail(ErrorKind::UnexpectedEnd, i))
    } else {
        literal_end(cs, i + 1, q)
    }
}

/// [13] PubidChar.
fn pubid_char(c: u32) -> bool {
    (c == 32)
        | (c == 13)
        | (c == 10)
        | ascii_letter(c)
        | digit(c)
        | (c == 45)
        | (c == 39)
        | (c == 40)
        | (c == 41)
        | (c == 43)
        | (c == 44)
        | (c == 46)
        | (c == 47)
        | (c == 58)
        | (c == 61)
        | (c == 63)
        | (c == 59)
        | (c == 33)
        | (c == 42)
        | (c == 35)
        | (c == 64)
        | (c == 36)
        | (c == 95)
        | (c == 37)
}

fn pubid_end(cs: &Vec<u32>, i: usize, q: u32) -> Result<usize, XmlError> {
    let c = at(cs, i);
    if c == q {
        Ok(i + 1)
    } else if pubid_char(c) {
        pubid_end(cs, i + 1, q)
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

/// [12] PubidLiteral at `i`: its end.
fn pubid_literal(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let q = at(cs, i);
    if quote(q) {
        pubid_end(cs, i + 1, q)
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

/// [75] ExternalID at `i`: its end.
fn external_id(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    if starts(cs, i, b"SYSTEM") {
        let j = spaces(cs, i + 6)?;
        system_literal(cs, j)
    } else if starts(cs, i, b"PUBLIC") {
        let j = spaces(cs, i + 6)?;
        let k = pubid_literal(cs, j)?;
        let m = spaces(cs, k)?;
        system_literal(cs, m)
    } else {
        Err(fail(ErrorKind::Syntax, i))
    }
}

/// Whether an ExternalID starts at `j` after white space from `i`.
fn external_follows(cs: &Vec<u32>, i: usize, j: usize) -> bool {
    (i < j) & (starts(cs, j, b"SYSTEM") | starts(cs, j, b"PUBLIC"))
}

fn push_entity(mut env: Vec<Entity>, e: Entity, offset: usize) -> Result<Vec<Entity>, XmlError> {
    if env.len() < usize::MAX {
        env.push(e);
        Ok(env)
    } else {
        Err(fail(ErrorKind::ResourceLimit, offset))
    }
}

/// `out` followed by the entity reference `cs[i..j]`, which is bypassed in
/// an entity value.
fn bypass(cs: &Vec<u32>, i: usize, j: usize, out: Vec<u32>) -> Result<Vec<u32>, XmlError> {
    copy_from(cs, i, j, out)
}

/// A reference at `i` in an entity value: a character reference is
/// replaced, a general entity reference is kept as it is.
fn value_reference(cs: &Vec<u32>, i: usize, text: Vec<u32>) -> Result<(Vec<u32>, usize), XmlError> {
    if at(cs, i + 1) == 35 {
        let (c, j) = char_reference(cs, i)?;
        let text = push_char(text, c, i)?;
        Ok((text, j))
    } else {
        let (_, j) = entity_name(cs, i)?;
        let text = bypass(cs, i, j, text)?;
        Ok((text, j))
    }
}

/// [9] EntityValue text from `i` up to the quote `q`, with character
/// references replaced: the replacement text and the position of the quote.
/// Parameter-entity references cannot occur in the internal subset.
fn entity_value(
    cs: &Vec<u32>,
    i: usize,
    q: u32,
    text: Vec<u32>,
) -> Result<(Vec<u32>, usize), XmlError> {
    let c = at(cs, i);
    if c == q {
        Ok((text, i))
    } else if c == 0 {
        Err(fail(ErrorKind::UnexpectedEnd, i))
    } else if c == 37 {
        Err(fail(ErrorKind::UnsupportedDeclaration, i))
    } else if c == 38 {
        let (text, j) = value_reference(cs, i, text)?;
        entity_value(cs, j, q, text)
    } else {
        let text = push_char(text, c, i)?;
        entity_value(cs, i + 1, q, text)
    }
}

/// Whether an NDataDecl starts at `j` after white space from `i`.
fn ndata_follows(cs: &Vec<u32>, i: usize, j: usize) -> bool {
    (i < j) & starts(cs, j, b"NDATA")
}

/// The rest of an external general entity definition after its ExternalID
/// ending at `i`: an optional NDataDecl.
fn external_rest(cs: &Vec<u32>, i: usize) -> Result<(EntityKind, usize), XmlError> {
    let j = skip_spaces(cs, i);
    if ndata_follows(cs, i, j) {
        let k = spaces(cs, j + 5)?;
        let end = ncname(cs, k)?;
        Ok((EntityKind::Unparsed, end))
    } else {
        Ok((EntityKind::External, i))
    }
}

/// [73] EntityDef at `i`: the kind, the replacement text and the end.
fn entity_definition(cs: &Vec<u32>, i: usize) -> Result<(EntityKind, Vec<u32>, usize), XmlError> {
    let q = at(cs, i);
    if quote(q) {
        let (text, j) = entity_value(cs, i + 1, q, Vec::new())?;
        Ok((EntityKind::Internal, text, j + 1))
    } else {
        let j = external_id(cs, i)?;
        let (kind, k) = external_rest(cs, j)?;
        Ok((kind, Vec::new(), k))
    }
}

/// [74] PEDef at `i`: its end.
fn parameter_definition(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let q = at(cs, i);
    if quote(q) {
        let (_, j) = entity_value(cs, i + 1, q, Vec::new())?;
        Ok(j + 1)
    } else {
        external_id(cs, i)
    }
}

/// `S? '>'` at `i`: the position after it.
fn declaration_close(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let j = skip_spaces(cs, i);
    if at(cs, j) == 62 {
        Ok(j + 1)
    } else {
        Err(fail(ErrorKind::Syntax, j))
    }
}

/// [72] PEDecl after `<!ENTITY S %` at `j`: parsed and not used.
fn parameter_declaration(cs: &Vec<u32>, j: usize) -> Result<usize, XmlError> {
    let k = spaces(cs, j + 1)?;
    let end = ncname(cs, k)?;
    let m = spaces(cs, end)?;
    let n = parameter_definition(cs, m)?;
    declaration_close(cs, n)
}

/// [71] GEDecl after `<!ENTITY S` at `j`, appended to `env`.
fn general_declaration(
    cs: &Vec<u32>,
    i: usize,
    j: usize,
    env: Vec<Entity>,
) -> Result<(Vec<Entity>, usize), XmlError> {
    let end = ncname(cs, j)?;
    let m = spaces(cs, end)?;
    let (kind, text, n) = entity_definition(cs, m)?;
    let close = declaration_close(cs, n)?;
    let name = copy_span(cs, j, end)?;
    let env = push_entity(env, Entity { name, kind, text }, i)?;
    Ok((env, close))
}

/// [70] EntityDecl at `i` (which begins with `<!ENTITY`).
fn entity_declaration(
    cs: &Vec<u32>,
    i: usize,
    env: Vec<Entity>,
) -> Result<(Vec<Entity>, usize), XmlError> {
    let j = spaces(cs, i + 8)?;
    if at(cs, j) == 37 {
        let close = parameter_declaration(cs, j)?;
        Ok((env, close))
    } else {
        general_declaration(cs, i, j, env)
    }
}

enum SubsetRule {
    Close,
    Entity,
    Comment,
    Pi,
    Unsupported,
    Invalid,
}

/// Whether an element type, attribute-list or notation declaration starts
/// at `i`.
fn other_declaration(cs: &Vec<u32>, i: usize) -> bool {
    starts(cs, i, b"<!ELEMENT") | starts(cs, i, b"<!ATTLIST") | starts(cs, i, b"<!NOTATION")
}

fn declaration_rule(cs: &Vec<u32>, i: usize) -> SubsetRule {
    if other_declaration(cs, i) {
        SubsetRule::Unsupported
    } else {
        SubsetRule::Invalid
    }
}

fn subset_rule(cs: &Vec<u32>, i: usize) -> SubsetRule {
    if at(cs, i) == 93 {
        SubsetRule::Close
    } else if at(cs, i) == 37 {
        SubsetRule::Unsupported
    } else if starts(cs, i, b"<!ENTITY") {
        SubsetRule::Entity
    } else if starts(cs, i, b"<!--") {
        SubsetRule::Comment
    } else if starts(cs, i, b"<?") {
        SubsetRule::Pi
    } else {
        declaration_rule(cs, i)
    }
}

/// [28b] intSubset from `i`: the general entities declared, appended to
/// `env`, and the position of the closing `]`.
fn internal_subset(
    cs: &Vec<u32>,
    i: usize,
    env: Vec<Entity>,
) -> Result<(Vec<Entity>, usize), XmlError> {
    let i = skip_spaces(cs, i);
    match subset_rule(cs, i) {
        SubsetRule::Close => Ok((env, i)),
        SubsetRule::Entity => {
            let (env, j) = entity_declaration(cs, i, env)?;
            internal_subset(cs, j, env)
        }
        SubsetRule::Comment => {
            let j = comment(cs, i)?;
            internal_subset(cs, j, env)
        }
        SubsetRule::Pi => {
            let j = pi(cs, i)?;
            internal_subset(cs, j, env)
        }
        SubsetRule::Unsupported => Err(fail(ErrorKind::UnsupportedDeclaration, i)),
        SubsetRule::Invalid => Err(fail(ErrorKind::Syntax, i)),
    }
}

/// The external identifier of a document type declaration, when present
/// after the name ending at `i`.
fn doctype_external(cs: &Vec<u32>, i: usize) -> Result<usize, XmlError> {
    let j = skip_spaces(cs, i);
    if external_follows(cs, i, j) {
        external_id(cs, j)
    } else {
        Ok(i)
    }
}

/// The rest of a document type declaration from `i`: an optional internal
/// subset and `>`.
fn doctype_rest(cs: &Vec<u32>, i: usize) -> Result<(Vec<Entity>, usize), XmlError> {
    let j = skip_spaces(cs, i);
    if at(cs, j) == 91 {
        let (env, k) = internal_subset(cs, j + 1, Vec::new())?;
        let close = declaration_close(cs, k + 1)?;
        Ok((env, close))
    } else if at(cs, j) == 62 {
        Ok((Vec::new(), j + 1))
    } else {
        Err(fail(ErrorKind::Syntax, j))
    }
}

/// [28] doctypedecl at `i`, when present: the declared general entities and
/// the position after it.
fn doctype(cs: &Vec<u32>, i: usize) -> Result<(Vec<Entity>, usize), XmlError> {
    if starts(cs, i, b"<!DOCTYPE") {
        let j = spaces(cs, i + 9)?;
        let (end, _) = qname(cs, j)?;
        let k = doctype_external(cs, end)?;
        doctype_rest(cs, k)
    } else {
        Ok((Vec::new(), i))
    }
}

/// [1] document over the decoded characters.
fn document(cs: &Vec<u32>, budget: usize) -> Result<Document, XmlError> {
    let i = xml_declaration(cs)?;
    let i = misc(cs, i)?;
    let (env, i) = doctype(cs, i)?;
    let i = misc(cs, i)?;
    if at(cs, i) != 60 {
        Err(fail(ErrorKind::Syntax, i))
    } else {
        let (root, j, _) = element(cs, i, &env, &Vec::new(), &Vec::new(), budget)?;
        let j = misc(cs, j)?;
        if j == cs.len() {
            Ok(Document { root })
        } else {
            Err(fail(ErrorKind::Syntax, j))
        }
    }
}

/// Read a UTF-8 XML document into the element tree of its infoset, with the
/// given entity expansion budget. Errors report byte offsets.
pub fn read(bytes: &Vec<u8>, limits: &Limits) -> ReadResult {
    match decode(bytes) {
        Err(e) => ReadResult::Error(e),
        Ok(cs) => match document(&cs, limits.expansion) {
            Ok(d) => ReadResult::Document(d),
            Err(e) => ReadResult::Error(fail(e.kind, byte_offset(bytes, e.offset))),
        },
    }
}
