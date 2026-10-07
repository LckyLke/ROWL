//! RDF 1.1 XML Syntax (W3C Recommendation, 25 February 2014) reading: the
//! element tree of an XML document (`xml::read`) to the triples of its graph.
//!
//! The element tree becomes the events of section 6: an element's URI is its
//! namespace name followed by its local name; its attributes lose the reserved
//! XML names, after `xml:base` has set the base IRI (resolved by
//! `references::resolve`, RFC 3986 section 5.2) and `xml:lang` the language;
//! the attributes without namespace `ID`, `about`, `resource`, `parseType` and
//! `type` are read in the RDF namespace and any other one is an error. Two
//! attributes of an element may not denote one URI. Text between elements
//! must be white space.
//!
//! The productions of section 7 then give the triples, in this order: a node
//! element's `rdf:type` triple, its property attributes in document order and
//! its property elements in order. A property element's object comes first
//! (the triples of a nested node element, of the members of a collection or
//! the property attributes of an empty property element), then the statement
//! and its reification when the element has `rdf:ID`, then the content of
//! `rdf:parseType="Resource"`. A collection member's triples are followed by
//! those of the later members and then by its `rdf:first` and `rdf:rest`
//! triples.
//!
//! IRIs from names, `rdf:about`, `rdf:resource`, `rdf:ID` and `rdf:type`
//! attributes must be RFC 3987 IRIs; attribute values that are resolved must be
//! RFC 3987 IRI references. `rdf:datatype` is used as written (RDF 1.1 does
//! not resolve it), must be an IRI and may not be rdf:langString. An empty
//! property element with only `rdf:datatype` (and `rdf:ID`) has the empty
//! literal of that datatype, which RDF 1.1 added as the erratum "allow
//! datatyped empty literals"; with property attributes it is declined.
//! `rdf:parseType="Literal"` and the other values read as Literal need XML
//! canonicalization and are declined with `UnsupportedParseType`.
//!
//! Blank nodes carry the caller's scope. `rdf:nodeID` gives the label of its
//! UTF-8 spelling; the `n`-th generated blank node, counted from 0 in document
//! order, has the label `0xFF` followed by the decimal digits of `n`, which no
//! UTF-8 label contains. Terms longer than `term_bytes`, and more than `items`
//! triples, generated blank nodes or `rdf:ID` values, or an `rdf:li` counter
//! of `items`, are a `ResourceLimit` error.
//!
//! Every condition below is a single comparison or call, multi-way decisions go
//! through a classifier and one `match`, and loops are recursive helpers.
#![allow(clippy::ptr_arg, clippy::manual_range_contains, clippy::len_zero)]
#![allow(clippy::too_many_arguments, clippy::type_complexity)]
#![allow(clippy::vec_init_then_push, clippy::redundant_pattern_matching)]

use crate::encoding::encode;
use crate::iri::validate_iri;
use crate::langtag::well_formed;
use crate::ntriples::append_encoded;
use crate::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfIri, RdfLiteral, Subject, Triple};
use crate::references::{is_reference, resolve};
use crate::regular::MatchResult;
use crate::xml::{self, Attribute, Element, Node};

/// Why an element tree has no RDF/XML graph.
#[derive(Clone, Copy)]
pub enum ErrorKind {
    /// An element without namespace, or a name that is not allowed where it
    /// occurs.
    InvalidName,
    /// An attribute without namespace other than ID, about, resource,
    /// parseType and type.
    UnqualifiedAttribute,
    /// Two attributes of an element that denote the same URI.
    DuplicateAttribute,
    /// Attributes that no production allows together.
    InvalidAttributes,
    /// Text other than white space between elements, or element content that
    /// no production allows.
    InvalidContent,
    /// An rdf:ID or rdf:nodeID value that is not an NCName.
    InvalidId,
    /// An rdf:ID value given twice with the same base IRI.
    DuplicateId,
    /// A code point that is not a Unicode scalar value.
    InvalidCharacter,
    /// A value that is not an RFC 3987 IRI reference, or an IRI that is not
    /// an RFC 3987 IRI.
    InvalidIri,
    /// A language that is not a well-formed BCP 47 language tag.
    InvalidLanguageTag,
    /// rdf:datatype naming rdf:langString.
    InvalidDatatype,
    /// rdf:parseType="Literal", or another value that is read as Literal.
    UnsupportedParseType,
    /// rdf:datatype together with property attributes on an empty property
    /// element.
    UnsupportedDatatype,
    /// A term or name longer than the term limit, or more triples, generated
    /// blank nodes or rdf:ID values than the item limit.
    ResourceLimit,
}

/// The limits of a reading.
pub struct Limits {
    /// The entity expansion budget of the XML layer.
    pub expansion: usize,
    /// The bytes of a term, a base IRI or a resolved reference, and the code
    /// points of a name; below `usize::MAX / 8`.
    pub term_bytes: usize,
    /// Triples, generated blank nodes and rdf:ID values, and the bound on
    /// rdf:li counters.
    pub items: usize,
}

/// The result of reading a document.
pub enum ReadResult {
    Graph(RawGraph),
    /// The bytes are no XML document the XML layer reads.
    XmlError(xml::XmlError),
    /// The element tree has no RDF/XML graph.
    Error(ErrorKind),
}

/// An rdf:ID value and the base IRI it was given against.
struct Id {
    value: Vec<u32>,
    base: Vec<u8>,
}

/// The triples so far, the number of generated blank nodes and the rdf:ID
/// values so far.
struct State {
    triples: Vec<Triple>,
    blanks: usize,
    ids: Vec<Id>,
}

/// An attribute event: its URI and string value.
struct Event {
    uri: Vec<u32>,
    value: Vec<u32>,
}

/// An element event: its base IRI, its language and its attribute events.
struct Prepared {
    base: Vec<u8>,
    lang: Vec<u32>,
    events: Vec<Event>,
}

// Words, bytes and constants.

fn copy_bytes_from(values: &Vec<u8>, i: usize, mut out: Vec<u8>) -> Vec<u8> {
    if i < values.len() {
        out.push(values[i]);
        copy_bytes_from(values, i + 1, out)
    } else {
        out
    }
}

fn copy_bytes(values: &Vec<u8>) -> Vec<u8> {
    copy_bytes_from(values, 0, Vec::new())
}

fn copy_word_from(values: &Vec<u32>, i: usize, mut out: Vec<u32>) -> Vec<u32> {
    if i < values.len() {
        out.push(values[i]);
        copy_word_from(values, i + 1, out)
    } else {
        out
    }
}

fn copy_word(values: &Vec<u32>) -> Vec<u32> {
    copy_word_from(values, 0, Vec::new())
}

fn constant_from(values: &[u8], i: usize, mut out: Vec<u8>) -> Vec<u8> {
    if i < values.len() {
        out.push(values[i]);
        constant_from(values, i + 1, out)
    } else {
        out
    }
}

/// The bytes of a constant.
fn constant(values: &[u8]) -> Vec<u8> {
    constant_from(values, 0, Vec::new())
}

fn ascii_word_from(values: &[u8], i: usize, mut out: Vec<u32>) -> Vec<u32> {
    if i < values.len() {
        out.push(values[i] as u32);
        ascii_word_from(values, i + 1, out)
    } else {
        out
    }
}

/// The code points of an ASCII constant.
fn ascii_word(values: &[u8]) -> Vec<u32> {
    ascii_word_from(values, 0, Vec::new())
}

fn rdf_iri(spelling: &[u8]) -> RdfIri {
    RdfIri {
        spelling: constant(spelling),
    }
}

/// `w` from `i` on and `v` from `j` on are the same code points.
fn same_word_from(w: &Vec<u32>, v: &Vec<u32>, i: usize) -> bool {
    if i < w.len() {
        if w[i] == v[i] {
            same_word_from(w, v, i + 1)
        } else {
            false
        }
    } else {
        true
    }
}

fn same_word(w: &Vec<u32>, v: &Vec<u32>) -> bool {
    if w.len() == v.len() {
        same_word_from(w, v, 0)
    } else {
        false
    }
}

fn same_bytes_from(w: &Vec<u8>, v: &Vec<u8>, i: usize) -> bool {
    if i < w.len() {
        if w[i] == v[i] {
            same_bytes_from(w, v, i + 1)
        } else {
            false
        }
    } else {
        true
    }
}

fn same_bytes(w: &Vec<u8>, v: &Vec<u8>) -> bool {
    if w.len() == v.len() {
        same_bytes_from(w, v, 0)
    } else {
        false
    }
}

/// The code points of `w` from `start + i` on are the ASCII bytes of
/// `pattern` from `i` on; the caller checks that they fit.
fn ascii_at(w: &Vec<u32>, start: usize, pattern: &[u8], i: usize) -> bool {
    if i < pattern.len() {
        if w[start + i] == pattern[i] as u32 {
            ascii_at(w, start, pattern, i + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// `w` is the ASCII word `pattern`.
fn is_ascii(w: &Vec<u32>, pattern: &[u8]) -> bool {
    if w.len() == pattern.len() {
        ascii_at(w, 0, pattern, 0)
    } else {
        false
    }
}

/// The length of the RDF namespace name.
const RDF_LENGTH: usize = 43;

/// `w` is the RDF namespace name followed by `name`.
fn is_rdf(w: &Vec<u32>, name: &[u8]) -> bool {
    if w.len() == RDF_LENGTH + name.len() {
        if ascii_at(w, 0, b"http://www.w3.org/1999/02/22-rdf-syntax-ns#", 0) {
            ascii_at(w, RDF_LENGTH, name, 0)
        } else {
            false
        }
    } else {
        false
    }
}

/// `w` extends the RDF namespace name (section 5.1 forbids such namespaces).
fn rdf_extension(w: &Vec<u32>) -> bool {
    if RDF_LENGTH < w.len() {
        ascii_at(w, 0, b"http://www.w3.org/1999/02/22-rdf-syntax-ns#", 0)
    } else {
        false
    }
}

/// White space (production [3] S).
fn space(c: u32) -> bool {
    c == 32 || c == 9 || c == 13 || c == 10
}

fn spaces_from(w: &Vec<u32>, i: usize) -> bool {
    if i < w.len() {
        if space(w[i]) {
            spaces_from(w, i + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// `c` may begin an NCName.
fn nc_start(c: u32) -> bool {
    c != 58 && xml::name_start(c)
}

/// `c` may continue an NCName.
fn nc_char(c: u32) -> bool {
    c != 58 && xml::name_char(c)
}

fn nc_rest(w: &Vec<u32>, i: usize) -> bool {
    if i < w.len() {
        if nc_char(w[i]) {
            nc_rest(w, i + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// `w` is an NCName.
fn ncname(w: &Vec<u32>) -> bool {
    if 0 < w.len() {
        if nc_start(w[0]) {
            nc_rest(w, 1)
        } else {
            false
        }
    } else {
        false
    }
}

/// `a` followed by `b`, when it has at most `limit` code points.
fn concat(a: &Vec<u32>, b: &Vec<u32>, limit: usize) -> Result<Vec<u32>, ErrorKind> {
    if a.len() <= limit {
        if b.len() <= limit - a.len() {
            Ok(copy_word_from(b, 0, copy_word(a)))
        } else {
            Err(ErrorKind::ResourceLimit)
        }
    } else {
        Err(ErrorKind::ResourceLimit)
    }
}

// UTF-8 spellings, IRIs and literals.

/// `out` followed by the UTF-8 bytes of `w` from `i` on, within `limit`
/// bytes.
fn utf8_from(w: &Vec<u32>, i: usize, mut out: Vec<u8>, limit: usize) -> Result<Vec<u8>, ErrorKind> {
    if i < w.len() {
        match encode(w[i]) {
            Some(encoded) => {
                if append_encoded(&mut out, encoded, limit) {
                    utf8_from(w, i + 1, out, limit)
                } else {
                    Err(ErrorKind::ResourceLimit)
                }
            }
            None => Err(ErrorKind::InvalidCharacter),
        }
    } else {
        Ok(out)
    }
}

/// The UTF-8 bytes of `w`, within the term limit.
fn utf8(w: &Vec<u32>, limits: &Limits) -> Result<Vec<u8>, ErrorKind> {
    utf8_from(w, 0, Vec::new(), limits.term_bytes)
}

/// Whether the bytes are an RFC 3987 IRI.
fn valid_iri(bytes: &Vec<u8>) -> bool {
    matches!(validate_iri(bytes), MatchResult::Matched(true))
}

/// The IRI spelled by `w`.
fn iri_of(w: &Vec<u32>, limits: &Limits) -> Result<RdfIri, ErrorKind> {
    let spelling = utf8(w, limits)?;
    if valid_iri(&spelling) {
        Ok(RdfIri { spelling })
    } else {
        Err(ErrorKind::InvalidIri)
    }
}

/// The reference spelled by `reference` resolved against `base`.
fn resolved_bytes(
    base: &Vec<u8>,
    reference: Vec<u8>,
    limits: &Limits,
) -> Result<Vec<u8>, ErrorKind> {
    if is_reference(&reference) {
        match resolve(base, &reference) {
            Some(target) => {
                if target.len() <= limits.term_bytes {
                    Ok(target)
                } else {
                    Err(ErrorKind::ResourceLimit)
                }
            }
            None => Err(ErrorKind::InvalidIri),
        }
    } else {
        Err(ErrorKind::InvalidIri)
    }
}

/// The IRI of the reference `v` resolved against `base`.
fn resolved(base: &Vec<u8>, v: &Vec<u32>, limits: &Limits) -> Result<RdfIri, ErrorKind> {
    let reference = utf8(v, limits)?;
    let target = resolved_bytes(base, reference, limits)?;
    if valid_iri(&target) {
        Ok(RdfIri { spelling: target })
    } else {
        Err(ErrorKind::InvalidIri)
    }
}

/// The IRI of `#` followed by `v`, resolved against `base`.
fn resolved_id(base: &Vec<u8>, v: &Vec<u32>, limits: &Limits) -> Result<RdfIri, ErrorKind> {
    let mut hash = Vec::new();
    hash.push(35);
    let reference = utf8_from(v, 0, hash, limits.term_bytes)?;
    let target = resolved_bytes(base, reference, limits)?;
    if valid_iri(&target) {
        Ok(RdfIri { spelling: target })
    } else {
        Err(ErrorKind::InvalidIri)
    }
}

/// The literal `v` in language `lang`: an xsd:string without language.
fn literal_of(v: &Vec<u32>, lang: &Vec<u32>, limits: &Limits) -> Result<RdfLiteral, ErrorKind> {
    let lexical = utf8(v, limits)?;
    if lang.len() == 0 {
        Ok(RdfLiteral {
            lexical,
            kind: LiteralKind::Datatype(rdf_iri(b"http://www.w3.org/2001/XMLSchema#string")),
        })
    } else {
        let tag = utf8(lang, limits)?;
        if well_formed(&tag) {
            Ok(RdfLiteral {
                lexical,
                kind: LiteralKind::Language(tag),
            })
        } else {
            Err(ErrorKind::InvalidLanguageTag)
        }
    }
}

/// The literal `v` of the datatype `d`.
fn typed_of(v: &Vec<u32>, d: &Vec<u32>, limits: &Limits) -> Result<RdfLiteral, ErrorKind> {
    let lexical = utf8(v, limits)?;
    let datatype = iri_of(d, limits)?;
    if lang_string(&datatype.spelling) {
        Err(ErrorKind::InvalidDatatype)
    } else {
        Ok(RdfLiteral {
            lexical,
            kind: LiteralKind::Datatype(datatype),
        })
    }
}

/// The bytes are rdf:langString.
fn lang_string(bytes: &Vec<u8>) -> bool {
    same_bytes(
        bytes,
        &constant(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"),
    )
}

// Blank nodes, rdf:ID values and triples.

/// `out` followed by the decimal digits of `n`.
fn digits(n: usize, out: Vec<u8>) -> Vec<u8> {
    let mut out = if n < 10 { out } else { digits(n / 10, out) };
    out.push(48 + (n % 10) as u8);
    out
}

/// `out` followed by the decimal digits of `n`, as code points.
fn digit_points(n: usize, out: Vec<u32>) -> Vec<u32> {
    let mut out = if n < 10 {
        out
    } else {
        digit_points(n / 10, out)
    };
    out.push(48 + (n % 10) as u32);
    out
}

/// The next generated blank node.
fn fresh(scope: &Vec<u8>, limits: &Limits, state: State) -> Result<(BlankNode, State), ErrorKind> {
    if state.blanks < limits.items {
        let mut label = Vec::new();
        label.push(255);
        let node = BlankNode {
            scope: copy_bytes(scope),
            label: digits(state.blanks, label),
        };
        Ok((
            node,
            State {
                triples: state.triples,
                blanks: state.blanks + 1,
                ids: state.ids,
            },
        ))
    } else {
        Err(ErrorKind::ResourceLimit)
    }
}

/// The blank node of an rdf:nodeID value.
fn node_id(v: &Vec<u32>, scope: &Vec<u8>, limits: &Limits) -> Result<BlankNode, ErrorKind> {
    if ncname(v) {
        let label = utf8(v, limits)?;
        Ok(BlankNode {
            scope: copy_bytes(scope),
            label,
        })
    } else {
        Err(ErrorKind::InvalidId)
    }
}

/// The rdf:ID value `v` with base `base` is not among the values from `k` on.
fn id_absent(ids: &Vec<Id>, v: &Vec<u32>, base: &Vec<u8>, k: usize) -> bool {
    if k < ids.len() {
        if same_id(&ids[k], v, base) {
            false
        } else {
            id_absent(ids, v, base, k + 1)
        }
    } else {
        true
    }
}

fn same_id(id: &Id, v: &Vec<u32>, base: &Vec<u8>) -> bool {
    same_word(&id.value, v) && same_bytes(&id.base, base)
}

/// The IRI of the rdf:ID value `v` given against `base` (section 5.4,
/// constraint-id), which is recorded.
fn id_iri(
    v: &Vec<u32>,
    base: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(RdfIri, State), ErrorKind> {
    if ncname(v) {
        let iri = resolved_id(base, v, limits)?;
        if id_absent(&state.ids, v, base, 0) {
            if state.ids.len() < limits.items {
                let mut ids = state.ids;
                ids.push(Id {
                    value: copy_word(v),
                    base: copy_bytes(base),
                });
                Ok((
                    iri,
                    State {
                        triples: state.triples,
                        blanks: state.blanks,
                        ids,
                    },
                ))
            } else {
                Err(ErrorKind::ResourceLimit)
            }
        } else {
            Err(ErrorKind::DuplicateId)
        }
    } else {
        Err(ErrorKind::InvalidId)
    }
}

/// The state with one more triple, within the item limit.
fn emit(state: State, triple: Triple, limits: &Limits) -> Result<State, ErrorKind> {
    if state.triples.len() < limits.items {
        let mut triples = state.triples;
        triples.push(triple);
        Ok(State {
            triples,
            blanks: state.blanks,
            ids: state.ids,
        })
    } else {
        Err(ErrorKind::ResourceLimit)
    }
}

fn copy_iri(iri: &RdfIri) -> RdfIri {
    RdfIri {
        spelling: copy_bytes(&iri.spelling),
    }
}

fn copy_blank(node: &BlankNode) -> BlankNode {
    BlankNode {
        scope: copy_bytes(&node.scope),
        label: copy_bytes(&node.label),
    }
}

fn copy_subject(subject: &Subject) -> Subject {
    match subject {
        Subject::Iri(iri) => Subject::Iri(copy_iri(iri)),
        Subject::Blank(node) => Subject::Blank(copy_blank(node)),
    }
}

fn copy_kind(kind: &LiteralKind) -> LiteralKind {
    match kind {
        LiteralKind::Datatype(iri) => LiteralKind::Datatype(copy_iri(iri)),
        LiteralKind::Language(tag) => LiteralKind::Language(copy_bytes(tag)),
    }
}

fn copy_object(object: &Object) -> Object {
    match object {
        Object::Iri(iri) => Object::Iri(copy_iri(iri)),
        Object::Blank(node) => Object::Blank(copy_blank(node)),
        Object::Literal(literal) => Object::Literal(RdfLiteral {
            lexical: copy_bytes(&literal.lexical),
            kind: copy_kind(&literal.kind),
        }),
    }
}

fn object_of(subject: &Subject) -> Object {
    match subject {
        Subject::Iri(iri) => Object::Iri(copy_iri(iri)),
        Subject::Blank(node) => Object::Blank(copy_blank(node)),
    }
}

fn rdf_triple(subject: &Subject, name: &[u8], object: Object) -> Triple {
    Triple {
        subject: copy_subject(subject),
        predicate: rdf_iri(name),
        object,
    }
}

/// The reification of `subject predicate object` by `r` (section 7.3).
fn reify(
    r: &RdfIri,
    subject: &Subject,
    predicate: &RdfIri,
    object: &Object,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    let node = Subject::Iri(copy_iri(r));
    let state1 = emit(
        state,
        rdf_triple(
            &node,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#subject",
            object_of(subject),
        ),
        limits,
    )?;
    let state2 = emit(
        state1,
        rdf_triple(
            &node,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate",
            Object::Iri(copy_iri(predicate)),
        ),
        limits,
    )?;
    let state3 = emit(
        state2,
        rdf_triple(
            &node,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#object",
            copy_object(object),
        ),
        limits,
    )?;
    emit(
        state3,
        rdf_triple(
            &node,
            b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
            Object::Iri(rdf_iri(
                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement",
            )),
        ),
        limits,
    )
}

// Attribute events (section 6.1.4).

/// `w` begins with `xml` in any case.
fn xml_letters(w: &Vec<u32>) -> bool {
    if 3 <= w.len() {
        letters_xml(w[0], w[1], w[2])
    } else {
        false
    }
}

fn letters_xml(a: u32, b: u32, c: u32) -> bool {
    (a == 120 || a == 88) && (b == 109 || b == 77) && (c == 108 || c == 76)
}

/// A reserved XML name, which RDF/XML removes (section 6.1.2).
fn reserved(a: &Attribute) -> bool {
    match &a.ns_prefix {
        Some(prefix) => xml_letters(prefix),
        None => xml_letters(&a.local_name),
    }
}

/// An attribute name without namespace that RDF/XML reads in the RDF
/// namespace.
fn unqualified(local: &Vec<u32>) -> bool {
    is_ascii(local, b"ID")
        || is_ascii(local, b"about")
        || is_ascii(local, b"resource")
        || is_ascii(local, b"parseType")
        || is_ascii(local, b"type")
}

/// The URI of an element or attribute name in namespace `ns`.
fn named_uri(ns: &Vec<u32>, local: &Vec<u32>, limits: &Limits) -> Result<Vec<u32>, ErrorKind> {
    if rdf_extension(ns) {
        Err(ErrorKind::InvalidName)
    } else {
        concat(ns, local, limits.term_bytes)
    }
}

/// The URI of an attribute event.
fn attribute_uri(a: &Attribute, limits: &Limits) -> Result<Vec<u32>, ErrorKind> {
    match &a.ns_name {
        Some(ns) => named_uri(ns, &a.local_name, limits),
        None => {
            if unqualified(&a.local_name) {
                concat(
                    &ascii_word(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
                    &a.local_name,
                    limits.term_bytes,
                )
            } else {
                Err(ErrorKind::UnqualifiedAttribute)
            }
        }
    }
}

/// The URI of an element event.
fn element_uri(e: &Element, limits: &Limits) -> Result<Vec<u32>, ErrorKind> {
    match &e.ns_name {
        Some(ns) => named_uri(ns, &e.local_name, limits),
        None => Err(ErrorKind::InvalidName),
    }
}

/// The events of the attributes from `i` on, after `out`.
fn events_from(
    attributes: &Vec<Attribute>,
    i: usize,
    mut out: Vec<Event>,
    limits: &Limits,
) -> Result<Vec<Event>, ErrorKind> {
    if i < attributes.len() {
        if reserved(&attributes[i]) {
            events_from(attributes, i + 1, out, limits)
        } else {
            let uri = attribute_uri(&attributes[i], limits)?;
            out.push(Event {
                uri,
                value: copy_word(&attributes[i].value),
            });
            events_from(attributes, i + 1, out, limits)
        }
    } else {
        Ok(out)
    }
}

/// No event from `k` on has the URI `uri`.
fn uri_absent(events: &Vec<Event>, uri: &Vec<u32>, k: usize) -> bool {
    if k < events.len() {
        if same_word(&events[k].uri, uri) {
            false
        } else {
            uri_absent(events, uri, k + 1)
        }
    } else {
        true
    }
}

/// The events from `i` on have distinct URIs.
fn distinct_from(events: &Vec<Event>, i: usize) -> bool {
    if i < events.len() {
        if uri_absent(events, &events[i].uri, i + 1) {
            distinct_from(events, i + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// The attribute in the XML namespace with local name `local`, from `i` on.
fn find_xml(attributes: &Vec<Attribute>, local: &[u8], i: usize) -> Option<usize> {
    if i < attributes.len() {
        if xml_attribute(&attributes[i], local) {
            Some(i)
        } else {
            find_xml(attributes, local, i + 1)
        }
    } else {
        None
    }
}

fn xml_attribute(a: &Attribute, local: &[u8]) -> bool {
    match &a.ns_name {
        Some(ns) => xml_named(ns, &a.local_name, local),
        None => false,
    }
}

fn xml_named(ns: &Vec<u32>, name: &Vec<u32>, local: &[u8]) -> bool {
    is_ascii(ns, b"http://www.w3.org/XML/1998/namespace") && is_ascii(name, local)
}

/// The base IRI of an element: its xml:base resolved against the base of
/// its parent (XML Base), or that base.
fn element_base(e: &Element, base: &Vec<u8>, limits: &Limits) -> Result<Vec<u8>, ErrorKind> {
    match find_xml(&e.attributes, b"base", 0) {
        Some(k) => {
            let reference = utf8(&e.attributes[k].value, limits)?;
            resolved_bytes(base, reference, limits)
        }
        None => Ok(copy_bytes(base)),
    }
}

/// The language of an element: its xml:lang, or the language of its parent.
fn element_lang(e: &Element, lang: &Vec<u32>) -> Vec<u32> {
    match find_xml(&e.attributes, b"lang", 0) {
        Some(k) => copy_word(&e.attributes[k].value),
        None => copy_word(lang),
    }
}

/// The element event of `e` in the base IRI and language of its parent.
fn prepare(
    e: &Element,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    limits: &Limits,
) -> Result<Prepared, ErrorKind> {
    let base1 = element_base(e, base, limits)?;
    let events = events_from(&e.attributes, 0, Vec::new(), limits)?;
    if distinct_from(&events, 0) {
        Ok(Prepared {
            base: base1,
            lang: element_lang(e, lang),
            events,
        })
    } else {
        Err(ErrorKind::DuplicateAttribute)
    }
}

/// The class of an attribute URI: 0 a property attribute, 1 rdf:ID,
/// 2 rdf:nodeID, 3 rdf:about, 4 rdf:resource, 5 rdf:parseType,
/// 6 rdf:datatype, 7 another syntax or old term.
fn class_of(uri: &Vec<u32>) -> u8 {
    if is_rdf(uri, b"ID") {
        1
    } else if is_rdf(uri, b"nodeID") {
        2
    } else if is_rdf(uri, b"about") {
        3
    } else if is_rdf(uri, b"resource") {
        4
    } else if is_rdf(uri, b"parseType") {
        5
    } else if is_rdf(uri, b"datatype") {
        6
    } else if other_syntax(uri) {
        7
    } else {
        0
    }
}

/// rdf:RDF, rdf:Description, rdf:li and the old terms.
fn other_syntax(uri: &Vec<u32>) -> bool {
    is_rdf(uri, b"RDF") || is_rdf(uri, b"Description") || is_rdf(uri, b"li") || old_term(uri)
}

fn old_term(uri: &Vec<u32>) -> bool {
    is_rdf(uri, b"aboutEach") || is_rdf(uri, b"aboutEachPrefix") || is_rdf(uri, b"bagID")
}

/// The first event from `i` on of class `class`.
fn find_class(events: &Vec<Event>, class: u8, i: usize) -> Option<usize> {
    if i < events.len() {
        if class_of(&events[i].uri) == class {
            Some(i)
        } else {
            find_class(events, class, i + 1)
        }
    } else {
        None
    }
}

/// Whether the attribute set `set` allows class `class`: 0 rdf:ID; 1 rdf:ID
/// and rdf:datatype; 2 rdf:ID and rdf:parseType; 3 rdf:ID, rdf:nodeID,
/// rdf:resource and property attributes; 4 rdf:ID, rdf:nodeID, rdf:about and
/// property attributes.
fn allows(set: u8, class: u8) -> bool {
    match set {
        0 => class == 1,
        1 => class == 1 || class == 6,
        2 => class == 1 || class == 5,
        3 => class == 0 || class == 1 || class == 2 || class == 4,
        _ => class == 0 || class == 1 || class == 2 || class == 3,
    }
}

/// The set `set` allows the events from `i` on.
fn within(events: &Vec<Event>, set: u8, i: usize) -> bool {
    if i < events.len() {
        if allows(set, class_of(&events[i].uri)) {
            within(events, set, i + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// No event has class `class`.
fn lacks(events: &Vec<Event>, class: u8) -> bool {
    match find_class(events, class, 0) {
        Some(_) => false,
        None => true,
    }
}

/// At most one of the classes `a` and `b` occurs among the events.
fn not_both(events: &Vec<Event>, a: u8, b: u8) -> bool {
    match find_class(events, a, 0) {
        Some(_) => lacks(events, b),
        None => true,
    }
}

// Node elements (section 7.2.11).

/// rdf:ID, rdf:nodeID and rdf:about: at most one of them.
fn one_identifier(events: &Vec<Event>) -> bool {
    not_both(events, 1, 2) && not_both(events, 1, 3) && not_both(events, 2, 3)
}

/// The URI is allowed on node elements.
fn node_uri(uri: &Vec<u32>) -> bool {
    match class_of(uri) {
        0 => true,
        7 => node_syntax(uri),
        _ => false,
    }
}

/// rdf:Description is the only other syntax term a node element may have.
fn node_syntax(uri: &Vec<u32>) -> bool {
    is_rdf(uri, b"Description")
}

/// The subject of a node element without rdf:ID and rdf:nodeID.
fn subject_about(
    p: &Prepared,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(Subject, State), ErrorKind> {
    match find_class(&p.events, 3, 0) {
        Some(k) => {
            let iri = resolved(&p.base, &p.events[k].value, limits)?;
            Ok((Subject::Iri(iri), state))
        }
        None => {
            let (node, state1) = fresh(scope, limits, state)?;
            Ok((Subject::Blank(node), state1))
        }
    }
}

/// The subject of a node element without rdf:ID.
fn subject_node(
    p: &Prepared,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(Subject, State), ErrorKind> {
    match find_class(&p.events, 2, 0) {
        Some(k) => {
            let node = node_id(&p.events[k].value, scope, limits)?;
            Ok((Subject::Blank(node), state))
        }
        None => subject_about(p, scope, limits, state),
    }
}

/// The subject of a node element: from rdf:ID, rdf:nodeID or rdf:about, or a
/// generated blank node.
fn subject_of(
    p: &Prepared,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(Subject, State), ErrorKind> {
    match find_class(&p.events, 1, 0) {
        Some(k) => {
            let (iri, state1) = id_iri(&p.events[k].value, &p.base, limits, state)?;
            Ok((Subject::Iri(iri), state1))
        }
        None => subject_node(p, scope, limits, state),
    }
}

/// The rdf:type triple of a typed node element.
fn type_triple(
    subject: &Subject,
    uri: &Vec<u32>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if is_rdf(uri, b"Description") {
        Ok(state)
    } else {
        let iri = iri_of(uri, limits)?;
        emit(
            state,
            rdf_triple(
                subject,
                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
                Object::Iri(iri),
            ),
            limits,
        )
    }
}

/// The triple of a property attribute: rdf:type with a resolved IRI, any
/// other with a literal in the language of the element.
fn attribute_triple(
    subject: &Subject,
    event: &Event,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if is_rdf(&event.uri, b"type") {
        let iri = resolved(base, &event.value, limits)?;
        emit(
            state,
            rdf_triple(
                subject,
                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
                Object::Iri(iri),
            ),
            limits,
        )
    } else {
        let predicate = iri_of(&event.uri, limits)?;
        let literal = literal_of(&event.value, lang, limits)?;
        emit(
            state,
            Triple {
                subject: copy_subject(subject),
                predicate,
                object: Object::Literal(literal),
            },
            limits,
        )
    }
}

/// The triples of the property attributes among the events from `i` on.
fn attribute_triples(
    subject: &Subject,
    events: &Vec<Event>,
    i: usize,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if i < events.len() {
        if class_of(&events[i].uri) == 0 {
            let state1 = attribute_triple(subject, &events[i], base, lang, limits, state)?;
            attribute_triples(subject, events, i + 1, base, lang, limits, state1)
        } else {
            attribute_triples(subject, events, i + 1, base, lang, limits, state)
        }
    } else {
        Ok(state)
    }
}

/// A node element in the base IRI and language of its parent: its subject
/// and the state after its triples.
fn node_element(
    e: &Element,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(Subject, State), ErrorKind> {
    let p = prepare(e, base, lang, limits)?;
    let uri = element_uri(e, limits)?;
    if node_uri(&uri) {
        node_body(e, &p, &uri, scope, limits, state)
    } else {
        Err(ErrorKind::InvalidName)
    }
}

fn node_body(
    e: &Element,
    p: &Prepared,
    uri: &Vec<u32>,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(Subject, State), ErrorKind> {
    if node_attributes(&p.events) {
        let (subject, state1) = subject_of(p, scope, limits, state)?;
        let state2 = type_triple(&subject, uri, limits, state1)?;
        let state3 = attribute_triples(&subject, &p.events, 0, &p.base, &p.lang, limits, state2)?;
        let state4 = property_elements(
            &e.children,
            0,
            &subject,
            &p.base,
            &p.lang,
            scope,
            limits,
            1,
            state3,
        )?;
        Ok((subject, state4))
    } else {
        Err(ErrorKind::InvalidAttributes)
    }
}

/// The attributes of a node element: at most one of rdf:ID, rdf:nodeID and
/// rdf:about, and property attributes.
fn node_attributes(events: &Vec<Event>) -> bool {
    within(events, 4, 0) && one_identifier(events)
}

// Property elements (sections 7.2.13 to 7.2.21).

/// The property elements among the children from `i` on, with the rdf:li
/// counter `li`.
fn property_elements(
    children: &Vec<Node>,
    i: usize,
    subject: &Subject,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    scope: &Vec<u8>,
    limits: &Limits,
    li: usize,
    state: State,
) -> Result<State, ErrorKind> {
    if i < children.len() {
        match &children[i] {
            Node::Text(text) => {
                if spaces_from(text, 0) {
                    property_elements(
                        children,
                        i + 1,
                        subject,
                        base,
                        lang,
                        scope,
                        limits,
                        li,
                        state,
                    )
                } else {
                    Err(ErrorKind::InvalidContent)
                }
            }
            Node::Element(e) => {
                let (li1, state1) =
                    property_element(e, subject, base, lang, scope, limits, li, state)?;
                property_elements(
                    children,
                    i + 1,
                    subject,
                    base,
                    lang,
                    scope,
                    limits,
                    li1,
                    state1,
                )
            }
        }
    } else {
        Ok(state)
    }
}

/// The predicate of a property element and the rdf:li counter after it
/// (section 7.4).
fn predicate_of(e: &Element, li: usize, limits: &Limits) -> Result<(RdfIri, usize), ErrorKind> {
    let uri = element_uri(e, limits)?;
    if is_rdf(&uri, b"li") {
        if li < limits.items {
            let member = digit_points(
                li,
                ascii_word(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#_"),
            );
            let iri = iri_of(&member, limits)?;
            Ok((iri, li + 1))
        } else {
            Err(ErrorKind::ResourceLimit)
        }
    } else if property_uri(&uri) {
        let iri = iri_of(&uri, limits)?;
        Ok((iri, li))
    } else {
        Err(ErrorKind::InvalidName)
    }
}

/// The URI is allowed on property elements.
fn property_uri(uri: &Vec<u32>) -> bool {
    match class_of(uri) {
        0 => true,
        7 => property_syntax(uri),
        _ => false,
    }
}

/// rdf:li is the only other syntax term a property element may have.
fn property_syntax(uri: &Vec<u32>) -> bool {
    is_rdf(uri, b"li")
}

/// The production of a property element: 0 parseType Resource, 1 parseType
/// Collection, 2 another parseType, 3 empty, 4 a node element inside, 5 text.
fn production(e: &Element, events: &Vec<Event>) -> u8 {
    match find_class(events, 5, 0) {
        Some(k) => parse_kind(&events[k].value),
        None => content_kind(&e.children),
    }
}

fn parse_kind(value: &Vec<u32>) -> u8 {
    if is_ascii(value, b"Resource") {
        0
    } else if is_ascii(value, b"Collection") {
        1
    } else {
        2
    }
}

fn content_kind(children: &Vec<Node>) -> u8 {
    if children.len() == 0 {
        3
    } else if has_element(children, 0) {
        4
    } else {
        5
    }
}

fn has_element(children: &Vec<Node>, i: usize) -> bool {
    if i < children.len() {
        match &children[i] {
            Node::Element(_) => true,
            Node::Text(_) => has_element(children, i + 1),
        }
    } else {
        false
    }
}

/// A property element of the node with subject `subject`: the rdf:li counter
/// and the state after its triples.
fn property_element(
    e: &Element,
    subject: &Subject,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    scope: &Vec<u8>,
    limits: &Limits,
    li: usize,
    state: State,
) -> Result<(usize, State), ErrorKind> {
    let p = prepare(e, base, lang, limits)?;
    let (predicate, li1) = predicate_of(e, li, limits)?;
    let state1 = property_body(e, &p, subject, predicate, scope, limits, state)?;
    Ok((li1, state1))
}

fn property_body(
    e: &Element,
    p: &Prepared,
    subject: &Subject,
    predicate: RdfIri,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    match production(e, &p.events) {
        0 => parse_resource(e, p, subject, predicate, scope, limits, state),
        1 => parse_collection(e, p, subject, predicate, scope, limits, state),
        2 => Err(ErrorKind::UnsupportedParseType),
        3 => empty_property(p, subject, predicate, scope, limits, state),
        4 => resource_property(e, p, subject, predicate, scope, limits, state),
        _ => literal_property(e, p, subject, predicate, limits, state),
    }
}

/// The statement `subject predicate object` and, when the element has
/// rdf:ID, its reification.
fn stated(
    subject: &Subject,
    predicate: RdfIri,
    object: Object,
    p: &Prepared,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    match find_class(&p.events, 1, 0) {
        Some(k) => {
            let (r, state1) = id_iri(&p.events[k].value, &p.base, limits, state)?;
            let state2 = emit(
                state1,
                Triple {
                    subject: copy_subject(subject),
                    predicate: copy_iri(&predicate),
                    object: copy_object(&object),
                },
                limits,
            )?;
            reify(&r, subject, &predicate, &object, limits, state2)
        }
        None => emit(
            state,
            Triple {
                subject: copy_subject(subject),
                predicate,
                object,
            },
            limits,
        ),
    }
}

/// The single node element among the children from `i` on, which are white
/// space otherwise; `found` is the one before `i`.
fn single_element(
    children: &Vec<Node>,
    i: usize,
    found: Option<usize>,
) -> Result<usize, ErrorKind> {
    if i < children.len() {
        match &children[i] {
            Node::Text(text) => {
                if spaces_from(text, 0) {
                    single_element(children, i + 1, found)
                } else {
                    Err(ErrorKind::InvalidContent)
                }
            }
            Node::Element(_) => match found {
                Some(_) => Err(ErrorKind::InvalidContent),
                None => single_element(children, i + 1, Some(i)),
            },
        }
    } else {
        match found {
            Some(k) => Ok(k),
            None => Err(ErrorKind::InvalidContent),
        }
    }
}

/// resourcePropertyElt (section 7.2.15).
fn resource_property(
    e: &Element,
    p: &Prepared,
    subject: &Subject,
    predicate: RdfIri,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if within(&p.events, 0, 0) {
        let k = single_element(&e.children, 0, None)?;
        match &e.children[k] {
            Node::Element(n) => {
                let (object, state1) = node_element(n, &p.base, &p.lang, scope, limits, state)?;
                stated(subject, predicate, object_of(&object), p, limits, state1)
            }
            Node::Text(_) => Err(ErrorKind::InvalidContent),
        }
    } else {
        Err(ErrorKind::InvalidAttributes)
    }
}

/// literalPropertyElt (section 7.2.16).
fn literal_property(
    e: &Element,
    p: &Prepared,
    subject: &Subject,
    predicate: RdfIri,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if within(&p.events, 1, 0) {
        if e.children.len() == 1 {
            match &e.children[0] {
                Node::Text(text) => {
                    let literal = text_literal(text, p, limits)?;
                    stated(
                        subject,
                        predicate,
                        Object::Literal(literal),
                        p,
                        limits,
                        state,
                    )
                }
                Node::Element(_) => Err(ErrorKind::InvalidContent),
            }
        } else {
            Err(ErrorKind::InvalidContent)
        }
    } else {
        Err(ErrorKind::InvalidAttributes)
    }
}

/// The literal of a text: typed by rdf:datatype, or in the language of the
/// element.
fn text_literal(text: &Vec<u32>, p: &Prepared, limits: &Limits) -> Result<RdfLiteral, ErrorKind> {
    match find_class(&p.events, 6, 0) {
        Some(k) => typed_of(text, &p.events[k].value, limits),
        None => literal_of(text, &p.lang, limits),
    }
}

/// parseTypeResourcePropertyElt (section 7.2.18).
fn parse_resource(
    e: &Element,
    p: &Prepared,
    subject: &Subject,
    predicate: RdfIri,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if within(&p.events, 2, 0) {
        let (node, state1) = fresh(scope, limits, state)?;
        let inner = Subject::Blank(node);
        let state2 = stated(subject, predicate, object_of(&inner), p, limits, state1)?;
        property_elements(
            &e.children,
            0,
            &inner,
            &p.base,
            &p.lang,
            scope,
            limits,
            1,
            state2,
        )
    } else {
        Err(ErrorKind::InvalidAttributes)
    }
}

/// parseTypeCollectionPropertyElt (section 7.2.19).
fn parse_collection(
    e: &Element,
    p: &Prepared,
    subject: &Subject,
    predicate: RdfIri,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if within(&p.events, 2, 0) {
        let (head, state1) = node_list(&e.children, 0, &p.base, &p.lang, scope, limits, state)?;
        stated(subject, predicate, object_of(&head), p, limits, state1)
    } else {
        Err(ErrorKind::InvalidAttributes)
    }
}

/// The members of a collection from `i` on: the first list node, or rdf:nil.
fn node_list(
    children: &Vec<Node>,
    i: usize,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(Subject, State), ErrorKind> {
    if i < children.len() {
        match &children[i] {
            Node::Text(text) => {
                if spaces_from(text, 0) {
                    node_list(children, i + 1, base, lang, scope, limits, state)
                } else {
                    Err(ErrorKind::InvalidContent)
                }
            }
            Node::Element(f) => {
                let (node, state1) = fresh(scope, limits, state)?;
                let list = Subject::Blank(node);
                let (member, state2) = node_element(f, base, lang, scope, limits, state1)?;
                let (rest, state3) = node_list(children, i + 1, base, lang, scope, limits, state2)?;
                let state4 = emit(
                    state3,
                    rdf_triple(
                        &list,
                        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#first",
                        object_of(&member),
                    ),
                    limits,
                )?;
                let state5 = emit(
                    state4,
                    rdf_triple(
                        &list,
                        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest",
                        object_of(&rest),
                    ),
                    limits,
                )?;
                Ok((list, state5))
            }
        }
    } else {
        Ok((
            Subject::Iri(rdf_iri(b"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil")),
            state,
        ))
    }
}

/// emptyPropertyElt (section 7.2.21): an empty literal, an empty typed
/// literal, or a resource with property attributes.
fn empty_property(
    p: &Prepared,
    subject: &Subject,
    predicate: RdfIri,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if within(&p.events, 0, 0) {
        let literal = literal_of(&Vec::new(), &p.lang, limits)?;
        stated(
            subject,
            predicate,
            Object::Literal(literal),
            p,
            limits,
            state,
        )
    } else if within(&p.events, 1, 0) {
        let literal = text_literal(&Vec::new(), p, limits)?;
        stated(
            subject,
            predicate,
            Object::Literal(literal),
            p,
            limits,
            state,
        )
    } else {
        empty_resource(p, subject, predicate, scope, limits, state)
    }
}

/// An empty property element with rdf:resource, rdf:nodeID or property
/// attributes.
fn empty_resource(
    p: &Prepared,
    subject: &Subject,
    predicate: RdfIri,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if lacks(&p.events, 6) {
        if within(&p.events, 3, 0) {
            if not_both(&p.events, 2, 4) {
                let (object, state1) = empty_object(p, scope, limits, state)?;
                let state2 =
                    attribute_triples(&object, &p.events, 0, &p.base, &p.lang, limits, state1)?;
                stated(subject, predicate, object_of(&object), p, limits, state2)
            } else {
                Err(ErrorKind::InvalidAttributes)
            }
        } else {
            Err(ErrorKind::InvalidAttributes)
        }
    } else {
        Err(ErrorKind::UnsupportedDatatype)
    }
}

/// The object of an empty property element: rdf:resource, rdf:nodeID or a
/// generated blank node.
fn empty_object(
    p: &Prepared,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<(Subject, State), ErrorKind> {
    match find_class(&p.events, 4, 0) {
        Some(k) => {
            let iri = resolved(&p.base, &p.events[k].value, limits)?;
            Ok((Subject::Iri(iri), state))
        }
        None => match find_class(&p.events, 2, 0) {
            Some(k) => {
                let node = node_id(&p.events[k].value, scope, limits)?;
                Ok((Subject::Blank(node), state))
            }
            None => {
                let (node, state1) = fresh(scope, limits, state)?;
                Ok((Subject::Blank(node), state1))
            }
        },
    }
}

// Documents (sections 7.2.8 to 7.2.10).

/// The node elements among the children from `i` on.
fn node_elements(
    children: &Vec<Node>,
    i: usize,
    base: &Vec<u8>,
    lang: &Vec<u32>,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    if i < children.len() {
        match &children[i] {
            Node::Text(text) => {
                if spaces_from(text, 0) {
                    node_elements(children, i + 1, base, lang, scope, limits, state)
                } else {
                    Err(ErrorKind::InvalidContent)
                }
            }
            Node::Element(n) => {
                let (_, state1) = node_element(n, base, lang, scope, limits, state)?;
                node_elements(children, i + 1, base, lang, scope, limits, state1)
            }
        }
    } else {
        Ok(state)
    }
}

/// The root element rdf:RDF with its node elements.
fn rdf_root(
    e: &Element,
    base: &Vec<u8>,
    scope: &Vec<u8>,
    limits: &Limits,
    state: State,
) -> Result<State, ErrorKind> {
    let p = prepare(e, base, &Vec::new(), limits)?;
    if p.events.len() == 0 {
        node_elements(&e.children, 0, &p.base, &p.lang, scope, limits, state)
    } else {
        Err(ErrorKind::InvalidAttributes)
    }
}

/// The graph of an element tree read against the base IRI `base`, with
/// blank nodes in `scope`: from the root rdf:RDF, or from a root node element
/// (section 7.2.1).
pub fn graph(
    root: &Element,
    base: &Vec<u8>,
    scope: &Vec<u8>,
    limits: &Limits,
) -> Result<RawGraph, ErrorKind> {
    if base.len() <= limits.term_bytes {
        let state = State {
            triples: Vec::new(),
            blanks: 0,
            ids: Vec::new(),
        };
        let uri = element_uri(root, limits)?;
        if is_rdf(&uri, b"RDF") {
            let state1 = rdf_root(root, base, scope, limits, state)?;
            Ok(RawGraph {
                triples: state1.triples,
            })
        } else {
            let (_, state1) = node_element(root, base, &Vec::new(), scope, limits, state)?;
            Ok(RawGraph {
                triples: state1.triples,
            })
        }
    } else {
        Err(ErrorKind::ResourceLimit)
    }
}

/// Reads an RDF/XML document against the base IRI `base`, with blank nodes in
/// `scope`.
pub fn read_with_limits(
    bytes: &Vec<u8>,
    base: &Vec<u8>,
    scope: &Vec<u8>,
    limits: &Limits,
) -> ReadResult {
    match xml::read(
        bytes,
        &xml::Limits {
            expansion: limits.expansion,
        },
    ) {
        xml::ReadResult::Document(document) => match graph(&document.root, base, scope, limits) {
            Ok(g) => ReadResult::Graph(g),
            Err(kind) => ReadResult::Error(kind),
        },
        xml::ReadResult::Error(e) => ReadResult::XmlError(e),
    }
}
