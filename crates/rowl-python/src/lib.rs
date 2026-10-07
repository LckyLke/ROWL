//! A C interface to the reasoner, used by the Python package in
//! `bindings/python` through `ctypes`.
//!
//! This is unverified glue: it converts between C buffers and the verified
//! pipeline and adds no reasoning of its own. Every answer comes from
//! [`rowl::reasoner::Reasoner`], whose reader, mapping and queries are proved
//! against the OWL 2 Direct Semantics.
//!
//! Text crosses the interface as UTF-8 bytes with an explicit length. A query
//! answers 1 (yes), 0 (no), -1 (no answer: the question is outside the
//! supported fragment or a limit was reached) or -2 (a null handle or text that
//! is not UTF-8). Lists and the OWL 2 DL verdict come back as JSON text that
//! the caller releases with [`rowl_string_free`].
use rowl::experimental::model::{
    AtLeastTwo, Axiom, DataProperty, Datatype, Individual, Iri, Literal, NamedIndividual,
    ObjectProperty, ObjectPropertyExpression,
};
use rowl::reasoner::{
    default_limits, document_error_words, named, rdfxml_error_words, xml_error_words, Classified,
    Document, LoadError, Reasoner, Syntax,
};
use std::ffi::{c_char, CStr, CString};
use std::ptr;

/// A document read once.
pub struct RowlReasoner {
    inner: Reasoner,
}

/// The document was read.
pub const ROWL_LOADED: i32 = 0;
/// The verified reader rejected the document.
pub const ROWL_REJECTED: i32 = 1;
/// The read document does not map into the OWL model.
pub const ROWL_UNSUPPORTED: i32 = 2;
/// The document pointer was null.
pub const ROWL_INVALID: i32 = 3;
/// The N-Triples or Turtle graph is not the RDF mapping of an OWL ontology
/// that the verified reverse mapping reads.
pub const ROWL_UNMAPPED: i32 = 4;
/// A document of the import closure imports an IRI that is the ontology IRI
/// or version IRI of no document of the catalog.
pub const ROWL_MISSING_IMPORT: i32 = 5;
/// A document of the import closure imports an IRI that several documents of
/// the catalog have as their ontology IRI or version IRI.
pub const ROWL_AMBIGUOUS_IMPORT: i32 = 6;
/// The import closure could not be assembled for another reason.
pub const ROWL_CLOSURE: i32 = 7;

/// The syntax code of a Functional Syntax document of a catalog.
pub const ROWL_SYNTAX_FUNCTIONAL: i32 = 0;
/// The syntax code of an N-Triples document of a catalog.
pub const ROWL_SYNTAX_NTRIPLES: i32 = 1;
/// The syntax code of a Turtle document of a catalog, read without a base IRI.
pub const ROWL_SYNTAX_TURTLE: i32 = 2;
/// The syntax code of an RDF/XML document of a catalog, read without a base
/// IRI: relative IRIs need an `xml:base` in force.
pub const ROWL_SYNTAX_RDFXML: i32 = 3;

const INVALID_ARGUMENT: i32 = -2;

fn answer(value: Option<bool>) -> i32 {
    match value {
        Some(true) => 1,
        Some(false) => 0,
        None => -1,
    }
}

/// The bytes `data[..len]`; `None` for a null pointer with a nonzero length.
///
/// # Safety
/// `data` must be null or point to `len` bytes that stay readable for `'a`.
unsafe fn bytes<'a>(data: *const u8, len: usize) -> Option<&'a [u8]> {
    if data.is_null() {
        if len == 0 {
            Some(&[])
        } else {
            None
        }
    } else {
        // SAFETY: the caller guarantees `len` readable bytes at `data`.
        Some(unsafe { std::slice::from_raw_parts(data, len) })
    }
}

/// The UTF-8 text `data[..len]`.
///
/// # Safety
/// As for [`bytes`].
unsafe fn text<'a>(data: *const u8, len: usize) -> Option<&'a str> {
    // SAFETY: forwarded from the caller.
    unsafe { bytes(data, len) }.and_then(|found| std::str::from_utf8(found).ok())
}

/// The reasoner behind a handle.
///
/// # Safety
/// `reasoner` must be null or a live handle from
/// [`rowl_reasoner_from_functional`], [`rowl_reasoner_from_ntriples`] or
/// [`rowl_reasoner_from_turtle`].
unsafe fn handle<'a>(reasoner: *const RowlReasoner) -> Option<&'a Reasoner> {
    if reasoner.is_null() {
        None
    } else {
        // SAFETY: the caller guarantees a live handle.
        Some(unsafe { &(*reasoner).inner })
    }
}

/// Owned C text for the caller, or null if the text has an interior NUL.
fn into_c(text: String) -> *mut c_char {
    match CString::new(text) {
        Ok(owned) => owned.into_raw(),
        Err(_) => ptr::null_mut(),
    }
}

/// `value` as a JSON string.
fn json_string(out: &mut String, value: &str) {
    out.push('"');
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// `items` as a JSON array of strings.
fn json_list(out: &mut String, items: &[String]) {
    out.push('[');
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        json_string(out, item);
    }
    out.push(']');
}

/// A classification as a JSON array of objects.
fn json_classification(classified: &[Classified]) -> String {
    let mut out = String::from("[");
    for (index, entry) in classified.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        out.push_str("{\"class\":");
        json_string(&mut out, &entry.class);
        out.push_str(",\"satisfiable\":");
        out.push_str(if entry.satisfiable { "true" } else { "false" });
        out.push_str(",\"superclasses\":");
        json_list(&mut out, &entry.superclasses);
        out.push('}');
    }
    out.push(']');
    out
}

/// The status code of a load error.
fn status_of(error: &LoadError) -> i32 {
    match error {
        LoadError::Document(_)
        | LoadError::Triples(_)
        | LoadError::Turtle(_)
        | LoadError::Xml(_)
        | LoadError::RdfXml(_)
        | LoadError::TooLong => ROWL_REJECTED,
        LoadError::Graph => ROWL_UNMAPPED,
        LoadError::Unsupported => ROWL_UNSUPPORTED,
        LoadError::InDocument { error, .. } => status_of(error),
        LoadError::MissingImport { .. } => ROWL_MISSING_IMPORT,
        LoadError::AmbiguousImport { .. } => ROWL_AMBIGUOUS_IMPORT,
        LoadError::Closure(_) => ROWL_CLOSURE,
    }
}

/// A load error in words.
fn load_message(error: &LoadError) -> String {
    match error {
        LoadError::Document(error) => document_error_words(error),
        LoadError::Triples(error) => format!("N-Triples parse error at byte {}", error.offset),
        LoadError::Turtle(error) => format!("Turtle parse error at byte {}", error.offset),
        LoadError::Xml(error) => xml_error_words(error),
        LoadError::RdfXml(kind) => format!("not an RDF/XML graph: {}", rdfxml_error_words(*kind)),
        LoadError::TooLong => "the document is too long for the RDF/XML reader's limits".into(),
        LoadError::Graph => {
            "the graph is not the RDF mapping of an OWL ontology the verified mapping reads".into()
        }
        LoadError::Unsupported => "the document does not map into the OWL model".into(),
        LoadError::InDocument { document, error } => format!("{document}: {}", load_message(error)),
        LoadError::MissingImport { document, iri } => format!(
            "{document}: imports {iri}, which is the ontology IRI or version IRI of no document of the catalog"
        ),
        LoadError::AmbiguousImport {
            document,
            iri,
            first,
            second,
        } => format!(
            "{document}: imports {iri}, which is the ontology IRI or version IRI of both {first} and {second}"
        ),
        LoadError::Closure(reason) => reason.clone(),
    }
}

/// The status code and handle of a load.
fn loaded(result: Result<Reasoner, LoadError>) -> (i32, *mut RowlReasoner) {
    match result {
        Ok(inner) => (ROWL_LOADED, Box::into_raw(Box::new(RowlReasoner { inner }))),
        Err(error) => (status_of(&error), ptr::null_mut()),
    }
}

/// The library's version as NUL-terminated text owned by the library.
#[no_mangle]
pub extern "C" fn rowl_version() -> *const c_char {
    static VERSION: &CStr = c"0.0.0";
    VERSION.as_ptr()
}

/// Read a Functional Syntax document. Returns a handle for the
/// other functions, or null with `status` set to [`ROWL_REJECTED`],
/// [`ROWL_UNSUPPORTED`] or [`ROWL_INVALID`].
///
/// # Safety
/// `data` must point to `len` readable bytes (or be null with `len` zero), and
/// `status` must be null or point to a writable `i32`.
#[no_mangle]
pub unsafe extern "C" fn rowl_reasoner_from_functional(
    data: *const u8,
    len: usize,
    status: *mut i32,
) -> *mut RowlReasoner {
    // SAFETY: forwarded from the caller.
    let (code, reasoner) = match unsafe { bytes(data, len) } {
        None => (ROWL_INVALID, ptr::null_mut()),
        Some(source) => loaded(Reasoner::from_functional(source, &default_limits())),
    };
    if !status.is_null() {
        // SAFETY: the caller guarantees that a non-null `status` is writable.
        unsafe { *status = code };
    }
    reasoner
}

/// Read an N-Triples document and the OWL ontology its graph encodes.
/// Returns a handle for the other functions, or null with `status`
/// set to [`ROWL_REJECTED`], [`ROWL_UNMAPPED`], [`ROWL_UNSUPPORTED`] or
/// [`ROWL_INVALID`].
///
/// # Safety
/// As for [`rowl_reasoner_from_functional`].
#[no_mangle]
pub unsafe extern "C" fn rowl_reasoner_from_ntriples(
    data: *const u8,
    len: usize,
    status: *mut i32,
) -> *mut RowlReasoner {
    // SAFETY: forwarded from the caller.
    let (code, reasoner) = match unsafe { bytes(data, len) } {
        None => (ROWL_INVALID, ptr::null_mut()),
        Some(source) => loaded(Reasoner::from_ntriples(source)),
    };
    if !status.is_null() {
        // SAFETY: the caller guarantees that a non-null `status` is writable.
        unsafe { *status = code };
    }
    reasoner
}

/// Read a Turtle document and the OWL ontology its graph encodes. A relative
/// IRI needs an `@base` or `BASE` directive before it. Returns a handle for
/// the other functions, or null with `status` set to [`ROWL_REJECTED`],
/// [`ROWL_UNMAPPED`], [`ROWL_UNSUPPORTED`] or [`ROWL_INVALID`].
///
/// # Safety
/// As for [`rowl_reasoner_from_functional`].
#[no_mangle]
pub unsafe extern "C" fn rowl_reasoner_from_turtle(
    data: *const u8,
    len: usize,
    status: *mut i32,
) -> *mut RowlReasoner {
    // SAFETY: forwarded from the caller.
    let (code, reasoner) = match unsafe { bytes(data, len) } {
        None => (ROWL_INVALID, ptr::null_mut()),
        Some(source) => loaded(Reasoner::from_turtle(source)),
    };
    if !status.is_null() {
        // SAFETY: the caller guarantees that a non-null `status` is writable.
        unsafe { *status = code };
    }
    reasoner
}

/// Read a Turtle document whose relative IRIs resolve against the UTF-8 base
/// IRI of `base_len` bytes at `base` until the document declares its own base.
/// Returns a handle as [`rowl_reasoner_from_turtle`] does.
///
/// # Safety
/// As for [`rowl_reasoner_from_functional`]; `base` must be null with length
/// zero or point to `base_len` readable bytes.
#[no_mangle]
pub unsafe extern "C" fn rowl_reasoner_from_turtle_with_base(
    data: *const u8,
    len: usize,
    base: *const u8,
    base_len: usize,
    status: *mut i32,
) -> *mut RowlReasoner {
    // SAFETY: forwarded from the caller.
    let (code, reasoner) = match unsafe { (bytes(data, len), bytes(base, base_len)) } {
        (Some(source), Some(base)) => loaded(Reasoner::from_turtle_with_base(source, base)),
        _ => (ROWL_INVALID, ptr::null_mut()),
    };
    if !status.is_null() {
        // SAFETY: the caller guarantees that a non-null `status` is writable.
        unsafe { *status = code };
    }
    reasoner
}

/// Read an RDF/XML document and the OWL ontology its graph encodes, with the
/// verified XML and RDF/XML readers. Relative IRIs resolve against the UTF-8
/// base IRI of `base_len` bytes at `base` (empty for none) until `xml:base`
/// gives another. Returns a handle for the other functions, or null with
/// `status` set to [`ROWL_REJECTED`], [`ROWL_UNMAPPED`], [`ROWL_UNSUPPORTED`]
/// or [`ROWL_INVALID`].
///
/// # Safety
/// As for [`rowl_reasoner_from_turtle_with_base`].
#[no_mangle]
pub unsafe extern "C" fn rowl_reasoner_from_rdfxml(
    data: *const u8,
    len: usize,
    base: *const u8,
    base_len: usize,
    status: *mut i32,
) -> *mut RowlReasoner {
    // SAFETY: forwarded from the caller.
    let (code, reasoner) = match unsafe { (bytes(data, len), bytes(base, base_len)) } {
        (Some(source), Some(base)) => loaded(Reasoner::from_rdfxml_with_base(source, base)),
        _ => (ROWL_INVALID, ptr::null_mut()),
    };
    if !status.is_null() {
        // SAFETY: the caller guarantees that a non-null `status` is writable.
        unsafe { *status = code };
    }
    reasoner
}

/// Read the import closure of the document at position `root` of a catalog
/// of `count` documents: document `i` has the `lens[i]` bytes at `datas[i]`,
/// the syntax code `syntaxes[i]` and, unless `names` is null, the UTF-8 name
/// of `name_lens[i]` bytes at `names[i]`, which messages use. Every document is
/// read by its verified reader, and the verified assembly follows the import
/// IRIs through the catalog; nothing is fetched. Returns a handle, or null with
/// `status` set to [`ROWL_REJECTED`], [`ROWL_UNMAPPED`], [`ROWL_UNSUPPORTED`],
/// [`ROWL_MISSING_IMPORT`], [`ROWL_AMBIGUOUS_IMPORT`], [`ROWL_CLOSURE`] or
/// [`ROWL_INVALID`] and, unless `message` is null, `*message` set to the reason
/// in words, which the caller releases with [`rowl_string_free`].
///
/// # Safety
/// `datas`, `lens` and `syntaxes` must point to `count` readable entries,
/// each data pointer to its length of readable bytes (or be null with length
/// zero); `names` and `name_lens` must be null or point to `count` entries
/// likewise; `status` and `message` must be null or writable.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn rowl_reasoner_from_documents(
    datas: *const *const u8,
    lens: *const usize,
    syntaxes: *const i32,
    names: *const *const u8,
    name_lens: *const usize,
    count: usize,
    root: usize,
    status: *mut i32,
    message: *mut *mut c_char,
) -> *mut RowlReasoner {
    // SAFETY: forwarded from the caller.
    let documents = unsafe { catalog(datas, lens, syntaxes, names, name_lens, count) };
    let (code, reasoner, text) = match documents {
        None => (ROWL_INVALID, ptr::null_mut(), None),
        Some(documents) => match Reasoner::from_documents(documents, root, &default_limits()) {
            Ok(inner) => (
                ROWL_LOADED,
                Box::into_raw(Box::new(RowlReasoner { inner })),
                None,
            ),
            Err(error) => (
                status_of(&error),
                ptr::null_mut(),
                Some(load_message(&error)),
            ),
        },
    };
    if !status.is_null() {
        // SAFETY: the caller guarantees that a non-null `status` is writable.
        unsafe { *status = code };
    }
    if !message.is_null() {
        let text = match text {
            Some(text) => into_c(text),
            None => ptr::null_mut(),
        };
        // SAFETY: the caller guarantees that a non-null `message` is writable.
        unsafe { *message = text };
    }
    reasoner
}

/// The documents of a catalog from C arrays; `None` for a null array, an
/// unknown syntax code or a name that is not UTF-8.
///
/// # Safety
/// As for [`rowl_reasoner_from_documents`].
unsafe fn catalog(
    datas: *const *const u8,
    lens: *const usize,
    syntaxes: *const i32,
    names: *const *const u8,
    name_lens: *const usize,
    count: usize,
) -> Option<Vec<Document>> {
    if count > 0 && (datas.is_null() || lens.is_null() || syntaxes.is_null()) {
        return None;
    }
    if !names.is_null() && name_lens.is_null() {
        return None;
    }
    let mut documents = Vec::with_capacity(count);
    for index in 0..count {
        // SAFETY: the caller guarantees `count` readable entries in each array.
        let (data, len, code) =
            unsafe { (*datas.add(index), *lens.add(index), *syntaxes.add(index)) };
        // SAFETY: the caller guarantees `len` readable bytes at `data`.
        let bytes = unsafe { bytes(data, len) }?.to_vec();
        let syntax = match code {
            ROWL_SYNTAX_FUNCTIONAL => Syntax::Functional,
            ROWL_SYNTAX_NTRIPLES => Syntax::NTriples,
            ROWL_SYNTAX_TURTLE => Syntax::Turtle(Vec::new()),
            ROWL_SYNTAX_RDFXML => Syntax::RdfXml(Vec::new()),
            _ => return None,
        };
        let name = if names.is_null() {
            format!("document {index}")
        } else {
            // SAFETY: the caller guarantees `count` readable names with their lengths.
            let (name, name_len) = unsafe { (*names.add(index), *name_lens.add(index)) };
            // SAFETY: forwarded from the caller.
            unsafe { text(name, name_len) }?.to_string()
        };
        documents.push(Document {
            name,
            syntax,
            bytes,
        });
    }
    Some(documents)
}

/// Release a handle. Null is ignored.
///
/// # Safety
/// `reasoner` must be null or a live handle, which is not used afterwards.
#[no_mangle]
pub unsafe extern "C" fn rowl_reasoner_free(reasoner: *mut RowlReasoner) {
    if !reasoner.is_null() {
        // SAFETY: the handle came from `Box::into_raw` and is released once.
        drop(unsafe { Box::from_raw(reasoner) });
    }
}

/// Whether the axioms have a model.
///
/// # Safety
/// `reasoner` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn rowl_consistent(reasoner: *const RowlReasoner) -> i32 {
    // SAFETY: forwarded from the caller.
    match unsafe { handle(reasoner) } {
        Some(found) => answer(found.consistent()),
        None => INVALID_ARGUMENT,
    }
}

/// Whether some model has an instance of the named class.
///
/// # Safety
/// `reasoner` must be null or a live handle; `class` must point to
/// `class_len` readable bytes.
#[no_mangle]
pub unsafe extern "C" fn rowl_satisfiable(
    reasoner: *const RowlReasoner,
    class: *const u8,
    class_len: usize,
) -> i32 {
    // SAFETY: forwarded from the caller.
    match unsafe { (handle(reasoner), text(class, class_len)) } {
        (Some(found), Some(iri)) => answer(found.satisfiable(&named(iri))),
        _ => INVALID_ARGUMENT,
    }
}

/// Whether every instance of the class `sub` is an instance of `sup` in every
/// model.
///
/// # Safety
/// `reasoner` must be null or a live handle; `sub` and `sup` must point to
/// `sub_len` and `sup_len` readable bytes.
#[no_mangle]
pub unsafe extern "C" fn rowl_subsumed(
    reasoner: *const RowlReasoner,
    sub: *const u8,
    sub_len: usize,
    sup: *const u8,
    sup_len: usize,
) -> i32 {
    // SAFETY: forwarded from the caller.
    match unsafe { (handle(reasoner), text(sub, sub_len), text(sup, sup_len)) } {
        (Some(found), Some(sub), Some(sup)) => answer(found.subsumed(&named(sub), &named(sup))),
        _ => INVALID_ARGUMENT,
    }
}

/// Whether the named individual is an instance of the named class in every
/// model.
///
/// # Safety
/// `reasoner` must be null or a live handle; `individual` and `class` must
/// point to `individual_len` and `class_len` readable bytes.
#[no_mangle]
pub unsafe extern "C" fn rowl_instance_of(
    reasoner: *const RowlReasoner,
    individual: *const u8,
    individual_len: usize,
    class: *const u8,
    class_len: usize,
) -> i32 {
    // SAFETY: forwarded from the caller.
    match unsafe {
        (
            handle(reasoner),
            text(individual, individual_len),
            text(class, class_len),
        )
    } {
        (Some(found), Some(individual), Some(class)) => {
            answer(found.instance_of(individual, &named(class)))
        }
        _ => INVALID_ARGUMENT,
    }
}

/// The fact of `kind` about named individuals: 0 an object property assertion
/// (`first` the property, `second` and `third` the individuals), 1 its
/// negative, 2 a data property assertion (`first` the property, `second` the
/// individual, `third` the lexical form and `fourth` the datatype IRI), 3 its
/// negative, 4 the equality and 5 the inequality of `first` and `second`.
fn fact(kind: i32, first: &str, second: &str, third: &str, fourth: &str) -> Option<Axiom> {
    let iri = |text: &str| Iri {
        spelling: text.as_bytes().to_vec(),
    };
    let individual = |text: &str| Individual::Named(NamedIndividual { iri: iri(text) });
    let role = || ObjectPropertyExpression::Property(ObjectProperty { iri: iri(first) });
    let property = || DataProperty { iri: iri(first) };
    let literal = || Literal {
        lexical: third.as_bytes().to_vec(),
        datatype: Datatype { iri: iri(fourth) },
    };
    let pair = || AtLeastTwo {
        first: individual(first),
        second: individual(second),
        rest: Vec::new(),
    };
    match kind {
        0 => Some(Axiom::ObjectPropertyAssertion(
            role(),
            individual(second),
            individual(third),
        )),
        1 => Some(Axiom::NegativeObjectPropertyAssertion(
            role(),
            individual(second),
            individual(third),
        )),
        2 => Some(Axiom::DataPropertyAssertion(
            property(),
            individual(second),
            literal(),
        )),
        3 => Some(Axiom::NegativeDataPropertyAssertion(
            property(),
            individual(second),
            literal(),
        )),
        4 => Some(Axiom::SameIndividual(pair())),
        5 => Some(Axiom::DifferentIndividuals(pair())),
        _ => None,
    }
}

/// Whether every model of the axioms satisfies the fact of `kind` (see
/// [`fact`]) about the given IRIs and literal; -2 for an unknown kind.
///
/// # Safety
/// `reasoner` must be null or a live handle, and each text pointer must be
/// null or point to its length of bytes.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn rowl_entails_fact(
    reasoner: *const RowlReasoner,
    kind: i32,
    first: *const u8,
    first_len: usize,
    second: *const u8,
    second_len: usize,
    third: *const u8,
    third_len: usize,
    fourth: *const u8,
    fourth_len: usize,
) -> i32 {
    // SAFETY: forwarded from the caller.
    match unsafe {
        (
            handle(reasoner),
            text(first, first_len),
            text(second, second_len),
            text(third, third_len),
            text(fourth, fourth_len),
        )
    } {
        (Some(found), Some(first), Some(second), Some(third), Some(fourth)) => {
            match fact(kind, first, second, third, fourth) {
                Some(fact) => answer(found.entails(&fact)),
                None => INVALID_ARGUMENT,
            }
        }
        _ => INVALID_ARGUMENT,
    }
}

/// The named classes the document declares or uses, as a JSON array of IRIs;
/// null for a null handle.
///
/// # Safety
/// `reasoner` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn rowl_classes(reasoner: *const RowlReasoner) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    match unsafe { handle(reasoner) } {
        Some(found) => {
            let mut out = String::new();
            json_list(&mut out, &found.classes());
            into_c(out)
        }
        None => ptr::null_mut(),
    }
}

/// The named individuals the document declares, asserts something about or
/// names in a class expression, as a JSON array of IRIs; null for a null
/// handle.
///
/// # Safety
/// `reasoner` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn rowl_individuals(reasoner: *const RowlReasoner) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    match unsafe { handle(reasoner) } {
        Some(found) => {
            let mut out = String::new();
            json_list(&mut out, &found.individuals());
            into_c(out)
        }
        None => ptr::null_mut(),
    }
}

/// The classification of the named classes as a JSON array of objects with
/// `class`, `satisfiable` and `superclasses`, or the JSON text `null` when some
/// question has no answer; null for a null handle.
///
/// # Safety
/// `reasoner` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn rowl_classify(reasoner: *const RowlReasoner) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    match unsafe { handle(reasoner) } {
        Some(found) => match found.classify() {
            Some(classified) => into_c(json_classification(&classified)),
            None => into_c(String::from("null")),
        },
        None => ptr::null_mut(),
    }
}

/// The first OWL 2 DL restriction the document violates, in words, as a JSON
/// string, or the JSON text `null` when the verified OWL 2 DL check accepts
/// the document; null for a null handle.
///
/// # Safety
/// `reasoner` must be null or a live handle.
#[no_mangle]
pub unsafe extern "C" fn rowl_dl_violation(reasoner: *const RowlReasoner) -> *mut c_char {
    // SAFETY: forwarded from the caller.
    match unsafe { handle(reasoner) } {
        Some(found) => match found.dl_violation() {
            Some(violation) => {
                let mut out = String::new();
                json_string(&mut out, &violation);
                into_c(out)
            }
            None => into_c(String::from("null")),
        },
        None => ptr::null_mut(),
    }
}

/// Release text returned by this library. Null is ignored.
///
/// # Safety
/// `text` must be null or text returned by this library that is not used
/// afterwards.
#[no_mangle]
pub unsafe extern "C" fn rowl_string_free(text: *mut c_char) {
    if !text.is_null() {
        // SAFETY: the text came from `CString::into_raw` and is released once.
        drop(unsafe { CString::from_raw(text) });
    }
}
