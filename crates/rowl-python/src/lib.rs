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
//! is not UTF-8). Lists come back as JSON text that the caller releases with
//! [`rowl_string_free`].
use rowl::reasoner::{default_limits, named, Classified, LoadError, Reasoner};
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

/// The status code and handle of a load.
fn loaded(result: Result<Reasoner, LoadError>) -> (i32, *mut RowlReasoner) {
    match result {
        Ok(inner) => (ROWL_LOADED, Box::into_raw(Box::new(RowlReasoner { inner }))),
        Err(LoadError::Document(_)) | Err(LoadError::Triples(_)) | Err(LoadError::Turtle(_)) => {
            (ROWL_REJECTED, ptr::null_mut())
        }
        Err(LoadError::Graph) => (ROWL_UNMAPPED, ptr::null_mut()),
        Err(LoadError::Unsupported) => (ROWL_UNSUPPORTED, ptr::null_mut()),
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

/// The named individuals the document asserts something about, as a JSON
/// array of IRIs; null for a null handle.
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
