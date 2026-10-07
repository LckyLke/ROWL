use rowl_python::*;
use std::ffi::CStr;
use std::ptr;

const MEDICATION: &[u8] = include_bytes!("../../../examples/medication-safety.ofn");
const IRI: &str = "https://example.org/medication/";

fn load(source: &[u8]) -> (*mut RowlReasoner, i32) {
    let mut status = -1;
    // SAFETY: the buffer and the status are valid for the call.
    let reasoner =
        unsafe { rowl_reasoner_from_functional(source.as_ptr(), source.len(), &mut status) };
    (reasoner, status)
}

fn iri(name: &str) -> String {
    format!("{IRI}{name}")
}

fn take(text: *mut std::ffi::c_char) -> String {
    assert!(!text.is_null());
    // SAFETY: the text came from the library and is released once.
    let owned = unsafe { CStr::from_ptr(text) }
        .to_str()
        .unwrap()
        .to_string();
    unsafe { rowl_string_free(text) };
    owned
}

#[test]
fn medication_questions_answer_through_the_c_interface() {
    let (reasoner, status) = load(MEDICATION);
    assert_eq!(status, ROWL_LOADED);
    assert!(!reasoner.is_null());
    // SAFETY: a live handle and readable text buffers.
    unsafe {
        assert_eq!(rowl_consistent(reasoner), 1);
        let (sub, sup) = (iri("Amoxicillin"), iri("Penicillin"));
        assert_eq!(
            rowl_subsumed(reasoner, sub.as_ptr(), sub.len(), sup.as_ptr(), sup.len()),
            1
        );
        assert_eq!(
            rowl_subsumed(reasoner, sup.as_ptr(), sup.len(), sub.as_ptr(), sub.len()),
            0
        );
        let alert = iri("AllergyAlert");
        for (patient, expected) in [("alice", 1), ("bob", 0), ("carol", 0)] {
            let patient = iri(patient);
            assert_eq!(
                rowl_instance_of(
                    reasoner,
                    patient.as_ptr(),
                    patient.len(),
                    alert.as_ptr(),
                    alert.len()
                ),
                expected
            );
        }
        assert_eq!(rowl_satisfiable(reasoner, alert.as_ptr(), alert.len()), 1);
        let classes = take(rowl_classes(reasoner));
        assert!(
            classes.starts_with('[') && classes.contains(&format!("\"{}\"", iri("Penicillin")))
        );
        let individuals = take(rowl_individuals(reasoner));
        assert!(individuals.contains(&format!("\"{}\"", iri("alice"))));
        let classified = take(rowl_classify(reasoner));
        assert!(classified.contains(&format!(
            "{{\"class\":\"{}\",\"satisfiable\":true,\"superclasses\":[\"{}\"]}}",
            iri("Amoxicillin"),
            iri("Penicillin")
        )));
        rowl_reasoner_free(reasoner);
    }
}

#[test]
fn rejected_documents_and_bad_arguments_are_reported() {
    let (reasoner, status) = load(b"Ontology(");
    assert!(reasoner.is_null());
    assert_eq!(status, ROWL_REJECTED);
    // SAFETY: null handles and pointers are accepted and rejected.
    unsafe {
        let mut status = -1;
        assert!(rowl_reasoner_from_functional(ptr::null(), 3, &mut status).is_null());
        assert_eq!(status, ROWL_INVALID);
        assert_eq!(rowl_consistent(ptr::null()), -2);
        assert!(rowl_classes(ptr::null()).is_null());
        rowl_reasoner_free(ptr::null_mut());
        rowl_string_free(ptr::null_mut());
    }
    let (reasoner, _) = load(MEDICATION);
    let invalid = [0xffu8, 0xfe];
    // SAFETY: a live handle and a readable buffer that is not UTF-8.
    unsafe {
        assert_eq!(
            rowl_satisfiable(reasoner, invalid.as_ptr(), invalid.len()),
            -2
        );
        rowl_reasoner_free(reasoner);
    }
    // SAFETY: the version is static NUL-terminated text.
    let version = unsafe { CStr::from_ptr(rowl_version()) };
    assert_eq!(version.to_str().unwrap(), "0.0.0");
}

#[test]
fn dl_violations_come_back_as_json_text() {
    let (reasoner, status) = load(MEDICATION);
    assert_eq!(status, ROWL_LOADED);
    // SAFETY: a live handle, released once.
    unsafe {
        assert_eq!(take(rowl_dl_violation(reasoner)), "null");
        rowl_reasoner_free(reasoner);
    }
    let undeclared =
        b"Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\nSubClassOf(:A :B))\n";
    let (reasoner, status) = load(undeclared);
    assert_eq!(status, ROWL_LOADED);
    // SAFETY: a live handle, released once.
    unsafe {
        assert_eq!(
            take(rowl_dl_violation(reasoner)),
            "\"https://example.org/A is used as a class but not declared as one (typing constraints, §5.8.1)\""
        );
        rowl_reasoner_free(reasoner);
        assert!(rowl_dl_violation(ptr::null()).is_null());
    }
}

const PRESCRIPTIONS: &[u8] =
    include_bytes!("../../../examples/imports/medication-prescriptions.ofn");
const VOCABULARY: &[u8] = include_bytes!("../../../examples/imports/medication-vocabulary.ttl");

/// Read a catalog through the C interface; the status, the handle and the message.
fn load_catalog(documents: &[(&str, &[u8], i32)]) -> (i32, *mut RowlReasoner, Option<String>) {
    let datas: Vec<*const u8> = documents.iter().map(|(_, data, _)| data.as_ptr()).collect();
    let lens: Vec<usize> = documents.iter().map(|(_, data, _)| data.len()).collect();
    let syntaxes: Vec<i32> = documents.iter().map(|(_, _, syntax)| *syntax).collect();
    let names: Vec<*const u8> = documents.iter().map(|(name, _, _)| name.as_ptr()).collect();
    let name_lens: Vec<usize> = documents.iter().map(|(name, _, _)| name.len()).collect();
    let mut status = -1;
    let mut message = ptr::null_mut();
    // SAFETY: every array has `documents.len()` entries pointing to live buffers.
    let reasoner = unsafe {
        rowl_reasoner_from_documents(
            datas.as_ptr(),
            lens.as_ptr(),
            syntaxes.as_ptr(),
            names.as_ptr(),
            name_lens.as_ptr(),
            documents.len(),
            0,
            &mut status,
            &mut message,
        )
    };
    let message = if message.is_null() {
        None
    } else {
        Some(take(message))
    };
    (status, reasoner, message)
}

#[test]
fn import_closures_load_through_the_c_interface() {
    let (status, reasoner, message) = load_catalog(&[
        ("prescriptions", PRESCRIPTIONS, ROWL_SYNTAX_FUNCTIONAL),
        ("vocabulary", VOCABULARY, ROWL_SYNTAX_TURTLE),
    ]);
    assert_eq!(status, ROWL_LOADED);
    assert!(message.is_none());
    // SAFETY: a live handle and readable text buffers.
    unsafe {
        let (alice, alert) = (iri("alice"), iri("AllergyAlert"));
        assert_eq!(
            rowl_instance_of(
                reasoner,
                alice.as_ptr(),
                alice.len(),
                alert.as_ptr(),
                alert.len()
            ),
            1
        );
        assert_eq!(take(rowl_dl_violation(reasoner)), "null");
        rowl_reasoner_free(reasoner);
    }
    let (status, reasoner, message) =
        load_catalog(&[("prescriptions", PRESCRIPTIONS, ROWL_SYNTAX_FUNCTIONAL)]);
    assert_eq!(status, ROWL_MISSING_IMPORT);
    assert!(reasoner.is_null());
    assert!(message
        .unwrap()
        .contains("https://example.org/medication/vocabulary/1.0"));
    let (status, _, _) = load_catalog(&[
        ("prescriptions", PRESCRIPTIONS, ROWL_SYNTAX_FUNCTIONAL),
        ("vocabulary", VOCABULARY, ROWL_SYNTAX_TURTLE),
        ("copy", VOCABULARY, ROWL_SYNTAX_TURTLE),
    ]);
    assert_eq!(status, ROWL_AMBIGUOUS_IMPORT);
    let (status, _, message) = load_catalog(&[("prescriptions", PRESCRIPTIONS, 9)]);
    assert_eq!(status, ROWL_INVALID);
    assert!(message.is_none());
}
