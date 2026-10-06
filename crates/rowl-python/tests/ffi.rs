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
