use std::process::{Command, Output};

fn example(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name)
}

fn rowl(arguments: &[&std::ffi::OsStr]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rowl"))
        .args(arguments)
        .output()
        .unwrap()
}

#[test]
fn instances_and_validation_read_the_import_closure() {
    let prescriptions = example("imports/medication-prescriptions.ofn");
    let directory = example("imports");
    let output = rowl(&[
        "instances".as_ref(),
        prescriptions.as_os_str(),
        "https://example.org/medication/AllergyAlert".as_ref(),
        "--imports".as_ref(),
        directory.as_os_str(),
    ]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "https://example.org/medication/alice\n"
    );
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains("has 2 of the 2 catalog document(s)"));
    let output = rowl(&[
        "validate".as_ref(),
        prescriptions.as_os_str(),
        "--imports".as_ref(),
        directory.as_os_str(),
    ]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "OWL 2 DL: valid\n"
    );
    // Alone, the prescriptions use classes they do not declare.
    let output = rowl(&["validate".as_ref(), prescriptions.as_os_str()]);
    assert!(!output.status.success());
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("not declared"));
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains("without --imports DIR only its own axioms are read"));
}

#[test]
fn a_missing_import_is_named_and_nothing_is_fetched() {
    let empty = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("empty-catalog");
    std::fs::create_dir_all(&empty).unwrap();
    let prescriptions = example("imports/medication-prescriptions.ofn");
    let output = rowl(&[
        "check".as_ref(),
        prescriptions.as_os_str(),
        "--imports".as_ref(),
        empty.as_os_str(),
    ]);
    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("imports https://example.org/medication/vocabulary/1.0"));
    assert!(error.contains("nothing is fetched"));
    let output = rowl(&["status".as_ref(), "--imports".as_ref(), empty.as_os_str()]);
    assert!(!output.status.success());
}
