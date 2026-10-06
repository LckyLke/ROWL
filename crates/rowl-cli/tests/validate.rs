use std::process::Command;

fn example(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name)
}

#[test]
fn valid_examples_are_reported_valid() {
    for name in [
        "medication-safety.ofn",
        "medication-safety.nt",
        "maintenance.nt",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_rowl"))
            .arg("validate")
            .arg(example(name))
            .output()
            .unwrap();
        assert!(output.status.success(), "{name}");
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            "OWL 2 DL: valid\n"
        );
        assert!(String::from_utf8(output.stderr)
            .unwrap()
            .contains("verified OWL 2 DL check"));
    }
}

#[test]
fn the_first_violation_is_reported_with_an_unsuccessful_status() {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("undeclared.ofn");
    std::fs::write(
        &path,
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n\
         Declaration(Class(:A)) SubClassOf(:A :B))\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("validate")
        .arg(&path)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "OWL 2 DL: not valid: https://example.org/B is used as a class but not declared as one \
         (typing constraints, §5.8.1)\n"
    );
}
