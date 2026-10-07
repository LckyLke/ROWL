use std::process::Command;

/// A document written to the test's temporary directory.
fn document(name: &str, text: &str) -> std::path::PathBuf {
    let directory = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("instances");
    std::fs::create_dir_all(&directory).unwrap();
    let file = directory.join(name);
    std::fs::write(&file, text).unwrap();
    file
}

fn instances(file: &std::path::Path, class: &str) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("instances")
        .arg(file)
        .arg(class)
        .output()
        .unwrap()
}

#[test]
fn individuals_named_only_in_class_expressions_are_asked_about() {
    let file = document(
        "weekend.ofn",
        "Prefix(:=<https://example.org/w/>)\nOntology(<https://example.org/w/onto>\nEquivalentClasses(:Weekend ObjectOneOf(:saturday :sunday))\nSubClassOf(:Holiday ObjectHasValue(:after :monday))\n)\n",
    );
    let output = instances(&file, "https://example.org/w/Weekend");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "https://example.org/w/saturday\nhttps://example.org/w/sunday\n"
    );
}

#[test]
fn undecided_individuals_are_named_and_fail_the_listing() {
    let file = document(
        "events.ofn",
        "Prefix(:=<https://example.org/d/>)\nOntology(<https://example.org/d/onto>\nDeclaration(DataProperty(:at))\nDataPropertyAssertion(:at :e1 \"2.5E1\"^^xsd:double)\nClassAssertion(:Event :e1)\n)\n",
    );
    let output = instances(&file, "https://example.org/d/Event");
    assert!(!output.status.success());
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "");
    let errors = String::from_utf8(output.stderr).unwrap();
    assert!(errors.contains("unknown: https://example.org/d/e1"));
    assert!(errors.contains("the list is incomplete"));
}

#[test]
fn an_inconsistent_ontology_lists_nothing_and_fails() {
    let file = document(
        "clash.ofn",
        "Prefix(:=<https://example.org/c/>)\nOntology(<https://example.org/c/onto>\nDisjointClasses(:Drug :Patient)\nClassAssertion(:Drug :x)\nClassAssertion(:Patient :x)\nClassAssertion(:Drug :y)\n)\n",
    );
    let output = instances(&file, "https://example.org/c/Patient");
    assert!(!output.status.success());
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "");
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains("The ontology is inconsistent"));
}

#[test]
fn a_rejected_functional_syntax_document_is_explained_with_its_byte() {
    let text = "Prefix(:=<https://example.org/e/>)\nOntology(<https://example.org/e/onto>\nClassAssertion(dc:Agent :x)\n)\n";
    let file = document("undeclared.ofn", text);
    let output = instances(&file, "https://example.org/e/Agent");
    assert!(!output.status.success());
    let offset = text.find("dc:Agent").unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(
        stderr.contains(&format!(
            "Functional Syntax error at byte {offset}: a prefix name without a Prefix declaration"
        )),
        "{stderr}"
    );
}
