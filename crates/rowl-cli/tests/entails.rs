use std::process::Command;

/// A document written to the test's temporary directory.
fn document(name: &str, text: &str) -> std::path::PathBuf {
    let directory = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("entails");
    std::fs::create_dir_all(&directory).unwrap();
    let file = directory.join(name);
    std::fs::write(&file, text).unwrap();
    file
}

fn entails(file: &std::path::Path, fact: &str) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("entails")
        .arg(file)
        .arg(fact)
        .output()
        .unwrap()
}

const FAMILY: &str = "Prefix(:=<https://example.org/f/>)
Ontology(<https://example.org/f/onto>
SubObjectPropertyOf(:hasMother :hasParent)
FunctionalObjectProperty(:hasMother)
ObjectPropertyAssertion(:hasMother :ann :beth)
ObjectPropertyAssertion(:hasMother :ann :mum)
)
";

#[test]
fn facts_are_read_with_the_document_prefixes_and_answered() {
    let file = document("family.ofn", FAMILY);
    for (fact, answer) in [
        ("ObjectPropertyAssertion(:hasParent :ann :beth)", "entailed: yes\n"),
        ("SameIndividual(:beth :mum)", "entailed: yes\n"),
        ("DifferentIndividuals(:ann :beth)", "entailed: no\n"),
        (
            "ObjectPropertyAssertion(<https://example.org/f/hasParent> <https://example.org/f/beth> <https://example.org/f/ann>)",
            "entailed: no\n",
        ),
    ] {
        let output = entails(&file, fact);
        assert!(output.status.success(), "{fact}");
        assert_eq!(String::from_utf8(output.stdout).unwrap(), answer, "{fact}");
    }
}

#[test]
fn a_fact_that_is_not_one_axiom_is_rejected() {
    let file = document("family-rejected.ofn", FAMILY);
    let output = entails(&file, "ObjectPropertyAssertion(:hasParent :ann");
    assert!(!output.status.success());
    let output = entails(
        &file,
        "SameIndividual(:ann :beth) SameIndividual(:ann :mum)",
    );
    assert!(!output.status.success());
}
