use std::process::Command;

fn example(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name)
}

#[test]
fn cli_answers_from_an_rdfxml_document() {
    let check = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("check")
        .arg(example("medication-safety.owl"))
        .output()
        .unwrap();
    assert!(check.status.success());
    assert_eq!(
        String::from_utf8(check.stdout).unwrap(),
        "consistent: yes\n"
    );
    let instances = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("instances")
        .arg(example("medication-safety.owl"))
        .arg("https://example.org/medication/AllergyAlert")
        .output()
        .unwrap();
    assert!(instances.status.success());
    assert_eq!(
        String::from_utf8(instances.stdout).unwrap(),
        "https://example.org/medication/alice\n"
    );
}

#[test]
fn cli_resolves_relative_iris_against_the_file() {
    let directory = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("rdfxml base");
    std::fs::create_dir_all(&directory).unwrap();
    let file = directory.join("drugs.owl");
    std::fs::write(
        &file,
        br##"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#">
  <owl:Class rdf:about="#Drug"/>
  <owl:Class rdf:about="#Opioid"><rdfs:subClassOf rdf:resource="#Drug"/></owl:Class>
</rdf:RDF>
"##,
    )
    .unwrap();
    let classify = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("classify")
        .arg(&file)
        .output()
        .unwrap();
    assert!(classify.status.success());
    let text = String::from_utf8(classify.stdout).unwrap();
    // The base is the file's own IRI, with the space percent-encoded.
    assert!(text.contains("rdfxml%20base/drugs.owl#Opioid"), "{text}");
    assert!(text.contains("rdfxml%20base/drugs.owl#Drug"), "{text}");
}

#[test]
fn cli_reports_why_an_rdfxml_document_fails() {
    let broken = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("broken.rdf");
    std::fs::write(
        &broken,
        b"<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"></rdf>\n",
    )
    .unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("check")
        .arg(&broken)
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let message = String::from_utf8(result.stderr).unwrap();
    assert!(message.contains("XML error at byte"), "{message}");
}
