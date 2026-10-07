use std::process::Command;

fn example(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name)
}

#[test]
fn cli_answers_from_a_turtle_document() {
    let check = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("check")
        .arg(example("medication-safety.ttl"))
        .output()
        .unwrap();
    assert!(check.status.success());
    assert_eq!(
        String::from_utf8(check.stdout).unwrap(),
        "consistent: yes\n"
    );
    let instances = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("instances")
        .arg(example("medication-safety.ttl"))
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
fn cli_reports_the_offset_of_a_turtle_error() {
    let broken = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("broken.ttl");
    std::fs::write(
        &broken,
        b"@prefix ex: <https://example.org/> .\nex:a ex:b .\n",
    )
    .unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("check")
        .arg(&broken)
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    assert!(String::from_utf8(result.stderr)
        .unwrap()
        .contains("Turtle parse error at byte"));
}
