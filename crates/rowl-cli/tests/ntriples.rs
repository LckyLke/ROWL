use std::process::Command;

fn fixture() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/maintenance.nt")
}
#[test]
fn cli_checks_and_exports_a_real_graph_without_polluting_export_bytes() {
    let check = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("check-nt")
        .arg(fixture())
        .output()
        .unwrap();
    assert!(check.status.success());
    assert!(String::from_utf8(check.stdout)
        .unwrap()
        .contains("15 triple occurrences"));
    let exported = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("export-nt")
        .arg(fixture())
        .output()
        .unwrap();
    assert!(exported.status.success());
    let rowl::experimental::ntriples::ReadResult::Graph(graph) =
        rowl::experimental::ntriples::read(&exported.stdout, &vec![])
    else {
        panic!("CLI export wasn't N-Triples")
    };
    assert_eq!(graph.triples.len(), 15);
    assert!(String::from_utf8(exported.stderr)
        .unwrap()
        .contains("proofs"));
}
#[test]
fn cli_reports_io_failure_with_unsuccessful_exit_status() {
    let missing = fixture().with_file_name("this-file-does-not-exist.nt");
    let result = Command::new(env!("CARGO_BIN_EXE_rowl"))
        .arg("check-nt")
        .arg(missing)
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    assert!(!result.stderr.is_empty());
}
