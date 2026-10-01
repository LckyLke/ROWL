use rowl::experimental::functional_header::{read_header_tail, SourceOntologyIdentity};
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

#[test]
fn maintenance_header_metadata_is_derived_from_the_original_document() {
    let bytes = b"Prefix(ex:=<https://example.org/maintenance/>) Ontology(ex:plant ex:v2 Import(ex:parts) Import(<urn:machines>) Declaration(Class(ex:Pump)))".to_vec();
    let prefix =
        read_prefix_header(&bytes, 100, 10, 100).unwrap_or_else(|_| panic!("source prefix syntax"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("source prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("source header values"));
    match header.identity {
        SourceOntologyIdentity::Named { ontology, version } => {
            assert_eq!(ontology.value, b"https://example.org/maintenance/plant");
            assert_eq!(
                version.expect("version").value,
                b"https://example.org/maintenance/v2"
            );
        }
        _ => panic!("named maintenance ontology"),
    }
    assert_eq!(
        header.imports[0].target.value,
        b"https://example.org/maintenance/parts"
    );
    assert_eq!(header.imports[1].target.value, b"urn:machines");
    assert!(matches!(header.remaining, Tokens::Cons { .. }));
}

#[test]
fn whole_source_failures_prevent_any_header_metadata_from_being_exposed() {
    let bytes = b"Ontology(<urn:plant> Import(<urn:parts>)) 10abc".to_vec();
    assert!(read_prefix_header(&bytes, 100, 10, 100).is_err());
    let bytes = b"Prefix(unused:=<urn:one:>) Prefix(unused:=<urn:two:>) Ontology(<urn:plant> Import(<urn:parts>))".to_vec();
    let prefix =
        read_prefix_header(&bytes, 100, 10, 100).unwrap_or_else(|_| panic!("raw prefix syntax"));
    assert!(matches!(
        check(&prefix.declarations),
        Check::Duplicate { .. }
    ));
}
