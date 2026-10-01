//! Source-derived ontology identity, version and original import references.
use rowl::experimental::functional_header::{read_header_tail, SourceOntologyIdentity};
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

fn main() {
    let bytes = b"Prefix(ex:=<https://example.org/maintenance/>) Ontology(ex:plant ex:v2 Import(ex:parts) Import(<urn:machines>) Declaration(Class(ex:Pump)))".to_vec();
    let prefix =
        read_prefix_header(&bytes, 100, 10, 100).unwrap_or_else(|_| panic!("source prefix syntax"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("source prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("source ontology identity/import syntax"));
    if let SourceOntologyIdentity::Named { ontology, version } = header.identity {
        println!("Ontology: {}", String::from_utf8_lossy(&ontology.value));
        if let Some(version) = version {
            println!("Version: {}", String::from_utf8_lossy(&version.value));
        }
    }
    for reference in header.imports {
        println!(
            "Import at source byte {}: {}",
            reference.keyword.start,
            String::from_utf8_lossy(&reference.target.value)
        );
    }
    println!("All metadata comes from the original source. Ontology annotations/axioms, canonical import assembly and reasoning remain pending.");
}
