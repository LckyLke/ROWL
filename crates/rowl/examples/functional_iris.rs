//! Source-derived IRI resolution; document-header parsing remains pending.
use rowl::experimental::functional_iris::{resolve_span, SourceIriError, SourceIriKind};
use rowl::experimental::prefixes::{check, Check, Declaration};

fn main() {
    let declarations = vec![Declaration {
        name: b"ex:".to_vec(),
        namespace: b"https://example.org/maintenance#".to_vec(),
    }];
    let table = match check(&declarations) {
        Check::Ready(table) => table,
        _ => panic!("the example requires a valid immutable prefix table"),
    };
    for (kind, token) in [
        (SourceIriKind::Abbreviated, "ex:Pump"),
        (SourceIriKind::Abbreviated, "ex:部品"),
        (SourceIriKind::Abbreviated, "owl:Thing"),
        (SourceIriKind::Full, "<urn:maintenance:pump7>"),
    ] {
        let value = resolve_span(
            &table,
            kind,
            &token.as_bytes().to_vec(),
            0,
            token.len(),
            100,
        )
        .unwrap_or_else(|_| panic!("the example source must resolve exactly"));
        println!(
            "{token} → {}",
            String::from_utf8(value).expect("proved IRI bytes are UTF-8")
        );
    }
    let source = b"missing:Pump".to_vec();
    match resolve_span(
        &table,
        SourceIriKind::Abbreviated,
        &source,
        0,
        source.len(),
        0,
    ) {
        Err(SourceIriError::UndeclaredPrefix { offset: 0 }) => {
            println!("missing:Pump → undeclared prefix at original byte 0 (before output budget)");
        }
        _ => panic!("the missing prefix must be diagnosed"),
    }
    println!("The prefix table is supplied explicitly. Complete OWL parsing and inference remain pending.");
}
