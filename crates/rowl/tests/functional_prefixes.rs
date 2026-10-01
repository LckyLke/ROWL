//! Source-derived prefix tables used by real source-token IRI resolution.
use rowl::experimental::functional::Terminal;
use rowl::experimental::functional_iris::{resolve_span, SourceIriKind};
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

#[test]
fn maintenance_names_resolve_using_declarations_read_from_the_same_source() {
    let source = b"# maintenance vocabulary\nPrefix(ex:=<https://example.org/maintenance#>) Ontology(<urn:maintenance> Declaration(Class(ex:Pump)) ClassAssertion(ex:Pump ex:pump7))".to_vec();
    let header = read_prefix_header(&source, 100, 10, 100)
        .unwrap_or_else(|_| panic!("complete original prefix/header syntax"));
    let table = match check(&header.declarations) {
        Check::Ready(table) => table,
        _ => panic!("the source declarations must form a valid immutable table"),
    };
    let mut tokens = header.remaining;
    let mut values = Vec::new();
    while let Tokens::Cons { token, next } = tokens {
        let kind = match token.terminal {
            Terminal::FullIri => Some(SourceIriKind::Full),
            Terminal::AbbreviatedIri => Some(SourceIriKind::Abbreviated),
            _ => None,
        };
        if let Some(kind) = kind {
            values.push(
                resolve_span(&table, kind, &source, token.start, token.end, 100)
                    .unwrap_or_else(|_| panic!("original source IRI must resolve exactly")),
            );
        }
        tokens = *next;
    }
    let expected: Vec<Vec<u8>> = [
        "urn:maintenance",
        "https://example.org/maintenance#Pump",
        "https://example.org/maintenance#Pump",
        "https://example.org/maintenance#pump7",
    ]
    .into_iter()
    .map(|value| value.as_bytes().to_vec())
    .collect();
    assert_eq!(values, expected);
}

#[test]
fn an_unused_duplicate_source_prefix_still_prevents_checked_table_construction() {
    let source = b"Prefix(unused:=<urn:first:>) Prefix(unused:=<urn:second:>) Ontology(Declaration(Class(owl:Thing)))".to_vec();
    let header = read_prefix_header(&source, 100, 10, 100)
        .unwrap_or_else(|_| panic!("the raw syntax must retain both original declarations"));
    assert!(matches!(
        check(&header.declarations),
        Check::Duplicate { .. }
    ));
}
