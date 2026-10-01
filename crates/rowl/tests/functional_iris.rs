//! Complete source-token IRI resolution, without an OWL AST or inference claim.
use rowl::experimental::functional::Terminal;
use rowl::experimental::functional_iris::{resolve_span, SourceIriKind};
use rowl::experimental::functional_lexer::{lex, LexResult, Tokens};
use rowl::experimental::prefixes::{check, Check, Declaration};

#[test]
fn maintenance_source_tokens_resolve_into_exact_entity_iri_values() {
    let source = b"Prefix(ex:=<https://example.org/maintenance#>) Ontology(<urn:maintenance> Declaration(Class(ex:Pump)) ClassAssertion(ex:Pump ex:pump7) AnnotationAssertion(rdfs:label ex:pump7 \"Pumpe\"@DE))".to_vec();
    // The declaration table is supplied explicitly until the complete source
    // header parser is proved. All entity boundaries below come from the lexer.
    let rows = vec![Declaration {
        name: b"ex:".to_vec(),
        namespace: b"https://example.org/maintenance#".to_vec(),
    }];
    let table = match check(&rows) {
        Check::Ready(table) => table,
        _ => panic!("valid prefix table"),
    };
    let mut tokens = match lex(&source, 50) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("complete source lexing"),
    };
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
                    .unwrap_or_else(|_| panic!("every selected IRI must resolve exactly")),
            );
        }
        tokens = *next;
    }
    let expected: Vec<Vec<u8>> = [
        "https://example.org/maintenance#",
        "urn:maintenance",
        "https://example.org/maintenance#Pump",
        "https://example.org/maintenance#Pump",
        "https://example.org/maintenance#pump7",
        "http://www.w3.org/2000/01/rdf-schema#label",
        "https://example.org/maintenance#pump7",
    ]
    .into_iter()
    .map(|value| value.as_bytes().to_vec())
    .collect();
    assert_eq!(values, expected);
    source_suffix_failure(source);
}
fn source_suffix_failure(mut source: Vec<u8>) {
    source.extend_from_slice(b" 10abc");
    assert!(!matches!(lex(&source, 50), LexResult::Tokens(_)));
}
