//! Full-source name-value integration; no OWL AST or inference is asserted.
use rowl::experimental::functional::Terminal;
use rowl::experimental::functional_lexer::{lex, LexResult, Tokens};
use rowl::experimental::functional_names::{read_span, NameKind};

#[test]
fn a_complete_maintenance_token_stream_supplies_all_five_name_families() {
    let source = b"Prefix(ex:=<https://example.org/maintenance#>) Ontology(<urn:maintenance> Declaration(Class(ex:Pump)) ClassAssertion(ex:Pump _:p) AnnotationAssertion(rdfs:label _:p \"Pumpe\"@DE))".to_vec();
    let mut tokens = match lex(&source, 50) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("the complete maintenance token stream must be accepted"),
    };
    let mut values = Vec::new();
    while let Tokens::Cons { token, next } = tokens {
        let kind = match token.terminal {
            Terminal::FullIri => Some(NameKind::FullIri),
            Terminal::PrefixName => Some(NameKind::PrefixName),
            Terminal::AbbreviatedIri => Some(NameKind::AbbreviatedIri),
            Terminal::NodeId => Some(NameKind::NodeId),
            Terminal::LanguageTag => Some(NameKind::LanguageTag),
            _ => None,
        };
        if let Some(kind) = kind {
            values.push(
                read_span(kind, &source, token.start, token.end, 100)
                    .unwrap_or_else(|_| panic!("every emitted name must have its exact value")),
            );
        }
        tokens = *next;
    }
    let expected: Vec<Vec<u8>> = [
        "ex:",
        "https://example.org/maintenance#",
        "urn:maintenance",
        "ex:Pump",
        "ex:Pump",
        "p",
        "rdfs:label",
        "p",
        "DE",
    ]
    .into_iter()
    .map(|value| value.as_bytes().to_vec())
    .collect();
    assert_eq!(values, expected);
}

#[test]
fn later_source_failure_prevents_a_successful_name_token_stream() {
    let prefix = b"Declaration(Class(<urn:maintenance:Pump>))";
    let mut source = prefix.to_vec();
    source.extend_from_slice(b" 10abc");
    assert!(!matches!(lex(&source, 30), LexResult::Tokens(_)));
    let mut source = prefix.to_vec();
    source.push(0xff);
    assert!(!matches!(lex(&source, 30), LexResult::Tokens(_)));
}
