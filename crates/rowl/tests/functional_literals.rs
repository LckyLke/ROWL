use rowl::experimental::functional_lexer::{lex, LexResult, Tokens};
use rowl::experimental::functional_literals::{read_literal, SourceLiteralForm};
use rowl::experimental::prefixes::{check, Check};
#[test]
fn public_literal_reader_retains_the_owl_plain_literal_expansion() {
    let bytes = b"\"Pump 7\"@de)".to_vec();
    let rows = Vec::new();
    let table = match check(&rows) {
        Check::Ready(table) => table,
        _ => panic!("table"),
    };
    let tokens = match lex(&bytes, 10) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("source"),
    };
    let (value, remaining) =
        read_literal(&table, &bytes, tokens, 9, 55).unwrap_or_else(|_| panic!("literal"));
    assert_eq!(value.lexical, b"Pump 7@de");
    assert_eq!(
        value.datatype,
        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"
    );
    assert!(matches!(value.form, SourceLiteralForm::Language(_)));
    assert!(matches!(remaining, Tokens::Cons { .. }));
}
#[test]
fn public_literal_reader_does_not_claim_normative_datatype_value_validity() {
    let bytes = b"\"+\"^^xsd:integer".to_vec();
    let rows = Vec::new();
    let table = match check(&rows) {
        Check::Ready(table) => table,
        _ => panic!("table"),
    };
    let tokens = match lex(&bytes, 10) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("source"),
    };
    let (value, _) =
        read_literal(&table, &bytes, tokens, 1, 100).unwrap_or_else(|_| panic!("literal"));
    assert_eq!(value.lexical, b"+");
    assert!(matches!(value.form, SourceLiteralForm::Typed { .. }));
}
#[test]
fn actual_source_prefix_table_and_header_supply_a_custom_literal_datatype() {
    use rowl::experimental::functional::Terminal;
    use rowl::experimental::functional_header::read_header_tail;
    use rowl::experimental::functional_prefixes::read_prefix_header;
    let bytes = b"Prefix(ex:=<HTTP://Example.org/%61#>) Ontology(<urn:plant> Annotation(ex:code \"007\"^^ex:Motor))".to_vec();
    let prefix = read_prefix_header(&bytes, 100, 10, 100)
        .unwrap_or_else(|_| panic!("original prefix syntax"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("source table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    // Locate the annotation's literal for this component test; full annotation parsing is separate.
    let mut rest = header.remaining;
    loop {
        match rest {
            Tokens::Empty => panic!("literal position"),
            Tokens::Cons { token, next } => {
                if matches!(token.terminal, Terminal::QuotedString) {
                    let (literal, remaining) =
                        read_literal(&table, &bytes, Tokens::Cons { token, next }, 3, 100)
                            .unwrap_or_else(|_| panic!("source literal"));
                    assert_eq!(literal.lexical, b"007");
                    assert_eq!(literal.datatype, b"HTTP://Example.org/%61#Motor");
                    assert!(matches!(remaining, Tokens::Cons { .. }));
                    break;
                }
                rest = *next;
            }
        }
    }
}
