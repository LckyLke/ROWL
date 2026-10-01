use rowl_frontend::functional::{Terminal, Token};
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::{lex, LexResult, Tokens};
use rowl_frontend::functional_literals::{
    read_literal, LiteralExpected, SourceLiteral, SourceLiteralError, SourceLiteralForm,
};
use rowl_frontend::functional_names::NameError;
use rowl_frontend::ntriples::ErrorKind;
use rowl_frontend::prefixes::{check, Check, Declaration};
const PLAIN: &[u8] = b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
fn tokens(source: &str) -> Tokens {
    match lex(&source.as_bytes().to_vec(), 100) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("fixture must lex completely"),
    }
}
fn read(
    source: &str,
    lexical: usize,
    datatype: usize,
) -> Result<(SourceLiteral, Tokens), SourceLiteralError> {
    let rows = Vec::new();
    let table = match check(&rows) {
        Check::Ready(table) => table,
        _ => panic!("empty table"),
    };
    read_literal(
        &table,
        &source.as_bytes().to_vec(),
        tokens(source),
        lexical,
        datatype,
    )
}
fn ready(source: &str, lexical: usize, datatype: usize) -> (SourceLiteral, Tokens) {
    read(source, lexical, datatype).unwrap_or_else(|_| panic!("fixture literal must read"))
}
fn cons(terminal: Terminal, start: usize, end: usize, next: Tokens) -> Tokens {
    Tokens::Cons {
        token: Token {
            terminal,
            start,
            end,
        },
        next: Box::new(next),
    }
}
#[test]
fn plain_shortcuts_use_normative_plain_literal_and_preserve_text_language_case() {
    for (source, expected) in [
        ("\"Pump\"", "Pump@"),
        ("\"Pump\"@DE-Latn", "Pump@DE-Latn"),
        ("\"mail@example.org\"", "mail@example.org@"),
        ("\"\"", "@"),
        ("\"设备\"@zh-Hant", "设备@zh-Hant"),
    ] {
        let (value, rest) = ready(source, 100, 100);
        assert_eq!(value.lexical, expected.as_bytes());
        assert_eq!(value.datatype, PLAIN);
        assert!(matches!(rest, Tokens::Empty));
        assert_eq!(
            &source.as_bytes()[value.quoted.start..value.quoted.end],
            &source.as_bytes()[..source.rfind('"').expect("closing quote") + 1]
        );
    }
}
#[test]
fn typed_literals_retain_exact_lexical_spelling_and_resolve_original_types() {
    for (source, lexical, datatype) in [
        (
            "\"001\"^^xsd:integer",
            b"001".as_slice(),
            b"http://www.w3.org/2001/XMLSchema#integer".as_slice(),
        ),
        ("\"abc\"^^rdf:PlainLiteral", b"abc".as_slice(), PLAIN),
        (
            "\"+\"^^xsd:integer",
            b"+".as_slice(),
            b"http://www.w3.org/2001/XMLSchema#integer".as_slice(),
        ),
        (
            "\"x\"^^<HTTP://Example.org/%61#Type>",
            b"x".as_slice(),
            b"HTTP://Example.org/%61#Type".as_slice(),
        ),
    ] {
        let (value, rest) = ready(source, lexical.len(), datatype.len());
        assert_eq!(value.lexical, lexical);
        assert_eq!(value.datatype, datatype);
        assert!(matches!(value.form, SourceLiteralForm::Typed { .. }));
        assert!(matches!(rest, Tokens::Empty));
    }
    // Parsing lexical bytes is deliberately separate from normative datatype validity.
}
#[test]
fn quotes_backslashes_newlines_and_unicode_have_exact_decoded_structural_bytes() {
    let source = "\"设备 \\\"pump\\\" \\\\ motor\nline\"@de";
    let (value, _) = ready(source, 100, 100);
    assert_eq!(value.lexical, "设备 \"pump\" \\ motor\nline@de".as_bytes());
    assert!(matches!(value.form, SourceLiteralForm::Language(_)));
    for source in [r#""foreign\n""#, r#""foreign\u0041""#] {
        assert!(matches!(
            lex(&source.as_bytes().to_vec(), 100),
            LexResult::NoToken { .. }
        ));
    }
}
#[test]
fn lexical_limits_count_decoded_bytes_added_separator_and_full_language_payload() {
    for (source, fit) in [("\"x\"", 2), ("\"x\"@de", 4), ("\"é\"", 3), ("\"\"", 1)] {
        assert!(matches!(
            read(source, fit - 1, 100),
            Err(SourceLiteralError::LexicalLimit { offset: 0 })
        ));
        assert_eq!(ready(source, fit, 100).0.lexical.len(), fit);
    }
    assert!(
        matches!(read("\"é\"", 1, 100), Err(SourceLiteralError::Quoted(error)) if matches!(error.kind, ErrorKind::ResourceLimit) && error.offset == 1)
    );
    assert!(matches!(
        read("\"\"@de", 1, 100),
        Err(SourceLiteralError::Language(NameError::ResourceLimit {
            offset: 3
        }))
    ));
}
#[test]
fn datatype_budget_and_error_priority_follow_written_syntax_then_payload_then_expansion() {
    assert!(matches!(
        read("\"x\"", 2, PLAIN.len() - 1),
        Err(SourceLiteralError::DatatypeLimit { offset: 0 })
    ));
    assert_eq!(ready("\"x\"", 2, PLAIN.len()).0.datatype, PLAIN);
    assert!(matches!(
        read("\"x\"", 1, 0),
        Err(SourceLiteralError::LexicalLimit { offset: 0 })
    ));
    assert!(matches!(
        read("\"abc\"^^)", 0, 0),
        Err(SourceLiteralError::Expected {
            expected: LiteralExpected::Datatype,
            offset: 7
        })
    ));
    assert!(matches!(
        read("\"abc\"^^", 0, 0),
        Err(SourceLiteralError::Expected {
            expected: LiteralExpected::Datatype,
            offset: 7
        })
    ));
    assert!(matches!(
        read("\"x\"^^missing:Type", 1, 100),
        Err(SourceLiteralError::Datatype(
            SourceIriError::UndeclaredPrefix { offset: 5 }
        ))
    ));
    assert!(matches!(
        read("\"x\"^^xsd:integer", 1, 0),
        Err(SourceLiteralError::Datatype(
            SourceIriError::ResourceLimit { offset: 5 }
        ))
    ));
}
#[test]
fn suffixes_and_source_tokens_are_preserved_after_exactly_one_two_or_three_tokens() {
    for prefix in ["\"设备\"", "\"设备\"@de", "\"设备\"^^xsd:string"] {
        let source = format!("{prefix}) Declaration(Class(<urn:Pump>))");
        let (value, rest) = ready(&source, 100, 100);
        assert_eq!(value.quoted.start, 0);
        assert_eq!(value.quoted.end, "\"设备\"".len());
        match value.form {
            SourceLiteralForm::Plain => {}
            SourceLiteralForm::Language(tag) => {
                assert_eq!(&source.as_bytes()[tag.start..tag.end], b"@de")
            }
            SourceLiteralForm::Typed {
                indicator,
                datatype,
            } => {
                assert_eq!(&source.as_bytes()[indicator.start..indicator.end], b"^^");
                assert_eq!(
                    &source.as_bytes()[datatype.start..datatype.end],
                    b"xsd:string"
                );
            }
        }
        match rest {
            Tokens::Cons { token, .. } => {
                assert!(matches!(token.terminal, Terminal::Close));
                assert_eq!(token.start, prefix.len());
            }
            _ => panic!("entire remaining token suffix"),
        }
    }
}
#[test]
fn caller_supplied_spans_are_revalidated_instead_of_trusting_terminal_flags() {
    let bytes = b"\"x\" tail".to_vec();
    let rows = Vec::new();
    let table = match check(&rows) {
        Check::Ready(table) => table,
        _ => panic!("empty table"),
    };
    for (start, end) in [(4, 3), (0, 99), (0, 8)] {
        assert!(
            matches!(read_literal(&table, &bytes, cons(Terminal::QuotedString, start, end, Tokens::Empty), 100, 100),
            Err(SourceLiteralError::InvalidSpan { offset }) if offset == start)
        );
    }
    assert!(
        matches!(read_literal(&table, &bytes, cons(Terminal::QuotedString, 4, 8, Tokens::Empty), 100, 100),
        Err(SourceLiteralError::Quoted(error)) if matches!(error.kind, ErrorKind::InvalidCharacter) && error.offset == 4)
    );
    assert!(matches!(
        read_literal(
            &table,
            &b"\"x\"@i-klingon".to_vec(),
            cons(
                Terminal::QuotedString,
                0,
                3,
                cons(Terminal::LanguageTag, 3, 13, Tokens::Empty)
            ),
            100,
            100
        ),
        Err(SourceLiteralError::Language(NameError::InvalidToken {
            offset: 3
        }))
    ));
}
#[test]
fn missing_quote_and_original_eof_offsets_remain_explicit() {
    assert!(matches!(
        read("# comment", 100, 100),
        Err(SourceLiteralError::Expected {
            expected: LiteralExpected::Quoted,
            offset: 9
        })
    ));
    assert!(matches!(
        read("设备:Pump", 100, 100),
        Err(SourceLiteralError::Expected {
            expected: LiteralExpected::Quoted,
            offset: 0
        })
    ));
    let source = "# Geräte\n\"x\"^^ # end";
    assert!(
        matches!(read(source, 100, 100), Err(SourceLiteralError::Expected { expected: LiteralExpected::Datatype, offset }) if offset == source.len())
    );
}
#[test]
fn custom_datatype_prefixes_keep_namespace_and_local_spelling_without_normalization() {
    let rows = vec![Declaration {
        name: b"types:".to_vec(),
        namespace: "HTTP://Example.org/设备/%61#".as_bytes().to_vec(),
    }];
    let table = match check(&rows) {
        Check::Ready(table) => table,
        _ => panic!("valid table"),
    };
    let source = "\"007\"^^types:Motor";
    let (value, _) = read_literal(&table, &source.as_bytes().to_vec(), tokens(source), 3, 100)
        .unwrap_or_else(|_| panic!("literal"));
    assert_eq!(value.lexical, b"007");
    assert_eq!(
        value.datatype,
        "HTTP://Example.org/设备/%61#Motor".as_bytes()
    );
}
