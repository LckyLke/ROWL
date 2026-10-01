use rowl_frontend::functional::{Keyword, Terminal, Token};
use rowl_frontend::functional_header::{
    read_header_tail, HeaderError, HeaderExpected, HeaderTail, SourceOntologyIdentity,
};
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_names::NameError;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::prefixes::{check, Check};

fn read(source: &str, count: usize, value: usize) -> Result<HeaderTail, HeaderError> {
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 100, 10, 100)
        .unwrap_or_else(|_| panic!("fixture prefix syntax must be complete"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("fixture declarations must form a normative prefix table"),
    };
    read_header_tail(&table, &bytes, prefix.remaining, count, value)
}
fn ready(source: &str, count: usize, value: usize) -> HeaderTail {
    read(source, count, value).unwrap_or_else(|_| panic!("fixture header must be accepted"))
}
fn expected(result: Result<HeaderTail, HeaderError>) -> (&'static str, usize) {
    match result {
        Err(HeaderError::Expected { expected, offset }) => {
            let kind = match expected {
                HeaderExpected::Open => "open",
                HeaderExpected::Iri => "iri",
                HeaderExpected::Close => "close",
            };
            (kind, offset)
        }
        _ => panic!("expected the first source syntax failure"),
    }
}

#[test]
fn anonymous_and_one_or_two_identity_values_preserve_every_source_token() {
    for source in ["Ontology()", "Ontology(Annotation(rdfs:label \"设备\"))"] {
        let tail = ready(source, 0, 0);
        assert!(matches!(tail.identity, SourceOntologyIdentity::Anonymous));
        assert!(tail.imports.is_empty());
        assert!(matches!(tail.remaining, Tokens::Cons { .. }));
    }
    let source =
        "# Geräte\nPrefix(ex:=<HTTP://Example.org/%61#>) Ontology(ex:Pump <urn:version:2>)";
    let tail = ready(source, 0, 100);
    match tail.identity {
        SourceOntologyIdentity::Named { ontology, version } => {
            assert_eq!(ontology.value, b"HTTP://Example.org/%61#Pump");
            assert_eq!(
                &source.as_bytes()[ontology.token.start..ontology.token.end],
                b"ex:Pump"
            );
            let version = version.expect("original version IRI");
            assert_eq!(version.value, b"urn:version:2");
            assert_eq!(
                &source.as_bytes()[version.token.start..version.token.end],
                b"<urn:version:2>"
            );
        }
        _ => panic!("two original identity values must be present"),
    }
    let tail = ready("Ontology(<urn:ontology>)", 0, 100);
    assert!(matches!(
        tail.identity,
        SourceOntologyIdentity::Named { version: None, .. }
    ));
}

#[test]
fn anonymous_imports_keep_repetitions_order_unicode_and_original_keyword_offsets() {
    let source = "# Geräte\nPrefix(:=<https://example.org/设备#>) Ontology(Import(:motor) Import(<urn:parts>) Import(:motor) Declaration(Class(owl:Thing)))";
    let tail = ready(source, 3, 100);
    assert!(matches!(tail.identity, SourceOntologyIdentity::Anonymous));
    let values: Vec<_> = tail
        .imports
        .iter()
        .map(|row| row.target.value.as_slice())
        .collect();
    assert_eq!(
        values,
        [
            "https://example.org/设备#motor".as_bytes(),
            b"urn:parts",
            "https://example.org/设备#motor".as_bytes()
        ]
    );
    let offsets: Vec<_> = source
        .match_indices("Import")
        .map(|(offset, _)| offset)
        .collect();
    for (row, offset) in tail.imports.iter().zip(offsets) {
        assert_eq!(row.keyword.start, offset);
        assert!(matches!(
            row.keyword.terminal,
            Terminal::Keyword(Keyword::Import)
        ));
        assert_eq!(&source[row.keyword.start..row.keyword.end], "Import");
    }
    assert!(
        matches!(tail.remaining, Tokens::Cons { token, .. } if matches!(token.terminal, Terminal::Keyword(Keyword::Declaration)))
    );
}

#[test]
fn annotations_axioms_closing_tokens_and_unexpected_suffixes_are_left_unchanged() {
    for suffix in [
        ")",
        "Annotation(rdfs:label \"parts\"))",
        "Declaration(Class(owl:Thing)))",
        "<urn:third>)",
    ] {
        let source = format!("Ontology(<urn:first> <urn:second> {suffix}");
        let tail = ready(&source, 0, 100);
        let mut tokens = tail.remaining;
        let mut spans = Vec::new();
        while let Tokens::Cons { token, next } = tokens {
            spans.push(&source[token.start..token.end]);
            tokens = *next;
        }
        assert_eq!(
            spans.concat(),
            suffix
                .chars()
                .filter(|character| !character.is_whitespace())
                .collect::<String>()
        );
    }
    // A partial header does not validate the final ontology body or close.
    let tail = ready("Ontology(<urn:first> Import(<urn:parts>)", 1, 100);
    assert!(matches!(tail.remaining, Tokens::Empty));
}

#[test]
fn every_truncated_import_body_uses_the_full_original_eof_after_discarded_trivia() {
    for (prefix, want) in [
        ("Ontology(Import", "open"),
        ("Ontology(Import(", "iri"),
        ("Ontology(Import(<urn:parts>", "close"),
    ] {
        let source = format!("{prefix} # Geräte");
        let (kind, offset) = expected(read(&source, 10, 100));
        assert_eq!(kind, want);
        assert_eq!(offset, source.len());
    }
}

#[test]
fn wrong_import_tokens_precede_resolution_and_report_original_unicode_offsets() {
    for (body, want, wrong) in [
        ("Import ex:Parts)", "open", "ex:Parts"),
        ("Import(\"parts\"))", "iri", "\"parts\""),
        (
            "Import(missing:Parts Import(<urn:later>))",
            "close",
            "Import(<urn:later>",
        ),
    ] {
        let source = format!("# Geräte\nOntology({body}");
        let (kind, offset) = expected(read(&source, 10, 0));
        assert_eq!(kind, want);
        assert_eq!(
            offset,
            source.find(wrong).expect("original first wrong token")
        );
    }
}

#[test]
fn independent_import_counts_and_final_iri_budgets_preserve_error_priority() {
    let source = "Ontology(Import(";
    assert!(matches!(
        read(source, 0, 0),
        Err(HeaderError::ImportLimit { offset: 9 })
    ));
    let source = "Ontology(Import(<urn:first>) Import(";
    assert!(
        matches!(read(source, 1, 100), Err(HeaderError::ImportLimit { offset }) if offset == source.rfind("Import").expect("second keyword"))
    );
    let source = "Prefix(veryLongPrefix:=<x:>) Ontology(veryLongPrefix:A Import(veryLongPrefix:B))";
    let tail = ready(source, 1, 3);
    assert_eq!(tail.imports[0].target.value, b"x:B");
    let source = "Ontology(<urn:ontology> <urn:version:2>)";
    assert!(
        matches!(read(source, 0, 12), Err(HeaderError::Iri(SourceIriError::Name(NameError::ResourceLimit { offset }))) if offset == source.find("urn:version").expect("version payload"))
    );
    let source = "Ontology(Import(<urn:parts>))";
    assert!(matches!(
        read(source, 1, 0),
        Err(HeaderError::Iri(SourceIriError::Name(
            NameError::ResourceLimit { offset: 17 }
        )))
    ));
}

#[test]
fn ontology_version_and_import_iris_use_their_original_undeclared_prefix_offsets() {
    for source in [
        "Ontology(missing:Ontology)",
        "Ontology(<urn:ontology> missing:Version)",
        "Ontology(Import(missing:Parts))",
    ] {
        assert!(
            matches!(read(source, 10, 100), Err(HeaderError::Iri(SourceIriError::UndeclaredPrefix { offset })) if offset == source.find("missing:").expect("undeclared original prefix"))
        );
    }
    let source = "Ontology(Import(missing:Parts))";
    assert!(
        matches!(read(source, 10, 0), Err(HeaderError::Iri(SourceIriError::UndeclaredPrefix { offset })) if offset == source.find("missing:").expect("import prefix"))
    );
}

#[test]
fn low_level_header_reader_revalidates_supplied_iri_spans() {
    let declarations = Vec::new();
    let table = match check(&declarations) {
        Check::Ready(table) => table,
        _ => panic!("empty normative table"),
    };
    let bytes = b"garbage".to_vec();
    let tokens = Tokens::Cons {
        token: Token {
            terminal: Terminal::FullIri,
            start: 0,
            end: bytes.len(),
        },
        next: Box::new(Tokens::Empty),
    };
    assert!(matches!(
        read_header_tail(&table, &bytes, tokens, 0, 100),
        Err(HeaderError::Iri(SourceIriError::Name(
            NameError::InvalidToken { offset: 0 }
        )))
    ));
}
