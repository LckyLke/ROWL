use rowl_frontend::functional::{Keyword, Terminal};
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_names::NameError;
use rowl_frontend::functional_prefixes::{
    read_prefix_header, PrefixExpected, PrefixHeader, PrefixReadError, PrefixSyntaxError,
};
use rowl_frontend::prefixes::{check, Check};

fn read(source: &str, count: usize, value: usize) -> PrefixHeader {
    read_prefix_header(&source.as_bytes().to_vec(), 100, count, value)
        .unwrap_or_else(|_| panic!("fixture must have its complete prefix/header opening"))
}
fn expected(result: Result<PrefixHeader, PrefixReadError>) -> (PrefixExpected, usize) {
    match result {
        Err(PrefixReadError::Syntax(PrefixSyntaxError::Expected { expected, offset })) => {
            (expected, offset)
        }
        _ => panic!("expected original syntax mismatch/EOF"),
    }
}
fn kind(expected: PrefixExpected) -> &'static str {
    match expected {
        PrefixExpected::Ontology => "ontology",
        PrefixExpected::Open => "open",
        PrefixExpected::Name => "name",
        PrefixExpected::Equals => "equals",
        PrefixExpected::Namespace => "namespace",
        PrefixExpected::Close => "close",
    }
}

#[test]
fn source_prefixes_preserve_unicode_order_case_and_namespace_spelling() {
    let source = "# Geräte\nPrefix(:=<https://example.org/maintenance#>)\nPrefix(é:=<HTTP://Example.org/%61#>) Prefix(e\u{301}:=<urn:decomposed:>)\nOntology(<urn:maintenance> Declaration(Class(:Pump)))";
    let header = read(source, 3, 100);
    let fields: Vec<_> = header
        .declarations
        .iter()
        .map(|row| (row.name.as_slice(), row.namespace.as_slice()))
        .collect();
    assert_eq!(
        fields,
        vec![
            (
                ":".as_bytes(),
                "https://example.org/maintenance#".as_bytes()
            ),
            ("é:".as_bytes(), "HTTP://Example.org/%61#".as_bytes()),
            ("e\u{301}:".as_bytes(), "urn:decomposed:".as_bytes()),
        ]
    );
    assert_eq!(
        header.ontology.start,
        source.find("Ontology").expect("ontology source")
    );
    assert_eq!(
        &source.as_bytes()[header.ontology.start..header.ontology.end],
        b"Ontology"
    );
    assert_eq!(
        &source.as_bytes()[header.opening.start..header.opening.end],
        b"("
    );
    assert!(matches!(
        header.ontology.terminal,
        Terminal::Keyword(Keyword::Ontology)
    ));
    assert!(matches!(header.opening.terminal, Terminal::Open));
    assert!(matches!(check(&header.declarations), Check::Ready(_)));
}

#[test]
fn no_declarations_and_every_ontology_body_token_remain_intact() {
    let source = "Ontology(<urn:test> Declaration(Class(owl:Thing)))";
    let header = read(source, 0, 0);
    assert!(header.declarations.is_empty());
    let mut remaining = header.remaining;
    let mut spellings = Vec::new();
    while let Tokens::Cons { token, next } = remaining {
        spellings.push(&source[token.start..token.end]);
        remaining = *next;
    }
    assert_eq!(
        spellings,
        [
            "<urn:test>",
            "Declaration",
            "(",
            "Class",
            "(",
            "owl:Thing",
            ")",
            ")",
            ")"
        ]
    );
}

#[test]
fn repeated_and_reserved_rows_survive_for_the_normative_checked_constructor() {
    let header = read(
        "Prefix(ex:=<urn:first:>) Prefix(ex:=<urn:second:>) Ontology()",
        2,
        100,
    );
    assert_eq!(header.declarations.len(), 2);
    match check(&header.declarations) {
        Check::Duplicate { first, second } => {
            assert!(std::ptr::eq(first, &header.declarations[0]));
            assert!(std::ptr::eq(second, &header.declarations[1]));
            assert_eq!(first.namespace, b"urn:first:");
            assert_eq!(second.namespace, b"urn:second:");
        }
        _ => panic!("duplicate source rows must be rejected by table construction"),
    }
    let header = read("Prefix(owl:=<urn:custom:>) Ontology()", 1, 100);
    assert!(
        matches!(check(&header.declarations), Check::ReservedName(row) if std::ptr::eq(row, &header.declarations[0]))
    );
    let header = read("Prefix(OWL:=<urn:custom:>) Ontology()", 1, 100);
    assert!(matches!(check(&header.declarations), Check::Ready(_)));
}

#[test]
fn every_truncated_syntax_stage_reports_the_original_full_source_length() {
    for (source, want) in [
        ("", "ontology"),
        ("# only a comment", "ontology"),
        ("Prefix", "open"),
        ("Prefix(", "name"),
        ("Prefix(ex:", "equals"),
        ("Prefix(ex:=", "namespace"),
        ("Prefix(ex:=<urn:part:>", "close"),
        ("Prefix(ex:=<urn:part:>)", "ontology"),
        ("Ontology", "open"),
    ] {
        let (actual, offset) = expected(read_prefix_header(
            &source.as_bytes().to_vec(),
            100,
            10,
            100,
        ));
        assert_eq!(kind(actual), want);
        assert_eq!(offset, source.len());
    }
}

#[test]
fn wrong_syntax_reports_the_first_actual_token_without_losing_unicode_offsets() {
    for (body, want, wrong) in [
        ("Prefix ex: Ontology()", "open", "ex:"),
        ("Prefix(<urn:part:>) Ontology()", "name", "<urn:part:>"),
        (
            "Prefix(ex: <urn:part:>) Ontology()",
            "equals",
            "<urn:part:>",
        ),
        ("Prefix(ex:=ex:Base) Ontology()", "namespace", "ex:Base"),
        ("Prefix(ex:=<urn:part:> Ontology()", "close", "Ontology"),
        ("Declaration(Class(owl:Thing))", "ontology", "Declaration"),
        ("Ontology ex:Pump", "open", "ex:Pump"),
    ] {
        let source = format!("# Geräte\n{body}");
        let (actual, offset) =
            expected(read_prefix_header(&source.as_bytes().to_vec(), 100, 10, 0));
        assert_eq!(kind(actual), want);
        assert_eq!(offset, source.find(wrong).expect("original wrong token"));
    }
}

#[test]
fn declaration_counts_precede_body_syntax_and_payload_limits_are_per_value() {
    let source = b"Prefix(".to_vec();
    assert!(matches!(
        read_prefix_header(&source, 100, 0, 0),
        Err(PrefixReadError::Syntax(
            PrefixSyntaxError::DeclarationLimit { offset: 0 }
        ))
    ));
    let source = "Prefix(ex:=<urn:part:>) Ontology()";
    assert!(matches!(
        read_prefix_header(&source.as_bytes().to_vec(), 100, 1, 0),
        Err(PrefixReadError::Syntax(PrefixSyntaxError::Name(
            NameError::ResourceLimit { offset: 7 }
        )))
    ));
    let iri_start = source.find("urn:part:").expect("IRI payload");
    assert!(
        matches!(read_prefix_header(&source.as_bytes().to_vec(), 100, 1, 3), Err(PrefixReadError::Syntax(PrefixSyntaxError::Name(NameError::ResourceLimit { offset })) ) if offset == iri_start)
    );
    assert_eq!(read(source, 1, 9).declarations.len(), 1);
    let source = "Prefix(a:=<x:A>) Prefix(b:=<x:B>) Ontology()";
    let second = source.rfind("Prefix").expect("second declaration");
    assert!(
        matches!(read_prefix_header(&source.as_bytes().to_vec(), 100, 1, 100), Err(PrefixReadError::Syntax(PrefixSyntaxError::DeclarationLimit { offset })) if offset == second)
    );
}

#[test]
fn later_lexical_failure_precedes_every_prefix_syntax_and_resource_outcome() {
    let source = b"Prefix(ex:=<urn:part:>) Ontology() 10abc".to_vec();
    assert!(matches!(
        read_prefix_header(&source, 100, 0, 0),
        Err(PrefixReadError::MissingSeparator { .. })
    ));
    let mut malformed = b"Prefix(ex:=<urn:part:>) Ontology()".to_vec();
    malformed.push(0xff);
    assert!(matches!(
        read_prefix_header(&malformed, 100, 0, 0),
        Err(PrefixReadError::InvalidText(_))
    ));
    assert!(matches!(
        read_prefix_header(&b"Ontology()".to_vec(), 0, 0, 0),
        Err(PrefixReadError::TokenLimit { offset: 0 })
    ));
    assert!(matches!(
        read_prefix_header(&b"Ontology() `".to_vec(), 100, 0, 0),
        Err(PrefixReadError::NoToken { .. })
    ));
}

#[test]
fn header_acceptance_explicitly_leaves_full_ontology_contents_for_the_next_parser() {
    let header = read("Prefix(ex:=<urn:part:>) Ontology(", 1, 100);
    assert!(matches!(header.remaining, Tokens::Empty));
    // Only the header opening is read. No complete ontology or consistency verdict
    // is implied by accepting this deliberately unfinished body.
    assert_eq!(header.declarations[0].namespace, b"urn:part:");
}
