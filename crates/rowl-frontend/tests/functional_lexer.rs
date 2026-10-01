use rowl_frontend::functional::Terminal;
use rowl_frontend::functional_lexer::{lex, LexResult, Tokens};
use rowl_frontend::unicode::TextError;

#[derive(Debug, PartialEq, Eq)]
struct Span {
    kind: &'static str,
    text: String,
    start: usize,
    end: usize,
}
#[derive(Debug, PartialEq, Eq)]
enum Failure {
    Utf8(usize),
    Xml(usize, u32),
    NoToken(usize),
    Separator(usize),
    Limit(usize),
}
fn kind(terminal: Terminal) -> &'static str {
    match terminal {
        Terminal::Keyword(_) => "keyword",
        Terminal::Open => "open",
        Terminal::Close => "close",
        Terminal::Equals => "equals",
        Terminal::DatatypeIndicator => "datatype",
        Terminal::Integer => "integer",
        Terminal::QuotedString => "string",
        Terminal::LanguageTag => "language",
        Terminal::NodeId => "blank",
        Terminal::FullIri => "iri",
        Terminal::PrefixName => "prefix",
        Terminal::AbbreviatedIri => "abbreviated",
        Terminal::Whitespace | Terminal::Comment => panic!("trivia must be discarded"),
    }
}
fn read(bytes: &[u8], limit: usize) -> Result<Vec<Span>, Failure> {
    let mut tokens = match lex(&bytes.to_vec(), limit) {
        LexResult::Tokens(tokens) => tokens,
        LexResult::InvalidText(TextError::InvalidUtf8 { offset }) => {
            return Err(Failure::Utf8(offset));
        }
        LexResult::InvalidText(TextError::NonXmlCharacter { offset, codepoint }) => {
            return Err(Failure::Xml(offset, codepoint));
        }
        LexResult::NoToken { offset } => return Err(Failure::NoToken(offset)),
        LexResult::MissingSeparator { offset } => return Err(Failure::Separator(offset)),
        LexResult::TokenLimit { offset } => return Err(Failure::Limit(offset)),
        LexResult::InvalidText(TextError::InvalidPosition { .. })
        | LexResult::InvalidSpan { .. } => panic!("unreachable source boundary"),
    };
    let mut spans = Vec::new();
    while let Tokens::Cons { token, next } = tokens {
        spans.push(Span {
            kind: kind(token.terminal),
            text: String::from_utf8(bytes[token.start..token.end].to_vec()).unwrap(),
            start: token.start,
            end: token.end,
        });
        tokens = *next;
    }
    Ok(spans)
}
fn texts(source: &str) -> Vec<String> {
    read(source.as_bytes(), usize::MAX)
        .unwrap()
        .into_iter()
        .map(|span| span.text)
        .collect()
}

#[test]
fn standard_separator_examples_and_exact_original_offsets() {
    for source in ["\"10\" ^^ xsd:integer", "\"10\"^^xsd:integer"] {
        assert_eq!(texts(source), ["\"10\"", "^^", "xsd:integer"]);
    }
    for source in ["\"abc\" @en", "\"abc\"@en"] {
        assert_eq!(texts(source), ["\"abc\"", "@en"]);
    }
    for (source, error) in [
        ("10abc", Failure::Separator(2)),
        ("\"a\"\"b\"", Failure::Separator(3)),
        ("\"abc\"@ en", Failure::NoToken(5)),
        ("pref: ABC", Failure::NoToken(6)),
    ] {
        assert_eq!(read(source.as_bytes(), 100), Err(error));
    }
    assert_eq!(texts("SubClassOf:ABC"), ["SubClassOf:ABC"]);
}

#[test]
fn real_ontology_source_preserves_every_regular_token_in_order() {
    let source = r#"# Maintenance vocabulary
Prefix(:=<urn:maintenance:>)
Ontology(<urn:maintenance>
 Declaration(Class(:Machine))
 Declaration(ObjectProperty(:hasPart))
 SubClassOf(ObjectIntersectionOf(:Machine ObjectSomeValuesFrom(:hasPart :FaultyPart)) :NeedsInspection)
 SubObjectPropertyOf(ObjectPropertyChain(:hasPart :hasPart) :nestedPart)
 SubClassOf(:Machine ObjectMinCardinality(1 :hasPart :Part))
 Annotation(rdfs:label "Werkstatt #1"@de)
 ClassAssertion(:Machine :pump1)
 ObjectPropertyAssertion(:hasPart :pump1 _:motor)
)"#;
    let spans = read(source.as_bytes(), 200).unwrap();
    let expected = [
        "Prefix",
        "(",
        ":",
        "=",
        "<urn:maintenance:>",
        ")",
        "Ontology",
        "(",
        "<urn:maintenance>",
        "Declaration",
        "(",
        "Class",
        "(",
        ":Machine",
        ")",
        ")",
        "Declaration",
        "(",
        "ObjectProperty",
        "(",
        ":hasPart",
        ")",
        ")",
        "SubClassOf",
        "(",
        "ObjectIntersectionOf",
        "(",
        ":Machine",
        "ObjectSomeValuesFrom",
        "(",
        ":hasPart",
        ":FaultyPart",
        ")",
        ")",
        ":NeedsInspection",
        ")",
        "SubObjectPropertyOf",
        "(",
        "ObjectPropertyChain",
        "(",
        ":hasPart",
        ":hasPart",
        ")",
        ":nestedPart",
        ")",
        "SubClassOf",
        "(",
        ":Machine",
        "ObjectMinCardinality",
        "(",
        "1",
        ":hasPart",
        ":Part",
        ")",
        ")",
        "Annotation",
        "(",
        "rdfs:label",
        "\"Werkstatt #1\"",
        "@de",
        ")",
        "ClassAssertion",
        "(",
        ":Machine",
        ":pump1",
        ")",
        "ObjectPropertyAssertion",
        "(",
        ":hasPart",
        ":pump1",
        "_:motor",
        ")",
        ")",
    ];
    assert_eq!(
        spans
            .iter()
            .map(|span| span.text.as_str())
            .collect::<Vec<_>>(),
        expected
    );
    for span in &spans {
        assert!(span.start < span.end);
        assert_eq!(&source[span.start..span.end], span.text);
    }
    assert!(spans.windows(2).all(|pair| pair[0].end <= pair[1].start));
}

#[test]
fn trivia_is_ignored_and_hashes_inside_tokens_are_preserved() {
    for source in ["", " \t\r\n", "#only a comment", " \n#one\r\n#two\n  "] {
        assert_eq!(read(source.as_bytes(), 0), Ok(Vec::new()));
    }
    assert_eq!(
        texts(" #first\r\nOntology( #inside\n ) #last"),
        ["Ontology", "(", ")"]
    );
    assert_eq!(
        texts("\" #comment\\\" \" #comment \"abc\""),
        ["\" #comment\\\" \""]
    );
    assert_eq!(texts("<urn:example#comment>"), ["<urn:example#comment>"]);
    assert_eq!(
        texts("\"first\n#second\"@en"),
        ["\"first\n#second\"", "@en"]
    );
}

#[test]
fn every_token_budget_reports_the_first_unemitted_source_position() {
    let source = " #leading\n Ontology( :Machine #separator\n :pump1 ) #trailing";
    let spans = read(source.as_bytes(), 100).unwrap();
    for (limit, span) in spans.iter().enumerate() {
        assert_eq!(
            read(source.as_bytes(), limit),
            Err(Failure::Limit(span.start))
        );
    }
    assert_eq!(read(source.as_bytes(), spans.len()), Ok(spans));
    // Reaching a token limit takes priority over checking that token's separator.
    assert_eq!(read(b"10abc", 0), Err(Failure::Limit(0)));
    assert_eq!(read(b"10abc", 1), Err(Failure::Separator(2)));
}

#[test]
fn later_errors_reject_the_entire_stream_and_xml_text_is_checked_first() {
    assert_eq!(read(b"Ontology() ABC", 100), Err(Failure::NoToken(11)));
    assert_eq!(read(b"Ontology() 10abc", 100), Err(Failure::Separator(13)));
    assert_eq!(read(b"Ontology() \xff", 0), Err(Failure::Utf8(11)));
    assert_eq!(read(b"Ontology() \x00", 0), Err(Failure::Xml(11, 0)));
    assert_eq!(read(b"\"unterminated", 100), Err(Failure::NoToken(0)));
    assert_eq!(
        read(b"Ontology() \"wrong\\n\"", 100),
        Err(Failure::NoToken(11))
    );
}

#[test]
fn unicode_endings_are_decoded_at_source_boundaries() {
    let source = "é:机器 𝒙:part <urn:部件#x>123";
    let spans = read(source.as_bytes(), 4).unwrap();
    assert_eq!(
        spans
            .iter()
            .map(|span| span.text.as_str())
            .collect::<Vec<_>>(),
        ["é:机器", "𝒙:part", "<urn:部件#x>", "123"]
    );
    assert_eq!(
        read("ex:é\"next\"".as_bytes(), 100),
        Err(Failure::Separator(5))
    );
    assert_eq!(
        read("𝒙:part\"next\"".as_bytes(), 100),
        Err(Failure::Separator(9))
    );
    assert_eq!(texts("\"é𝒙\"^^xsd:string"), ["\"é𝒙\"", "^^", "xsd:string"]);
}

#[test]
fn every_regular_terminal_family_is_emitted_with_its_own_kind() {
    for (source, expected) in [
        ("Class", "keyword"),
        ("(", "open"),
        (")", "close"),
        ("=", "equals"),
        ("^^", "datatype"),
        ("003", "integer"),
        ("\"text\"", "string"),
        ("@en-Latn-US", "language"),
        ("_:b1", "blank"),
        ("<urn:part>", "iri"),
        ("ex:", "prefix"),
        ("ex:part", "abbreviated"),
    ] {
        let spans = read(source.as_bytes(), 1).unwrap();
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].kind, expected);
        assert_eq!(spans[0].text, source);
    }
}
