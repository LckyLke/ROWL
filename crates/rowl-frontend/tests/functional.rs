use rowl_frontend::functional::{
    grammar, longest, next_terminal, recognize, Keyword, Selection, Terminal,
};
use rowl_frontend::longest::PrefixResult;
use rowl_frontend::regular::{matches_utf8, MatchResult};
use rowl_frontend::unicode::TextError;

fn matches(terminal: Terminal, text: &str) -> bool {
    match recognize(terminal, &text.as_bytes().to_vec()) {
        MatchResult::Matched(value) => value,
        MatchResult::MalformedUtf8(_) => panic!("valid Rust str"),
    }
}
fn endpoint(terminal: Terminal, text: &str, start: usize) -> Option<usize> {
    match longest(terminal, &text.as_bytes().to_vec(), start) {
        PrefixResult::Matched(value) => value,
        PrefixResult::MalformedUtf8(_) => panic!("valid boundary"),
    }
}
#[test]
fn every_normative_keyword_is_exact_case_sensitive_and_nonempty() {
    for (keyword, text) in [
        (Keyword::Prefix, "Prefix"),
        (Keyword::Ontology, "Ontology"),
        (Keyword::Import, "Import"),
        (Keyword::Declaration, "Declaration"),
        (Keyword::Class, "Class"),
        (Keyword::Datatype, "Datatype"),
        (Keyword::ObjectProperty, "ObjectProperty"),
        (Keyword::DataProperty, "DataProperty"),
        (Keyword::AnnotationProperty, "AnnotationProperty"),
        (Keyword::NamedIndividual, "NamedIndividual"),
        (Keyword::Annotation, "Annotation"),
        (Keyword::AnnotationAssertion, "AnnotationAssertion"),
        (Keyword::SubAnnotationPropertyOf, "SubAnnotationPropertyOf"),
        (
            Keyword::AnnotationPropertyDomain,
            "AnnotationPropertyDomain",
        ),
        (Keyword::AnnotationPropertyRange, "AnnotationPropertyRange"),
        (Keyword::ObjectInverseOf, "ObjectInverseOf"),
        (Keyword::DataIntersectionOf, "DataIntersectionOf"),
        (Keyword::DataUnionOf, "DataUnionOf"),
        (Keyword::DataComplementOf, "DataComplementOf"),
        (Keyword::DataOneOf, "DataOneOf"),
        (Keyword::DatatypeRestriction, "DatatypeRestriction"),
        (Keyword::ObjectIntersectionOf, "ObjectIntersectionOf"),
        (Keyword::ObjectUnionOf, "ObjectUnionOf"),
        (Keyword::ObjectComplementOf, "ObjectComplementOf"),
        (Keyword::ObjectOneOf, "ObjectOneOf"),
        (Keyword::ObjectSomeValuesFrom, "ObjectSomeValuesFrom"),
        (Keyword::ObjectAllValuesFrom, "ObjectAllValuesFrom"),
        (Keyword::ObjectHasValue, "ObjectHasValue"),
        (Keyword::ObjectHasSelf, "ObjectHasSelf"),
        (Keyword::ObjectMinCardinality, "ObjectMinCardinality"),
        (Keyword::ObjectMaxCardinality, "ObjectMaxCardinality"),
        (Keyword::ObjectExactCardinality, "ObjectExactCardinality"),
        (Keyword::DataSomeValuesFrom, "DataSomeValuesFrom"),
        (Keyword::DataAllValuesFrom, "DataAllValuesFrom"),
        (Keyword::DataHasValue, "DataHasValue"),
        (Keyword::DataMinCardinality, "DataMinCardinality"),
        (Keyword::DataMaxCardinality, "DataMaxCardinality"),
        (Keyword::DataExactCardinality, "DataExactCardinality"),
        (Keyword::SubClassOf, "SubClassOf"),
        (Keyword::EquivalentClasses, "EquivalentClasses"),
        (Keyword::DisjointClasses, "DisjointClasses"),
        (Keyword::DisjointUnion, "DisjointUnion"),
        (Keyword::SubObjectPropertyOf, "SubObjectPropertyOf"),
        (Keyword::ObjectPropertyChain, "ObjectPropertyChain"),
        (
            Keyword::EquivalentObjectProperties,
            "EquivalentObjectProperties",
        ),
        (
            Keyword::DisjointObjectProperties,
            "DisjointObjectProperties",
        ),
        (Keyword::ObjectPropertyDomain, "ObjectPropertyDomain"),
        (Keyword::ObjectPropertyRange, "ObjectPropertyRange"),
        (Keyword::InverseObjectProperties, "InverseObjectProperties"),
        (
            Keyword::FunctionalObjectProperty,
            "FunctionalObjectProperty",
        ),
        (
            Keyword::InverseFunctionalObjectProperty,
            "InverseFunctionalObjectProperty",
        ),
        (Keyword::ReflexiveObjectProperty, "ReflexiveObjectProperty"),
        (
            Keyword::IrreflexiveObjectProperty,
            "IrreflexiveObjectProperty",
        ),
        (Keyword::SymmetricObjectProperty, "SymmetricObjectProperty"),
        (
            Keyword::AsymmetricObjectProperty,
            "AsymmetricObjectProperty",
        ),
        (
            Keyword::TransitiveObjectProperty,
            "TransitiveObjectProperty",
        ),
        (Keyword::SubDataPropertyOf, "SubDataPropertyOf"),
        (
            Keyword::EquivalentDataProperties,
            "EquivalentDataProperties",
        ),
        (Keyword::DisjointDataProperties, "DisjointDataProperties"),
        (Keyword::DataPropertyDomain, "DataPropertyDomain"),
        (Keyword::DataPropertyRange, "DataPropertyRange"),
        (Keyword::FunctionalDataProperty, "FunctionalDataProperty"),
        (Keyword::DatatypeDefinition, "DatatypeDefinition"),
        (Keyword::HasKey, "HasKey"),
        (Keyword::SameIndividual, "SameIndividual"),
        (Keyword::DifferentIndividuals, "DifferentIndividuals"),
        (Keyword::ClassAssertion, "ClassAssertion"),
        (Keyword::ObjectPropertyAssertion, "ObjectPropertyAssertion"),
        (
            Keyword::NegativeObjectPropertyAssertion,
            "NegativeObjectPropertyAssertion",
        ),
        (Keyword::DataPropertyAssertion, "DataPropertyAssertion"),
        (
            Keyword::NegativeDataPropertyAssertion,
            "NegativeDataPropertyAssertion",
        ),
    ] {
        assert!(matches(Terminal::Keyword(keyword), text));
    }
    assert!(!matches(
        Terminal::Keyword(Keyword::SubClassOf),
        "subClassOf"
    ));
    assert!(!matches(Terminal::Keyword(Keyword::Ontology), "ontology"));
    assert!(!matches(Terminal::Keyword(Keyword::Prefix), "Prefix:"));
    assert!(!matches(
        Terminal::Keyword(Keyword::Class),
        "ClassAssertion"
    ));
    assert!(!matches(Terminal::Keyword(Keyword::Annotation), ""));
}
#[test]
fn punctuation_and_variable_productions_match_complete_tokens() {
    for (terminal, text) in [
        (Terminal::Open, "("),
        (Terminal::Close, ")"),
        (Terminal::Equals, "="),
        (Terminal::DatatypeIndicator, "^^"),
        (Terminal::Integer, "0000000000000000000000000000000007"),
        (Terminal::PrefixName, ":"),
        (Terminal::PrefixName, "é:"),
        (Terminal::AbbreviatedIri, ":pump17"),
        (Terminal::NodeId, "_:7"),
        (Terminal::FullIri, "<https://example.org/pump#part>"),
    ] {
        assert!(matches(terminal, text), "{text:?}");
    }
    for (terminal, text) in [
        (Terminal::Open, "()"),
        (Terminal::DatatypeIndicator, "^"),
        (Terminal::DatatypeIndicator, "^ ^"),
        (Terminal::Integer, "+1"),
        (Terminal::Integer, "1.0"),
        (Terminal::Integer, "１"),
        (Terminal::Integer, ""),
        (Terminal::PrefixName, "_:"),
        (Terminal::AbbreviatedIri, "ex:"),
        (Terminal::NodeId, "_:"),
        (Terminal::FullIri, "<relative>"),
        (Terminal::FullIri, "<http://example.org/\\u0041>"),
    ] {
        assert!(!matches(terminal, text), "{text:?}");
    }
}
#[test]
fn quoted_strings_keep_multiline_text_and_only_the_two_owl_escapes() {
    for text in [
        r#""""#,
        r#""machine""#,
        r#""a\"b\\c""#,
        "\"line one\nline two\r\t机\"",
        r##""#comment <urn:example:> @en ^^""##,
    ] {
        assert!(matches(Terminal::QuotedString, text), "{text:?}");
    }
    for text in [
        r#""a\n""#,
        r#""a\t""#,
        r#""a\u0041""#,
        r#""a\U00000041""#,
        r#""a\'""#,
        "\"unclosed",
        "\"a\"extra",
        "\"\u{0}\"",
    ] {
        assert!(!matches(Terminal::QuotedString, text), "{text:?}");
    }
    let source = "\"#comment\\\" body\" #ignored";
    assert_eq!(
        endpoint(Terminal::QuotedString, source, 0),
        source.find(" #ignored")
    );
}
#[test]
fn language_tags_follow_the_explicit_langtag_production() {
    for text in [
        "@en",
        "@EN-lAtN-us",
        "@zh-cmn-Hans",
        "@en-fubar",
        "@de-DE-x-private",
        "@en-a-test-a-again",
    ] {
        assert!(matches(Terminal::LanguageTag, text), "{text:?}");
    }
    for text in [
        "@",
        "@ en",
        "@en_uk",
        "@x-private",
        "@i-klingon",
        "@en-gb-oed",
    ] {
        assert!(!matches(Terminal::LanguageTag, text), "{text:?}");
    }
    // The broader Language-Tag production remains available for RDF.
    assert!(matches!(
        matches_utf8(rowl_frontend::langtag::grammar(), &b"i-klingon".to_vec()),
        MatchResult::Matched(true)
    ));
    assert!(matches!(
        matches_utf8(rowl_frontend::langtag::grammar(), &b"x-private".to_vec()),
        MatchResult::Matched(true)
    ));
}
#[test]
fn comments_stop_before_cr_or_lf_and_do_not_change_string_or_iri_context() {
    for text in ["#", "#comment", "#\t机 <#> \"quoted\"", "##"] {
        assert!(matches(Terminal::Comment, text), "{text:?}");
    }
    assert!(!matches(Terminal::Comment, "#comment\n"));
    assert!(!matches(Terminal::Comment, "#comment\r"));
    assert!(!matches(Terminal::Comment, "#\u{0}"));
    assert_eq!(
        endpoint(Terminal::Comment, "#comment\r\nOntology()", 0),
        Some(8)
    );
    assert_eq!(
        endpoint(Terminal::FullIri, "<urn:example:#comment>#ignored", 0),
        Some(22)
    );
    assert!(matches(Terminal::Whitespace, " \t\r\n"));
    assert!(!matches(Terminal::Whitespace, ""));
    assert!(!matches(Terminal::Whitespace, "\u{a0}"));
    assert!(!matches(Terminal::Whitespace, "\u{b}"));
}
#[test]
fn greedy_keyword_name_competition_and_exact_byte_endpoints() {
    let text = "SubClassOf:ABC)";
    assert_eq!(
        endpoint(Terminal::Keyword(Keyword::SubClassOf), text, 0),
        Some(10)
    );
    assert_eq!(endpoint(Terminal::AbbreviatedIri, text, 0), Some(14));
    assert_eq!(endpoint(Terminal::PrefixName, text, 0), Some(11));
    assert_eq!(endpoint(Terminal::Integer, "10abc", 0), Some(2));
    assert_eq!(endpoint(Terminal::QuotedString, "x\"é𐀀\"", 1), Some(9));
    assert_eq!(endpoint(Terminal::LanguageTag, "\"abc\"@en", 5), Some(8));
}
#[test]
fn every_terminal_rejects_empty_input_without_hiding_malformed_suffixes() {
    for terminal in [
        Terminal::Keyword(Keyword::Ontology),
        Terminal::Open,
        Terminal::Close,
        Terminal::Equals,
        Terminal::DatatypeIndicator,
        Terminal::Integer,
        Terminal::QuotedString,
        Terminal::LanguageTag,
        Terminal::NodeId,
        Terminal::FullIri,
        Terminal::PrefixName,
        Terminal::AbbreviatedIri,
        Terminal::Whitespace,
        Terminal::Comment,
    ] {
        assert!(!matches(terminal, ""));
    }
    let mut bytes = b"Ontology".to_vec();
    bytes.push(0xff);
    assert!(matches!(
        recognize(Terminal::Keyword(Keyword::Ontology), &bytes),
        MatchResult::MalformedUtf8(TextError::InvalidUtf8 { offset: 8 })
    ));
    assert!(matches!(
        longest(Terminal::Keyword(Keyword::Ontology), &bytes, 0),
        PrefixResult::MalformedUtf8(TextError::InvalidUtf8 { offset: 8 })
    ));
    assert!(matches!(
        longest(Terminal::Whitespace, &bytes, 0),
        PrefixResult::MalformedUtf8(TextError::InvalidUtf8 { offset: 8 })
    ));
    let _ = grammar(Terminal::QuotedString);
}

#[test]
fn combined_selection_uses_the_entire_inventory_and_returns_actual_source_spans() {
    for (text, start, end, expected) in [
        ("SubClassOf:ABC)", 0, 14, Terminal::AbbreviatedIri),
        (
            "SubClassOf(:Pump :Machine)",
            0,
            10,
            Terminal::Keyword(Keyword::SubClassOf),
        ),
        ("Prefix(:=<urn:maintenance:>)", 6, 7, Terminal::Open),
        ("Prefix(:=<urn:maintenance:>)", 7, 8, Terminal::PrefixName),
        ("Prefix(:=<urn:maintenance:>)", 8, 9, Terminal::Equals),
        ("Prefix(:=<urn:maintenance:>)", 9, 27, Terminal::FullIri),
        ("#comment\r\nOntology()", 0, 8, Terminal::Comment),
        (" \t\r\nOntology()", 0, 4, Terminal::Whitespace),
        ("\"abc\"@en", 5, 8, Terminal::LanguageTag),
        ("10abc", 0, 2, Terminal::Integer),
    ] {
        let Selection::Token(token) = next_terminal(&text.as_bytes().to_vec(), start) else {
            panic!("expected a selected terminal");
        };
        assert_eq!((token.start, token.end), (start, end), "{text:?}");
        // Compare the selected source to the independently supplied expected grammar.
        assert!(matches(expected, &text[start..end]), "{text:?}");
        assert!(matches(token.terminal, &text[start..end]), "{text:?}");
        assert!(token.end > token.start);
    }
    // Selection is one lexer stage: the separator stage must later reject 10abc.
    assert!(matches!(
        next_terminal(&b"unknownWord".to_vec(), 0),
        Selection::NoMatch
    ));
    assert!(matches!(next_terminal(&Vec::new(), 0), Selection::NoMatch));
    assert!(matches!(
        next_terminal(&vec![0xff], 0),
        Selection::MalformedUtf8(TextError::InvalidUtf8 { offset: 0 })
    ));
}
