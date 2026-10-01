use rowl_frontend::functional::{recognize, Keyword, Terminal};
use rowl_frontend::regular::MatchResult;

fn inventory() -> Vec<(Terminal, &'static str)> {
    let keywords = [
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
    ];
    let mut terminals: Vec<_> = keywords
        .into_iter()
        .map(|(key, text)| (Terminal::Keyword(key), text))
        .collect();
    terminals.extend([
        (Terminal::Open, "("),
        (Terminal::Close, ")"),
        (Terminal::Equals, "="),
        (Terminal::DatatypeIndicator, "^^"),
        (Terminal::Integer, "003"),
        (Terminal::QuotedString, "\"faulty #part\""),
        (Terminal::LanguageTag, "@en-Latn-US"),
        (Terminal::NodeId, "_:motor1"),
        (Terminal::FullIri, "<urn:maintenance:part>"),
        (Terminal::PrefixName, "ex:"),
        (Terminal::AbbreviatedIri, "ex:part"),
        (Terminal::Whitespace, " \t\r\n"),
        (Terminal::Comment, "#comment Ω"),
    ]);
    terminals
}
fn recognized(terminal: Terminal, source: &str) -> bool {
    match recognize(terminal, &source.as_bytes().to_vec()) {
        MatchResult::Matched(value) => value,
        MatchResult::MalformedUtf8(_) => panic!("every fixture is complete UTF-8"),
    }
}

#[test]
fn every_standard_terminal_fixture_has_exactly_one_whole_token_kind() {
    let terminals = inventory();
    assert_eq!(terminals.len(), 84);
    for (expected, (_, source)) in terminals.iter().enumerate() {
        let matching: Vec<_> = terminals
            .iter()
            .enumerate()
            .filter_map(|(index, (terminal, _))| recognized(*terminal, source).then_some(index))
            .collect();
        assert_eq!(matching, [expected], "whole source {source:?}");
    }
}

#[test]
fn unicode_names_and_keyword_name_competition_never_share_a_whole_kind() {
    let terminals = inventory();
    for source in [
        "Class:",
        "Class:part",
        ":",
        ":部件",
        "é:",
        "é:部件",
        "𐀀:ä",
        "_:9",
        "_:é",
        "\"#x\r\ny\"",
        "<urn:部件#x>",
    ] {
        let matching = terminals
            .iter()
            .filter(|(terminal, _)| recognized(*terminal, source))
            .count();
        assert_eq!(matching, 1, "whole source {source:?}");
    }
    for source in ["", "ABC", "10abc", "ex:\\escaped", "#comment\n"] {
        let matching = terminals
            .iter()
            .filter(|(terminal, _)| recognized(*terminal, source))
            .count();
        assert_eq!(matching, 0, "nonterminal source {source:?}");
    }
}

#[test]
fn every_utf8_endpoint_has_at_most_one_candidate_kind() {
    let terminals = inventory();
    for source in [
        "SubClassOf:部件(",
        "<urn:part#comment>123",
        "\"quoted\\\"#part\"@en",
        "_:é ",
        "000abc",
        "é:部件. ",
    ] {
        for endpoint in 1..=source.len() {
            if !source.is_char_boundary(endpoint) {
                continue;
            }
            let segment = &source[..endpoint];
            let matching = terminals
                .iter()
                .filter(|(terminal, _)| recognized(*terminal, segment))
                .count();
            assert!(matching <= 1, "endpoint {endpoint} of {source:?}");
        }
    }
}
