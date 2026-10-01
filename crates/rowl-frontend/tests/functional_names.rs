use rowl_frontend::functional_names::{read_span, NameError, NameKind};

fn value(kind: NameKind, source: &[u8], start: usize, end: usize, limit: usize) -> Vec<u8> {
    read_span(kind, &source.to_vec(), start, end, limit)
        .unwrap_or_else(|_| panic!("fixture must have its complete exact name payload"))
}
fn error(result: Result<Vec<u8>, NameError>) -> (&'static str, usize) {
    match result {
        Err(NameError::InvalidSpan { offset }) => ("span", offset),
        Err(NameError::InvalidToken { offset }) => ("token", offset),
        Err(NameError::ResourceLimit { offset }) => ("limit", offset),
        Ok(_) => panic!("expected an exact phase/source-offset diagnosis"),
    }
}

#[test]
fn all_five_families_preserve_exact_nonquoted_values() {
    for (kind, source, expected) in [
        (
            NameKind::FullIri,
            "<https://example.org/部品%2f#Ä>",
            "https://example.org/部品%2f#Ä",
        ),
        (NameKind::FullIri, "<urn:part:Pump>", "urn:part:Pump"),
        (NameKind::PrefixName, "éx:", "éx:"),
        (NameKind::PrefixName, ":", ":"),
        (NameKind::AbbreviatedIri, "éx:部品.端", "éx:部品.端"),
        (NameKind::AbbreviatedIri, ":Pump", ":Pump"),
        (NameKind::NodeId, "_:部品.端", "部品.端"),
        (NameKind::NodeId, "_:0", "0"),
        (NameKind::LanguageTag, "@EN-gb", "EN-gb"),
        (
            NameKind::LanguageTag,
            "@en-Latn-US-u-ca-gregory",
            "en-Latn-US-u-ca-gregory",
        ),
    ] {
        assert_eq!(
            value(kind, source.as_bytes(), 0, source.len(), expected.len()),
            expected.as_bytes()
        );
    }
}

#[test]
fn original_unicode_source_spans_and_marker_excluding_budgets_are_exact() {
    for (kind, token, expected, head) in [
        (NameKind::FullIri, "<urn:部品>", "urn:部品", 1),
        (NameKind::PrefixName, "部品:", "部品:", 0),
        (NameKind::AbbreviatedIri, "ex:部品", "ex:部品", 0),
        (NameKind::NodeId, "_:部品", "部品", 2),
        (NameKind::LanguageTag, "@EN-gb", "EN-gb", 1),
    ] {
        let text = format!("# Geräte\n{token} suffix");
        let source = text.as_bytes().to_vec();
        let start = text.find(token).expect("fixture token");
        let end = start + token.len();
        assert_eq!(
            value(kind, &source, start, end, expected.len()),
            expected.as_bytes()
        );
        assert_eq!(
            error(read_span(kind, &source, start, end, expected.len() - 1)),
            ("limit", start + head)
        );
        assert_eq!(
            value(kind, &source, start, end, usize::MAX),
            expected.as_bytes()
        );
    }
}

#[test]
fn incorrect_families_and_nonfunctional_escape_rules_are_rejected() {
    for (kind, source) in [
        (NameKind::FullIri, "<relative>"),
        (NameKind::FullIri, "<urn:part>junk"),
        (NameKind::FullIri, r"<urn:part\u0041>"),
        (NameKind::PrefixName, "ex:Pump"),
        (NameKind::PrefixName, "0ex:"),
        (NameKind::AbbreviatedIri, "ex:"),
        (NameKind::AbbreviatedIri, "ex:Pump:Part"),
        (NameKind::AbbreviatedIri, r"ex:Pump\~"),
        (NameKind::NodeId, "_:"),
        (NameKind::NodeId, "_:Pump."),
        (NameKind::LanguageTag, "@en_uk"),
        (NameKind::LanguageTag, "@en-"),
    ] {
        assert_eq!(
            error(read_span(
                kind,
                &source.as_bytes().to_vec(),
                0,
                source.len(),
                0
            )),
            ("token", 0)
        );
    }
}

#[test]
fn range_errors_precede_indexing_and_every_empty_kind_is_rejected() {
    let source = b"ex:Pump".to_vec();
    for (start, end) in [(2, 1), (0, source.len() + 1), (usize::MAX, usize::MAX)] {
        assert_eq!(
            error(read_span(NameKind::AbbreviatedIri, &source, start, end, 0)),
            ("span", start)
        );
    }
    for kind in [
        NameKind::FullIri,
        NameKind::PrefixName,
        NameKind::AbbreviatedIri,
        NameKind::NodeId,
        NameKind::LanguageTag,
    ] {
        assert_eq!(
            error(read_span(kind, &source, 2, 2, usize::MAX)),
            ("token", 2)
        );
    }
}

#[test]
fn malformed_or_split_utf8_is_rejected_at_the_original_token_span() {
    let source = "# Geräte\néx:部品".as_bytes().to_vec();
    let start = "# Geräte\n".len();
    assert_eq!(
        error(read_span(
            NameKind::AbbreviatedIri,
            &source,
            start + 1,
            source.len(),
            100
        )),
        ("token", start + 1)
    );
    assert_eq!(
        error(read_span(
            NameKind::AbbreviatedIri,
            &source,
            start,
            source.len() - 1,
            100
        )),
        ("token", start)
    );
    let source = [b'x', b'x', b'e', b'x', b':', 0xc0, 0xaf].to_vec();
    assert_eq!(
        error(read_span(
            NameKind::AbbreviatedIri,
            &source,
            2,
            source.len(),
            100
        )),
        ("token", 2)
    );
}

#[test]
fn bytes_outside_the_selected_span_are_a_separate_lexer_obligation() {
    let source = [0xff, b'e', b'x', b':', b'P', 0xff].to_vec();
    assert_eq!(value(NameKind::AbbreviatedIri, &source, 1, 5, 4), b"ex:P");
    assert_eq!(
        error(read_span(NameKind::AbbreviatedIri, &source, 1, 6, 100)),
        ("token", 1)
    );
}
