use rowl_frontend::functional_iris::{
    resolve_span, split_abbreviated, SourceIriError, SourceIriKind,
};
use rowl_frontend::functional_names::NameError;
use rowl_frontend::prefixes::{check, Check, Declaration, PrefixTable};

fn declaration(name: &str, namespace: &str) -> Declaration {
    Declaration {
        name: name.as_bytes().to_vec(),
        namespace: namespace.as_bytes().to_vec(),
    }
}
fn checked(rows: &Vec<Declaration>) -> PrefixTable<'_> {
    match check(rows) {
        Check::Ready(table) => table,
        _ => panic!("fixture must form a complete valid prefix table"),
    }
}
fn value(table: &PrefixTable<'_>, kind: SourceIriKind, source: &str, limit: usize) -> Vec<u8> {
    resolve_span(
        table,
        kind,
        &source.as_bytes().to_vec(),
        0,
        source.len(),
        limit,
    )
    .unwrap_or_else(|_| panic!("fixture must resolve to its complete absolute IRI"))
}
fn error(result: Result<Vec<u8>, SourceIriError>) -> (&'static str, usize) {
    match result {
        Err(SourceIriError::Name(NameError::InvalidSpan { offset })) => ("span", offset),
        Err(SourceIriError::Name(NameError::InvalidToken { offset })) => ("token", offset),
        Err(SourceIriError::Name(NameError::ResourceLimit { offset })) => ("name-limit", offset),
        Err(SourceIriError::UndeclaredPrefix { offset }) => ("undeclared", offset),
        Err(SourceIriError::ResourceLimit { offset }) => ("limit", offset),
        Err(SourceIriError::InvalidExpandedIri { offset }) => ("expanded-iri", offset),
        Err(SourceIriError::InvalidParts { .. }) => panic!("proved unreachable internal fallback"),
        Ok(_) => panic!("expected a complete phase/source-offset diagnosis"),
    }
}

#[test]
fn all_implicit_standard_prefixes_resolve_directly_from_source_bytes() {
    let rows = Vec::new();
    let table = checked(&rows);
    for (token, expected) in [
        (
            "rdf:type",
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
        ),
        ("rdfs:label", "http://www.w3.org/2000/01/rdf-schema#label"),
        ("xsd:integer", "http://www.w3.org/2001/XMLSchema#integer"),
        ("owl:Thing", "http://www.w3.org/2002/07/owl#Thing"),
    ] {
        assert_eq!(
            value(&table, SourceIriKind::Abbreviated, token, expected.len()),
            expected.as_bytes()
        );
    }
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &b"OWL:Thing".to_vec(),
            0,
            9,
            0
        )),
        ("undeclared", 0)
    );
}

#[test]
fn unicode_default_and_case_distinct_names_preserve_exact_spelling() {
    let rows = vec![
        declaration(":", "https://example.org/maintenance#"),
        declaration("é:", "HTTP://Example.org/%61#"),
        declaration("e\u{301}:", "urn:decomposed:"),
        declaration("OWL:", "urn:custom:"),
    ];
    let table = checked(&rows);
    for (token, expected) in [
        (":Pump", "https://example.org/maintenance#Pump"),
        ("é:部品.端", "HTTP://Example.org/%61#部品.端"),
        ("e\u{301}:机", "urn:decomposed:机"),
        ("OWL:Thing", "urn:custom:Thing"),
        ("owl:Thing", "http://www.w3.org/2002/07/owl#Thing"),
    ] {
        assert_eq!(
            value(&table, SourceIriKind::Abbreviated, token, expected.len()),
            expected.as_bytes()
        );
    }
}

#[test]
fn separator_is_derived_from_original_nonzero_unicode_source_spans() {
    let text = "# Geräte\néx:部品.端 suffix";
    let source = text.as_bytes().to_vec();
    let token = "éx:部品.端";
    let start = text.find(token).expect("fixture token");
    let end = start + token.len();
    let parts = split_abbreviated(&source, start, end)
        .unwrap_or_else(|_| panic!("source partition must be valid"));
    assert_eq!(parts.prefix, "éx:".as_bytes());
    assert_eq!(parts.local, "部品.端".as_bytes());
    let rows = vec![declaration("éx:", "urn:part:")];
    let table = checked(&rows);
    let expected = "urn:part:部品.端";
    assert_eq!(
        resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &source,
            start,
            end,
            expected.len()
        )
        .unwrap_or_else(|_| panic!("bounded exact IRI")),
        expected.as_bytes()
    );
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &source,
            start,
            end,
            expected.len() - 1
        )),
        ("limit", start)
    );
}

#[test]
fn budgets_count_final_iri_bytes_even_when_the_source_prefix_is_longer() {
    let rows = vec![declaration("VeryLongSourcePrefix:", "x:")];
    let table = checked(&rows);
    let source = "VeryLongSourcePrefix:A";
    assert!(source.len() > 3);
    assert_eq!(value(&table, SourceIriKind::Abbreviated, source, 3), b"x:A");
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &source.as_bytes().to_vec(),
            0,
            source.len(),
            2
        )),
        ("limit", 0)
    );
}

#[test]
fn invalid_source_precedes_lookup_and_lookup_precedes_output_budget() {
    let rows = Vec::new();
    let table = checked(&rows);
    for text in [
        "",
        "missing:",
        "0ex:Pump",
        "ex:Pump:Part",
        "ex:Pump.",
        "_:Pump",
        "<urn:Pump>",
    ] {
        assert_eq!(
            error(resolve_span(
                &table,
                SourceIriKind::Abbreviated,
                &text.as_bytes().to_vec(),
                0,
                text.len(),
                0
            )),
            ("token", 0)
        );
    }
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &b"missing:Pump".to_vec(),
            0,
            12,
            0
        )),
        ("undeclared", 0)
    );
    let malformed = vec![b'e', b'x', b':', 0xff];
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &malformed,
            0,
            malformed.len(),
            usize::MAX
        )),
        ("token", 0)
    );
}

#[test]
fn expanded_iri_is_revalidated_after_source_grammar_and_budget_checks() {
    let rows = vec![declaration("ex:", "urn:part:")];
    let table = checked(&rows);
    // SPARQL 2008 PN_CHARS_BASE includes this scalar, while RFC 3987 ucschar
    // excludes the final noncharacters in each supplementary plane.
    let source = "ex:\u{1ffff}";
    assert!(split_abbreviated(&source.as_bytes().to_vec(), 0, source.len()).is_ok());
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &source.as_bytes().to_vec(),
            0,
            source.len(),
            usize::MAX
        )),
        ("expanded-iri", 0)
    );
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Abbreviated,
            &source.as_bytes().to_vec(),
            0,
            source.len(),
            0
        )),
        ("limit", 0)
    );
}

#[test]
fn full_iri_values_strip_only_angle_markers_and_keep_payload_start_errors() {
    let rows = Vec::new();
    let table = checked(&rows);
    let token = "<HTTP://Example.org/%2f#部品>";
    let expected = "HTTP://Example.org/%2f#部品";
    let text = format!("# Unicode Geräte\n{token}");
    let source = text.as_bytes().to_vec();
    let start = text.find(token).expect("fixture token");
    assert_eq!(
        resolve_span(
            &table,
            SourceIriKind::Full,
            &source,
            start,
            source.len(),
            expected.len()
        )
        .unwrap_or_else(|_| panic!("full IRI")),
        expected.as_bytes()
    );
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Full,
            &source,
            start,
            source.len(),
            expected.len() - 1
        )),
        ("name-limit", start + 1)
    );
    assert_eq!(
        error(resolve_span(
            &table,
            SourceIriKind::Full,
            &b"<relative>".to_vec(),
            0,
            10,
            usize::MAX
        )),
        ("token", 0)
    );
}

#[test]
fn invalid_ranges_are_rejected_before_subtraction_copying_or_indexing() {
    let rows = Vec::new();
    let table = checked(&rows);
    let source = b"owl:Thing".to_vec();
    for (start, end) in [
        (2, 1),
        (0, source.len() + 1),
        (usize::MAX, usize::MAX),
        (usize::MAX, 0),
    ] {
        for kind in [SourceIriKind::Full, SourceIriKind::Abbreviated] {
            assert_eq!(
                error(resolve_span(&table, kind, &source, start, end, 0)),
                ("span", start)
            );
        }
        assert!(
            matches!(split_abbreviated(&source, start, end), Err(SourceIriError::Name(NameError::InvalidSpan{offset})) if offset == start)
        );
    }
}
