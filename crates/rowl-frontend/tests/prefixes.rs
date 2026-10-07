use rowl_frontend::names::validate_local;
use rowl_frontend::prefixes::{self, Check, Declaration, Expansion, PrefixTable, Standard};
use rowl_frontend::regular::MatchResult;

fn declaration(name: &str, namespace: &str) -> Declaration {
    Declaration {
        name: name.as_bytes().to_vec(),
        namespace: namespace.as_bytes().to_vec(),
    }
}
fn checked(rows: &Vec<Declaration>) -> PrefixTable<'_> {
    match prefixes::check(rows) {
        Check::Ready(table) => table,
        _ => panic!("fixture must form a valid table"),
    }
}
fn expand(table: &PrefixTable<'_>, prefix: &str, local: &str, limit: usize) -> Expansion {
    prefixes::expand_parts(
        table,
        &prefix.as_bytes().to_vec(),
        &local.as_bytes().to_vec(),
        limit,
    )
}
fn expanded(result: Expansion) -> Vec<u8> {
    match result {
        Expansion::Expanded(value) => value,
        _ => panic!("expected exact expansion"),
    }
}

#[test]
fn implicit_standards_have_exact_names_and_namespaces() {
    let rows = Vec::new();
    let table = checked(&rows);
    for (name, key, ns) in [
        (
            "rdf:",
            Standard::Rdf,
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
        ),
        (
            "rdfs:",
            Standard::Rdfs,
            "http://www.w3.org/2000/01/rdf-schema#",
        ),
        ("xsd:", Standard::Xsd, "http://www.w3.org/2001/XMLSchema#"),
        ("owl:", Standard::Owl, "http://www.w3.org/2002/07/owl#"),
    ] {
        assert_eq!(prefixes::namespace(key), ns.as_bytes());
        assert!(prefixes::standard(&name.as_bytes().to_vec()).is_some());
        assert_eq!(
            prefixes::lookup(&table, &name.as_bytes().to_vec()).as_deref(),
            Some(ns.as_bytes())
        );
        assert_eq!(
            expanded(expand(&table, name, "Thing", usize::MAX)),
            format!("{ns}Thing").as_bytes()
        );
        // OWL 2 forbids declaring the name; with exactly its own namespace the
        // declaration changes nothing and is accepted, as OWL API tools write it.
        let restated = vec![declaration(name, ns)];
        let restated_table = checked(&restated);
        assert_eq!(
            prefixes::lookup(&restated_table, &name.as_bytes().to_vec()).as_deref(),
            Some(ns.as_bytes())
        );
        let twice = vec![declaration(name, ns), declaration(name, ns)];
        assert!(matches!(prefixes::check(&twice), Check::Duplicate { .. }));
        let reserved = vec![declaration(name, "urn:other:")];
        assert!(
            matches!(prefixes::check(&reserved), Check::ReservedName(row) if std::ptr::eq(row, &reserved[0]))
        );
    }
    assert!(prefixes::lookup(&table, &b"OWL:".to_vec()).is_none());
    assert!(prefixes::lookup(&table, &b"absent:".to_vec()).is_none());
}

#[test]
fn default_unicode_and_case_distinct_prefixes_preserve_bytes() {
    let rows = vec![
        declaration(":", "https://example.org/maintenance#"),
        declaration("OWL:", "HTTP://Example.org/%61#"),
        declaration("é:", "urn:é:"),
        declaration("e\u{301}:", "urn:decomposed:"),
    ];
    let table = checked(&rows);
    assert!(std::ptr::eq(prefixes::declarations(&table), &rows));
    assert_eq!(
        expanded(expand(&table, ":", "Pump", usize::MAX)),
        b"https://example.org/maintenance#Pump"
    );
    assert_eq!(
        expanded(expand(&table, "OWL:", "A..B", usize::MAX)),
        b"HTTP://Example.org/%61#A..B"
    );
    assert_eq!(
        expanded(expand(&table, "é:", "机", usize::MAX)),
        "urn:é:机".as_bytes()
    );
    assert_eq!(
        expanded(expand(&table, "e\u{301}:", "机", usize::MAX)),
        "urn:decomposed:机".as_bytes()
    );
}

#[test]
fn duplicate_names_are_rejected_even_with_identical_namespaces() {
    for ns in ["urn:first:", "urn:second:"] {
        let rows = vec![
            declaration("ex:", "urn:first:"),
            declaration("other:", "urn:other:"),
            declaration("ex:", ns),
            declaration("ex:", "urn:third:"),
        ];
        assert!(
            matches!(prefixes::check(&rows), Check::Duplicate { first, second } if std::ptr::eq(first, &rows[0]) && std::ptr::eq(second, &rows[2]))
        );
    }
}

#[test]
fn every_declaration_is_checked_with_exact_first_phase_and_source_priority() {
    let mut rows = vec![
        declaration("ex:", "urn:ok:"),
        declaration("_:", "relative"),
        declaration("owl:", "relative"),
    ];
    assert!(
        matches!(prefixes::check(&rows), Check::InvalidName(row) if std::ptr::eq(row, &rows[1]))
    );
    rows[1] = declaration("owl:", "relative");
    assert!(
        matches!(prefixes::check(&rows), Check::ReservedName(row) if std::ptr::eq(row, &rows[1]))
    );
    rows[1] = declaration("ex:", "relative");
    assert!(
        matches!(prefixes::check(&rows), Check::InvalidNamespace(row) if std::ptr::eq(row, &rows[1]))
    );
    rows[1] = declaration("ex:", "urn:ok:");
    assert!(
        matches!(prefixes::check(&rows), Check::Duplicate { first, second } if std::ptr::eq(first, &rows[0]) && std::ptr::eq(second, &rows[1]))
    );
    rows[1] = declaration("unused:", "urn:unused:");
    assert!(
        matches!(prefixes::check(&rows), Check::ReservedName(row) if std::ptr::eq(row, &rows[2]))
    );
}

#[test]
fn caller_supplied_parts_cannot_bypass_grammar_or_failure_priority() {
    let rows = vec![declaration("ex:", "urn:example:")];
    let table = checked(&rows);
    assert!(matches!(
        expand(&table, "_:", "bad:local", 0),
        Expansion::InvalidPrefix
    ));
    assert!(matches!(
        expand(&table, "ex:", "a:b", 0),
        Expansion::InvalidLocal
    ));
    assert!(matches!(
        expand(&table, "missing:", "A", 0),
        Expansion::UndeclaredPrefix
    ));
    assert!(matches!(
        expand(&table, "missing:", "", 0),
        Expansion::InvalidLocal
    ));
    assert!(matches!(
        prefixes::expand_parts(&table, &vec![0xff], &b"A".to_vec(), 0),
        Expansion::InvalidPrefix
    ));
    assert!(matches!(
        prefixes::expand_parts(&table, &b"ex:".to_vec(), &vec![0xff], 0),
        Expansion::InvalidLocal
    ));
}

#[test]
fn output_limit_counts_utf8_bytes_with_exact_boundary_and_no_sum_overflow() {
    let rows = vec![declaration("ex:", "urn:é:")];
    let table = checked(&rows);
    let expected = "urn:é:机".as_bytes();
    for limit in [0, 1, expected.len() - 1] {
        assert!(matches!(
            expand(&table, "ex:", "机", limit),
            Expansion::ResourceLimit
        ));
    }
    for limit in [expected.len(), expected.len() + 1, usize::MAX] {
        assert_eq!(expanded(expand(&table, "ex:", "机", limit)), expected);
    }
}

#[test]
fn valid_namespace_and_local_still_require_final_absolute_iri_validation() {
    let rows = vec![
        declaration("authority:", "x://[::1]"),
        declaration("ex:", "urn:example:"),
    ];
    let table = checked(&rows);
    assert!(matches!(
        expand(&table, "authority:", "A", usize::MAX),
        Expansion::InvalidExpandedIri
    ));
    // PN_CHARS_BASE includes plane-ending code points which IRI ucschar excludes.
    let local = "\u{1ffff}";
    assert!(matches!(
        validate_local(&local.as_bytes().to_vec()),
        MatchResult::Matched(true)
    ));
    assert!(matches!(
        expand(&table, "ex:", local, usize::MAX),
        Expansion::InvalidExpandedIri
    ));
    assert!(matches!(
        expand(&table, "ex:", local, 0),
        Expansion::ResourceLimit
    ));
}

#[test]
fn malformed_namespace_is_rejected_at_the_original_declaration() {
    let mut rows = vec![declaration("ex:", "urn:example:")];
    rows[0].namespace.push(0xff);
    assert!(
        matches!(prefixes::check(&rows), Check::InvalidNamespace(row) if std::ptr::eq(row, &rows[0]))
    );
}
