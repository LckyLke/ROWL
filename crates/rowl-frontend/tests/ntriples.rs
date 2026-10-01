use rowl_frontend::encoding::{encode, Encoded};
use rowl_frontend::langtag::well_formed;
use rowl_frontend::ntriples::*;
use rowl_frontend::rdf::*;
use std::collections::BTreeMap;

type BlankKey = (Vec<u8>, Vec<u8>);
fn key(b: &BlankNode) -> BlankKey {
    (b.scope.clone(), b.label.clone())
}
fn node(
    a: &BlankNode,
    b: &BlankNode,
    forward: &mut BTreeMap<BlankKey, BlankKey>,
    reverse: &mut BTreeMap<BlankKey, BlankKey>,
) {
    let left = key(a);
    let right = key(b);
    if let Some(known) = forward.insert(left.clone(), right.clone()) {
        assert_eq!(known, right);
    }
    if let Some(known) = reverse.insert(right, left.clone()) {
        assert_eq!(known, left);
    }
}
// Independent bijection check: every term position is preserved, and neither
// repeated nodes nor distinct nodes can change their identity relationships.
fn same_graph(a: &RawGraph, b: &RawGraph) {
    assert_eq!(a.triples.len(), b.triples.len());
    let mut forward = BTreeMap::new();
    let mut reverse = BTreeMap::new();
    for (a, b) in a.triples.iter().zip(&b.triples) {
        assert_eq!(a.predicate.spelling, b.predicate.spelling);
        match (&a.subject, &b.subject) {
            (Subject::Iri(a), Subject::Iri(b)) => assert_eq!(a.spelling, b.spelling),
            (Subject::Blank(a), Subject::Blank(b)) => node(a, b, &mut forward, &mut reverse),
            _ => panic!("subject kind changed"),
        }
        match (&a.object, &b.object) {
            (Object::Iri(a), Object::Iri(b)) => assert_eq!(a.spelling, b.spelling),
            (Object::Blank(a), Object::Blank(b)) => node(a, b, &mut forward, &mut reverse),
            (Object::Literal(a), Object::Literal(b)) => {
                assert_eq!(a.lexical, b.lexical);
                match (&a.kind, &b.kind) {
                    (LiteralKind::Datatype(a), LiteralKind::Datatype(b)) => {
                        assert_eq!(a.spelling, b.spelling)
                    }
                    (LiteralKind::Language(a), LiteralKind::Language(b)) => assert_eq!(a, b),
                    _ => panic!("literal kind changed"),
                }
            }
            _ => panic!("object kind changed"),
        }
    }
}
fn graph(bytes: &[u8], scope: &[u8]) -> RawGraph {
    match read(&bytes.to_vec(), &scope.to_vec()) {
        ReadResult::Graph(g) => g,
        ReadResult::Error(e) => panic!("input rejected at {}", e.offset),
    }
}
fn bytes(g: &RawGraph) -> Vec<u8> {
    match write(g, 1_000_000) {
        WriteResult::Bytes(b) => b,
        _ => panic!("valid graph rejected"),
    }
}
fn iri(value: &str) -> RdfIri {
    RdfIri {
        spelling: value.as_bytes().to_vec(),
    }
}

#[test]
fn utf8_encoder_matches_rust_for_every_scalar_and_rejects_non_scalars() {
    for cp in 0..=0x110000 {
        let expected = char::from_u32(cp);
        match (encode(cp), expected) {
            (None, None) => {}
            (Some(encoded), Some(ch)) => {
                let value = match encoded {
                    Encoded::One(a) => vec![a],
                    Encoded::Two(a, b) => vec![a, b],
                    Encoded::Three(a, b, c) => vec![a, b, c],
                    Encoded::Four(a, b, c, d) => vec![a, b, c, d],
                };
                assert_eq!(value, ch.encode_utf8(&mut [0; 4]).as_bytes(), "U+{cp:X}");
            }
            _ => panic!("scalar classification differs at U+{cp:X}"),
        }
    }
    for cp in [u32::MAX, 0x12345678, 0x7fffffff] {
        assert!(encode(cp).is_none());
    }
}

#[test]
fn language_tags_follow_well_formed_abnf_rather_than_registry_validity() {
    for tag in [
        "en",
        "de-DE",
        "zh-Hant-CN",
        "zh-cmn-Hans-CN",
        "en-abc-def-ghi",
        "abcd-Latn",
        "abcdefgh",
        "sl-rozaj-biske-1994",
        "EN-gb-OED",
        "I-KLINGON",
        "x-a-B-12345678",
        "en-a-foo-b-bar-x-a",
        "en-rozaj-ROZAJ",
        "en-a-foo-A-bar",
        "zzzzzzzz-ZZ",
    ] {
        assert!(well_formed(&tag.as_bytes().to_vec()), "well-formed: {tag}");
    }
    for tag in [
        "",
        "e",
        "x",
        "en-",
        "-en",
        "en--US",
        "abcdefghi",
        "en-abcdefghi",
        "en-a",
        "en-x",
        "en-1234-abcd",
        "en-abc-def-ghi-jkl",
        "en-ß",
        "en_US",
        "12-US",
        "en-us-latn",
        "i-unknown",
    ] {
        assert!(!well_formed(&tag.as_bytes().to_vec()), "malformed: {tag}");
    }
    assert!(!well_formed(&vec![255]));
}

#[test]
fn whitespace_comments_blank_labels_and_repeated_facts_are_preserved() {
    let input = b"# heading\r\n\n<urn:s><urn:p>_:9.a.\r_:9.a<urn:p>\"Alice\". # tail\n_:9.a<urn:p>\"Alice\".\n";
    let g = graph(input, b"document-1");
    assert_eq!(g.triples.len(), 3);
    let Object::Blank(b) = &g.triples[0].object else {
        panic!("blank missing")
    };
    assert_eq!(b.label, b"9.a");
    assert_eq!(b.scope, b"document-1");
    let Subject::Blank(s) = &g.triples[1].subject else {
        panic!("blank missing")
    };
    assert_eq!(key(b), key(s));
    same_graph(&g, &graph(&bytes(&g), b"export"));
    for input in [b"".as_slice(), b" #no newline", b" \t\r\n# comment\n\n"] {
        assert!(graph(input, b"empty").triples.is_empty());
    }
}

#[test]
fn trivia_preserves_token_hashes_and_does_not_join_triple_lines() {
    let valid = "\t# leading 🚀\r\n<urn:s#frag><urn:p>\"inside # text\".\t# trailing é\r\n\n# EOF";
    let g = graph(valid.as_bytes(), b"comments");
    assert_eq!(g.triples.len(), 1);
    let Subject::Iri(s) = &g.triples[0].subject else {
        panic!("missing subject")
    };
    assert_eq!(s.spelling, b"urn:s#frag");
    let Object::Literal(l) = &g.triples[0].object else {
        panic!("missing literal")
    };
    assert_eq!(l.lexical, b"inside # text");
    for invalid in [
        b"<urn:s>\n<urn:p><urn:o>.".as_slice(),
        b"<urn:s># body\n<urn:p><urn:o>.",
        b"<urn:s><urn:p>\r\n<urn:o>.",
        b"<urn:s><urn:p><urn:o>\n.",
    ] {
        assert!(matches!(
            read(&invalid.to_vec(), &vec![]),
            ReadResult::Error(_)
        ));
    }
    let mut malformed = "# good é".as_bytes().to_vec();
    let bad_offset = malformed.len();
    malformed.extend_from_slice(&[0xc0, 0x80, b'\n']);
    let ReadResult::Error(e) = read(&malformed, &vec![]) else {
        panic!("malformed comment accepted")
    };
    assert_eq!(e.offset, bad_offset);
    assert!(matches!(e.kind, ErrorKind::MalformedUtf8));
}

#[test]
fn blank_labels_cover_normative_unicode_boundaries_and_internal_dots() {
    let intervals = [
        (0x41, 0x5a),
        (0x61, 0x7a),
        (0xc0, 0xd6),
        (0xd8, 0xf6),
        (0xf8, 0x2ff),
        (0x370, 0x37d),
        (0x37f, 0x1fff),
        (0x200c, 0x200d),
        (0x2070, 0x218f),
        (0x2c00, 0x2fef),
        (0x3001, 0xd7ff),
        (0xf900, 0xfdcf),
        (0xfdf0, 0xfffd),
        (0x10000, 0xeffff),
    ];
    for cp in intervals
        .into_iter()
        .flat_map(|(low, high)| [low, high])
        .chain([0x30, 0x39, 0x5f, 0x3a])
    {
        let ch = char::from_u32(cp).unwrap();
        let label = format!("{ch}..a");
        let input = format!("_:{label}<urn:p>_:{label}.");
        let g = graph(input.as_bytes(), b"scope\0\xff");
        let Subject::Blank(s) = &g.triples[0].subject else {
            panic!("missing blank subject")
        };
        let Object::Blank(o) = &g.triples[0].object else {
            panic!("missing blank object")
        };
        assert_eq!(s.label, label.as_bytes(), "U+{cp:X}");
        assert_eq!(key(s), key(o));
        assert_eq!(s.scope, b"scope\0\xff");
    }
    for cp in [
        0x40, 0x5b, 0x60, 0x7b, 0xbf, 0xd7, 0xf7, 0x300, 0x36f, 0x37e, 0x2000, 0x200e, 0x2190,
        0x2ff0, 0x3000, 0xf8ff, 0xfdd0, 0xfffe, 0xf0000,
    ] {
        let ch = char::from_u32(cp).unwrap();
        let input = format!("_:{ch}<urn:p><urn:o>.");
        let ReadResult::Error(e) = read(&input.into_bytes(), &vec![]) else {
            panic!("invalid first blank character U+{cp:X} accepted")
        };
        assert_eq!(e.offset, 2);
        assert!(matches!(e.kind, ErrorKind::InvalidBlankLabel));
    }
    let g = graph(b"_:a....b<urn:p>_:a....b.", b"dot");
    let Subject::Blank(s) = &g.triples[0].subject else {
        panic!("missing blank")
    };
    assert_eq!(s.label, b"a....b");
    assert!(matches!(
        read(&b"_:a<urn:p>_:a..".to_vec(), &vec![]),
        ReadResult::Error(_)
    ));
}

#[test]
fn escapes_exact_iris_language_case_and_ill_typed_lexical_values_survive_export() {
    let input = br#"<urn:\u00E9><urn:p>"A\t\b\n\r\f\"\'\\\u0000\U0001F680"@de-DE .
<urn:%61><urn:p>"not-an-integer"^^<http://www.w3.org/2001/XMLSchema#integer> .
<urn:a><urn:p>"01"^^<http://www.w3.org/2001/XMLSchema#integer> .
<urn:empty><urn:p>"" .
"#;
    let g = graph(input, b"source");
    let Subject::Iri(s) = &g.triples[0].subject else {
        panic!("iri missing")
    };
    assert_eq!(s.spelling, "urn:é".as_bytes());
    let Object::Literal(l) = &g.triples[0].object else {
        panic!("literal missing")
    };
    assert_eq!(l.lexical, "A\t\u{8}\n\r\u{c}\"'\\\0🚀".as_bytes());
    let LiteralKind::Language(tag) = &l.kind else {
        panic!("tag missing")
    };
    assert_eq!(tag, b"de-DE");
    let out = bytes(&g);
    same_graph(&g, &graph(&out, b"reload"));
    assert!(out.windows(8).any(|w| w == b"@de-DE ."));
    assert!(out.windows(7).any(|w| w == b"urn:%61"));
}

#[test]
fn unicode_escapes_preserve_exact_values_and_source_diagnostics() {
    for (escaped, cp) in [
        ("\\u0000", 0),
        ("\\u007F", 0x7f),
        ("\\u0080", 0x80),
        ("\\u07fF", 0x7ff),
        ("\\u0800", 0x800),
        ("\\uD7fF", 0xd7ff),
        ("\\uE000", 0xe000),
        ("\\uFFFF", 0xffff),
        ("\\U00010000", 0x10000),
        ("\\U0010FFFF", 0x10ffff),
    ] {
        let input = format!("<urn:s><urn:p>\"{escaped}\".");
        let g = graph(input.as_bytes(), b"values");
        let Object::Literal(literal) = &g.triples[0].object else {
            panic!("literal missing")
        };
        let expected = char::from_u32(cp).unwrap().to_string();
        assert_eq!(literal.lexical, expected.as_bytes());
    }
    let g = graph(br#"<urn:s><urn:p>"\u0061f\U00000061f"."#, b"count");
    let Object::Literal(literal) = &g.triples[0].object else {
        panic!("literal missing")
    };
    assert_eq!(literal.lexical, b"afaf"); // exactly four/eight digits, not a greedy hex run
    let prefix = b"<urn:s><urn:p>\"";
    for escaped in [
        "\\uD800",
        "\\uDBFF",
        "\\uDC00",
        "\\uDFFF",
        "\\U00110000",
        "\\UFFFFFFFF",
        "\\u00g0",
        "\\U0000000z",
        "\\q",
    ] {
        let input = format!("<urn:s><urn:p>\"{escaped}\".");
        let ReadResult::Error(e) = read(&input.into_bytes(), &vec![]) else {
            panic!("invalid escape accepted")
        };
        assert!(matches!(e.kind, ErrorKind::InvalidEscape));
        assert_eq!(e.offset, prefix.len());
    }
    for truncated in [b"\\".as_slice(), b"\\u0", b"\\U000000"] {
        let mut input = prefix.to_vec();
        input.extend_from_slice(truncated);
        let ReadResult::Error(e) = read(&input, &vec![]) else {
            panic!("truncated escape accepted")
        };
        assert!(matches!(e.kind, ErrorKind::UnexpectedEnd));
        assert_eq!(e.offset, input.len());
    }
    let mut malformed = prefix.to_vec();
    malformed.extend_from_slice(b"\\u00");
    let offset = malformed.len();
    malformed.extend_from_slice(&[0xff, b'"', b'.']);
    let ReadResult::Error(e) = read(&malformed, &vec![]) else {
        panic!("malformed escape unit accepted")
    };
    assert!(matches!(e.kind, ErrorKind::MalformedUtf8));
    assert_eq!(e.offset, offset);
    for input in [
        br#"<urn:\n><urn:p><urn:o>."#.as_slice(),
        br#"<urn:\t><urn:p><urn:o>."#,
    ] {
        let ReadResult::Error(e) = read(&input.to_vec(), &vec![]) else {
            panic!("ECHAR in IRI accepted")
        };
        assert!(matches!(e.kind, ErrorKind::InvalidEscape));
        assert_eq!(e.offset, 5);
    }
}

#[test]
fn multibyte_quoted_output_budgets_keep_original_input_offsets() {
    for payload in ["🚀🚀🚀", "\\U0001F680\\U0001F680\\U0001F680"] {
        let input = format!("<urn:s><urn:p>\"{payload}\".").into_bytes();
        let prefix = b"<urn:s><urn:p>\"".len();
        let input_unit = if payload.starts_with('\\') { 10 } else { 4 };
        for max_term_bytes in 5..12 {
            let result = read_with_limits(
                &input,
                &vec![],
                &Limits {
                    max_term_bytes,
                    max_triples: 1,
                },
            );
            let ReadResult::Error(e) = result else {
                panic!("oversized output term accepted")
            };
            assert!(matches!(e.kind, ErrorKind::ResourceLimit));
            assert_eq!(e.offset, prefix + (max_term_bytes / 4) * input_unit);
        }
        let ReadResult::Graph(g) = read_with_limits(
            &input,
            &vec![],
            &Limits {
                max_term_bytes: 12,
                max_triples: 1,
            },
        ) else {
            panic!("exact output budget rejected")
        };
        let Object::Literal(literal) = &g.triples[0].object else {
            panic!("literal missing")
        };
        assert_eq!(literal.lexical, "🚀🚀🚀".as_bytes());
    }
}

#[test]
fn language_token_limits_case_and_stage_offsets_are_exact() {
    let prefix = b"<urn:s><urn:p>\"x\"";
    for suffix in [b"@".as_slice(), b"@9.", b"@en-", b"@en--US.", b"@en-a."] {
        let input = [prefix.as_slice(), suffix].concat();
        let ReadResult::Error(error) = read(&input, &vec![]) else {
            panic!("invalid language token accepted")
        };
        assert!(matches!(error.kind, ErrorKind::InvalidLanguageTag));
        assert_eq!(error.offset, prefix.len());
    }
    for (suffix, offset) in [(b"@en\x80.".as_slice(), 3), (b"@en-\xff.".as_slice(), 4)] {
        let input = [prefix.as_slice(), suffix].concat();
        let ReadResult::Error(error) = read(&input, &vec![]) else {
            panic!("malformed UTF-8 in tag accepted")
        };
        assert!(matches!(error.kind, ErrorKind::MalformedUtf8));
        assert_eq!(error.offset, prefix.len() + offset);
    }
    let input = [prefix.as_slice(), b"@EN-Latn-US."].concat();
    for max_term_bytes in [9, 10] {
        match read_with_limits(
            &input,
            &vec![],
            &Limits {
                max_term_bytes,
                max_triples: 1,
            },
        ) {
            ReadResult::Error(error) => {
                assert_eq!(max_term_bytes, 9);
                assert!(matches!(error.kind, ErrorKind::ResourceLimit));
                assert_eq!(error.offset, prefix.len() + 1);
            }
            ReadResult::Graph(graph) => {
                assert_eq!(max_term_bytes, 10);
                let Object::Literal(value) = &graph.triples[0].object else {
                    panic!("literal missing")
                };
                let LiteralKind::Language(tag) = &value.kind else {
                    panic!("language tag missing")
                };
                assert_eq!(tag, b"EN-Latn-US");
            }
        }
    }
    // The exact copy budget precedes the RFC grammar check in the error contract.
    let invalid = [prefix.as_slice(), b"@abcdefghij."].concat();
    for max_term_bytes in [9, 10] {
        let ReadResult::Error(error) = read_with_limits(
            &invalid,
            &vec![],
            &Limits {
                max_term_bytes,
                max_triples: 1,
            },
        ) else {
            panic!("invalid tag accepted")
        };
        if max_term_bytes == 9 {
            assert!(matches!(error.kind, ErrorKind::ResourceLimit));
            assert_eq!(error.offset, prefix.len() + 1);
        } else {
            assert!(matches!(error.kind, ErrorKind::InvalidLanguageTag));
            assert_eq!(error.offset, prefix.len());
        }
    }
}

#[test]
fn malformed_sources_return_errors_with_offsets_without_partial_success() {
    for input in [
        b"<relative><urn:p><urn:o>.".as_slice(),
        b"<urn:s><urn:p>_:.",
        b"<urn:s><urn:p>\"a\n\".",
        b"<urn:s><urn:p>\"\\uD800\".",
        b"<urn:s><urn:p>\"\\U00110000\".",
        b"<urn:s><urn:p>\"\\q\".",
        b"<urn:s><urn:p>\"a\"@e.",
        b"<urn:s><urn:p>\"a\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#langString>.",
        b"<urn:s><urn:p><urn:o>",
        b"<urn:s><urn:p><urn:o>. <urn:s><urn:p><urn:o>.",
    ] {
        assert!(
            matches!(read(&input.to_vec(), &vec![]), ReadResult::Error(_)),
            "accepted {}",
            String::from_utf8_lossy(input)
        );
    }
    let ReadResult::Error(e) = read(&vec![35, 255], &vec![]) else {
        panic!("bad comment UTF-8 accepted")
    };
    assert_eq!(e.offset, 1);
    assert!(matches!(e.kind, ErrorKind::MalformedUtf8));
    let ReadResult::Error(e) = read(&b"<urn:s><urn:p>\"\\u123".to_vec(), &vec![]) else {
        panic!("truncated escape accepted")
    };
    assert_eq!(e.offset, 20);
    assert!(matches!(e.kind, ErrorKind::UnexpectedEnd));
}

#[test]
fn distinct_document_scopes_and_arbitrary_raw_blank_keys_do_not_alias() {
    let g = RawGraph {
        triples: [vec![], vec![0, 255], b"scope".to_vec()]
            .into_iter()
            .map(|scope| Triple {
                subject: Subject::Blank(BlankNode {
                    scope: scope.clone(),
                    label: vec![255, 0],
                }),
                predicate: iri("urn:p"),
                object: Object::Blank(BlankNode {
                    scope,
                    label: vec![255, 0],
                }),
            })
            .collect(),
    };
    let output = bytes(&g);
    same_graph(&g, &graph(&output, b"new-scope"));
    assert!(output.is_ascii());
    let a = graph(b"_:b<urn:p>_:b.", b"a");
    let b = graph(b"_:b<urn:p>_:b.", b"b");
    let Subject::Blank(a) = &a.triples[0].subject else {
        panic!("missing")
    };
    let Subject::Blank(b) = &b.triples[0].subject else {
        panic!("missing")
    };
    assert_ne!(key(a), key(b));
}

#[test]
fn count_limits_and_exact_export_budgets_have_typed_outcomes() {
    let source = b"<urn:s><urn:p>\"a\".".to_vec();
    for limits in [
        Limits {
            max_term_bytes: 4,
            max_triples: 1,
        },
        Limits {
            max_term_bytes: 100,
            max_triples: 0,
        },
    ] {
        let ReadResult::Error(e) = read_with_limits(&source, &vec![], &limits) else {
            panic!("limit ignored")
        };
        assert!(matches!(e.kind, ErrorKind::ResourceLimit));
    }
    assert!(matches!(
        read_with_limits(
            &vec![],
            &vec![],
            &Limits {
                max_term_bytes: 0,
                max_triples: 0
            }
        ),
        ReadResult::Graph(_)
    ));
    let g = graph(&source, b"source");
    let output = bytes(&g);
    for limit in 0..output.len() {
        assert!(matches!(
            write(&g, limit),
            WriteResult::Error(WriteError::ResourceLimit)
        ));
    }
    let WriteResult::Bytes(exact) = write(&g, output.len()) else {
        panic!("exact budget rejected")
    };
    assert_eq!(exact, output);
}

#[test]
fn export_rejects_raw_invalid_terms_but_not_ill_typed_values() {
    for (lexical, kind) in [
        (vec![255], LiteralKind::Datatype(iri("urn:type"))),
        (b"a".to_vec(), LiteralKind::Language(b"en_XX".to_vec())),
        (b"a".to_vec(), LiteralKind::Datatype(iri("relative"))),
        (
            b"a".to_vec(),
            LiteralKind::Datatype(iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#langString")),
        ),
    ] {
        let g = RawGraph {
            triples: vec![Triple {
                subject: Subject::Iri(iri("urn:s")),
                predicate: iri("urn:p"),
                object: Object::Literal(RdfLiteral { lexical, kind }),
            }],
        };
        assert!(matches!(write(&g, 1000), WriteResult::Error(_)));
    }
}

#[test]
#[ignore = "requires the official W3C N-Triples suite in ROWL_NTRIPLES_SUITE_DIR"]
fn official_w3c_syntax_cases_and_positive_graph_roundtrips() {
    let directory = std::path::PathBuf::from(
        std::env::var_os("ROWL_NTRIPLES_SUITE_DIR").expect("suite directory required"),
    );
    let manifest = std::fs::read_to_string(directory.join("manifest.ttl")).unwrap();
    let mut expected = None;
    let mut count = 0;
    for line in manifest.lines() {
        if line.contains("rdf:type rdft:TestNTriplesPositiveSyntax") {
            expected = Some(true)
        }
        if line.contains("rdf:type rdft:TestNTriplesNegativeSyntax") {
            expected = Some(false)
        }
        if let Some(action) = line.split("mf:action").nth(1) {
            let name = action.split('<').nth(1).unwrap().split('>').next().unwrap();
            let input = std::fs::read(directory.join(name)).unwrap();
            let result = read(&input, &b"suite".to_vec());
            assert_eq!(
                matches!(result, ReadResult::Graph(_)),
                expected.take().unwrap(),
                "W3C case {name}"
            );
            if let ReadResult::Graph(g) = result {
                same_graph(&g, &graph(&bytes(&g), b"roundtrip"));
            }
            count += 1;
        }
    }
    assert_eq!(count, 68, "manifest was incomplete or unexpectedly changed");
}

#[test]
fn literal_kinds_bind_exact_datatypes_and_charge_only_source_terms() {
    let source =
        b"<urn:s><urn:p>\"x\".\n<urn:s><urn:p>\"01\"^^<urn:d>.\n<urn:s><urn:p>\"z\"@EN.".to_vec();
    let ReadResult::Graph(graph) = read_with_limits(
        &source,
        &b"kinds".to_vec(),
        &Limits {
            max_term_bytes: 5,
            max_triples: 3,
        },
    ) else {
        panic!("source-sized terms should fit; implicit xsd:string is not a source term")
    };
    let kinds: Vec<_> = graph
        .triples
        .iter()
        .map(|triple| {
            let Object::Literal(value) = &triple.object else {
                panic!("literal missing")
            };
            match &value.kind {
                LiteralKind::Datatype(iri) => (value.lexical.clone(), iri.spelling.clone()),
                LiteralKind::Language(tag) => (value.lexical.clone(), tag.clone()),
            }
        })
        .collect();
    assert_eq!(
        kinds,
        vec![
            (
                b"x".to_vec(),
                b"http://www.w3.org/2001/XMLSchema#string".to_vec()
            ),
            (b"01".to_vec(), b"urn:d".to_vec()),
            (b"z".to_vec(), b"EN".to_vec()),
        ]
    );
    // Escaping part of the datatype cannot disguise rdf:langString as a
    // datatype without the language tag that RDF 1.1 requires.
    let start = b"<urn:s><urn:p>\"x\"";
    for suffix in [
        br#"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#langString>."#.as_slice(),
        br#"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#lang\u0053tring>."#,
    ] {
        let input = [start.as_slice(), suffix].concat();
        let ReadResult::Error(error) = read(&input, &vec![]) else {
            panic!("unpaired langString accepted")
        };
        assert!(matches!(error.kind, ErrorKind::InvalidLiteralKind));
        assert_eq!(error.offset, start.len());
    }
    let single_caret = [start.as_slice(), b"^<urn:d>."].concat();
    let ReadResult::Error(error) = read(&single_caret, &vec![]) else {
        panic!("single caret accepted")
    };
    assert!(matches!(error.kind, ErrorKind::InvalidLiteralKind));
    assert_eq!(error.offset, start.len() + 1);
}

#[test]
fn whole_document_reports_the_first_failure_without_exposing_a_prefix() {
    let first = b"# leading\r\n<urn:s><urn:p>_:shared. # trailing\r\n";
    let second = b"_:shared<urn:p>\"01\"^^<urn:d>.";
    let source = [first.as_slice(), second.as_slice()].concat();
    let scope = b"document".to_vec();
    let g = graph(&source, &scope);
    assert_eq!(g.triples.len(), 2);
    let Object::Blank(a) = &g.triples[0].object else {
        panic!("blank missing")
    };
    let Subject::Blank(b) = &g.triples[1].subject else {
        panic!("blank missing")
    };
    assert_eq!(key(a), key(b));
    for (suffix, expected_kind, expected_offset) in [
        (
            b"_:shared<urn:p>\"unterminated".as_slice(),
            ErrorKind::UnexpectedEnd,
            first.len() + b"_:shared<urn:p>\"unterminated".len(),
        ),
        (
            b"_:shared<urn:p><urn:o>.x".as_slice(),
            ErrorKind::ExpectedLineEnd,
            first.len() + b"_:shared<urn:p><urn:o>.".len(),
        ),
    ] {
        let input = [first.as_slice(), suffix].concat();
        let ReadResult::Error(error) = read(&input, &scope) else {
            panic!("malformed suffix exposed a graph")
        };
        assert_eq!(
            std::mem::discriminant(&error.kind),
            std::mem::discriminant(&expected_kind)
        );
        assert_eq!(error.offset, expected_offset);
    }
    let limits = Limits {
        max_term_bytes: 100,
        max_triples: 1,
    };
    let ReadResult::Error(error) = read_with_limits(&source, &scope, &limits) else {
        panic!("second triple exceeded count")
    };
    assert!(matches!(error.kind, ErrorKind::ResourceLimit));
    assert_eq!(error.offset, first.len());
    // A malformed next triple retains its syntax diagnostic even at the
    // count boundary: the count limit is applied only to a complete triple.
    let invalid = [first.as_slice(), b"_:shared<urn:p>?"].concat();
    let ReadResult::Error(error) = read_with_limits(&invalid, &scope, &limits) else {
        panic!("invalid object accepted")
    };
    assert!(matches!(error.kind, ErrorKind::ExpectedObject));
    assert_eq!(error.offset, first.len() + 15);
}
