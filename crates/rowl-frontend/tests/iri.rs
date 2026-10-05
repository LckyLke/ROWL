use rowl_frontend::iri::{validate_iri, validate_reference};
use rowl_frontend::regular::MatchResult;
use rowl_frontend::unicode::TextError;

fn accepted(input: &str, relative: bool) -> bool {
    let bytes = input.as_bytes().to_vec();
    match if relative {
        validate_reference(&bytes)
    } else {
        validate_iri(&bytes)
    } {
        MatchResult::Matched(value) => value,
        MatchResult::MalformedUtf8(_) => panic!("test str must be valid UTF-8"),
    }
}

#[test]
fn complete_iri_and_reference_productions() {
    for input in [
        "http://example.org/pump#part",
        "urn:example:machine",
        "x:",
        "x:?",
        "x:#",
        "x:/",
        "x://",
        "x://///",
        "HTTP://user:pass@example.org:80/a%20b?x=y#z",
        "http://例え.テスト/機械",
        "x://@host:",
        "x:a:b",
        "x://999.0.0.1/",
        "x://[vF.a:b]/",
        "x://[V1.a]/",
    ] {
        assert!(accepted(input, false), "IRI: {input}");
        assert!(accepted(input, true), "reference: {input}");
    }
    for input in [
        "",
        "pump",
        "../motor",
        "/motor",
        "//host/motor",
        "?query",
        "#fragment",
        "a/b:c",
    ] {
        assert!(!accepted(input, false), "relative IRI: {input}");
        assert!(accepted(input, true), "reference: {input}");
    }
    for input in [
        "1scheme:x",
        "a b:c",
        "x:a b",
        "x:%",
        "x:%a",
        "x:%gg",
        "x://[bad]/",
        "x://[v.a]/",
        "x://[v1.]/",
        "x://[v1.é]/",
        "x://[::1%25eth0]/",
        "x://host:abc/",
        "x://a@@host/",
        "x:<>",
        "x:\\",
        "x:a#b#c",
        "x:a\n",
    ] {
        assert!(!accepted(input, false), "invalid IRI: {input:?}");
        assert!(!accepted(input, true), "invalid reference: {input:?}");
    }
}

#[test]
fn all_ipv6_compression_positions_and_embedded_ipv4() {
    assert!(accepted("x://[1:2:3:4:5:6:7:8]/", false));
    for start in 0..8 {
        for count in 1..=8 - start {
            let before = (1..=start)
                .map(|n| format!("{n:x}"))
                .collect::<Vec<_>>()
                .join(":");
            let after = (start + count + 1..=8)
                .map(|n| format!("{n:x}"))
                .collect::<Vec<_>>()
                .join(":");
            let host = format!("{before}::{after}");
            assert!(host.parse::<std::net::Ipv6Addr>().is_ok());
            assert!(accepted(&format!("x://[{host}]/"), false), "{host}");
        }
    }
    for host in [
        "::192.0.2.1",
        "::ffff:192.0.2.1",
        "1:2:3:4:5:6:192.0.2.1",
        "1::2:192.0.2.1",
    ] {
        assert!(accepted(&format!("x://[{host}]/"), false), "{host}");
    }
    for host in [
        "1:2:3:4:5:6:7",
        "1:2:3:4:5:6:7:8:9",
        "1::2::3",
        "12345::",
        "::256.0.2.1",
        "::192.00.2.1",
    ] {
        assert!(!accepted(&format!("x://[{host}]/"), false), "{host}");
    }
}

#[test]
fn unicode_boundaries_and_query_only_private_characters() {
    for cp in [
        0xa0, 0xd7ff, 0xf900, 0xfdcf, 0xfdf0, 0xffef, 0x10000, 0xdfffd, 0xe1000, 0xefffd,
    ] {
        let c = char::from_u32(cp).unwrap();
        assert!(accepted(&format!("x:{c}"), false), "ucschar {cp:x}");
    }
    for cp in [
        0x80, 0x9f, 0xfdd0, 0xfdef, 0xfff0, 0xffff, 0x1fffe, 0xe0000, 0xe0fff, 0xefffe, 0x10ffff,
    ] {
        let c = char::from_u32(cp).unwrap();
        assert!(!accepted(&format!("x:{c}"), false), "not ucschar {cp:x}");
        assert!(!accepted(&format!("x:?{c}"), false), "not query {cp:x}");
    }
    for cp in [0xe000, 0xf8ff, 0xf0000, 0xffffd, 0x100000, 0x10fffd] {
        let c = char::from_u32(cp).unwrap();
        assert!(accepted(&format!("x:?{c}"), false));
        assert!(!accepted(&format!("x:{c}"), false));
        assert!(!accepted(&format!("x:#{c}"), false));
        assert!(!accepted(&format!("x://{c}/"), false));
    }
}

#[test]
fn malformed_utf8_is_distinct_from_well_encoded_grammar_rejection() {
    let mut bytes = b"not-an-iri".to_vec();
    bytes.extend([0xc0, 0x80]);
    assert!(matches!(
        validate_iri(&bytes),
        MatchResult::MalformedUtf8(TextError::InvalidUtf8 { offset: 10 })
    ));
    assert!(matches!(
        validate_iri(&b"not-an-iri".to_vec()),
        MatchResult::Matched(false)
    ));
}

/// A small deterministic generator, so failures reproduce.
struct Seed(u64);
impl Seed {
    fn next(&mut self, bound: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % bound
    }
}

#[test]
fn plain_iris_are_answered_exactly_as_by_the_grammar() {
    use rowl_frontend::iri::iri;
    use rowl_frontend::regular::matches_utf8;
    let pieces: [&[u8]; 31] = [
        b"a",
        b"Z",
        b"h",
        b"t",
        b"p",
        b"s",
        b"0",
        b"9",
        b":",
        b"/",
        b"//",
        b"#",
        b"?",
        b".",
        b"-",
        b"_",
        b"~",
        b"+",
        b"@",
        b"%",
        b"%2F",
        b"[",
        b"]",
        b" ",
        b"\\",
        "é".as_bytes(),
        b"\xff",
        b"!",
        b"=",
        b"http://",
        b"https://example.org/",
    ];
    let mut seed = Seed(7);
    let mut plain = 0;
    for _ in 0..5000 {
        let mut bytes = Vec::new();
        for _ in 0..seed.next(12) {
            bytes.extend_from_slice(pieces[seed.next(pieces.len())]);
        }
        let fast = validate_iri(&bytes);
        let grammar = matches_utf8(iri(), &bytes);
        match (&fast, &grammar) {
            (MatchResult::Matched(a), MatchResult::Matched(b)) => assert_eq!(a, b, "{bytes:?}"),
            (MatchResult::MalformedUtf8(_), MatchResult::MalformedUtf8(_)) => {}
            _ => panic!("different kinds of answer for {bytes:?}"),
        }
        if matches!(grammar, MatchResult::Matched(true)) && bytes.starts_with(b"h") {
            plain += 1;
        }
    }
    assert!(plain > 25, "the inputs must include many IRIs");
    for input in [
        "https://example.org/gen/C12345",
        "http://www.w3.org/2002/07/owl#Thing",
        "http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
        "urn:x://a",
        "x://",
        "x://h#/a/b",
    ] {
        assert!(accepted(input, false), "IRI: {input}");
    }
}
