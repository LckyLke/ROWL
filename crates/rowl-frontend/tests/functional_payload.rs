use rowl_frontend::functional::{next_terminal, recognize, Selection, Terminal};
use rowl_frontend::functional_payload::read_quoted;
use rowl_frontend::ntriples::{ErrorKind, ReadError};
use rowl_frontend::regular::MatchResult;

fn spelling(payload: &str) -> String {
    let mut source = String::from("\"");
    for cp in payload.chars() {
        if cp == '"' || cp == '\\' {
            source.push('\\');
        }
        source.push(cp);
    }
    source.push('"');
    source
}
fn decoded(source: &Vec<u8>, start: usize, limit: usize) -> (Vec<u8>, usize) {
    match read_quoted(source, start, limit) {
        Ok(result) => result,
        Err(error) => panic!("unexpected failure at {}", error.offset),
    }
}
fn rejected(source: &[u8], start: usize, limit: usize) -> ReadError {
    match read_quoted(&source.to_vec(), start, limit) {
        Err(error) => error,
        Ok(_) => panic!("expected rejection"),
    }
}

#[test]
fn every_small_xml_word_matches_independent_spelling_and_unescaping() {
    let alphabet = ['a', '\n', '\r', '\t', 'é', '🧪', '"', '\\'];
    let mut words = vec![String::new()];
    for cp in alphabet {
        words.push(cp.to_string());
        for other in alphabet {
            words.push(format!("{cp}{other}"));
        }
    }
    for payload in words {
        let quoted = spelling(&payload);
        assert!(matches!(
            recognize(Terminal::QuotedString, &quoted.as_bytes().to_vec()),
            MatchResult::Matched(true)
        ));
        let source = format!("xx{quoted}@en").into_bytes();
        let (output, end) = decoded(&source, 2, payload.len());
        assert_eq!(output, payload.as_bytes());
        assert_eq!(end, 2 + quoted.len());
        match next_terminal(&source, 2) {
            Selection::Token(token) => {
                assert!(matches!(token.terminal, Terminal::QuotedString));
                assert_eq!(token.start, 2);
                assert_eq!(token.end, end);
            }
            _ => panic!("quoted token must be selected"),
        }
        if !payload.is_empty() {
            let error = rejected(&source, 2, payload.len() - 1);
            assert!(matches!(error.kind, ErrorKind::ResourceLimit));
        }
    }
}

#[test]
fn foreign_escapes_and_malformed_units_report_original_first_offsets() {
    let invalid: &[(&[u8], usize, bool)] = &[
        (b"plain", 0, false),
        (b"\"\\n\"", 1, true),
        (b"\"\\t\"", 1, true),
        (b"\"\\u0041\"", 1, true),
        (b"\"\\U00000041\"", 1, true),
        (b"\"\\'\"", 1, true),
        (b"\"\0\"", 1, false),
        (b"\"a\x0b\"", 2, false),
    ];
    for &(source, offset, escape) in invalid {
        let error = rejected(source, 0, 100);
        assert_eq!(error.offset, offset);
        if escape {
            assert!(matches!(error.kind, ErrorKind::InvalidEscape));
        } else {
            assert!(matches!(error.kind, ErrorKind::InvalidCharacter));
        }
    }
    for source in [b"".as_slice(), b"\"", b"\"abc", b"\"\\"] {
        let error = rejected(source, 0, 100);
        assert!(matches!(error.kind, ErrorKind::UnexpectedEnd));
        assert_eq!(error.offset, source.len());
    }
    for source in [
        b"\"\xc0\x80\"".as_slice(),
        b"\"\xed\xa0\x80\"",
        b"\"\\\xff\"",
    ] {
        let error = rejected(source, 0, 100);
        assert!(matches!(error.kind, ErrorKind::MalformedUtf8));
        assert_eq!(error.offset, if source[1] == b'\\' { 2 } else { 1 });
    }
    let error = rejected(b"\"\"", 3, 100);
    assert!(matches!(error.kind, ErrorKind::MalformedUtf8));
    assert_eq!(error.offset, 3);
}

#[test]
fn byte_budgets_count_decoded_units_and_preserve_source_escape_offsets() {
    for payload in ["", "a", "é", "界", "🧪", "\"", "\\", "é\"🧪"] {
        let source = spelling(payload).into_bytes();
        for limit in 0..=payload.len() {
            if limit == payload.len() {
                let (output, end) = decoded(&source, 0, limit);
                assert_eq!(output, payload.as_bytes());
                assert_eq!(end, source.len());
            } else {
                let mut source_offset = 1;
                let mut output_bytes = 0;
                let expected = payload
                    .chars()
                    .find_map(|cp| {
                        let begin = source_offset;
                        source_offset += cp.len_utf8() + usize::from(cp == '"' || cp == '\\');
                        output_bytes += cp.len_utf8();
                        (output_bytes > limit).then_some(begin)
                    })
                    .expect("insufficient budget must fail on a payload unit");
                let error = rejected(&source, 0, limit);
                assert!(matches!(error.kind, ErrorKind::ResourceLimit));
                assert_eq!(error.offset, expected);
            }
        }
    }
}

#[test]
fn token_reader_stops_at_the_first_unescaped_quote_and_lexer_checks_suffix() {
    let source = b"\"a\\\"b\"@en \"later\"".to_vec();
    let (output, end) = decoded(&source, 0, 3);
    assert_eq!(output, b"a\"b");
    assert_eq!(end, 6);
    assert_eq!(&source[end..], b"@en \"later\"");
    let source = b"\"ok\"\xff".to_vec();
    assert_eq!(decoded(&source, 0, 2), (b"ok".to_vec(), 4));
    assert!(matches!(
        next_terminal(&source, 0),
        Selection::MalformedUtf8(_)
    ));
}

#[test]
fn raw_xml_character_boundaries_and_multiline_text_are_preserved() {
    for cp in [9, 10, 13, 32, 0xd7ff, 0xe000, 0xfffd, 0x10000, 0x10ffff] {
        let payload = char::from_u32(cp).unwrap().to_string();
        let source = spelling(&payload).into_bytes();
        let (output, end) = decoded(&source, 0, payload.len());
        assert_eq!(output, payload.as_bytes());
        assert_eq!(end, source.len());
    }
    for cp in [0, 8, 11, 12, 14, 31, 0xfffe, 0xffff] {
        let payload = char::from_u32(cp).unwrap().to_string();
        let error = rejected(spelling(&payload).as_bytes(), 0, 10);
        assert!(matches!(error.kind, ErrorKind::InvalidCharacter));
        assert_eq!(error.offset, 1);
    }
    let payload = "faulty\r\n\tmotor: 温度 \"high\"\\sensor";
    let source = spelling(payload).into_bytes();
    assert_eq!(decoded(&source, 0, payload.len()).0, payload.as_bytes());
}
