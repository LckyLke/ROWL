use rowl_frontend::names::{validate_abbreviated, validate_local, validate_node, validate_prefix};
use rowl_frontend::regular::MatchResult;
use rowl_frontend::unicode::TextError;

fn matched(validate: fn(&Vec<u8>) -> MatchResult, text: &str) -> bool {
    match validate(&text.as_bytes().to_vec()) {
        MatchResult::Matched(value) => value,
        MatchResult::MalformedUtf8(_) => panic!("Rust str has valid UTF-8"),
    }
}

const BASE_RANGES: [(u32, u32); 14] = [
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

fn base(c: char) -> bool {
    BASE_RANGES
        .iter()
        .any(|&(lo, hi)| (lo..=hi).contains(&u32::from(c)))
}
fn tail(c: char) -> bool {
    base(c)
        || c == '_'
        || c == '-'
        || c.is_ascii_digit()
        || c == '\u{b7}'
        || ('\u{300}'..='\u{36f}').contains(&c)
        || ('\u{203f}'..='\u{2040}').contains(&c)
}
fn word(text: &str, local: bool) -> bool {
    let mut chars = text.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (base(first) || (local && (first == '_' || first.is_ascii_digit())))
        && chars.all(|c| tail(c) || c == '.')
        && !text.ends_with('.')
}
fn prefix(text: &str) -> bool {
    text.strip_suffix(':')
        .is_some_and(|label| label.is_empty() || word(label, false))
}
fn abbreviated(text: &str) -> bool {
    text.split_once(':')
        .is_some_and(|(label, local)| (label.is_empty() || word(label, false)) && word(local, true))
}

#[test]
fn small_words_agree_with_independent_character_and_boundary_oracle() {
    let alphabet = ['a', '_', '7', '.', ':', '-', '\u{300}', '%'];
    let mut level = vec![String::new()];
    for _ in 0..=3 {
        for text in &level {
            assert_eq!(
                matched(validate_prefix, text),
                prefix(text),
                "prefix {text:?}"
            );
            assert_eq!(
                matched(validate_local, text),
                word(text, true),
                "local {text:?}"
            );
            assert_eq!(
                matched(validate_abbreviated, text),
                abbreviated(text),
                "IRI {text:?}"
            );
            assert_eq!(
                matched(validate_node, text),
                text.strip_prefix("_:").is_some_and(|s| word(s, true)),
                "node {text:?}"
            );
        }
        level = level
            .iter()
            .flat_map(|s| alphabet.iter().map(move |c| format!("{s}{c}")))
            .collect();
    }
}

#[test]
fn unicode_base_intervals_and_gaps_have_exact_boundaries() {
    let mut points = Vec::new();
    for (lo, hi) in BASE_RANGES {
        points.extend([lo - 1, lo, hi, hi + 1]);
    }
    for cp in points {
        let Some(c) = char::from_u32(cp) else {
            continue;
        };
        assert_eq!(
            matched(validate_prefix, &format!("{c}:")),
            base(c),
            "U+{cp:X}"
        );
        assert_eq!(
            matched(validate_local, &c.to_string()),
            base(c) || c == '_' || c.is_ascii_digit(),
            "U+{cp:X}"
        );
    }
}

#[test]
fn owl_names_use_the_referenced_2008_grammar() {
    for text in [":", "a:", "A..b:", "é:", "𐀀:", "a\u{300}:"] {
        assert!(matched(validate_prefix, text), "{text:?}");
    }
    for text in ["", "a", "7:", "_:", "a.:", "a:b:", "%61:", "\\u0061:"] {
        assert!(!matched(validate_prefix, text), "{text:?}");
    }
    for text in ["7", "_", "a..b", "a\u{300}", "𐀀"] {
        assert!(matched(validate_local, text), "{text:?}");
    }
    for text in ["", ".a", "a.", "-a", "\u{300}a", "a:b", "%61", "a\\~b"] {
        assert!(!matched(validate_local, text), "{text:?}");
    }
    assert!(matched(validate_abbreviated, ":Pump"));
    assert!(matched(validate_node, "_:7"));
    assert!(!matched(validate_abbreviated, "ex:"));
    assert!(!matched(validate_abbreviated, "_:node"));
    assert!(!matched(validate_node, "_:"));
}

#[test]
fn malformed_suffix_remains_visible_after_a_grammar_mismatch() {
    for validate in [
        validate_prefix,
        validate_local,
        validate_abbreviated,
        validate_node,
    ] {
        let mut bytes = b"!bad".to_vec();
        bytes.extend([0xf0, 0x80, 0x80, 0x80]);
        match validate(&bytes) {
            MatchResult::MalformedUtf8(TextError::InvalidUtf8 { offset }) => assert_eq!(offset, 4),
            _ => panic!("must validate the complete source, including a malformed suffix"),
        }
    }
}
