use rowl_frontend::longest::{longest_prefix, longest_valid_prefix, PrefixResult};
use rowl_frontend::regular::{alternate, repeat, sequence, Expression};
use rowl_frontend::unicode::TextError;

fn letter(c: char) -> Expression {
    Expression::Interval {
        lower: u32::from(c),
        upper: u32::from(c),
    }
}
fn literal(text: &str) -> Expression {
    text.chars()
        .fold(Expression::Epsilon, |prior, c| sequence(prior, letter(c)))
}
fn choices(words: &[&str]) -> Expression {
    words.iter().fold(Expression::Empty, |prior, word| {
        alternate(prior, literal(word))
    })
}
fn endpoint(expression: Expression, text: &str, offset: usize) -> Option<usize> {
    match longest_prefix(expression, &text.as_bytes().to_vec(), offset) {
        PrefixResult::Matched(value) => value,
        PrefixResult::MalformedUtf8(_) => panic!("fixture starts at a valid UTF-8 boundary"),
    }
}

fn valid_endpoint(expression: Expression, text: &str, offset: usize) -> Option<usize> {
    match longest_valid_prefix(expression, &text.as_bytes().to_vec(), offset) {
        PrefixResult::Matched(value) => value,
        PrefixResult::MalformedUtf8(_) => panic!("fixture starts at a valid UTF-8 boundary"),
    }
}

#[test]
fn greedy_matching_selects_longer_names_over_keyword_prefixes() {
    let words = ["SubClassOf", "SubClassOf:ABC", "SubClassOf:AB"];
    assert_eq!(endpoint(choices(&words), "SubClassOf:ABC)", 0), Some(14));
    assert_eq!(
        endpoint(choices(&words), "SubClassOf(Pump Machine)", 0),
        Some(10)
    );
    assert_eq!(endpoint(choices(&words), "SubClassOf:ABX", 0), Some(13));
    assert_eq!(endpoint(choices(&words), "SomethingElse", 0), None);
}

#[test]
fn finite_languages_agree_with_independent_prefix_search_at_every_utf8_boundary() {
    let languages: &[&[&str]] = &[
        &[],
        &[""],
        &["a", "aa", "aé"],
        &["é", "é𐀀", "𐀀a"],
        &["", ":", "a:", "é:a"],
        &["a", "é", "𐀀", "aé𐀀"],
    ];
    let alphabet = ['a', 'é', '𐀀', ':'];
    let mut level = vec![String::new()];
    for _ in 0..=3 {
        for text in &level {
            for start in text
                .char_indices()
                .map(|(index, _)| index)
                .chain(std::iter::once(text.len()))
            {
                for words in languages {
                    let expected = words
                        .iter()
                        .filter(|word| text[start..].starts_with(**word))
                        .map(|word| start + word.len())
                        .max();
                    assert_eq!(
                        endpoint(choices(words), text, start),
                        expected,
                        "{text:?} at {start}: {words:?}"
                    );
                }
            }
        }
        level = level
            .iter()
            .flat_map(|s| alphabet.iter().map(move |c| format!("{s}{c}")))
            .collect();
    }
}

#[test]
fn early_stopping_scan_agrees_with_the_full_scan_on_valid_text() {
    let sample = |index: usize| match index {
        0 => Expression::Empty,
        1 => Expression::Epsilon,
        2 => choices(&["a", "aa", "aé"]),
        3 => choices(&["é", "é𐀀", "𐀀a"]),
        4 => repeat(sequence(letter('é'), letter('𐀀'))),
        _ => sequence(repeat(letter('a')), letter(':')),
    };
    for text in ["", "a", "aaé", "é𐀀é𐀀:", "aaaa:a", "𐀀aé", ":::"] {
        for start in text
            .char_indices()
            .map(|(index, _)| index)
            .chain(std::iter::once(text.len()))
        {
            for index in 0..6 {
                assert_eq!(
                    valid_endpoint(sample(index), text, start),
                    endpoint(sample(index), text, start),
                    "{text:?} at {start}, expression {index}"
                );
            }
        }
    }
}

#[test]
fn repeated_multibyte_units_choose_exact_exclusive_byte_endpoints() {
    for (text, start, expected) in [
        ("é𐀀é𐀀!", 0, 12),
        ("xé𐀀!", 1, 7),
        ("é𐀀é!", 0, 6),
        ("!", 0, 0),
    ] {
        assert_eq!(
            endpoint(repeat(sequence(letter('é'), letter('𐀀'))), text, start),
            Some(expected)
        );
    }
    assert_eq!(
        endpoint(sequence(repeat(letter('a')), letter('b')), "aaaabx", 0),
        Some(5)
    );
}

#[test]
fn empty_match_and_no_match_are_distinct_even_at_end_of_input() {
    for (text, start) in [("", 0), ("abc", 0), ("abc", 3)] {
        assert_eq!(endpoint(Expression::Epsilon, text, start), Some(start));
        assert_eq!(endpoint(Expression::Empty, text, start), None);
    }
}

#[test]
fn malformed_suffix_is_reported_even_after_a_valid_earlier_match() {
    for suffix in [
        vec![0xff],
        vec![0xc0, 0x80],
        vec![0xed, 0xa0, 0x80],
        vec![0xf0, 0x90],
    ] {
        let mut bytes = "aé".as_bytes().to_vec();
        bytes.extend(suffix);
        for expression in [literal("a"), Expression::Epsilon, Expression::Empty] {
            assert!(matches!(
                longest_prefix(expression, &bytes, 0),
                PrefixResult::MalformedUtf8(TextError::InvalidUtf8 { offset: 3 })
            ));
        }
    }
}

#[test]
fn invalid_positions_and_positions_inside_a_unit_return_exact_diagnostics() {
    let bytes = "é".as_bytes().to_vec();
    assert!(matches!(
        longest_prefix(Expression::Epsilon, &bytes, 1),
        PrefixResult::MalformedUtf8(TextError::InvalidUtf8 { offset: 1 })
    ));
    assert!(matches!(
        longest_prefix(Expression::Epsilon, &bytes, 3),
        PrefixResult::MalformedUtf8(TextError::InvalidPosition { offset: 3 })
    ));
    assert!(matches!(
        longest_prefix(Expression::Epsilon, &bytes, usize::MAX),
        PrefixResult::MalformedUtf8(TextError::InvalidPosition { offset: usize::MAX })
    ));
    assert_eq!(endpoint(Expression::Epsilon, "é", 2), Some(2));
}
