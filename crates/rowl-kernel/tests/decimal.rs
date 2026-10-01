use rowl_kernel::decimal::{read, read_span, ReadError};
use rowl_kernel::probes::Natural;

fn value(number: &Natural) -> usize {
    let mut current = number;
    let mut result = 0;
    while let Natural::Succ(previous) = current {
        result += 1;
        current = previous;
    }
    result
}
fn accepted(bytes: &[u8]) -> usize {
    value(&read(&bytes.to_vec()).unwrap_or_else(|_| panic!("expected a complete decimal word")))
}
fn diagnosis(result: Result<Natural, ReadError>) -> (&'static str, usize) {
    match result {
        Err(ReadError::InvalidSpan { offset }) => ("span", offset),
        Err(ReadError::Empty { offset }) => ("empty", offset),
        Err(ReadError::InvalidDigit { offset }) => ("digit", offset),
        Ok(_) => panic!("expected an exact original source diagnostic"),
    }
}

#[test]
fn all_single_bytes_follow_the_ascii_decimal_grammar() {
    for byte in u8::MIN..=u8::MAX {
        match read(&vec![byte]) {
            Ok(number) => {
                assert!(byte.is_ascii_digit());
                assert_eq!(value(&number), usize::from(byte - b'0'));
            }
            Err(error) => {
                assert!(!byte.is_ascii_digit());
                assert_eq!(diagnosis(Err(error)), ("digit", 0));
            }
        }
    }
}

#[test]
fn positional_values_and_leading_zeroes_match_an_independent_small_integer_oracle() {
    for expected in 0..=257 {
        for zeroes in 0..=3 {
            let source = format!("{}{expected}", "0".repeat(zeroes));
            assert_eq!(accepted(source.as_bytes()), expected);
        }
    }
    assert_eq!(accepted(b"999"), 999);
}

#[test]
fn byte_spans_retain_original_offsets_and_ignore_unselected_bytes() {
    let source = b"#prefix ObjectMinCardinality(0003 :hasPart :Part) #suffix".to_vec();
    let start = source.iter().position(|byte| *byte == b'0').unwrap();
    assert_eq!(
        value(
            &read_span(&source, start, start + 4).unwrap_or_else(|_| panic!("valid chosen digits"))
        ),
        3
    );
    let malformed = b"context(001x23)".to_vec();
    assert_eq!(diagnosis(read_span(&malformed, 8, 14)), ("digit", 11));
    assert_eq!(diagnosis(read(&malformed)), ("digit", 0));
}

#[test]
fn every_range_and_empty_phase_is_explicit() {
    let source = b"123".to_vec();
    for start in 0..=5 {
        for end in 0..=5 {
            let result = read_span(&source, start, end);
            if start > end || end > source.len() {
                assert_eq!(diagnosis(result), ("span", start));
            } else if start == end {
                assert_eq!(diagnosis(result), ("empty", start));
            } else {
                let expected = source[start..end]
                    .iter()
                    .fold(0, |value, byte| value * 10 + usize::from(byte - b'0'));
                assert_eq!(
                    value(&result.unwrap_or_else(|_| panic!("valid nonempty span"))),
                    expected
                );
            }
        }
    }
    assert_eq!(diagnosis(read(&Vec::new())), ("empty", 0));
    assert_eq!(
        diagnosis(read_span(&source, usize::MAX, usize::MAX)),
        ("span", usize::MAX)
    );
    assert_eq!(diagnosis(read_span(&source, 0, usize::MAX)), ("span", 0));
}

#[test]
fn signs_spaces_unicode_digits_and_later_errors_never_expose_a_partial_value() {
    for (source, offset) in [
        ("+3", 0),
        ("-3", 0),
        (" 3", 0),
        ("3 ", 1),
        ("3.0", 1),
        ("٣", 0),
        ("３", 0),
        ("003x", 3),
        ("003\n", 3),
    ] {
        assert_eq!(
            diagnosis(read(&source.as_bytes().to_vec())),
            ("digit", offset)
        );
    }
    assert_eq!(diagnosis(read(&vec![b'0', b'3', 0xff])), ("digit", 2));
}

#[test]
fn long_leading_zeroes_preserve_small_exact_values() {
    let mut source = vec![b'0'; 128];
    source.extend_from_slice(b"003");
    assert_eq!(accepted(&source), 3);
    assert_eq!(accepted(&[b'0'; 128]), 0);
}
