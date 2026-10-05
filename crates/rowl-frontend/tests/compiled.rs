use rowl_frontend::compiled::{compile, longest_valid, matches, table};
use rowl_frontend::iri::{iri, validate_iri};
use rowl_frontend::longest::{longest_prefix, PrefixResult};
use rowl_frontend::regular::{
    alternate, copy_expression, matches_utf8, repeat, sequence, Expression, MatchResult,
};
use rowl_frontend::unicode::TextError;

fn error_offset(error: &TextError) -> (u8, usize) {
    match error {
        TextError::InvalidPosition { offset } => (0, *offset),
        TextError::InvalidUtf8 { offset } => (1, *offset),
        TextError::NonXmlCharacter { offset, .. } => (2, *offset),
    }
}

/// A small deterministic generator, so failures reproduce.
struct Seed(u64);
impl Seed {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % bound
    }
}

const ALPHABET: [char; 4] = ['a', 'é', '𐀀', ':'];

fn expression(seed: &mut Seed, depth: u32) -> Expression {
    let choice = if depth == 0 {
        seed.next(3)
    } else {
        seed.next(7)
    };
    match choice {
        0 => Expression::Epsilon,
        1 => Expression::Empty,
        2 => {
            let c = u32::from(ALPHABET[seed.next(4) as usize]);
            Expression::Interval {
                lower: c,
                upper: c + seed.next(2) as u32,
            }
        }
        3 | 4 => Expression::Alternative(
            Box::new(expression(seed, depth - 1)),
            Box::new(expression(seed, depth - 1)),
        ),
        5 => Expression::Sequence(
            Box::new(expression(seed, depth - 1)),
            Box::new(expression(seed, depth - 1)),
        ),
        _ => Expression::Repeat(Box::new(expression(seed, depth - 1))),
    }
}

fn text(seed: &mut Seed) -> String {
    (0..seed.next(6))
        .map(|_| ALPHABET[seed.next(4) as usize])
        .collect()
}

fn same_match(left: &MatchResult, right: &MatchResult) -> bool {
    match (left, right) {
        (MatchResult::Matched(a), MatchResult::Matched(b)) => a == b,
        (MatchResult::MalformedUtf8(a), MatchResult::MalformedUtf8(b)) => {
            error_offset(a) == error_offset(b)
        }
        _ => false,
    }
}

fn compiled_match(grammar: &Expression, bytes: &Vec<u8>) -> MatchResult {
    let mut nodes = table();
    let root = compile(&mut nodes, grammar);
    matches(&nodes, root, bytes).expect("a small table has room")
}

#[test]
fn compiled_matching_agrees_with_derivatives_on_random_grammars() {
    let mut seed = Seed(7);
    for _ in 0..3000 {
        let grammar = expression(&mut seed, 4);
        for _ in 0..4 {
            let bytes = text(&mut seed).into_bytes();
            let expected = matches_utf8(copy_expression(&grammar), &bytes);
            let actual = compiled_match(&grammar, &bytes);
            assert!(same_match(&expected, &actual));
        }
    }
}

#[test]
fn compiled_matching_reports_malformed_utf8_like_derivatives() {
    let grammar = repeat(alternate(
        Expression::Interval {
            lower: 97,
            upper: 97,
        },
        Expression::Epsilon,
    ));
    for bytes in [
        vec![97, 0xff],
        vec![0xc0, 0x80],
        vec![97, 97, 0xed, 0xa0, 0x80],
    ] {
        let expected = matches_utf8(copy_expression(&grammar), &bytes);
        let actual = compiled_match(&grammar, &bytes);
        match (expected, actual) {
            (MatchResult::MalformedUtf8(a), MatchResult::MalformedUtf8(b)) => {
                assert_eq!(error_offset(&a), error_offset(&b))
            }
            _ => panic!("malformed input is reported"),
        }
    }
}

#[test]
fn compiled_longest_prefix_agrees_with_derivatives_on_valid_text() {
    let mut seed = Seed(11);
    for _ in 0..3000 {
        let grammar = expression(&mut seed, 4);
        let mut nodes = table();
        let root = compile(&mut nodes, &grammar);
        let source = text(&mut seed);
        for start in source
            .char_indices()
            .map(|(index, _)| index)
            .chain(std::iter::once(source.len()))
        {
            let bytes = source.clone().into_bytes();
            let expected = match longest_prefix(copy_expression(&grammar), &bytes, start) {
                PrefixResult::Matched(value) => value,
                PrefixResult::MalformedUtf8(_) => panic!("valid text"),
            };
            let actual = match longest_valid(&nodes, root, &bytes, start) {
                Some(PrefixResult::Matched(value)) => value,
                _ => panic!("valid text and a small table"),
            };
            assert_eq!(expected, actual, "{source:?} at {start}");
        }
    }
}

#[test]
fn iri_validation_keeps_the_derivative_answers() {
    for sample in [
        "https://example.org/b/C17",
        "http://www.w3.org/2001/XMLSchema#integer",
        "urn:x",
        "http://[::1]/a",
        "http://[::1]a",
        "http://user@host:8080/p?q=1#f",
        "http://[v7.x]/",
        "http://1.2.3.4/",
        "http://256.1.1.1/",
        "mailto:%41%zz",
        "1http://x",
        "http://example.org/é𐀀",
        "",
        ":",
    ] {
        let bytes = sample.as_bytes().to_vec();
        assert!(
            same_match(&validate_iri(&bytes), &matches_utf8(iri(), &bytes)),
            "{sample}"
        );
    }
    let _ = sequence(Expression::Epsilon, Expression::Epsilon);
}
