use rowl_frontend::regular::{copy_expression, derivative, matches_utf8, Expression, MatchResult};
use rowl_frontend::unicode::TextError;

// An independent oracle splits words into concatenands. It uses neither
// derivatives nor the executable nullable function.
fn accepts(expression: &Expression, word: &[u32]) -> bool {
    match expression {
        Expression::Empty => false,
        Expression::Epsilon => word.is_empty(),
        Expression::Interval { lower, upper } => {
            word.len() == 1 && *lower <= word[0] && word[0] <= *upper
        }
        Expression::Alternative(a, b) => accepts(a, word) || accepts(b, word),
        Expression::Sequence(a, b) => {
            (0..=word.len()).any(|split| accepts(a, &word[..split]) && accepts(b, &word[split..]))
        }
        Expression::Repeat(inner) => {
            word.is_empty()
                || (1..=word.len()).any(|split| {
                    accepts(inner, &word[..split]) && accepts(expression, &word[split..])
                })
        }
    }
}

fn words(alphabet: &[u32], remaining: usize, current: &mut Vec<u32>, output: &mut Vec<Vec<u32>>) {
    output.push(current.clone());
    if remaining > 0 {
        for cp in alphabet {
            current.push(*cp);
            words(alphabet, remaining - 1, current, output);
            current.pop();
        }
    }
}

#[test]
fn matching_and_derivatives_agree_with_word_splitting_oracle() {
    let atoms = [
        Expression::Empty,
        Expression::Epsilon,
        Expression::Interval {
            lower: 97,
            upper: 98,
        },
        Expression::Interval {
            lower: 233,
            upper: 233,
        },
        Expression::Interval { lower: 5, upper: 2 },
    ];
    let mut expressions: Vec<_> = atoms.iter().map(copy_expression).collect();
    for a in &atoms {
        expressions.push(Expression::Repeat(Box::new(copy_expression(a))));
        for b in &atoms {
            expressions.push(Expression::Alternative(
                Box::new(copy_expression(a)),
                Box::new(copy_expression(b)),
            ));
            expressions.push(Expression::Sequence(
                Box::new(copy_expression(a)),
                Box::new(copy_expression(b)),
            ));
        }
    }
    expressions.push(Expression::Repeat(Box::new(Expression::Alternative(
        Box::new(Expression::Epsilon),
        Box::new(Expression::Repeat(Box::new(copy_expression(&atoms[2])))),
    ))));
    let alphabet = [0, 97, 98, 233];
    let mut samples = Vec::new();
    words(&alphabet, 3, &mut Vec::new(), &mut samples);
    for expression in &expressions {
        for word in &samples {
            let encoded: String = word.iter().map(|cp| char::from_u32(*cp).unwrap()).collect();
            match matches_utf8(copy_expression(expression), &encoded.into_bytes()) {
                MatchResult::Matched(actual) => assert_eq!(actual, accepts(expression, word)),
                MatchResult::MalformedUtf8(_) => panic!("oracle word has valid encoding"),
            }
            for cp in alphabet {
                let derived = derivative(copy_expression(expression), cp);
                let mut whole = vec![cp];
                whole.extend(word);
                assert_eq!(accepts(&derived, word), accepts(expression, &whole));
            }
        }
    }
}

#[test]
fn malformed_suffix_cannot_be_hidden_by_grammar_rejection() {
    let bytes = vec![b'x', 0xc3, 0xa9, 0xf4, 0x90, 0x80, 0x80];
    match matches_utf8(Expression::Empty, &bytes) {
        MatchResult::MalformedUtf8(TextError::InvalidUtf8 { offset }) => assert_eq!(offset, 3),
        _ => panic!("the malformed unit must still be diagnosed"),
    }
}

#[test]
fn lexical_matcher_does_not_impose_xml_character_policy() {
    for cp in [0, 0xb, 0xffff, 0x10ffff] {
        let bytes = char::from_u32(cp).unwrap().to_string().into_bytes();
        assert!(matches!(
            matches_utf8(
                Expression::Interval {
                    lower: cp,
                    upper: cp
                },
                &bytes
            ),
            MatchResult::Matched(true)
        ));
    }
}
