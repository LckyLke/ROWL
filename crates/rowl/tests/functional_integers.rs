//! Source-to-value integration through the actual selector and complete lexer.
use rowl::experimental::functional::{next_terminal, Selection, Terminal};
use rowl::experimental::functional_lexer::{lex, LexResult, Tokens};
use rowl::experimental::{decimal, Natural};

fn small_value(number: &Natural) -> usize {
    let mut remaining = number;
    let mut value = 0;
    while let Natural::Succ(previous) = remaining {
        value += 1;
        remaining = previous;
    }
    value
}

#[test]
fn actual_greatest_token_preserves_the_original_span_and_exact_value() {
    let text = "# Geräte\nObjectMinCardinality(003 :hasPart :Part)";
    let source = text.as_bytes().to_vec();
    let start = text.find("003").expect("fixture integer");
    let token = match next_terminal(&source, start) {
        Selection::Token(token) if matches!(token.terminal, Terminal::Integer) => token,
        _ => panic!("expected an integer from the actual source selector"),
    };
    assert_eq!(token.start, start);
    assert_eq!(token.end, start + 3);
    assert_eq!(&source[token.start..token.end], b"003");
    let number = decimal::read_span(&source, token.start, token.end)
        .unwrap_or_else(|_| panic!("a selected integer must have a value"));
    assert_eq!(small_value(&number), 3);
}

#[test]
fn all_six_cardinality_terminal_contexts_supply_their_exact_integer_values() {
    for expression in [
        "ObjectMinCardinality(003 :hasPart :Part)",
        "ObjectMaxCardinality(003 :hasPart :Part)",
        "ObjectExactCardinality(003 :hasPart)",
        "DataMinCardinality(003 :measurement xsd:integer)",
        "DataMaxCardinality(003 :measurement xsd:integer)",
        "DataExactCardinality(003 :measurement)",
    ] {
        let source = format!("# Geräte\n{expression}").into_bytes();
        let mut tokens = match lex(&source, 20) {
            LexResult::Tokens(tokens) => tokens,
            _ => panic!("all complete cardinality token contexts must be accepted"),
        };
        let mut numbers = Vec::new();
        while let Tokens::Cons { token, next } = tokens {
            if matches!(token.terminal, Terminal::Integer) {
                assert_eq!(&source[token.start..token.end], b"003");
                let number = decimal::read_span(&source, token.start, token.end)
                    .unwrap_or_else(|_| panic!("every integer in the stream must have a value"));
                numbers.push(small_value(&number));
            }
            tokens = *next;
        }
        assert_eq!(numbers, [3]);
    }
}

#[test]
fn invalid_integer_contexts_do_not_expose_a_successful_partial_stream() {
    for source in [
        "ObjectMinCardinality(003x :hasPart :Part)",
        "ObjectMinCardinality(-3 :hasPart :Part)",
        "ObjectMinCardinality(٣ :hasPart :Part)",
        "ObjectMinCardinality(３ :hasPart :Part)",
        "ObjectMinCardinality(003 :hasPart :Part) 10abc",
    ] {
        assert!(!matches!(
            lex(&source.as_bytes().to_vec(), 20),
            LexResult::Tokens(_)
        ));
    }
}
