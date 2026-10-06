//! The ASCII scanners for prefix names and abbreviated IRIs agree with the
//! grammar-based greatest-prefix matcher whenever they answer, and the
//! validated-text matcher that uses them agrees with the standard one.
use rowl_frontend::functional::{
    longest, longest_valid, next_terminal, next_terminal_fast, Selection, Terminal,
};
use rowl_frontend::longest::PrefixResult;
use rowl_frontend::names::{ascii_abbreviated, ascii_prefix};
use std::mem::discriminant;

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

/// ASCII name characters, dots and colons, delimiters and whitespace, and
/// letters, marks and other characters outside ASCII, some of them name
/// characters (`é`, `·`, the combining grave accent, `‿`, `𐀀`, `Ω`) and some
/// not (`×`).
const PIECES: [&str; 32] = [
    "a", "Z", "q", "0", "7", "_", "-", ".", ":", "..", "a.", ".b", "x:", ":y", "ab", "é", "·",
    "\u{300}", "\u{203f}", "𐀀", "Ω", "×", "(", ")", " ", "\n", "<", ">", "#", "\"", "@", "^",
];

fn endpoint(result: PrefixResult) -> Option<usize> {
    match result {
        PrefixResult::Matched(end) => end,
        PrefixResult::MalformedUtf8(_) => panic!("a Rust str is valid UTF-8"),
    }
}

type Shape = (
    std::mem::Discriminant<Terminal>,
    Option<std::mem::Discriminant<rowl_frontend::functional::Keyword>>,
    usize,
    usize,
);

fn shape(selection: Selection) -> Option<Shape> {
    match selection {
        Selection::NoMatch => None,
        Selection::Token(token) => {
            let keyword = match token.terminal {
                Terminal::Keyword(keyword) => Some(discriminant(&keyword)),
                _ => None,
            };
            Some((
                discriminant(&token.terminal),
                keyword,
                token.start,
                token.end,
            ))
        }
        Selection::MalformedUtf8(_) => panic!("a Rust str is valid UTF-8"),
    }
}

#[test]
fn ascii_name_scanners_agree_with_the_grammars() {
    let mut seed = Seed(7);
    let mut answered = 0;
    let mut matched = 0;
    let mut declined = 0;
    for round in 0..3000 {
        let text: String = (0..seed.next(9))
            .map(|_| PIECES[seed.next(PIECES.len())])
            .collect();
        let bytes = text.as_bytes().to_vec();
        let starts = text
            .char_indices()
            .map(|(index, _)| index)
            .chain(std::iter::once(text.len()));
        for position in starts {
            for terminal in [Terminal::PrefixName, Terminal::AbbreviatedIri] {
                let expected = endpoint(longest(terminal, &bytes, position));
                let actual = endpoint(longest_valid(terminal, &bytes, position));
                assert_eq!(actual, expected, "{text:?} at {position}");
                let fast = match terminal {
                    Terminal::PrefixName => ascii_prefix(&bytes, position),
                    _ => ascii_abbreviated(&bytes, position),
                };
                match fast {
                    Some(result) => {
                        assert_eq!(endpoint(result), expected, "{text:?} at {position}");
                        answered += 1;
                        if expected.is_some() {
                            matched += 1;
                        }
                    }
                    None => declined += 1,
                }
            }
            if round % 10 == 0 {
                assert_eq!(
                    shape(next_terminal_fast(&bytes, position)),
                    shape(next_terminal(&bytes, position)),
                    "{text:?} at {position}"
                );
            }
        }
    }
    assert!(
        answered > 20000 && matched > 2000 && declined > 2000,
        "{answered} answered, {matched} matched, {declined} declined"
    );
}

#[test]
fn ascii_name_scanners_on_typical_names() {
    for (text, prefix, abbreviated) in [
        (":C123 ", Some(1), Some(5)),
        ("owl:Thing)", Some(4), Some(9)),
        ("a.b:c.d. ", Some(4), Some(7)),
        ("ab.:x", None, None),
        ("1a:b", None, None),
        ("_:b1", None, None),
        (":", Some(1), None),
        (":-a", Some(1), None),
        (":.a", Some(1), None),
        (":_a.", Some(1), Some(3)),
        ("x:9", Some(2), Some(3)),
        ("x::y", Some(2), None),
        ("SubClassOf(", None, None),
    ] {
        let bytes = text.as_bytes().to_vec();
        let found = |result: Option<PrefixResult>| endpoint(result.expect("ASCII decides"));
        assert_eq!(found(ascii_prefix(&bytes, 0)), prefix, "{text:?}");
        assert_eq!(found(ascii_abbreviated(&bytes, 0)), abbreviated, "{text:?}");
    }
    for text in ["é:x", "aé:x", "a:é", "a:bé", "a:b.\u{300}"] {
        let bytes = text.as_bytes().to_vec();
        assert!(ascii_abbreviated(&bytes, 0).is_none(), "{text:?}");
    }
    assert!(ascii_prefix(&"aé:x".as_bytes().to_vec(), 0).is_none());
    assert!(ascii_prefix(&"a:é".as_bytes().to_vec(), 0).is_some());
}
