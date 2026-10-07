//! The ASCII scanners for prefix names and abbreviated IRIs agree with the
//! grammar-based greatest-prefix matcher whenever they answer, and the
//! validated-text matcher that uses them agrees with the standard one.
use rowl_frontend::functional::{
    grammar, longest, longest_valid, next_terminal, next_terminal_fast, recognize, Selection,
    Terminal,
};
use rowl_frontend::longest::PrefixResult;
use rowl_frontend::names::{
    ascii_abbreviated, ascii_prefix, full_iri, validate_abbreviated, validate_local,
    validate_prefix,
};
use rowl_frontend::regular::{matches_utf8, MatchResult};
use rowl_frontend::unicode::TextError;
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

/// Mostly name pieces, for buffers that are often whole names.
const NAME_PIECES: [&str; 16] = [
    "a", "Z", "q7", "0", "_", "-", ".", ":", "x:", ":y", "é", "·", "\u{300}", "𐀀", " ", "(",
];

fn outcome(result: MatchResult) -> Result<bool, (u8, usize)> {
    match result {
        MatchResult::Matched(value) => Ok(value),
        MatchResult::MalformedUtf8(TextError::InvalidPosition { offset }) => Err((0, offset)),
        MatchResult::MalformedUtf8(TextError::InvalidUtf8 { offset }) => Err((1, offset)),
        MatchResult::MalformedUtf8(TextError::NonXmlCharacter { offset, .. }) => Err((2, offset)),
    }
}

fn by_grammar(terminal: Terminal, bytes: &Vec<u8>) -> Result<bool, (u8, usize)> {
    outcome(matches_utf8(grammar(terminal), bytes))
}

#[test]
fn whole_name_recognition_agrees_with_the_grammars() {
    let mut seed = Seed(11);
    let mut accepted = 0;
    for _ in 0..3000 {
        let mut bytes: Vec<u8> = (0..seed.next(6))
            .flat_map(|_| NAME_PIECES[seed.next(NAME_PIECES.len())].bytes())
            .collect();
        if seed.next(8) == 0 {
            let at = seed.next(bytes.len() + 1);
            bytes.insert(at, 0xff);
        }
        for terminal in [Terminal::PrefixName, Terminal::AbbreviatedIri] {
            let expected = by_grammar(terminal, &bytes);
            assert_eq!(outcome(recognize(terminal, &bytes)), expected, "{bytes:?}");
            if expected == Ok(true) {
                accepted += 1;
            }
        }
        assert_eq!(
            outcome(validate_prefix(&bytes)),
            by_grammar(Terminal::PrefixName, &bytes),
            "{bytes:?}"
        );
        assert_eq!(
            outcome(validate_abbreviated(&bytes)),
            by_grammar(Terminal::AbbreviatedIri, &bytes),
            "{bytes:?}"
        );
        // A local name is exactly what follows the empty prefix name `:`.
        let mut prefixed = vec![b':'];
        prefixed.extend_from_slice(&bytes);
        let local = outcome(validate_local(&bytes));
        match by_grammar(Terminal::AbbreviatedIri, &prefixed) {
            Ok(value) => assert_eq!(local, Ok(value), "{bytes:?}"),
            Err((kind, offset)) => assert_eq!(local, Err((kind, offset - 1)), "{bytes:?}"),
        }
    }
    assert!(accepted > 200, "{accepted} accepted");
}

/// Pieces of full IRI tokens: brackets, scheme and authority delimiters, path,
/// query and fragment characters, percent escapes (valid and not), IP literal
/// brackets, characters outside ASCII (`é` is allowed, U+E000 only in queries,
/// U+FFFE nowhere) and characters no IRI has (space, `"`, `{`, `|`).
const IRI_PIECES: [&str; 30] = [
    "<", ">", "<>", "http:", "a:", "//", "/", "a", "Z9", ".", "-", "~", "?", "#", "%20", "%G1",
    "@", ":", "[", "]", "::1", "é", "\u{e000}", "\u{fffe}", " ", "\"", "{", "|", "x:y", "\n",
];

#[test]
fn full_iri_scanner_agrees_with_the_grammar() {
    let mut seed = Seed(11);
    let mut matched = 0;
    let mut refused = 0;
    for _ in 0..3000 {
        // Mostly token-shaped text: `<`, a scheme, random pieces and `>`.
        let mut text = String::new();
        if seed.next(4) != 0 {
            text.push('<');
            text.push_str(["http:", "a:", "urn:x:", "x+y.z-1:"][seed.next(4)]);
        }
        for _ in 0..seed.next(8) {
            text.push_str(IRI_PIECES[seed.next(IRI_PIECES.len())]);
        }
        if seed.next(3) != 0 {
            text.push('>');
        }
        for _ in 0..seed.next(3) {
            text.push_str(IRI_PIECES[seed.next(IRI_PIECES.len())]);
        }
        let bytes = text.as_bytes().to_vec();
        let starts = text
            .char_indices()
            .map(|(index, _)| index)
            .chain(std::iter::once(text.len()));
        for position in starts {
            let expected = endpoint(longest(Terminal::FullIri, &bytes, position));
            let actual = endpoint(longest_valid(Terminal::FullIri, &bytes, position));
            assert_eq!(actual, expected, "{text:?} at {position}");
            if let Some(result) = full_iri(&bytes, position) {
                assert_eq!(endpoint(result), expected, "{text:?} at {position}");
                if expected.is_some() {
                    matched += 1;
                } else {
                    refused += 1;
                }
            }
        }
    }
    assert!(
        matched > 500 && refused > 500,
        "{matched} matched, {refused} refused"
    );
    for (text, end) in [
        ("<http://example.org/a#b> ", Some(24)),
        ("<urn:x>>", Some(7)),
        ("<a:b c>", None),
        ("<a:b", None),
        ("<a:%G1>", None),
        ("<http://[::1]/é?q#f>", Some(21)),
        ("<rel/ative>", None),
    ] {
        let bytes = text.as_bytes().to_vec();
        assert_eq!(
            endpoint(longest(Terminal::FullIri, &bytes, 0)),
            end,
            "{text:?}"
        );
        assert_eq!(
            endpoint(full_iri(&bytes, 0).expect("a `<` decides")),
            end,
            "{text:?}"
        );
    }
    assert!(full_iri(&b"a:b".to_vec(), 0).is_none());
}
