use rowl_kernel::pattern_counts::{automaton, profile_count, Automaton};
use rowl_kernel::patterns::pattern_expression;

fn joint(patterns: &[&str]) -> Automaton {
    let expressions = patterns
        .iter()
        .map(|p| pattern_expression(&p.as_bytes().to_vec()).expect("a regular expression"))
        .collect();
    automaton(&expressions).expect("an automaton")
}

fn count(
    auto: &Automaton,
    first: u8,
    last: u8,
    profile: &[bool],
    low: usize,
    high: Option<usize>,
    cap: usize,
) -> usize {
    profile_count(auto, first, last, &profile.to_vec(), low, high, cap).expect("settled counts")
}

#[test]
fn finite_and_infinite_patterns() {
    let auto = joint(&["a|b"]);
    assert_eq!(count(&auto, 0, 7, &[true], 0, None, 100), 2);
    assert_eq!(count(&auto, 0, 7, &[false], 0, None, 100), 100);
    assert_eq!(count(&auto, 0, 7, &[true], 2, None, 100), 0);
    let auto = joint(&["[0-9]{2}"]);
    assert_eq!(count(&auto, 0, 7, &[true], 0, None, 1000), 100);
    assert_eq!(count(&auto, 0, 7, &[true], 0, None, 50), 50);
    let auto = joint(&["(ab)*"]);
    assert_eq!(count(&auto, 0, 7, &[true], 0, Some(5), 100), 3);
    assert_eq!(count(&auto, 0, 7, &[true], 0, None, 100), 100);
    assert_eq!(count(&auto, 0, 7, &[true], 3, Some(4), 100), 0);
    let auto = joint(&[""]);
    assert_eq!(count(&auto, 0, 7, &[true], 0, None, 100), 1);
}

#[test]
fn combinations_of_patterns() {
    let auto = joint(&["a*", "b*"]);
    assert_eq!(count(&auto, 0, 7, &[true, true], 0, None, 100), 1);
    assert_eq!(count(&auto, 0, 7, &[true, false], 0, None, 100), 100);
    assert_eq!(count(&auto, 0, 7, &[true, false], 0, Some(4), 100), 3);
    let auto = joint(&["[a-c]", "[b-d]", "[^b]"]);
    assert_eq!(count(&auto, 0, 7, &[true, true, false], 0, None, 100), 1);
    assert_eq!(count(&auto, 0, 7, &[true, true, true], 0, None, 100), 1);
    assert_eq!(count(&auto, 0, 7, &[true, false, true], 0, None, 100), 1);
    assert_eq!(count(&auto, 0, 7, &[false, true, true], 0, None, 100), 1);
}

#[test]
fn ranks_of_strings() {
    // "a b" is a token but no name token; "ab" is a language tag.
    let auto = joint(&["a b|ab"]);
    assert_eq!(count(&auto, 2, 3, &[true], 0, None, 100), 1);
    assert_eq!(count(&auto, 6, 7, &[true], 0, None, 100), 1);
    assert_eq!(count(&auto, 3, 6, &[true], 0, None, 100), 0);
    // The empty string is a token and no name token.
    let auto = joint(&[""]);
    assert_eq!(count(&auto, 2, 3, &[true], 0, None, 100), 1);
    assert_eq!(count(&auto, 0, 2, &[true], 0, None, 100), 0);
    // Tab, line feed and carriage return are the strings of one character
    // that are no normalized strings; `.` takes the tab only.
    let auto = joint(&["."]);
    assert_eq!(count(&auto, 0, 1, &[true], 0, None, 100), 1);
    assert_eq!(count(&auto, 0, 1, &[false], 1, Some(2), 100), 2);
}
