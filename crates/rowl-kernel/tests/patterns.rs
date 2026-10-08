use rowl_kernel::patterns::{pattern_expression, pattern_matches};

fn matches(pattern: &str, text: &str) -> bool {
    let expression = pattern_expression(&pattern.as_bytes().to_vec())
        .unwrap_or_else(|| panic!("no expression for {pattern:?}"));
    pattern_matches(&expression, &text.as_bytes().to_vec()).unwrap()
}

fn read(pattern: &str) -> bool {
    pattern_expression(&pattern.as_bytes().to_vec()).is_some()
}

#[test]
fn branches_pieces_and_quantifiers() {
    assert!(matches("abc", "abc"));
    assert!(!matches("abc", "ab"));
    assert!(matches("", ""));
    assert!(!matches("", "a"));
    assert!(matches("a|b", "b"));
    assert!(matches("a|", ""));
    assert!(matches("(ab)*", "ababab"));
    assert!(!matches("(ab)*", "aba"));
    assert!(matches("a+b?", "aaab"));
    assert!(!matches("a+b?", "b"));
    assert!(matches("a{2,3}", "aaa"));
    assert!(!matches("a{2,3}", "aaaa"));
    assert!(!matches("a{2,3}", "a"));
    assert!(matches("a{2}", "aa"));
    assert!(matches("a{2,}", "aaaaa"));
    assert!(!matches("a{2,}", "a"));
    assert!(matches("x{0}", ""));
    assert!(matches("a{007}", "aaaaaaa"));
    assert!(matches("(a|bc){0,2}d", "bcad"));
    assert!(matches("é+", "éé"));
}

#[test]
fn character_classes() {
    assert!(matches("[a-z]+", "hello"));
    assert!(!matches("[a-z]+", "Hello"));
    assert!(matches("[^a]", "b"));
    assert!(!matches("[^a]", "a"));
    assert!(matches("[^^]", "a"));
    assert!(!matches("[^^]", "^"));
    assert!(matches("[a^]", "^"));
    assert!(matches("[a-z-[aeiou]]", "b"));
    assert!(!matches("[a-z-[aeiou]]", "e"));
    assert!(matches("[a-]", "-"));
    assert!(matches("[-a]", "-"));
    assert!(matches("[--]", "-"));
    assert!(matches("[a-k-z]", "-"));
    assert!(matches("[a-k-z]", "z"));
    assert!(!matches("[a-k-z]", "m"));
    assert!(matches("[a--[a]]", "-"));
    assert!(!matches("[a--[a]]", "a"));
    assert!(matches("[\\--z]", "a"));
    assert!(matches("[+-\\-]", ","));
    assert!(matches("\\s\\S", " x"));
    assert!(!matches("\\s", "x"));
    assert!(matches("\\i\\c*", "_a.b-1"));
    assert!(!matches("\\i", "1"));
    assert!(matches("\\I", "1"));
    assert!(matches("\\C", " "));
    assert!(matches(".*", "any text"));
    assert!(!matches(".", "\n"));
    assert!(matches("\\n\\t\\.", "\n\t."));
    assert!(matches("[\\n\\]]", "]"));
    assert!(matches("[\\s-[ ]]", "\t"));
    assert!(!matches("[\\s-[ ]]", " "));
    assert!(matches("[^\\s]", "x"));
    assert!(matches("[^a-[b]]", "c"));
    assert!(!matches("[^a-[b]]", "b"));
}

#[test]
fn invalid_expressions_and_left_out_escapes() {
    for pattern in [
        "a**",
        "a{3,2}",
        "a{,2}",
        "{",
        "]",
        "[]",
        "[^]",
        "[--z]",
        "[a--]",
        "[a-\\d]",
        "(a",
        "a)",
        "\\q",
        "[a-[b]x]",
        "a{x}",
        "[[]",
        "*",
        "a|*",
        "[a-z-[aeiou]",
    ] {
        assert!(!read(pattern), "{pattern:?} should give no expression");
    }
    for pattern in [
        "\\d",
        "\\D",
        "\\w",
        "\\W",
        "\\p{L}",
        "\\P{IsBasicLatin}",
        "[\\d]",
    ] {
        assert!(!read(pattern), "{pattern:?} needs the Unicode database");
    }
    assert!(!read("(a{1000}){1000}"));
    assert!(read("a{1000}"));
}
