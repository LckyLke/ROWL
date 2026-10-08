use rowl_kernel::lang_ranges::{basic_range, free_tags, lowered, range_matches, root_free};

fn bytes(text: &str) -> Vec<u8> {
    text.as_bytes().to_vec()
}

fn ranges(texts: &[&str]) -> Vec<Vec<u8>> {
    texts.iter().map(|text| bytes(text)).collect()
}

#[test]
fn basic_ranges_follow_rfc_4647() {
    for range in ["*", "en", "EN-gb", "x-a1", "abcdefgh-12345678", "de-1996"] {
        assert!(basic_range(&bytes(range)), "{range}");
    }
    for range in [
        "",
        "-",
        "en-",
        "-en",
        "en--gb",
        "1en",
        "abcdefghi",
        "en-123456789",
        "en_GB",
        "e*",
        "**",
    ] {
        assert!(!basic_range(&bytes(range)), "{range}");
    }
    assert_eq!(lowered(&bytes("EN-Gb-1A")), bytes("en-gb-1a"));
}

#[test]
fn ranges_match_tags_by_basic_filtering() {
    assert!(range_matches(&bytes("*"), &bytes("de")));
    assert!(range_matches(&bytes("en"), &bytes("en")));
    assert!(range_matches(&bytes("en"), &bytes("en-gb")));
    assert!(!range_matches(&bytes("en"), &bytes("eng")));
    assert!(!range_matches(&bytes("en-gb"), &bytes("en")));
    assert!(!range_matches(&bytes("en"), &bytes("de")));
}

#[test]
fn free_tags_are_found_along_the_grammar() {
    // No well-formed tag is `a` or continues it; `x` has private-use tags.
    assert!(!free_tags(&bytes("a"), &ranges(&["a"])));
    assert!(free_tags(&bytes("x"), &ranges(&["x"])));
    // `en` itself is free of `en-gb`.
    assert!(free_tags(&bytes("en"), &ranges(&["en", "en-gb"])));
    // The grandfathered tags `i-…` are the only tags that `i` matches.
    let mut all = vec!["i"];
    all.extend([
        "i-ami",
        "i-bnn",
        "i-default",
        "i-enochian",
        "i-hak",
        "i-klingon",
        "i-lux",
        "i-mingo",
        "i-navajo",
        "i-pwn",
        "i-tao",
        "i-tay",
        "i-tsu",
    ]);
    assert!(!free_tags(&bytes("i"), &ranges(&all)));
    assert!(free_tags(&bytes("i"), &ranges(&all[..13])));
    // Some tag matches none of a few ranges, so `*` has tags free of them.
    assert!(root_free(&ranges(&["en", "de", "x"])));
    assert!(free_tags(&bytes("*"), &ranges(&["*", "en"])));
}
