use rowl_kernel::references::{is_reference, resolve, split, Parts, Span};

const BASE: &str = "http://a/b/c/d;p?q";

fn resolved(base: &str, reference: &str) -> Option<String> {
    resolve(&base.as_bytes().to_vec(), &reference.as_bytes().to_vec())
        .map(|bytes| String::from_utf8(bytes).expect("resolution keeps UTF-8"))
}

fn check(cases: &[(&str, &str)]) {
    for (reference, target) in cases {
        assert_eq!(
            resolved(BASE, reference).as_deref(),
            Some(*target),
            "resolving {reference:?}"
        );
    }
}

/// RFC 3986 section 5.4.1.
#[test]
fn normal_examples() {
    check(&[
        ("g:h", "g:h"),
        ("g", "http://a/b/c/g"),
        ("./g", "http://a/b/c/g"),
        ("g/", "http://a/b/c/g/"),
        ("/g", "http://a/g"),
        ("//g", "http://g"),
        ("?y", "http://a/b/c/d;p?y"),
        ("g?y", "http://a/b/c/g?y"),
        ("#s", "http://a/b/c/d;p?q#s"),
        ("g#s", "http://a/b/c/g#s"),
        ("g?y#s", "http://a/b/c/g?y#s"),
        (";x", "http://a/b/c/;x"),
        ("g;x", "http://a/b/c/g;x"),
        ("g;x?y#s", "http://a/b/c/g;x?y#s"),
        ("", "http://a/b/c/d;p?q"),
        (".", "http://a/b/c/"),
        ("./", "http://a/b/c/"),
        ("..", "http://a/b/"),
        ("../", "http://a/b/"),
        ("../g", "http://a/b/g"),
        ("../..", "http://a/"),
        ("../../", "http://a/"),
        ("../../g", "http://a/g"),
    ]);
}

/// RFC 3986 section 5.4.2, with the strict reading of "http:g".
#[test]
fn abnormal_examples() {
    check(&[
        ("../../../g", "http://a/g"),
        ("../../../../g", "http://a/g"),
        ("/./g", "http://a/g"),
        ("/../g", "http://a/g"),
        ("g.", "http://a/b/c/g."),
        (".g", "http://a/b/c/.g"),
        ("g..", "http://a/b/c/g.."),
        ("..g", "http://a/b/c/..g"),
        ("./../g", "http://a/b/g"),
        ("./g/.", "http://a/b/c/g/"),
        ("g/./h", "http://a/b/c/g/h"),
        ("g/../h", "http://a/b/c/h"),
        ("g;x=1/./y", "http://a/b/c/g;x=1/y"),
        ("g;x=1/../y", "http://a/b/c/y"),
        ("g?y/./x", "http://a/b/c/g?y/./x"),
        ("g?y/../x", "http://a/b/c/g?y/../x"),
        ("g#s/./x", "http://a/b/c/g#s/./x"),
        ("g#s/../x", "http://a/b/c/g#s/../x"),
        ("http:g", "http:g"),
    ]);
}

/// Absolute references also lose their dot segments; bases without an
/// authority merge without a leading slash; non-ASCII characters are opaque.
#[test]
fn further_cases() {
    assert_eq!(
        resolved(BASE, "http://x/a/../b/./c").as_deref(),
        Some("http://x/b/c")
    );
    assert_eq!(resolved("a:b", "c").as_deref(), Some("a:c"));
    assert_eq!(resolved("a:b/c", "d").as_deref(), Some("a:b/d"));
    assert_eq!(resolved("a:", "d").as_deref(), Some("a:d"));
    assert_eq!(resolved("http://a", "b").as_deref(), Some("http://a/b"));
    assert_eq!(resolved("http://a", "").as_deref(), Some("http://a"));
    assert_eq!(
        resolved("http://ä/ö/ü", "ß/../é").as_deref(),
        Some("http://ä/ö/é")
    );
    assert_eq!(
        resolved("http://a/b", "#ö").as_deref(),
        Some("http://a/b#ö")
    );
    // The RFC algorithm can produce a path that starts with "//" and no authority.
    assert_eq!(resolved("a:b", "/.//:a").as_deref(), Some("a://:a"));
    // A reference without a scheme needs a base with one; one with a scheme
    // needs no base.
    assert_eq!(resolved("//a/b", "c"), None);
    assert_eq!(resolved("", "c"), None);
    assert_eq!(resolved("", "x:y/./z").as_deref(), Some("x:y/z"));
    assert_eq!(
        resolved("//a/b", "http://h/p/../q#f").as_deref(),
        Some("http://h/q#f")
    );
}

fn span(bytes: &[u8], span: Option<Span>) -> Option<String> {
    span.map(|span| String::from_utf8(bytes[span.start..span.end].to_vec()).unwrap())
}

fn parts(text: &str) -> [Option<String>; 5] {
    let bytes = text.as_bytes().to_vec();
    let parts: Parts = split(&bytes);
    [
        span(&bytes, parts.scheme),
        span(&bytes, parts.authority),
        span(&bytes, Some(parts.path)),
        span(&bytes, parts.query),
        span(&bytes, parts.fragment),
    ]
}

fn some(text: &str) -> Option<String> {
    Some(text.to_string())
}

/// RFC 3986 Appendix B.
#[test]
fn appendix_b_components() {
    assert_eq!(
        parts("http://www.ics.uci.edu/pub/ietf/uri/#Related"),
        [
            some("http"),
            some("www.ics.uci.edu"),
            some("/pub/ietf/uri/"),
            None,
            some("Related")
        ]
    );
    assert_eq!(parts(""), [None, None, some(""), None, None]);
    assert_eq!(parts("?#"), [None, None, some(""), some(""), some("")]);
    assert_eq!(parts(":a"), [None, None, some(":a"), None, None]);
    assert_eq!(parts("a/b:c"), [None, None, some("a/b:c"), None, None]);
    assert_eq!(parts("//"), [None, some(""), some(""), None, None]);
    assert_eq!(
        parts("a:b?c?d#e#f"),
        [some("a"), None, some("b"), some("c?d"), some("e#f")]
    );
}

#[test]
fn references_are_recognized() {
    for text in [
        "",
        "#",
        "#a/b",
        "a",
        "a/b",
        "/a",
        "//a/b",
        "../a",
        "a#b",
        "http://a/b",
        "x:y",
        "?q",
        "a?b#c",
        "%41",
        "ö",
        "a@b",
        "a:b:c",
    ] {
        assert!(is_reference(&text.as_bytes().to_vec()), "{text:?}");
    }
    for text in ["a b", "%4", "a#b#c", ":a", "a:b/c:d^", "[", "\u{0}", "a\\b"] {
        assert!(!is_reference(&text.as_bytes().to_vec()), "{text:?}");
    }
    assert!(!is_reference(&vec![0xff]));
}
