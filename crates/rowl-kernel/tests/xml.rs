//! Regression tests for the XML layer of the RDF/XML reader.
use rowl_kernel::xml::{read, Element, ErrorKind, Limits, Node, ReadResult};

fn text(word: &[u32]) -> String {
    word.iter().map(|&c| char::from_u32(c).unwrap()).collect()
}

fn option(word: &Option<Vec<u32>>) -> String {
    match word {
        Some(w) => text(w),
        None => "-".to_string(),
    }
}

/// A compact rendering of an element tree: `{ns}local[attrs](children)`.
fn render(e: &Element) -> String {
    let mut out = format!("{{{}}}{}", option(&e.ns_name), text(&e.local_name));
    if !e.attributes.is_empty() {
        out.push('[');
        for (k, a) in e.attributes.iter().enumerate() {
            if k > 0 {
                out.push(' ');
            }
            out.push_str(&format!(
                "{{{}}}{}={:?}",
                option(&a.ns_name),
                text(&a.local_name),
                text(&a.value)
            ));
        }
        out.push(']');
    }
    if !e.children.is_empty() {
        out.push('(');
        for (k, child) in e.children.iter().enumerate() {
            if k > 0 {
                out.push(' ');
            }
            match child {
                Node::Element(c) => out.push_str(&render(c)),
                Node::Text(t) => out.push_str(&format!("{:?}", text(t))),
            }
        }
        out.push(')');
    }
    out
}

fn parse(source: &str) -> Result<String, ErrorKind> {
    match read(&source.as_bytes().to_vec(), &Limits { expansion: 1 << 20 }) {
        ReadResult::Document(d) => Ok(render(&d.root)),
        ReadResult::Error(e) => Err(e.kind),
    }
}

fn accepts(source: &str, expected: &str) {
    match parse(source) {
        Ok(tree) => assert_eq!(tree, expected, "{source}"),
        Err(kind) => panic!("rejected {source:?}: {}", std::any::type_name_of_val(&kind)),
    }
}

fn rejects(source: &str) -> ErrorKind {
    match parse(source) {
        Ok(tree) => panic!("accepted {source:?} as {tree}"),
        Err(kind) => kind,
    }
}

#[test]
fn elements_attributes_and_text() {
    accepts("<a/>", "{-}a");
    accepts("<a></a>", "{-}a");
    accepts("<a x='1' y=\"2\"/>", "{-}a[{-}x=\"1\" {-}y=\"2\"]");
    accepts(
        "<?xml version=\"1.0\" encoding=\"utf-8\" standalone='yes'?>\n<a>hi<b/>there</a>\n",
        "{-}a(\"hi\" {-}b \"there\")",
    );
    accepts("<a>x<!-- c -->y<?p d?>z</a>", "{-}a(\"xyz\")");
    accepts("<a><![CDATA[<&]]]]></a>", "{-}a(\"<&]]\")");
    accepts("<a>&lt;&#65;&#x42;&amp;</a>", "{-}a(\"<AB&\")");
    accepts(
        "<a\r\nb='x\r\ny\tz'>1\r2\r\n3</a\n>",
        "{-}a[{-}b=\"x y z\"](\"1\\n2\\n3\")",
    );
    accepts("\u{feff}<a/>", "{-}a");
    accepts("<a b='&#10;'/>", "{-}a[{-}b=\"\\n\"]");
}

#[test]
fn namespaces() {
    accepts(
        "<r:a xmlns:r='urn:r' xmlns='urn:d'><b r:c='1' d='2'/><e xmlns=''/></r:a>",
        "{urn:r}a({urn:d}b[{urn:r}c=\"1\" {-}d=\"2\"] {-}e)",
    );
    accepts(
        "<a xml:lang='en'/>",
        "{-}a[{http://www.w3.org/XML/1998/namespace}lang=\"en\"]",
    );
    assert!(matches!(rejects("<p:a/>"), ErrorKind::UndeclaredPrefix));
    assert!(matches!(
        rejects("<a xmlns:p=''/>"),
        ErrorKind::ReservedNamespace
    ));
    assert!(matches!(
        rejects("<a xmlns:p='urn:x' xmlns:q='urn:x' p:b='1' q:b='2'/>"),
        ErrorKind::DuplicateAttribute
    ));
    assert!(matches!(
        rejects("<a b='1' b='2'/>"),
        ErrorKind::DuplicateAttribute
    ));
    assert!(matches!(
        rejects("<a:b:c xmlns:a='u'/>"),
        ErrorKind::InvalidName
    ));
    assert!(matches!(
        rejects("<xmlns:a xmlns:xmlns='u'/>"),
        ErrorKind::ReservedNamespace
    ));
}

#[test]
fn entities() {
    let dtd = "<!DOCTYPE r [\n  <!ENTITY owl \"http://www.w3.org/2002/07/owl#\" >\n  <!ENTITY e '&owl;Thing'>\n  <!ENTITY m '<b x=\"&owl;\"/>t'>\n  <!ENTITY % p 'ignored'>\n  <!ENTITY x SYSTEM 'x.xml'>\n  <!-- c --><?pi?>\n]>\n";
    accepts(
        &format!("{dtd}<r a='&owl;Class'>&e;</r>"),
        "{-}r[{-}a=\"http://www.w3.org/2002/07/owl#Class\"](\"http://www.w3.org/2002/07/owl#Thing\")",
    );
    accepts(
        &format!("{dtd}<r>1&m;2</r>"),
        "{-}r(\"1\" {-}b[{-}x=\"http://www.w3.org/2002/07/owl#\"] \"t2\")",
    );
    assert!(matches!(
        rejects(&format!("{dtd}<r>&x;</r>")),
        ErrorKind::UndeclaredEntity
    ));
    assert!(matches!(rejects("<r>&u;</r>"), ErrorKind::UndeclaredEntity));
    assert!(matches!(
        rejects("<!DOCTYPE r [<!ENTITY a '&b;'><!ENTITY b '&a;'>]><r>&a;</r>"),
        ErrorKind::RecursiveEntity
    ));
    rejects("<!DOCTYPE r [<!ENTITY a '<b>'>]><r>&a;</r>");
    assert!(matches!(
        rejects("<!DOCTYPE r [<!ENTITY a '</r>'>]><r>&a;</r>"),
        ErrorKind::EntityBoundary
    ));
    assert!(matches!(
        rejects("<!DOCTYPE r [<!ENTITY a '<b>'>]><r x='&a;'/>"),
        ErrorKind::Syntax
    ));
    assert!(matches!(
        rejects("<!DOCTYPE r [<!ELEMENT r ANY>]><r/>"),
        ErrorKind::UnsupportedDeclaration
    ));
    // Attribute-value normalization of §3.3.3 and its example.
    accepts(
        "<!DOCTYPE r [<!ENTITY d '&#xD;'><!ENTITY a '&#xA;'><!ENTITY da '&#xD;&#xA;'>]><r a=\"&d;&d;A&a;&#x20;&a;B&da;\" b='&#xd;&#xd;A&#xa;&#xa;B&#xd;&#xa;'/>",
        "{-}r[{-}a=\"  A   B  \" {-}b=\"\\r\\rA\\n\\nB\\r\\n\"]",
    );
    // The billion laughs stop at the budget.
    let mut laughs = String::from("<!DOCTYPE r [<!ENTITY l0 'ha'>");
    for k in 1..10 {
        laughs.push_str(&format!(
            "<!ENTITY l{k} '{}'>",
            format!("&l{};", k - 1).repeat(10)
        ));
    }
    laughs.push_str("]><r>&l9;</r>");
    assert!(matches!(rejects(&laughs), ErrorKind::ResourceLimit));
}

#[test]
fn malformed_documents() {
    for source in [
        "",
        "<a>",
        "<a></b>",
        "<a/><b/>",
        "<a>]]></a>",
        "<a><!-- a -- b --></a>",
        "<a><?xml x?></a>",
        " <?xml version='1.0'?><a/>",
        "<a x='<'/>",
        "<a x=1/>",
        "<a>&#0;</a>",
        "<a>&#xD800;</a>",
        "<a>&#99999999999;</a>",
        "<a b='1'c='2'/>",
        "<?xml version='2.0'?><a/>",
    ] {
        rejects(source);
    }
    assert!(matches!(
        rejects("<?xml version='1.0' encoding='ISO-8859-1'?><a/>"),
        ErrorKind::UnsupportedEncoding
    ));
    assert!(matches!(
        read(&vec![60, 97, 0xff, 47, 62], &Limits { expansion: 0 }),
        ReadResult::Error(e) if matches!(e.kind, ErrorKind::MalformedUtf8) && e.offset == 2
    ));
    assert!(matches!(
        read(&b"<a>\n\x01</a>".to_vec(), &Limits { expansion: 0 }),
        ReadResult::Error(e) if matches!(e.kind, ErrorKind::NonXmlCharacter) && e.offset == 4
    ));
    assert!(matches!(
        read(&"<a>\r\n\u{e9}</b>".as_bytes().to_vec(), &Limits { expansion: 0 }),
        ReadResult::Error(e) if matches!(e.kind, ErrorKind::MismatchedEndTag) && e.offset == 7
    ));
}
