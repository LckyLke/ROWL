//! Regression tests for the RDF/XML reader: the examples of RDF 1.1 XML
//! Syntax section 2, its productions and the documents it does not accept.
use rowl_kernel::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfIri, Subject};
use rowl_kernel::rdfxml::{read_with_limits, ErrorKind, Limits, ReadResult};

const RDF: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const EX: &str = "http://example.org/stuff/1.0/";
const DC: &str = "http://purl.org/dc/elements/1.1/";
const BASE: &str = "http://example.org/dir/doc";

fn limits() -> Limits {
    Limits {
        expansion: 1 << 20,
        term_bytes: 1 << 20,
        items: 1 << 20,
    }
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("UTF-8 term")
}

fn iri(value: &RdfIri) -> String {
    format!("<{}>", text(&value.spelling))
}

/// Blank nodes print with their scope; generated labels begin with the byte
/// 0xFF, which UTF-8 never contains, and print as `[n]`.
fn blank(node: &BlankNode) -> String {
    let scope = text(&node.scope);
    match node.label.first() {
        Some(255) => format!("{scope}[{}]", text(&node.label[1..])),
        _ => format!("{scope}_:{}", text(&node.label)),
    }
}

fn shown(graph: &RawGraph) -> Vec<String> {
    graph
        .triples
        .iter()
        .map(|triple| {
            let subject = match &triple.subject {
                Subject::Iri(value) => iri(value),
                Subject::Blank(node) => blank(node),
            };
            let object = match &triple.object {
                Object::Iri(value) => iri(value),
                Object::Blank(node) => blank(node),
                Object::Literal(literal) => match &literal.kind {
                    LiteralKind::Datatype(datatype) => {
                        format!("{:?}^^{}", text(&literal.lexical), iri(datatype))
                    }
                    LiteralKind::Language(tag) => {
                        format!("{:?}@{}", text(&literal.lexical), text(tag))
                    }
                },
            };
            format!("{subject} {} {object}", iri(&triple.predicate))
        })
        .collect()
}

fn read(source: &str) -> ReadResult {
    read_with_limits(
        &source.as_bytes().to_vec(),
        &BASE.as_bytes().to_vec(),
        &b"s".to_vec(),
        &limits(),
    )
}

fn graph(source: &str) -> Vec<String> {
    match read(source) {
        ReadResult::Graph(graph) => shown(&graph),
        ReadResult::XmlError(error) => panic!("not XML at byte {}: {source}", error.offset),
        ReadResult::Error(kind) => panic!("rejected ({}): {source}", name(kind)),
    }
}

fn name(kind: ErrorKind) -> &'static str {
    match kind {
        ErrorKind::InvalidName => "InvalidName",
        ErrorKind::UnqualifiedAttribute => "UnqualifiedAttribute",
        ErrorKind::DuplicateAttribute => "DuplicateAttribute",
        ErrorKind::InvalidAttributes => "InvalidAttributes",
        ErrorKind::InvalidContent => "InvalidContent",
        ErrorKind::InvalidId => "InvalidId",
        ErrorKind::DuplicateId => "DuplicateId",
        ErrorKind::InvalidCharacter => "InvalidCharacter",
        ErrorKind::InvalidIri => "InvalidIri",
        ErrorKind::InvalidLanguageTag => "InvalidLanguageTag",
        ErrorKind::InvalidDatatype => "InvalidDatatype",
        ErrorKind::UnsupportedParseType => "UnsupportedParseType",
        ErrorKind::UnsupportedDatatype => "UnsupportedDatatype",
        ErrorKind::ResourceLimit => "ResourceLimit",
    }
}

fn failure(source: &str) -> &'static str {
    match read(source) {
        ReadResult::Graph(graph) => panic!("accepted {source} as {:?}", shown(&graph)),
        ReadResult::XmlError(_) => "XmlError",
        ReadResult::Error(kind) => name(kind),
    }
}

fn lines(expected: &[&str]) -> Vec<String> {
    expected
        .iter()
        .map(|line| {
            line.replace("rdf:", RDF)
                .replace("xsd:", XSD)
                .replace("ex:", EX)
                .replace("dc:", DC)
        })
        .collect()
}

fn document(body: &str) -> String {
    format!(
        "<?xml version=\"1.0\"?>\n<rdf:RDF xmlns:rdf=\"{RDF}\" xmlns:dc=\"{DC}\" xmlns:ex=\"{EX}\">\n{body}\n</rdf:RDF>\n"
    )
}

#[test]
fn specification_examples() {
    // Example 7.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://www.w3.org/TR/rdf-syntax-grammar" dc:title="RDF1.1 XML Syntax">
    <ex:editor>
      <rdf:Description ex:fullName="Dave Beckett">
        <ex:homePage rdf:resource="http://purl.org/net/dajobe/" />
      </rdf:Description>
    </ex:editor>
  </rdf:Description>"#
        )),
        lines(&[
            "<http://www.w3.org/TR/rdf-syntax-grammar> <dc:title> \"RDF1.1 XML Syntax\"^^<xsd:string>",
            "s[0] <ex:fullName> \"Dave Beckett\"^^<xsd:string>",
            "s[0] <ex:homePage> <http://purl.org/net/dajobe/>",
            "<http://www.w3.org/TR/rdf-syntax-grammar> <ex:editor> s[0]",
        ])
    );
    // Example 8.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://www.w3.org/TR/rdf-syntax-grammar">
    <dc:title>RDF 1.1 XML Syntax</dc:title>
    <dc:title xml:lang="en">RDF 1.1 XML Syntax</dc:title>
    <dc:title xml:lang="en-US">RDF 1.1 XML Syntax</dc:title>
  </rdf:Description>
  <rdf:Description rdf:about="http://example.org/buecher/baum" xml:lang="de">
    <dc:title>Der Baum</dc:title>
    <dc:description>Das Buch ist außergewöhnlich</dc:description>
    <dc:title xml:lang="en">The Tree</dc:title>
  </rdf:Description>"#
        )),
        lines(&[
            "<http://www.w3.org/TR/rdf-syntax-grammar> <dc:title> \"RDF 1.1 XML Syntax\"^^<xsd:string>",
            "<http://www.w3.org/TR/rdf-syntax-grammar> <dc:title> \"RDF 1.1 XML Syntax\"@en",
            "<http://www.w3.org/TR/rdf-syntax-grammar> <dc:title> \"RDF 1.1 XML Syntax\"@en-US",
            "<http://example.org/buecher/baum> <dc:title> \"Der Baum\"@de",
            "<http://example.org/buecher/baum> <dc:description> \"Das Buch ist außergewöhnlich\"@de",
            "<http://example.org/buecher/baum> <dc:title> \"The Tree\"@en",
        ])
    );
    // Example 9: XML literals are declined.
    assert_eq!(
        failure(&document(
            r#"<rdf:Description rdf:about="http://example.org/item01">
    <ex:prop rdf:parseType="Literal" xmlns:a="http://example.org/a#"><a:Box required="true"/></ex:prop>
  </rdf:Description>"#
        )),
        "UnsupportedParseType"
    );
    // Example 10.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://example.org/item01">
    <ex:size rdf:datatype="http://www.w3.org/2001/XMLSchema#int">123</ex:size>
  </rdf:Description>"#
        )),
        lines(&["<http://example.org/item01> <ex:size> \"123\"^^<xsd:int>"])
    );
    // Example 11.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://www.w3.org/TR/rdf-syntax-grammar" dc:title="RDF 1.1 XML Syntax">
    <ex:editor rdf:nodeID="abc"/>
  </rdf:Description>
  <rdf:Description rdf:nodeID="abc" ex:fullName="Dave Beckett">
    <ex:homePage rdf:resource="http://purl.org/net/dajobe/"/>
  </rdf:Description>"#
        )),
        lines(&[
            "<http://www.w3.org/TR/rdf-syntax-grammar> <dc:title> \"RDF 1.1 XML Syntax\"^^<xsd:string>",
            "<http://www.w3.org/TR/rdf-syntax-grammar> <ex:editor> s_:abc",
            "s_:abc <ex:fullName> \"Dave Beckett\"^^<xsd:string>",
            "s_:abc <ex:homePage> <http://purl.org/net/dajobe/>",
        ])
    );
    // Example 12.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://www.w3.org/TR/rdf-syntax-grammar" dc:title="RDF 1.1 XML Syntax">
    <ex:editor rdf:parseType="Resource">
      <ex:fullName>Dave Beckett</ex:fullName>
      <ex:homePage rdf:resource="http://purl.org/net/dajobe/"/>
    </ex:editor>
  </rdf:Description>"#
        )),
        lines(&[
            "<http://www.w3.org/TR/rdf-syntax-grammar> <dc:title> \"RDF 1.1 XML Syntax\"^^<xsd:string>",
            "<http://www.w3.org/TR/rdf-syntax-grammar> <ex:editor> s[0]",
            "s[0] <ex:fullName> \"Dave Beckett\"^^<xsd:string>",
            "s[0] <ex:homePage> <http://purl.org/net/dajobe/>",
        ])
    );
    // Example 13.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://www.w3.org/TR/rdf-syntax-grammar" dc:title="RDF 1.1 XML Syntax">
    <ex:editor ex:fullName="Dave Beckett" />
    <!-- Note the ex:homePage property has been ignored for this example -->
  </rdf:Description>"#
        )),
        lines(&[
            "<http://www.w3.org/TR/rdf-syntax-grammar> <dc:title> \"RDF 1.1 XML Syntax\"^^<xsd:string>",
            "s[0] <ex:fullName> \"Dave Beckett\"^^<xsd:string>",
            "<http://www.w3.org/TR/rdf-syntax-grammar> <ex:editor> s[0]",
        ])
    );
    // Examples 14 and 15 give the same graph.
    let typed = lines(&[
        "<http://example.org/thing> <rdf:type> <ex:Document>",
        "<http://example.org/thing> <dc:title> \"A marvelous thing\"^^<xsd:string>",
    ]);
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://example.org/thing">
    <rdf:type rdf:resource="http://example.org/stuff/1.0/Document"/>
    <dc:title>A marvelous thing</dc:title>
  </rdf:Description>"#
        )),
        typed
    );
    assert_eq!(
        graph(&document(
            r#"<ex:Document rdf:about="http://example.org/thing">
    <dc:title>A marvelous thing</dc:title>
  </ex:Document>"#
        )),
        typed
    );
    // Example 16.
    assert_eq!(
        graph(&format!(
            r#"<rdf:RDF xmlns:rdf="{RDF}" xmlns:ex="{EX}" xml:base="http://example.org/here/">
  <rdf:Description rdf:ID="snack">
    <ex:prop rdf:resource="fruit/apple"/>
  </rdf:Description>
</rdf:RDF>"#
        )),
        lines(&[
            "<http://example.org/here/#snack> <ex:prop> <http://example.org/here/fruit/apple>"
        ])
    );
    // Examples 17 and 18 give the same graph.
    let sequence = lines(&[
        "<http://example.org/favourite-fruit> <rdf:type> <rdf:Seq>",
        "<http://example.org/favourite-fruit> <rdf:_1> <http://example.org/banana>",
        "<http://example.org/favourite-fruit> <rdf:_2> <http://example.org/apple>",
        "<http://example.org/favourite-fruit> <rdf:_3> <http://example.org/pear>",
    ]);
    assert_eq!(
        graph(&document(
            r#"<rdf:Seq rdf:about="http://example.org/favourite-fruit">
    <rdf:_1 rdf:resource="http://example.org/banana"/>
    <rdf:_2 rdf:resource="http://example.org/apple"/>
    <rdf:_3 rdf:resource="http://example.org/pear"/>
  </rdf:Seq>"#
        )),
        sequence
    );
    assert_eq!(
        graph(&document(
            r#"<rdf:Seq rdf:about="http://example.org/favourite-fruit">
    <rdf:li rdf:resource="http://example.org/banana"/>
    <rdf:li rdf:resource="http://example.org/apple"/>
    <rdf:li rdf:resource="http://example.org/pear"/>
  </rdf:Seq>"#
        )),
        sequence
    );
    // Example 19.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="http://example.org/basket">
    <ex:hasFruit rdf:parseType="Collection">
      <rdf:Description rdf:about="http://example.org/banana"/>
      <rdf:Description rdf:about="http://example.org/apple"/>
      <rdf:Description rdf:about="http://example.org/pear"/>
    </ex:hasFruit>
  </rdf:Description>"#
        )),
        lines(&[
            "s[2] <rdf:first> <http://example.org/pear>",
            "s[2] <rdf:rest> <rdf:nil>",
            "s[1] <rdf:first> <http://example.org/apple>",
            "s[1] <rdf:rest> s[2]",
            "s[0] <rdf:first> <http://example.org/banana>",
            "s[0] <rdf:rest> s[1]",
            "<http://example.org/basket> <ex:hasFruit> s[0]",
        ])
    );
    // Example 20.
    assert_eq!(
        graph(&format!(
            r#"<rdf:RDF xmlns:rdf="{RDF}" xmlns:ex="{EX}" xml:base="http://example.org/triples/">
  <rdf:Description rdf:about="http://example.org/">
    <ex:prop rdf:ID="triple1">blah</ex:prop>
  </rdf:Description>
</rdf:RDF>"#
        )),
        lines(&[
            "<http://example.org/> <ex:prop> \"blah\"^^<xsd:string>",
            "<http://example.org/triples/#triple1> <rdf:subject> <http://example.org/>",
            "<http://example.org/triples/#triple1> <rdf:predicate> <ex:prop>",
            "<http://example.org/triples/#triple1> <rdf:object> \"blah\"^^<xsd:string>",
            "<http://example.org/triples/#triple1> <rdf:type> <rdf:Statement>",
        ])
    );
}

#[test]
fn productions() {
    // A root node element, relative IRIs against the document base, an
    // unqualified attribute and rdf:type as a property attribute.
    assert_eq!(
        graph(&format!(
            r##"<ex:Thing xmlns:rdf="{RDF}" xmlns:ex="{EX}" about="#a" rdf:type="other" ex:p="v"/>"##
        )),
        lines(&[
            "<http://example.org/dir/doc#a> <rdf:type> <ex:Thing>",
            "<http://example.org/dir/doc#a> <rdf:type> <http://example.org/dir/other>",
            "<http://example.org/dir/doc#a> <ex:p> \"v\"^^<xsd:string>",
        ])
    );
    // Empty property elements: an empty literal, an empty typed literal and a
    // generated object with a property attribute; nested xml:base and
    // xml:lang; reification of an empty property element.
    assert_eq!(
        graph(&document(
            r#"<rdf:Description rdf:about="a" xml:lang="en">
    <ex:p/>
    <ex:q rdf:datatype="http://www.w3.org/2001/XMLSchema#string"></ex:q>
    <ex:r ex:s="t" xml:base="http://example.org/b/" xml:lang=""/>
    <ex:u rdf:ID="i" rdf:resource="c" xml:base="http://example.org/b/"/>
  </rdf:Description>"#
        )),
        lines(&[
            "<http://example.org/dir/a> <ex:p> \"\"@en",
            "<http://example.org/dir/a> <ex:q> \"\"^^<xsd:string>",
            "s[0] <ex:s> \"t\"^^<xsd:string>",
            "<http://example.org/dir/a> <ex:r> s[0]",
            "<http://example.org/dir/a> <ex:u> <http://example.org/b/c>",
            "<http://example.org/b/#i> <rdf:subject> <http://example.org/dir/a>",
            "<http://example.org/b/#i> <rdf:predicate> <ex:u>",
            "<http://example.org/b/#i> <rdf:object> <http://example.org/b/c>",
            "<http://example.org/b/#i> <rdf:type> <rdf:Statement>",
        ])
    );
    // An empty collection, rdf:li counters per node, and an rdf:nodeID object.
    assert_eq!(
        graph(&document(
            r#"<rdf:Bag rdf:nodeID="n">
    <rdf:li>one</rdf:li>
    <ex:p rdf:parseType="Collection"/>
    <rdf:li><rdf:Description><rdf:li rdf:nodeID="n"/></rdf:Description></rdf:li>
  </rdf:Bag>"#
        )),
        lines(&[
            "s_:n <rdf:type> <rdf:Bag>",
            "s_:n <rdf:_1> \"one\"^^<xsd:string>",
            "s_:n <ex:p> <rdf:nil>",
            "s[0] <rdf:_1> s_:n",
            "s_:n <rdf:_2> s[0]",
        ])
    );
}

#[test]
fn documents_without_a_graph() {
    for (body, kind) in [
        (
            r#"<rdf:Description rdf:aboutEach="x"/>"#,
            "InvalidAttributes",
        ),
        (r#"<rdf:li/>"#, "InvalidName"),
        (
            r#"<rdf:Description><rdf:Description/></rdf:Description>"#,
            "InvalidName",
        ),
        (r#"<rdf:Description rdf:li="x"/>"#, "InvalidAttributes"),
        (r#"<rdf:Description foo="x"/>"#, "UnqualifiedAttribute"),
        (
            r#"<rdf:Description about="a" rdf:about="a"/>"#,
            "DuplicateAttribute",
        ),
        (
            r#"<rdf:Description rdf:ID="a" rdf:about="a"/>"#,
            "InvalidAttributes",
        ),
        (
            r#"<rdf:Description rdf:ID="a"/><rdf:Description rdf:ID="a"/>"#,
            "DuplicateId",
        ),
        (r#"<rdf:Description rdf:ID="1a"/>"#, "InvalidId"),
        (r#"<rdf:Description rdf:nodeID="a:b"/>"#, "InvalidId"),
        (
            r#"<rdf:Description>text</rdf:Description>"#,
            "InvalidContent",
        ),
        (r#"text"#, "InvalidContent"),
        (
            r#"<rdf:Description><ex:p rdf:resource="a">x</ex:p></rdf:Description>"#,
            "InvalidAttributes",
        ),
        (
            r#"<rdf:Description><ex:p rdf:parseType="Other"/></rdf:Description>"#,
            "UnsupportedParseType",
        ),
        (
            r#"<rdf:Description><ex:p rdf:datatype="http://e/d" ex:q="v"/></rdf:Description>"#,
            "UnsupportedDatatype",
        ),
        (
            r#"<rdf:Description><ex:p rdf:resource="a" rdf:nodeID="b"/></rdf:Description>"#,
            "InvalidAttributes",
        ),
        (
            r#"<rdf:Description><ex:p><ex:A/><ex:B/></ex:p></rdf:Description>"#,
            "InvalidContent",
        ),
        (r#"<rdf:Description rdf:about="a b"/>"#, "InvalidIri"),
        (
            r#"<rdf:Description xml:lang="e_n" ex:p="v"/>"#,
            "InvalidLanguageTag",
        ),
        (
            r#"<rdf:Description><ex:p rdf:datatype="http://www.w3.org/1999/02/22-rdf-syntax-ns#langString">x</ex:p></rdf:Description>"#,
            "InvalidDatatype",
        ),
        (
            r#"<e xmlns:x="http://www.w3.org/1999/02/22-rdf-syntax-ns#x"><x:a/></e>"#,
            "InvalidName",
        ),
    ] {
        assert_eq!(failure(&document(body)), kind, "{body}");
    }
    assert_eq!(failure("<a/>"), "InvalidName");
    assert_eq!(failure("<a"), "XmlError");
    assert_eq!(
        failure(&format!(r#"<rdf:RDF xmlns:rdf="{RDF}" rdf:about="a"/>"#)),
        "InvalidAttributes"
    );
}

#[test]
fn limits_are_errors() {
    let source = document(r#"<rdf:Description rdf:about="a" ex:p="v"/>"#);
    let small = |term_bytes, items| {
        read_with_limits(
            &source.as_bytes().to_vec(),
            &BASE.as_bytes().to_vec(),
            &b"s".to_vec(),
            &Limits {
                expansion: 0,
                term_bytes,
                items,
            },
        )
    };
    assert!(matches!(small(1 << 10, 1), ReadResult::Graph(_)));
    assert!(matches!(
        small(1 << 10, 0),
        ReadResult::Error(ErrorKind::ResourceLimit)
    ));
    assert!(matches!(
        small(20, 1),
        ReadResult::Error(ErrorKind::ResourceLimit)
    ));
}
