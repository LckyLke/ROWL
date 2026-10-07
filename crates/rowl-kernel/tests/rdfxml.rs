//! Regression tests for the RDF/XML reader: the examples of RDF 1.1 XML
//! Syntax section 2, its productions and the documents it does not accept.
use rowl_kernel::import_catalog::rdfxml_limits;
use rowl_kernel::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfIri, Subject};
use rowl_kernel::rdfxml::{read_with_limits, ErrorKind, Limits, ReadResult};
use rowl_kernel::{ntriples, turtle};

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

/// A term of a test graph, independent of the reader's types.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Term {
    Iri(Vec<u8>),
    Blank(usize),
    Literal(Vec<u8>, bool, Vec<u8>),
}

type Set = std::collections::BTreeSet<(Term, Term, Term)>;

/// How often each blank node occurs as a subject and as an object.
type Degrees = [(usize, usize)];

/// The triples of a raw graph as a set, with blank nodes numbered by identity
/// and language tags in lower case.
fn graph_set(raw: &RawGraph) -> (Set, usize) {
    let mut blanks: std::collections::BTreeMap<(Vec<u8>, Vec<u8>), usize> = Default::default();
    let mut node = |b: &BlankNode| {
        let next = blanks.len();
        Term::Blank(
            *blanks
                .entry((b.scope.clone(), b.label.clone()))
                .or_insert(next),
        )
    };
    let mut set = Set::new();
    for triple in &raw.triples {
        let subject = match &triple.subject {
            Subject::Iri(value) => Term::Iri(value.spelling.clone()),
            Subject::Blank(b) => node(b),
        };
        let object = match &triple.object {
            Object::Iri(value) => Term::Iri(value.spelling.clone()),
            Object::Blank(b) => node(b),
            Object::Literal(literal) => match &literal.kind {
                LiteralKind::Datatype(datatype) => {
                    Term::Literal(literal.lexical.clone(), false, datatype.spelling.clone())
                }
                LiteralKind::Language(tag) => {
                    Term::Literal(literal.lexical.clone(), true, tag.to_ascii_lowercase())
                }
            },
        };
        set.insert((
            subject,
            Term::Iri(triple.predicate.spelling.clone()),
            object,
        ));
    }
    (set, blanks.len())
}

/// Whether two graphs are equal up to a renaming of blank nodes: a bijection
/// of their blank nodes maps one triple set onto the other. Backtracking over
/// candidates that occur equally often as subjects and as objects, which
/// suffices for the small graphs of the tests.
fn isomorphic(a: &RawGraph, b: &RawGraph) -> bool {
    let (left, left_blanks) = graph_set(a);
    let (right, right_blanks) = graph_set(b);
    if left.len() != right.len() || left_blanks != right_blanks {
        return false;
    }
    let degrees = |graph: &Set, count: usize| {
        let mut degrees = vec![(0usize, 0usize); count];
        for (s, _, o) in graph {
            if let Term::Blank(n) = s {
                degrees[*n].0 += 1;
            }
            if let Term::Blank(n) = o {
                degrees[*n].1 += 1;
            }
        }
        degrees
    };
    let left_degrees = degrees(&left, left_blanks);
    let right_degrees = degrees(&right, right_blanks);
    fn image(term: &Term, map: &[Option<usize>]) -> Option<Term> {
        match term {
            Term::Blank(n) => map[*n].map(Term::Blank),
            other => Some(other.clone()),
        }
    }
    fn consistent(left: &Set, right: &Set, map: &[Option<usize>]) -> bool {
        left.iter()
            .all(|(s, p, o)| match (image(s, map), image(o, map)) {
                (Some(s), Some(o)) => right.contains(&(s, p.clone(), o)),
                _ => true,
            })
    }
    fn search(
        index: usize,
        map: &mut Vec<Option<usize>>,
        used: &mut Vec<bool>,
        sets: (&Set, &Set),
        degrees: (&Degrees, &Degrees),
    ) -> bool {
        if index == map.len() {
            return consistent(sets.0, sets.1, map);
        }
        for candidate in 0..used.len() {
            if !used[candidate] && degrees.0[index] == degrees.1[candidate] {
                map[index] = Some(candidate);
                used[candidate] = true;
                if consistent(sets.0, sets.1, map) && search(index + 1, map, used, sets, degrees) {
                    return true;
                }
                used[candidate] = false;
                map[index] = None;
            }
        }
        false
    }
    let mut map = vec![None; left_blanks];
    let mut used = vec![false; right_blanks];
    search(
        0,
        &mut map,
        &mut used,
        (&left, &right),
        (&left_degrees, &right_degrees),
    )
}

fn example(name: &str) -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name);
    std::fs::read(path).expect("example file")
}

fn ntriples_graph(bytes: &[u8]) -> RawGraph {
    match ntriples::read(&bytes.to_vec(), &b"nt".to_vec()) {
        ntriples::ReadResult::Graph(graph) => graph,
        ntriples::ReadResult::Error(error) => panic!("N-Triples error at byte {}", error.offset),
    }
}

#[test]
fn examples_are_their_ntriples_graphs() {
    for (owl, nt, triples) in [
        ("maintenance.owl", "maintenance.nt", 15),
        ("medication-safety.owl", "medication-safety.nt", 60),
    ] {
        let graph = match read_with_limits(
            &example(owl),
            &Vec::new(),
            &b"owl".to_vec(),
            &rdfxml_limits(),
        ) {
            ReadResult::Graph(graph) => graph,
            ReadResult::XmlError(error) => panic!("{owl}: XML error at byte {}", error.offset),
            ReadResult::Error(kind) => panic!("{owl}: {}", name(kind)),
        };
        assert_eq!(graph.triples.len(), triples, "{owl}");
        assert!(isomorphic(&graph, &ntriples_graph(&example(nt))), "{owl}");
    }
}

/// The evaluation tests whose documents use XML literals, which the reader
/// declines.
const XML_LITERAL_CASES: [&str; 3] = [
    "rdf-containers-syntax-vs-schema/test004.rdf",
    "xml-canon/test001.rdf",
    "xml-canon/test002.rdf",
];

#[test]
#[ignore = "requires the official W3C RDF/XML suite in ROWL_RDFXML_SUITE_DIR"]
fn official_w3c_rdfxml_cases() {
    let directory = std::path::PathBuf::from(
        std::env::var_os("ROWL_RDFXML_SUITE_DIR").expect("suite directory required"),
    );
    // Each document is read against its own URL, the suite's base.
    let source = "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-xml/";
    let bytes = |name: &str| std::fs::read(directory.join(name)).unwrap();
    // The manifest is Turtle, read by the verified Turtle reader.
    let turtle::ReadResult::Graph(manifest) = turtle::read(
        &bytes("manifest.ttl"),
        &b"manifest".to_vec(),
        &format!("{source}manifest.ttl").into_bytes(),
    ) else {
        panic!("the manifest is Turtle")
    };
    let rdft = "http://www.w3.org/ns/rdftest#";
    let mf = "http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#";
    let value = |subject: &Subject, predicate: &str| {
        manifest.triples.iter().find_map(|triple| {
            let same = match (&triple.subject, subject) {
                (Subject::Iri(a), Subject::Iri(b)) => a.spelling == b.spelling,
                _ => false,
            };
            match &triple.object {
                Object::Iri(object)
                    if same && triple.predicate.spelling == predicate.as_bytes() =>
                {
                    Some(text(&object.spelling))
                }
                _ => None,
            }
        })
    };
    let mut counts = std::collections::BTreeMap::new();
    let mut failures = Vec::new();
    for triple in &manifest.triples {
        let Object::Iri(kind) = &triple.object else {
            continue;
        };
        if triple.predicate.spelling != format!("{RDF}type").into_bytes() {
            continue;
        }
        let kind = text(&kind.spelling);
        let Some(kind) = kind.strip_prefix(rdft) else {
            continue;
        };
        let action = value(&triple.subject, &format!("{mf}action")).expect("an action");
        let name = action
            .strip_prefix(source)
            .expect("a suite file")
            .to_string();
        let result = read_with_limits(
            &bytes(&name),
            &action.clone().into_bytes(),
            &b"suite".to_vec(),
            &rdfxml_limits(),
        );
        let passed = match kind {
            "TestXMLNegativeSyntax" => !matches!(result, ReadResult::Graph(_)),
            "TestXMLEval" => {
                let expected = value(&triple.subject, &format!("{mf}result")).expect("a result");
                let expected = expected.strip_prefix(source).expect("a suite file");
                match &result {
                    ReadResult::Graph(graph) => {
                        isomorphic(graph, &ntriples_graph(&bytes(expected)))
                    }
                    _ => false,
                }
            }
            other => panic!("unknown test type {other}"),
        };
        *counts.entry(kind.to_string()).or_insert(0) += 1;
        if !passed {
            failures.push(name);
        }
    }
    failures.sort();
    assert_eq!(
        failures, XML_LITERAL_CASES,
        "exactly the cases with XML literals fail"
    );
    assert_eq!(
        counts.values().sum::<usize>(),
        166,
        "manifest was incomplete or unexpectedly changed: {counts:?}"
    );
}
