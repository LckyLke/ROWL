use rowl_kernel::rdf::{BlankNode, LiteralKind, Object, RawGraph, RdfIri, Subject};
use rowl_kernel::turtle::{read, read_with_limits, ErrorKind, Limits, ReadError, ReadResult};

const RDF: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const BASE: &str = "http://example.org/dir/doc";

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("UTF-8 term")
}

fn iri(value: &RdfIri) -> String {
    format!("<{}>", text(&value.spelling))
}

/// Blank nodes print with their scope; the reader's own labels begin with a
/// byte that UTF-8 never contains and print as `[n]` and `(n)`.
fn blank(node: &BlankNode) -> String {
    let scope = text(&node.scope);
    match node.label.first() {
        Some(255) => format!("{scope}[{}]", text(&node.label[1..])),
        Some(254) => format!("{scope}({})", text(&node.label[1..])),
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

fn graph(source: &str) -> Vec<String> {
    match read(
        &source.as_bytes().to_vec(),
        &b"s".to_vec(),
        &BASE.as_bytes().to_vec(),
    ) {
        ReadResult::Graph(graph) => shown(&graph),
        ReadResult::Error(error) => panic!("rejected at {}: {source:?}", error.offset),
    }
}

fn failure(source: &[u8]) -> ReadError {
    match read(&source.to_vec(), &b"s".to_vec(), &BASE.as_bytes().to_vec()) {
        ReadResult::Graph(_) => panic!("accepted: {:?}", String::from_utf8_lossy(source)),
        ReadResult::Error(error) => error,
    }
}

fn lines(expected: &[&str]) -> Vec<String> {
    expected
        .iter()
        .map(|line| line.replace("rdf:", RDF).replace("xsd:", XSD))
        .collect()
}

#[test]
fn directives_and_relative_iris() {
    assert_eq!(
        graph(
            "@prefix ex: <http://example.org/ns#> .\n\
             PREFIX p: <p/>\n\
             <a> ex:b <../c> .\n\
             @base <http://other.example/x/y> .\n\
             <z> p:q <#f> .\n\
             BaSe <//host/> \n\
             <r> p:s <> .\n\
             prefix ex: <http://example.org/second#>\n\
             ex:t ex:u ex:v ."
        ),
        lines(&[
            "<http://example.org/dir/a> <http://example.org/ns#b> <http://example.org/c>",
            "<http://other.example/x/z> <http://example.org/dir/p/q> <http://other.example/x/y#f>",
            "<http://host/r> <http://example.org/dir/p/s> <http://host/>",
            "<http://example.org/second#t> <http://example.org/second#u> <http://example.org/second#v>",
        ])
    );
}

#[test]
fn predicate_and_object_lists() {
    assert_eq!(
        graph("<s> <p> <o1>, <o2> ; <q> <o3> ;; ; a <C> ; ."),
        lines(&[
            "<http://example.org/dir/s> <http://example.org/dir/p> <http://example.org/dir/o1>",
            "<http://example.org/dir/s> <http://example.org/dir/p> <http://example.org/dir/o2>",
            "<http://example.org/dir/s> <http://example.org/dir/q> <http://example.org/dir/o3>",
            "<http://example.org/dir/s> <rdf:type> <http://example.org/dir/C>",
        ])
    );
}

#[test]
fn blank_nodes_and_property_lists() {
    assert_eq!(
        graph(
            "@prefix : <http://e/> .\n\
             _:a :p [] .\n\
             [ :q _:a ; :r [ :s :t ] ] :u :v .\n\
             [ :w :x ] .\n\
             [] :y _:b.c ."
        ),
        lines(&[
            "s_:a <http://e/p> s[31]",
            "s[36] <http://e/q> s_:a",
            "s[50] <http://e/s> <http://e/t>",
            "s[36] <http://e/r> s[50]",
            "s[36] <http://e/u> <http://e/v>",
            "s[70] <http://e/w> <http://e/x>",
            "s[82] <http://e/y> s_:b.c",
        ])
    );
}

#[test]
fn collections() {
    assert_eq!(
        graph("@prefix : <http://e/> .\n:a :b () .\n( :c ( ) [ :d :e ] ) :f ( 1 ) ."),
        lines(&[
            "<http://e/a> <http://e/b> <rdf:nil>",
            "s(37) <rdf:first> <http://e/c>",
            "s(37) <rdf:rest> s(40)",
            "s(40) <rdf:first> <rdf:nil>",
            "s(40) <rdf:rest> s(44)",
            "s[44] <http://e/d> <http://e/e>",
            "s(44) <rdf:first> s[44]",
            "s(44) <rdf:rest> <rdf:nil>",
            "s(61) <rdf:first> \"1\"^^<xsd:integer>",
            "s(61) <rdf:rest> <rdf:nil>",
            "s(37) <http://e/f> s(61)",
        ])
    );
}

#[test]
fn string_literals() {
    assert_eq!(
        graph(
            "<s> <p> \"a\\tb\\u00E9\" , 'it\\'s' , \"\"\"one\n\"two\"\n\"\"\" , '''x''y''' , \
             \"chat\"@fr-CA , 'x' ^^ <http://d/t> , \"\\U0001F600\" ."
        )
        .iter()
        .map(|line| line
            .split_once("<http://example.org/dir/p> ")
            .unwrap()
            .1
            .to_string())
        .collect::<Vec<_>>(),
        lines(&[
            "\"a\\tbé\"^^<xsd:string>",
            "\"it's\"^^<xsd:string>",
            "\"one\\n\\\"two\\\"\\n\"^^<xsd:string>",
            "\"x''y\"^^<xsd:string>",
            "\"chat\"@fr-CA",
            "\"x\"^^<http://d/t>",
            "\"😀\"^^<xsd:string>",
        ])
    );
}

/// Tokens are the longest matches: three quotes that begin no long string
/// are an empty string followed by a quote, and a `-` that no subtag follows
/// ends a language tag.
#[test]
fn longest_matches_back_off() {
    assert_eq!(
        graph("<s> <p> ( \"\"\"x\" '''y' \"z\"@en-.5 ) ."),
        lines(&[
            "s(10) <rdf:first> \"\"^^<xsd:string>",
            "s(10) <rdf:rest> s(12)",
            "s(12) <rdf:first> \"x\"^^<xsd:string>",
            "s(12) <rdf:rest> s(16)",
            "s(16) <rdf:first> \"\"^^<xsd:string>",
            "s(16) <rdf:rest> s(18)",
            "s(18) <rdf:first> \"y\"^^<xsd:string>",
            "s(18) <rdf:rest> s(22)",
            "s(22) <rdf:first> \"z\"@en",
            "s(22) <rdf:rest> s(28)",
            "s(28) <rdf:first> \"-.5\"^^<xsd:decimal>",
            "s(28) <rdf:rest> <rdf:nil>",
            "<http://example.org/dir/s> <http://example.org/dir/p> s(10)",
        ])
    );
}

#[test]
fn numbers_and_booleans() {
    assert_eq!(
        graph("<s> <p> 1, -2, +3.5, .5, 1e3, 2.E-1, -.5e+2, true, false ."),
        lines(&[
            "<http://example.org/dir/s> <http://example.org/dir/p> \"1\"^^<xsd:integer>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \"-2\"^^<xsd:integer>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \"+3.5\"^^<xsd:decimal>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \".5\"^^<xsd:decimal>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \"1e3\"^^<xsd:double>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \"2.E-1\"^^<xsd:double>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \"-.5e+2\"^^<xsd:double>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \"true\"^^<xsd:boolean>",
            "<http://example.org/dir/s> <http://example.org/dir/p> \"false\"^^<xsd:boolean>",
        ])
    );
    // `4.` is the integer 4 followed by the statement's period.
    assert_eq!(graph("<s> <p> 4.").len(), 1);
}

#[test]
fn prefixed_names() {
    assert_eq!(
        graph(
            "@prefix e.x: <http://e/> . @prefix : <http://d/> .\n\
             e.x:a.b :c\\~d\\.e%41f:g : . :0 e.x:_h \"z\"^^e.x:dt .\n\
             :x :y :z. e.x:é:: :a :b."
        ),
        lines(&[
            "<http://e/a.b> <http://d/c~d.e%41f:g> <http://d/>",
            "<http://d/0> <http://e/_h> \"z\"^^<http://e/dt>",
            "<http://d/x> <http://d/y> <http://d/z>",
            "<http://e/é::> <http://d/a> <http://d/b>",
        ])
    );
}

#[test]
fn keywords_yield_to_longer_prefixed_names() {
    assert_eq!(
        graph(
            "@prefix PREFIX: <http://p/> . @prefix a: <http://a/> . @prefix true: <http://t/> .\n\
             PREFIX:s a:p true:o . PREFIX:s a true: ."
        ),
        lines(&[
            "<http://p/s> <http://a/p> <http://t/o>",
            "<http://p/s> <rdf:type> <http://t/>",
        ])
    );
}

#[test]
fn comments_and_white_space() {
    assert_eq!(
        graph("# head\n<s> # c1\n <p> # c2\r\n [ # c3\n ] # c4\n . # tail"),
        lines(&["<http://example.org/dir/s> <http://example.org/dir/p> s[28]"])
    );
    assert!(graph("").is_empty());
    assert!(graph("  # only a comment").is_empty());
}

/// A rejected source, the offset of its first error and its kind.
type Case = (&'static [u8], usize, fn(&ErrorKind) -> bool);

#[test]
fn errors_report_their_first_offset() {
    let cases: &[Case] = &[
        (b"<s> <p> <o>", 11, |k| {
            matches!(k, ErrorKind::ExpectedPeriod)
        }),
        (b"<s> <p> .", 8, |k| matches!(k, ErrorKind::ExpectedObject)),
        (b"<s> . ", 4, |k| matches!(k, ErrorKind::ExpectedVerb)),
        (b"\"s\" <p> <o> .", 0, |k| {
            matches!(k, ErrorKind::ExpectedSubject)
        }),
        (b"x:s <p> <o> .", 0, |k| {
            matches!(k, ErrorKind::UndefinedPrefix)
        }),
        (b"<s> <p> [ <q> <o> .", 18, |k| {
            matches!(k, ErrorKind::ExpectedBracket)
        }),
        (b"<s> <p> ( <o> .", 14, |k| {
            matches!(k, ErrorKind::ExpectedObject)
        }),
        (b"<s> <p> ( <o>", 13, |k| {
            matches!(k, ErrorKind::UnexpectedEnd)
        }),
        (
            b"<s> <p> \"x\"^^<http://www.w3.org/1999/02/22-rdf-syntax-ns#langString> .",
            11,
            |k| matches!(k, ErrorKind::InvalidLiteralKind),
        ),
        (b"<s> <p> \"x\"^<t> .", 11, |k| {
            matches!(k, ErrorKind::InvalidLiteralKind)
        }),
        (b"<s> <p> \"x\"@1 .", 11, |k| {
            matches!(k, ErrorKind::InvalidLanguageTag)
        }),
        (b"<s> <p> \"a\nb\" .", 10, |k| {
            matches!(k, ErrorKind::InvalidCharacter)
        }),
        (b"<s> <p> \"\\q\" .", 9, |k| {
            matches!(k, ErrorKind::InvalidEscape)
        }),
        (b"<s> <p> <a b> .", 10, |k| {
            matches!(k, ErrorKind::InvalidCharacter)
        }),
        (b"<s> <p> <%zz> .", 8, |k| {
            matches!(k, ErrorKind::InvalidIri)
        }),
        (b"<s> <p> _:-a .", 10, |k| {
            matches!(k, ErrorKind::InvalidBlankLabel)
        }),
        (b"<s> <p> _a .", 8, |k| {
            matches!(k, ErrorKind::InvalidBlankLabel)
        }),
        (b"@prefix <x> .", 8, |k| {
            matches!(k, ErrorKind::ExpectedPrefix)
        }),
        (b"@base x .", 6, |k| matches!(k, ErrorKind::ExpectedIri)),
        (b"PREFIX x: <y> .", 14, |k| {
            matches!(k, ErrorKind::ExpectedSubject)
        }),
        (b"<s> <p> \xff .", 8, |k| {
            matches!(k, ErrorKind::MalformedUtf8)
        }),
        (b"<s> <p> 'x", 10, |k| matches!(k, ErrorKind::UnexpectedEnd)),
        (b"<s> <p> \"\"\"x\"\" .", 10, |k| {
            matches!(k, ErrorKind::ExpectedPeriod)
        }),
        (b"<s> <p> + .", 8, |k| {
            matches!(k, ErrorKind::ExpectedObject)
        }),
        (b"<s> <p> tru .", 8, |k| {
            matches!(k, ErrorKind::ExpectedObject)
        }),
        (b"<s> b <o> .", 4, |k| matches!(k, ErrorKind::ExpectedVerb)),
        (b"<s> <p> <o> ; , <o> .", 14, |k| {
            matches!(k, ErrorKind::ExpectedVerb)
        }),
        (b"@prefixes x: <y> .", 0, |k| {
            matches!(k, ErrorKind::ExpectedSubject)
        }),
    ];
    for (source, offset, kind) in cases {
        let error = failure(source);
        assert_eq!(
            error.offset,
            *offset,
            "offset for {:?}",
            String::from_utf8_lossy(source)
        );
        assert!(
            kind(&error.kind),
            "kind for {:?}",
            String::from_utf8_lossy(source)
        );
    }
}

#[test]
fn relative_iris_need_a_base() {
    let source = b"<s> <p> <o> .".to_vec();
    match read(&source, &b"s".to_vec(), &Vec::new()) {
        ReadResult::Error(error) => {
            assert_eq!(error.offset, 0);
            assert!(matches!(error.kind, ErrorKind::InvalidIri));
        }
        ReadResult::Graph(_) => panic!("a relative IRI without a base"),
    }
    let absolute = b"<http://a/s> <http://a/p> <http://a/./o> .".to_vec();
    match read(&absolute, &b"s".to_vec(), &Vec::new()) {
        ReadResult::Graph(graph) => assert_eq!(
            shown(&graph),
            vec!["<http://a/s> <http://a/p> <http://a/o>".to_string()]
        ),
        ReadResult::Error(error) => panic!("rejected at {}", error.offset),
    }
}

#[test]
fn limits_bound_terms_and_triples() {
    let source = b"@prefix e: <http://e/> . e:s e:p ( e:a e:b ) .".to_vec();
    let scope = b"s".to_vec();
    let base = Vec::new();
    let limited = |terms: usize, triples: usize| {
        read_with_limits(
            &source,
            &scope,
            &base,
            &Limits {
                max_term_bytes: terms,
                max_triples: triples,
            },
        )
    };
    match limited(64, 5) {
        ReadResult::Graph(graph) => assert_eq!(graph.triples.len(), 5),
        ReadResult::Error(error) => panic!("rejected at {}", error.offset),
    }
    match limited(64, 4) {
        ReadResult::Error(error) => {
            assert!(matches!(error.kind, ErrorKind::ResourceLimit));
            assert_eq!(error.offset, 33);
        }
        ReadResult::Graph(_) => panic!("more triples than the limit"),
    }
    match limited(9, 5) {
        ReadResult::Error(error) => {
            assert!(matches!(error.kind, ErrorKind::ResourceLimit));
            assert_eq!(error.offset, 25);
        }
        ReadResult::Graph(_) => panic!("a term longer than the limit"),
    }
}

#[test]
fn equal_labels_share_one_node_and_scopes_separate_documents() {
    let source = b"_:x <http://p> _:x .".to_vec();
    for scope in [b"one".to_vec(), b"two".to_vec()] {
        match read(&source, &scope, &Vec::new()) {
            ReadResult::Graph(graph) => {
                let triple = &graph.triples[0];
                match (&triple.subject, &triple.object) {
                    (Subject::Blank(a), Object::Blank(b)) => {
                        assert_eq!(a.scope, scope);
                        assert_eq!((&a.scope, &a.label), (&b.scope, &b.label));
                    }
                    _ => panic!("blank nodes expected"),
                }
            }
            ReadResult::Error(error) => panic!("rejected at {}", error.offset),
        }
    }
}

/// A term of a test graph, independent of the reader's types.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Term {
    Iri(Vec<u8>),
    Blank(usize),
    Literal(Vec<u8>, bool, Vec<u8>),
}

type Graph = std::collections::BTreeSet<(Term, Term, Term)>;

/// How often a blank node is a subject and an object.
type Degree = (usize, usize);

/// The triples of a raw graph as a set, with blank nodes numbered by identity.
fn graph_set(raw: &RawGraph) -> (Graph, usize) {
    let mut blanks: std::collections::BTreeMap<(Vec<u8>, Vec<u8>), usize> = Default::default();
    let mut node = |b: &BlankNode| {
        let next = blanks.len();
        Term::Blank(
            *blanks
                .entry((b.scope.clone(), b.label.clone()))
                .or_insert(next),
        )
    };
    let mut set = Graph::new();
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

/// Whether two graphs are isomorphic: a bijection of blank nodes maps one
/// triple set onto the other. Backtracking over candidates with equal counts
/// of occurrences, which suffices for the small graphs of the suite.
fn isomorphic(a: &RawGraph, b: &RawGraph) -> bool {
    let (left, left_blanks) = graph_set(a);
    let (right, right_blanks) = graph_set(b);
    if left.len() != right.len() || left_blanks != right_blanks {
        return false;
    }
    let degree = |graph: &Graph, count: usize| {
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
    let left_degrees = degree(&left, left_blanks);
    let right_degrees = degree(&right, right_blanks);
    fn image(term: &Term, map: &[Option<usize>]) -> Option<Term> {
        match term {
            Term::Blank(n) => map[*n].map(Term::Blank),
            other => Some(other.clone()),
        }
    }
    fn consistent(left: &Graph, right: &Graph, map: &[Option<usize>]) -> bool {
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
        left: &Graph,
        right: &Graph,
        degrees: (&[Degree], &[Degree]),
    ) -> bool {
        if index == map.len() {
            return consistent(left, right, map);
        }
        for candidate in 0..used.len() {
            if !used[candidate] && degrees.0[index] == degrees.1[candidate] {
                map[index] = Some(candidate);
                used[candidate] = true;
                if consistent(left, right, map)
                    && search(index + 1, map, used, left, right, degrees)
                {
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
        &left,
        &right,
        (&left_degrees, &right_degrees),
    )
}

#[test]
#[ignore = "requires the official W3C Turtle suite in ROWL_TURTLE_SUITE_DIR"]
fn official_w3c_turtle_cases() {
    let directory = std::path::PathBuf::from(
        std::env::var_os("ROWL_TURTLE_SUITE_DIR").expect("suite directory required"),
    );
    // The suite's `mf:assumedTestBase`: each document is read against its own URL.
    let source = "https://w3c.github.io/rdf-tests/rdf/rdf11/rdf-turtle/";
    let read_turtle = |name: &str| {
        let bytes = std::fs::read(directory.join(name)).unwrap();
        read(
            &bytes,
            &b"suite".to_vec(),
            &format!("{source}{name}").into_bytes(),
        )
    };
    // The manifest is itself read by the reader under test.
    let ReadResult::Graph(manifest) = read_turtle("manifest.ttl") else {
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
        let result = read_turtle(&name);
        let passed = match kind {
            "TestTurtlePositiveSyntax" => matches!(result, ReadResult::Graph(_)),
            "TestTurtleNegativeSyntax" | "TestTurtleNegativeEval" => {
                matches!(result, ReadResult::Error(_))
            }
            "TestTurtleEval" => {
                let expected = value(&triple.subject, &format!("{mf}result")).expect("a result");
                let expected = expected.strip_prefix(source).expect("a suite file");
                let bytes = std::fs::read(directory.join(expected)).unwrap();
                let rowl_kernel::ntriples::ReadResult::Graph(expected) =
                    rowl_kernel::ntriples::read(&bytes, &b"expected".to_vec())
                else {
                    panic!("the expected graph {expected} is N-Triples")
                };
                match &result {
                    ReadResult::Graph(graph) => isomorphic(graph, &expected),
                    ReadResult::Error(_) => false,
                }
            }
            other => panic!("unknown test type {other}"),
        };
        *counts.entry(kind.to_string()).or_insert(0) += 1;
        if !passed {
            let detail = match &result {
                ReadResult::Error(error) => format!("error at {}", error.offset),
                ReadResult::Graph(graph) => format!("{} triples", graph.triples.len()),
            };
            failures.push(format!("{kind} {name}: {detail}"));
        }
    }
    assert!(
        failures.is_empty(),
        "failing W3C cases:\n{}",
        failures.join("\n")
    );
    assert_eq!(
        counts.values().sum::<usize>(),
        313,
        "manifest was incomplete or unexpectedly changed: {counts:?}"
    );
}
