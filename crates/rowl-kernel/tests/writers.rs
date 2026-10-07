//! Round trips of the N-Triples and Turtle writers through the readers.
use rowl_kernel::rdf::{
    BlankNode, LiteralKind, Object, RawGraph, RdfIri, RdfLiteral, Subject, Triple,
};
use rowl_kernel::{ntriples, turtle};

fn iri(value: &str) -> RdfIri {
    RdfIri {
        spelling: value.as_bytes().to_vec(),
    }
}

fn blank(scope: &[u8], label: &[u8]) -> BlankNode {
    BlankNode {
        scope: scope.to_vec(),
        label: label.to_vec(),
    }
}

fn literal(lexical: &[u8], kind: LiteralKind) -> Object {
    Object::Literal(RdfLiteral {
        lexical: lexical.to_vec(),
        kind,
    })
}

fn triple(subject: Subject, predicate: &str, object: Object) -> Triple {
    Triple {
        subject,
        predicate: iri(predicate),
        object,
    }
}

/// The label the readers give a written blank node in their scope.
fn written_label(node: &BlankNode) -> Vec<u8> {
    let mut label = b"b".to_vec();
    for byte in &node.scope {
        label.extend(format!("{byte:02x}").bytes());
    }
    label.push(b'_');
    for byte in &node.label {
        label.extend(format!("{byte:02x}").bytes());
    }
    label
}

fn same_iri(a: &RdfIri, b: &RdfIri) -> bool {
    a.spelling == b.spelling
}

fn renamed(node: &BlankNode, read: &BlankNode, scope: &[u8]) -> bool {
    read.scope == scope && read.label == written_label(node)
}

/// Whether `read` is `original` with every blank node renamed into `scope`.
fn round_trip(original: &RawGraph, read: &RawGraph, scope: &[u8]) -> bool {
    original.triples.len() == read.triples.len()
        && original.triples.iter().zip(&read.triples).all(|(a, b)| {
            let subject = match (&a.subject, &b.subject) {
                (Subject::Iri(x), Subject::Iri(y)) => same_iri(x, y),
                (Subject::Blank(x), Subject::Blank(y)) => renamed(x, y, scope),
                _ => false,
            };
            let object = match (&a.object, &b.object) {
                (Object::Iri(x), Object::Iri(y)) => same_iri(x, y),
                (Object::Blank(x), Object::Blank(y)) => renamed(x, y, scope),
                (Object::Literal(x), Object::Literal(y)) => {
                    x.lexical == y.lexical
                        && match (&x.kind, &y.kind) {
                            (LiteralKind::Datatype(p), LiteralKind::Datatype(q)) => same_iri(p, q),
                            (LiteralKind::Language(p), LiteralKind::Language(q)) => p == q,
                            _ => false,
                        }
                }
                _ => false,
            };
            subject && same_iri(&a.predicate, &b.predicate) && object
        })
}

fn sample() -> RawGraph {
    let string = || LiteralKind::Datatype(iri("http://www.w3.org/2001/XMLSchema#string"));
    RawGraph {
        triples: vec![
            triple(
                Subject::Iri(iri("https://example.org/s")),
                "https://example.org/p",
                Object::Iri(iri("https://example.org/o?x=1#frag")),
            ),
            triple(
                Subject::Blank(blank(b"doc", b"a1")),
                "https://example.org/p",
                Object::Blank(blank(b"", b"")),
            ),
            triple(
                Subject::Blank(blank(&[0, 255, 7], &[0xfe, b'.', b' '])),
                "https://example.org/caf\u{e9}",
                literal(b"quote \" backslash \\ line\nreturn\r tab\t", string()),
            ),
            triple(
                Subject::Iri(iri("urn:x:\u{1F600}")),
                "https://example.org/p",
                literal(
                    "Gr\u{fc}\u{df}e".as_bytes(),
                    LiteralKind::Language(b"de-CH-1996".to_vec()),
                ),
            ),
            triple(
                Subject::Iri(iri("https://example.org/s")),
                "https://example.org/p",
                literal(
                    b"",
                    LiteralKind::Datatype(iri("http://www.w3.org/2001/XMLSchema#integer")),
                ),
            ),
            triple(
                Subject::Iri(iri("https://example.org/s")),
                "https://example.org/p",
                literal(b"x", LiteralKind::Language(b"EN-gb-OED".to_vec())),
            ),
            triple(
                Subject::Iri(iri("https://example.org/s")),
                "https://example.org/p",
                Object::Iri(iri("https://example.org/s")),
            ),
        ],
    }
}

#[test]
fn ntriples_writer_round_trips_through_the_reader() {
    let graph = sample();
    let ntriples::WriteResult::Bytes(bytes) = ntriples::write(&graph, usize::MAX) else {
        panic!("the sample is representable")
    };
    let ntriples::ReadResult::Graph(read) = ntriples::read(&bytes, &b"reread".to_vec()) else {
        panic!("the reader reads what the writer writes")
    };
    assert!(round_trip(&graph, &read, b"reread"));
}

#[test]
fn turtle_writer_round_trips_through_the_reader() {
    let graph = sample();
    let turtle::WriteResult::Bytes(bytes) = turtle::write(&graph, usize::MAX) else {
        panic!("the sample is representable")
    };
    for base in [&b""[..], b"https://example.org/base/"] {
        let turtle::ReadResult::Graph(read) =
            turtle::read(&bytes, &b"reread".to_vec(), &base.to_vec())
        else {
            panic!("the reader reads what the writer writes")
        };
        assert!(round_trip(&graph, &read, b"reread"));
    }
}

#[test]
fn empty_graphs_write_nothing() {
    let graph = RawGraph { triples: vec![] };
    assert!(matches!(ntriples::write(&graph, 0), ntriples::WriteResult::Bytes(b) if b.is_empty()));
    assert!(matches!(turtle::write(&graph, 0), turtle::WriteResult::Bytes(b) if b.is_empty()));
}

fn single(object: Object) -> RawGraph {
    RawGraph {
        triples: vec![triple(
            Subject::Iri(iri("https://example.org/s")),
            "https://example.org/p",
            object,
        )],
    }
}

/// Recognizes the error a graph must be rejected with.
type Expected = fn(&rowl_kernel::rdf_write::WriteError) -> bool;

#[test]
fn unrepresentable_terms_have_typed_errors() {
    use rowl_kernel::rdf_write::WriteError;
    let cases: Vec<(RawGraph, Expected)> = vec![
        (single(Object::Iri(iri("relative"))), |e| {
            matches!(e, WriteError::InvalidIri)
        }),
        (single(Object::Iri(iri("https://example.org/a b"))), |e| {
            matches!(e, WriteError::InvalidIri)
        }),
        (
            single(literal(
                &[0xff],
                LiteralKind::Datatype(iri("http://www.w3.org/2001/XMLSchema#string")),
            )),
            |e| matches!(e, WriteError::MalformedLiteralUtf8),
        ),
        (
            single(literal(b"a", LiteralKind::Language(b"en_XX".to_vec()))),
            |e| matches!(e, WriteError::InvalidLanguageTag),
        ),
        (
            single(literal(b"a", LiteralKind::Language(b"en-".to_vec()))),
            |e| matches!(e, WriteError::InvalidLanguageTag),
        ),
        (
            single(literal(b"a", LiteralKind::Language(b"en1".to_vec()))),
            |e| matches!(e, WriteError::InvalidLanguageTag),
        ),
        (
            single(literal(b"a", LiteralKind::Language(b"".to_vec()))),
            |e| matches!(e, WriteError::InvalidLanguageTag),
        ),
        (
            single(literal(
                b"a",
                LiteralKind::Datatype(iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#langString")),
            )),
            |e| matches!(e, WriteError::InvalidLiteralKind),
        ),
    ];
    for (graph, expected) in &cases {
        let ntriples::WriteResult::Error(error) = ntriples::write(graph, usize::MAX) else {
            panic!("N-Triples cannot carry the graph")
        };
        assert!(expected(&error));
        let turtle::WriteResult::Error(error) = turtle::write(graph, usize::MAX) else {
            panic!("Turtle cannot carry the graph")
        };
        assert!(expected(&error));
    }
}

#[test]
fn turtle_refuses_iris_that_resolution_changes() {
    use rowl_kernel::rdf_write::WriteError;
    let graph = single(Object::Iri(iri("https://example.org/a/../b")));
    assert!(matches!(
        turtle::write(&graph, usize::MAX),
        turtle::WriteResult::Error(WriteError::IriChangedByResolution)
    ));
    let ntriples::WriteResult::Bytes(bytes) = ntriples::write(&graph, usize::MAX) else {
        panic!("N-Triples carries the IRI unresolved")
    };
    let ntriples::ReadResult::Graph(read) = ntriples::read(&bytes, &b"s".to_vec()) else {
        panic!("the reader reads what the writer writes")
    };
    assert!(round_trip(&graph, &read, b"s"));
}

#[test]
fn the_first_fault_is_reported_before_any_budget() {
    use rowl_kernel::rdf_write::WriteError;
    let mut graph = sample();
    graph.triples.push(triple(
        Subject::Iri(iri("https://example.org/s")),
        "relative",
        Object::Iri(iri("https://example.org/o")),
    ));
    assert!(matches!(
        ntriples::write(&graph, 0),
        ntriples::WriteResult::Error(WriteError::InvalidIri)
    ));
}

#[test]
fn budgets_are_exact() {
    use rowl_kernel::rdf_write::WriteError;
    let graph = sample();
    let ntriples::WriteResult::Bytes(bytes) = ntriples::write(&graph, usize::MAX) else {
        panic!("the sample is representable")
    };
    for limit in [0, 1, bytes.len() / 2, bytes.len() - 1] {
        assert!(matches!(
            ntriples::write(&graph, limit),
            ntriples::WriteResult::Error(WriteError::ResourceLimit)
        ));
        assert!(matches!(
            turtle::write(&graph, limit),
            turtle::WriteResult::Error(WriteError::ResourceLimit)
        ));
    }
    assert!(
        matches!(ntriples::write(&graph, bytes.len()), ntriples::WriteResult::Bytes(b) if b == bytes)
    );
    assert!(
        matches!(turtle::write(&graph, bytes.len()), turtle::WriteResult::Bytes(b) if b == bytes)
    );
}
