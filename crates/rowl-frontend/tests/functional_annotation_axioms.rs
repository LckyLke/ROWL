use rowl_frontend::functional::{Keyword, Terminal};
use rowl_frontend::functional_annotation_axioms::{
    read_annotation_axiom, AnnotationAxiomError, AnnotationAxiomExpected, SourceAnnotationAxiom,
    SourceAnnotationAxiomBody, SourceAnnotationSubject,
};
use rowl_frontend::functional_annotations::{
    read_annotations, AnnotationError, AnnotationExpected, AnnotationLimits, SourceAnnotationValue,
};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_literals::SourceLiteralError;
use rowl_frontend::functional_names::NameError;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::prefixes::{check, Check};

const LABEL: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#label";
const COMMENT: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#comment";

fn limits(depth: usize, count: usize, iri: usize) -> AnnotationLimits {
    AnnotationLimits {
        depth,
        count,
        iri,
        lexical: 100,
    }
}
/// Read one annotation axiom at the first axiom position of a source document.
fn read(
    source: &str,
    limits: &AnnotationLimits,
) -> Result<(SourceAnnotationAxiom, Tokens), AnnotationAxiomError> {
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 200, 10, 100)
        .unwrap_or_else(|_| panic!("fixture prefix syntax must be complete"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("fixture declarations must form a normative prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("fixture header must be accepted"));
    let ontology = read_annotations(&table, &bytes, header.remaining, &self::limits(2, 10, 100))
        .unwrap_or_else(|_| panic!("fixture ontology annotations must be accepted"));
    read_annotation_axiom(&table, &bytes, ontology.remaining, limits)
}
fn ready(source: &str, limits: &AnnotationLimits) -> (SourceAnnotationAxiom, Tokens) {
    read(source, limits).unwrap_or_else(|_| panic!("fixture annotation axiom must be accepted"))
}
fn expected(
    result: Result<(SourceAnnotationAxiom, Tokens), AnnotationAxiomError>,
) -> (&'static str, usize) {
    match result {
        Err(AnnotationAxiomError::Expected { expected, offset }) => {
            let kind = match expected {
                AnnotationAxiomExpected::Keyword => "keyword",
                AnnotationAxiomExpected::Open => "open",
                AnnotationAxiomExpected::Property => "property",
                AnnotationAxiomExpected::Subject => "subject",
                AnnotationAxiomExpected::Iri => "iri",
                AnnotationAxiomExpected::Close => "close",
            };
            (kind, offset)
        }
        _ => panic!("expected the first source syntax failure"),
    }
}
fn closes_the_ontology(remaining: Tokens) -> bool {
    match remaining {
        Tokens::Cons { token, next } => {
            matches!(token.terminal, Terminal::Close) && matches!(*next, Tokens::Empty)
        }
        Tokens::Empty => false,
    }
}

#[test]
fn assertions_keep_property_subject_and_value_families() {
    let source = "Prefix(ex:=<https://example.org/plant#>) Ontology(\
        AnnotationAssertion(rdfs:label ex:pump \"Pumpe\"@de))";
    let (axiom, remaining) = ready(source, &limits(1, 10, 100));
    assert!(matches!(
        axiom.keyword.terminal,
        Terminal::Keyword(Keyword::AnnotationAssertion)
    ));
    assert!(axiom.annotations.is_empty());
    match axiom.body {
        SourceAnnotationAxiomBody::Assertion {
            property,
            subject,
            value,
        } => {
            assert_eq!(property.value, LABEL);
            match subject {
                SourceAnnotationSubject::Iri(iri) => {
                    assert_eq!(iri.value, b"https://example.org/plant#pump");
                    assert_eq!(&source[iri.token.start..iri.token.end], "ex:pump");
                }
                SourceAnnotationSubject::Anonymous { .. } => panic!("expected an IRI subject"),
            }
            match value {
                SourceAnnotationValue::Literal(literal) => {
                    assert_eq!(literal.lexical, b"Pumpe@de");
                }
                _ => panic!("expected a literal value"),
            }
        }
        _ => panic!("expected an assertion"),
    }
    assert!(closes_the_ontology(remaining));
    // Anonymous subjects keep their label; values may be IRIs or node IDs.
    let source = "Ontology(AnnotationAssertion(rdfs:seeAlso _:sheet <urn:manual>) \
        AnnotationAssertion(rdfs:seeAlso <urn:pump> _:sheet))";
    let (axiom, remaining) = ready(source, &limits(1, 10, 100));
    match axiom.body {
        SourceAnnotationAxiomBody::Assertion { subject, value, .. } => {
            assert!(matches!(
                subject,
                SourceAnnotationSubject::Anonymous { ref label, .. } if label == b"sheet"
            ));
            assert!(
                matches!(value, SourceAnnotationValue::Iri(ref iri) if iri.value == b"urn:manual")
            );
        }
        _ => panic!("expected an assertion"),
    }
    match remaining {
        Tokens::Cons { token, .. } => assert!(matches!(
            token.terminal,
            Terminal::Keyword(Keyword::AnnotationAssertion)
        )),
        Tokens::Empty => panic!("the second axiom must remain"),
    }
}

#[test]
fn subproperty_domain_and_range_keep_both_iris_and_axiom_annotations() {
    let source = "Prefix(ex:=<https://example.org/plant#>) Ontology(\
        SubAnnotationPropertyOf(Annotation(rdfs:comment \"narrower\") ex:shortLabel rdfs:label))";
    let (axiom, _) = ready(source, &limits(1, 10, 100));
    assert_eq!(axiom.annotations.len(), 1);
    assert_eq!(axiom.annotations[0].property.value, COMMENT);
    match axiom.body {
        SourceAnnotationAxiomBody::SubProperty {
            sub_property,
            super_property,
        } => {
            assert_eq!(sub_property.value, b"https://example.org/plant#shortLabel");
            assert_eq!(super_property.value, LABEL);
        }
        _ => panic!("expected a subproperty axiom"),
    }
    for (keyword, domain) in [
        ("AnnotationPropertyDomain", true),
        ("AnnotationPropertyRange", false),
    ] {
        let source = format!(
            "Prefix(ex:=<https://example.org/plant#>) Ontology({keyword}(ex:code ex:Machine))"
        );
        let (axiom, remaining) = ready(&source, &limits(1, 10, 100));
        let (property, target) = match axiom.body {
            SourceAnnotationAxiomBody::Domain {
                property,
                domain: target,
            } if domain => (property, target),
            SourceAnnotationAxiomBody::Range { property, range } if !domain => (property, range),
            _ => panic!("expected the {keyword} body"),
        };
        assert_eq!(property.value, b"https://example.org/plant#code");
        assert_eq!(target.value, b"https://example.org/plant#Machine");
        assert!(closes_the_ontology(remaining));
    }
}

#[test]
fn syntax_errors_report_the_first_missing_or_wrong_terminal() {
    let cases = [
        (
            "Ontology(Declaration(Class(<urn:a>)))",
            "keyword",
            "Declaration",
        ),
        (
            "Ontology(AnnotationAssertion rdfs:label <urn:a> \"x\"))",
            "open",
            "rdfs:label",
        ),
        (
            "Ontology(AnnotationAssertion(_:p <urn:a> \"x\"))",
            "property",
            "_:p",
        ),
        (
            "Ontology(AnnotationAssertion(rdfs:label \"x\" \"y\"))",
            "subject",
            "\"x\"",
        ),
        (
            "Ontology(AnnotationAssertion(rdfs:label <urn:a> \"x\" \"y\"))",
            "close",
            "\"y\"",
        ),
        (
            "Ontology(SubAnnotationPropertyOf(rdfs:label _:p))",
            "property",
            "_:p",
        ),
        (
            "Ontology(AnnotationPropertyDomain(rdfs:label \"x\"))",
            "iri",
            "\"x\"",
        ),
        (
            "Ontology(AnnotationPropertyRange(rdfs:label <urn:a> <urn:b>))",
            "close",
            "<urn:b>",
        ),
    ];
    for (source, kind, at) in cases {
        let offset = source.rfind(at).expect("fixture offset");
        assert_eq!(
            expected(read(source, &limits(1, 10, 100))),
            (kind, offset),
            "{source}"
        );
    }
    for (source, kind) in [
        ("Ontology(AnnotationAssertion", "open"),
        ("Ontology(AnnotationAssertion(", "property"),
        ("Ontology(AnnotationAssertion(rdfs:label", "subject"),
        ("Ontology(SubAnnotationPropertyOf(rdfs:label", "property"),
        ("Ontology(AnnotationPropertyRange(rdfs:label", "iri"),
        (
            "Ontology(AnnotationPropertyDomain(rdfs:label <urn:a>",
            "close",
        ),
    ] {
        assert_eq!(
            expected(read(source, &limits(1, 10, 100))),
            (kind, source.len()),
            "{source}"
        );
    }
    // A missing assertion value is the value reader's own diagnostic.
    let missing = "Ontology(AnnotationAssertion(rdfs:label <urn:a>))";
    assert!(matches!(
        read(missing, &limits(1, 10, 100)),
        Err(AnnotationAxiomError::Value(AnnotationError::Expected {
            expected: AnnotationExpected::Value,
            offset
        })) if offset == missing.rfind(')').expect("value position") - 1
    ));
}

#[test]
fn resolution_label_literal_and_annotation_failures_keep_their_typed_phase() {
    let property = "Ontology(AnnotationAssertion(nope:p <urn:a> \"x\"))";
    assert!(matches!(
        read(property, &limits(1, 10, 100)),
        Err(AnnotationAxiomError::Iri(SourceIriError::UndeclaredPrefix { offset }))
            if offset == property.find("nope").expect("property")
    ));
    let subject = "Ontology(AnnotationAssertion(rdfs:label nope:s \"x\"))";
    assert!(matches!(
        read(subject, &limits(1, 10, 100)),
        Err(AnnotationAxiomError::Iri(SourceIriError::UndeclaredPrefix { offset }))
            if offset == subject.find("nope").expect("subject")
    ));
    let label = "Ontology(AnnotationAssertion(<urn:p> _:motorcontroller \"x\"))";
    assert!(matches!(
        read(label, &limits(1, 10, 10)),
        Err(AnnotationAxiomError::Anonymous(NameError::ResourceLimit { offset }))
            if offset == label.find("_:").expect("label") + 2
    ));
    let literal = "Ontology(AnnotationAssertion(rdfs:label <urn:a> \"x\"^^nope:t))";
    assert!(matches!(
        read(literal, &limits(1, 10, 100)),
        Err(AnnotationAxiomError::Value(AnnotationError::Literal(
            SourceLiteralError::Datatype(SourceIriError::UndeclaredPrefix { .. })
        )))
    ));
    let target = "Ontology(AnnotationPropertyDomain(rdfs:label nope:C))";
    assert!(matches!(
        read(target, &limits(1, 10, 100)),
        Err(AnnotationAxiomError::Iri(SourceIriError::UndeclaredPrefix { offset }))
            if offset == target.find("nope").expect("domain")
    ));
    let annotated = "Ontology(AnnotationAssertion(Annotation(Annotation(rdfs:comment \"a\") \
        rdfs:comment \"b\") rdfs:label <urn:a> \"x\"))";
    let nested = annotated
        .match_indices("Annotation(")
        .nth(1)
        .expect("nested")
        .0;
    assert!(matches!(
        read(annotated, &limits(1, 10, 100)),
        Err(AnnotationAxiomError::Annotation(AnnotationError::DepthLimit { offset }))
            if offset == nested
    ));
    assert!(read(annotated, &limits(2, 10, 100)).is_ok());
}
