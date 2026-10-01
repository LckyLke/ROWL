use rowl_frontend::functional::{Keyword, Terminal};
use rowl_frontend::functional_annotations::{
    read_annotations, AnnotationError, AnnotationExpected, AnnotationLimits, SourceAnnotation,
    SourceAnnotationValue, SourceAnnotations,
};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::{lex, LexResult, Tokens};
use rowl_frontend::functional_literals::{SourceLiteralError, SourceLiteralForm};
use rowl_frontend::functional_names::NameError;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::prefixes::{check, Check};

const PLAIN: &[u8] = b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const LABEL: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#label";
const COMMENT: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#comment";

fn limits(depth: usize, count: usize) -> AnnotationLimits {
    AnnotationLimits {
        depth,
        count,
        iri: 100,
        lexical: 100,
    }
}
/// Read the ontology annotations that follow the actual source header.
fn read(source: &str, limits: &AnnotationLimits) -> Result<SourceAnnotations, AnnotationError> {
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 200, 10, 100)
        .unwrap_or_else(|_| panic!("fixture prefix syntax must be complete"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("fixture declarations must form a normative prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("fixture header must be accepted"));
    read_annotations(&table, &bytes, header.remaining, limits)
}
fn ready(source: &str, limits: &AnnotationLimits) -> SourceAnnotations {
    read(source, limits).unwrap_or_else(|_| panic!("fixture annotations must be accepted"))
}
fn expected(result: Result<SourceAnnotations, AnnotationError>) -> (&'static str, usize) {
    match result {
        Err(AnnotationError::Expected { expected, offset }) => {
            let kind = match expected {
                AnnotationExpected::Open => "open",
                AnnotationExpected::Property => "property",
                AnnotationExpected::Value => "value",
                AnnotationExpected::Close => "close",
            };
            (kind, offset)
        }
        _ => panic!("expected the first source syntax failure"),
    }
}
fn spelling(source: &str, start: usize, end: usize) -> &str {
    &source[start..end]
}
fn literal(annotation: &SourceAnnotation) -> (&[u8], &[u8]) {
    match &annotation.value {
        SourceAnnotationValue::Literal(literal) => (&literal.lexical, &literal.datatype),
        _ => panic!("expected a literal annotation value"),
    }
}

#[test]
fn ontology_annotations_keep_source_order_tokens_and_all_value_families() {
    let source = "Prefix(ex:=<https://example.org/plant#>) Ontology(ex:plant \
        Annotation(rdfs:label \"Pumpe 7\"@de) Annotation(ex:part ex:motor) \
        Annotation(ex:spare _:motor2) Annotation(<urn:code> \"007\"^^xsd:integer) \
        Declaration(Class(ex:Pump)))";
    let output = ready(source, &limits(1, 10));
    assert_eq!(output.annotations.len(), 4);
    for annotation in &output.annotations {
        assert!(matches!(
            annotation.keyword.terminal,
            Terminal::Keyword(Keyword::Annotation)
        ));
        assert_eq!(
            spelling(source, annotation.keyword.start, annotation.keyword.end),
            "Annotation"
        );
        assert!(annotation.annotations.is_empty());
    }
    let first = &output.annotations[0];
    assert_eq!(first.property.value, LABEL);
    assert_eq!(
        spelling(source, first.property.token.start, first.property.token.end),
        "rdfs:label"
    );
    assert_eq!(literal(first), (b"Pumpe 7@de".as_slice(), PLAIN));
    match &output.annotations[1].value {
        SourceAnnotationValue::Iri(iri) => {
            assert_eq!(iri.value, b"https://example.org/plant#motor");
            assert_eq!(spelling(source, iri.token.start, iri.token.end), "ex:motor");
        }
        _ => panic!("expected an IRI value"),
    }
    match &output.annotations[2].value {
        SourceAnnotationValue::Anonymous { token, label } => {
            assert_eq!(label, b"motor2");
            assert_eq!(spelling(source, token.start, token.end), "_:motor2");
            assert!(matches!(token.terminal, Terminal::NodeId));
        }
        _ => panic!("expected an anonymous value"),
    }
    let fourth = &output.annotations[3];
    assert_eq!(fourth.property.value, b"urn:code");
    assert_eq!(
        literal(fourth),
        (
            b"007".as_slice(),
            b"http://www.w3.org/2001/XMLSchema#integer".as_slice()
        )
    );
    match output.remaining {
        Tokens::Cons { token, .. } => {
            assert!(matches!(
                token.terminal,
                Terminal::Keyword(Keyword::Declaration)
            ));
            assert_eq!(&source[token.start..token.end], "Declaration");
        }
        Tokens::Empty => panic!("the first axiom must remain unparsed"),
    }
}

#[test]
fn nested_annotations_are_read_recursively_in_source_order() {
    let source = "Ontology(Annotation(Annotation(Annotation(rdfs:comment \"deep\") \
        rdfs:comment \"middle\") Annotation(rdfs:comment \"sibling\") rdfs:label \"outer\"))";
    let output = ready(source, &limits(3, 10));
    assert_eq!(output.annotations.len(), 1);
    let outer = &output.annotations[0];
    assert_eq!(outer.property.value, LABEL);
    assert_eq!(literal(outer).0, b"outer@");
    assert_eq!(outer.annotations.len(), 2);
    let middle = &outer.annotations[0];
    assert_eq!(middle.property.value, COMMENT);
    assert_eq!(literal(middle).0, b"middle@");
    assert_eq!(middle.annotations.len(), 1);
    assert_eq!(literal(&middle.annotations[0]).0, b"deep@");
    assert!(middle.annotations[0].annotations.is_empty());
    assert_eq!(literal(&outer.annotations[1]).0, b"sibling@");
    match output.remaining {
        Tokens::Cons { token, next } => {
            assert!(matches!(token.terminal, Terminal::Close));
            assert!(matches!(*next, Tokens::Empty));
        }
        Tokens::Empty => panic!("the ontology closing token must remain"),
    }
}

#[test]
fn nesting_depth_is_checked_at_the_first_annotation_beyond_the_allowance() {
    let source = "Ontology(Annotation(Annotation(Annotation(rdfs:comment \"deep\") \
        rdfs:comment \"middle\") rdfs:label \"outer\"))";
    let innermost = source
        .match_indices("Annotation")
        .nth(2)
        .expect("innermost")
        .0;
    assert!(read(source, &limits(3, 10)).is_ok());
    assert!(matches!(
        read(source, &limits(2, 10)),
        Err(AnnotationError::DepthLimit { offset }) if offset == innermost
    ));
    let first = source.find("Annotation").expect("outer keyword");
    assert!(matches!(
        read(source, &limits(0, 10)),
        Err(AnnotationError::DepthLimit { offset }) if offset == first
    ));
    // A zero allowance still accepts a sequence without annotations.
    let output = ready("Ontology(Declaration(Class(<urn:a>)))", &limits(0, 0));
    assert!(output.annotations.is_empty());
}

#[test]
fn count_limits_apply_to_each_sequence_separately() {
    let two = "Ontology(Annotation(rdfs:label \"a\") Annotation(rdfs:label \"b\"))";
    let second = two.match_indices("Annotation").nth(1).expect("second").0;
    assert!(matches!(
        read(two, &limits(1, 1)),
        Err(AnnotationError::CountLimit { offset }) if offset == second
    ));
    assert_eq!(ready(two, &limits(1, 2)).annotations.len(), 2);
    let nested = "Ontology(Annotation(Annotation(rdfs:comment \"x\") \
        Annotation(rdfs:comment \"y\") rdfs:label \"a\"))";
    let nested_second = nested.match_indices("Annotation").nth(2).expect("nested").0;
    assert!(matches!(
        read(nested, &limits(2, 1)),
        Err(AnnotationError::CountLimit { offset }) if offset == nested_second
    ));
    let output = ready(nested, &limits(2, 2));
    assert_eq!(output.annotations.len(), 1);
    assert_eq!(output.annotations[0].annotations.len(), 2);
    // The depth check precedes the count check at the same keyword.
    assert!(matches!(
        read(two, &limits(0, 0)),
        Err(AnnotationError::DepthLimit { .. })
    ));
}

#[test]
fn syntax_errors_report_the_first_missing_or_wrong_terminal() {
    let cases = [
        (
            "Ontology(Annotation rdfs:label \"x\"))",
            "open",
            "rdfs:label",
        ),
        (
            "Ontology(Annotation(\"x\" rdfs:label))",
            "property",
            "\"x\"",
        ),
        ("Ontology(Annotation(_:a rdfs:label))", "property", "_:a"),
        ("Ontology(Annotation(rdfs:label))", "value", ")"),
        (
            "Ontology(Annotation(rdfs:label Class(<urn:a>)))",
            "value",
            "Class",
        ),
        (
            "Ontology(Annotation(rdfs:label \"x\" \"y\"))",
            "close",
            "\"y\"",
        ),
        (
            "Ontology(Annotation(rdfs:label <urn:a> <urn:b>))",
            "close",
            "<urn:b>",
        ),
        (
            "Ontology(Annotation(Annotation(rdfs:label) rdfs:label \"x\"))",
            "value",
            ")",
        ),
    ];
    for (source, kind, at) in cases {
        let offset = source.rfind(at).expect("fixture offset");
        let offset = if at == ")" {
            source.find(at).expect("first closing token")
        } else {
            offset
        };
        assert_eq!(
            expected(read(source, &limits(2, 10))),
            (kind, offset),
            "{source}"
        );
    }
    for (source, kind) in [
        ("Ontology(Annotation", "open"),
        ("Ontology(Annotation(", "property"),
        ("Ontology(Annotation(rdfs:label", "value"),
        ("Ontology(Annotation(rdfs:label \"x\"", "close"),
    ] {
        assert_eq!(
            expected(read(source, &limits(2, 10))),
            (kind, source.len()),
            "{source}"
        );
    }
}

#[test]
fn property_value_label_and_literal_failures_keep_their_typed_phase() {
    let undeclared = "Ontology(Annotation(nope:label \"x\"))";
    assert!(matches!(
        read(undeclared, &limits(1, 10)),
        Err(AnnotationError::Property(SourceIriError::UndeclaredPrefix { offset }))
            if offset == undeclared.find("nope").expect("property")
    ));
    let value = "Ontology(Annotation(rdfs:seeAlso nope:part))";
    assert!(matches!(
        read(value, &limits(1, 10)),
        Err(AnnotationError::Iri(SourceIriError::UndeclaredPrefix { offset }))
            if offset == value.find("nope").expect("value")
    ));
    let typed = "Ontology(Annotation(rdfs:label \"7\"^^nope:int))";
    assert!(matches!(
        read(typed, &limits(1, 10)),
        Err(AnnotationError::Literal(SourceLiteralError::Datatype(
            SourceIriError::UndeclaredPrefix { .. }
        )))
    ));
    let label = "Ontology(Annotation(rdfs:seeAlso _:motor))";
    let tight = AnnotationLimits {
        depth: 1,
        count: 10,
        iri: 4,
        lexical: 100,
    };
    // The property is checked first, so its budget failure wins over the label.
    assert!(matches!(
        read(label, &tight),
        Err(AnnotationError::Property(
            SourceIriError::ResourceLimit { .. }
        ))
    ));
    let roomy_property = AnnotationLimits {
        depth: 1,
        count: 10,
        iri: 10,
        lexical: 100,
    };
    // The label budget excludes the `_:` marker; its offset is the label start.
    let long_label = "Ontology(Annotation(<urn:p> _:motorcontroller))";
    let label_start = long_label.find("_:").expect("label") + 2;
    assert!(matches!(
        read(long_label, &roomy_property),
        Err(AnnotationError::Anonymous(NameError::ResourceLimit { offset })) if offset == label_start
    ));
    assert!(read(
        "Ontology(Annotation(<urn:p> _:motor10chr))",
        &roomy_property
    )
    .is_ok());
    let short = AnnotationLimits {
        depth: 1,
        count: 10,
        iri: 100,
        lexical: 3,
    };
    let text = "Ontology(Annotation(rdfs:label \"abc\"))";
    assert!(matches!(
        read(text, &short),
        Err(AnnotationError::Literal(SourceLiteralError::LexicalLimit { offset }))
            if offset == text.find('"').expect("quote")
    ));
    let full = AnnotationLimits {
        depth: 1,
        count: 10,
        iri: 7,
        lexical: 100,
    };
    let long = "Ontology(Annotation(<urn:property> \"x\"))";
    assert!(matches!(
        read(long, &full),
        Err(AnnotationError::Property(SourceIriError::Name(
            NameError::ResourceLimit { .. }
        )))
    ));
}

#[test]
fn nested_failures_take_priority_over_later_outer_parts() {
    let nested = "Ontology(Annotation(Annotation(nope:x \"a\") nope:y \"b\"))";
    assert!(matches!(
        read(nested, &limits(2, 10)),
        Err(AnnotationError::Property(SourceIriError::UndeclaredPrefix { offset }))
            if offset == nested.find("nope:x").expect("nested property")
    ));
    let outer = "Ontology(Annotation(Annotation(rdfs:comment \"a\") nope:y \"b\"))";
    assert!(matches!(
        read(outer, &limits(2, 10)),
        Err(AnnotationError::Property(SourceIriError::UndeclaredPrefix { offset }))
            if offset == outer.find("nope:y").expect("outer property")
    ));
    // A complete later annotation cannot hide an earlier failure.
    let earlier = "Ontology(Annotation(rdfs:label) Annotation(rdfs:label \"b\"))";
    assert_eq!(
        expected(read(earlier, &limits(1, 10))),
        ("value", earlier.find(')').expect("value position"))
    );
}

#[test]
fn literal_shortcuts_expand_and_typed_spelling_is_preserved_inside_annotations() {
    let source = "Ontology(Annotation(rdfs:label \"mail@example.org\") \
        Annotation(rdfs:label \"Gerät\"@DE-Latn) Annotation(rdfs:label \"+01\"^^xsd:integer))";
    let output = ready(source, &limits(1, 10));
    assert_eq!(
        literal(&output.annotations[0]),
        (b"mail@example.org@".as_slice(), PLAIN)
    );
    assert_eq!(
        literal(&output.annotations[1]),
        ("Gerät@DE-Latn".as_bytes(), PLAIN)
    );
    match &output.annotations[2].value {
        SourceAnnotationValue::Literal(literal) => {
            assert_eq!(literal.lexical, b"+01");
            assert!(matches!(literal.form, SourceLiteralForm::Typed { .. }));
        }
        _ => panic!("expected a typed literal"),
    }
}

#[test]
fn absent_annotations_and_unexpected_suffixes_remain_unchanged() {
    let output = ready("Ontology()", &limits(1, 0));
    assert!(output.annotations.is_empty());
    assert!(matches!(output.remaining, Tokens::Cons { .. }));
    let bytes = Vec::new();
    let rows = Vec::new();
    let table = match check(&rows) {
        Check::Ready(table) => table,
        _ => panic!("empty table"),
    };
    let output = read_annotations(&table, &bytes, Tokens::Empty, &limits(1, 1))
        .unwrap_or_else(|_| panic!("empty token stream"));
    assert!(output.annotations.is_empty());
    assert!(matches!(output.remaining, Tokens::Empty));
    // The reader does not validate tokens after the maximal annotation run.
    let source = b"Annotation(rdfs:label \"x\") ) ) Prefix".to_vec();
    let tokens = match lex(&source, 100) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("fixture must lex"),
    };
    let output = read_annotations(&table, &source, tokens, &limits(1, 5))
        .unwrap_or_else(|_| panic!("leading annotation"));
    assert_eq!(output.annotations.len(), 1);
    match output.remaining {
        Tokens::Cons { token, .. } => assert_eq!(token.start, source.len() - ") ) Prefix".len()),
        Tokens::Empty => panic!("suffix must remain"),
    }
}

#[test]
fn unicode_source_offsets_are_original_byte_positions() {
    let source = "Prefix(設備:=<https://example.org/設備#>) Ontology(\
        Annotation(設備:名前 \"ポンプ\"@ja) Annotation(設備:名前 nope:x))";
    let failure = read(source, &limits(1, 10));
    let offset = source.find("nope:x").expect("multibyte offset");
    assert!(matches!(
        failure,
        Err(AnnotationError::Iri(SourceIriError::UndeclaredPrefix { offset: actual })) if actual == offset
    ));
    let output = ready(
        "Prefix(設備:=<https://example.org/設備#>) Ontology(Annotation(設備:名前 \"ポンプ\"@ja))",
        &limits(1, 10),
    );
    assert_eq!(
        output.annotations[0].property.value,
        "https://example.org/設備#名前".as_bytes()
    );
    assert_eq!(literal(&output.annotations[0]).0, "ポンプ@ja".as_bytes());
}
