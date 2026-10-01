use rowl_frontend::functional::{Keyword, Terminal};
use rowl_frontend::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotationValue,
};
use rowl_frontend::functional_declarations::{
    read_declaration, DeclarationError, DeclarationExpected, SourceDeclaration, SourceEntityKind,
};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::{lex, LexResult, Tokens};
use rowl_frontend::functional_names::NameError;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::prefixes::{check, Check};

fn limits(depth: usize, count: usize, iri: usize) -> AnnotationLimits {
    AnnotationLimits {
        depth,
        count,
        iri,
        lexical: 100,
    }
}
/// Read one declaration at the first axiom position of a complete source
/// document: after the header and its ontology annotations.
fn read(
    source: &str,
    limits: &AnnotationLimits,
) -> Result<(SourceDeclaration, Tokens), DeclarationError> {
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
    read_declaration(&table, &bytes, ontology.remaining, limits)
}
fn ready(source: &str, limits: &AnnotationLimits) -> (SourceDeclaration, Tokens) {
    read(source, limits).unwrap_or_else(|_| panic!("fixture declaration must be accepted"))
}
fn expected(
    result: Result<(SourceDeclaration, Tokens), DeclarationError>,
) -> (&'static str, usize) {
    match result {
        Err(DeclarationError::Expected { expected, offset }) => {
            let kind = match expected {
                DeclarationExpected::Declaration => "declaration",
                DeclarationExpected::Open => "open",
                DeclarationExpected::Entity => "entity",
                DeclarationExpected::Iri => "iri",
                DeclarationExpected::Close => "close",
            };
            (kind, offset)
        }
        _ => panic!("expected the first source syntax failure"),
    }
}
fn kind_name(kind: SourceEntityKind) -> &'static str {
    match kind {
        SourceEntityKind::Class => "Class",
        SourceEntityKind::Datatype => "Datatype",
        SourceEntityKind::ObjectProperty => "ObjectProperty",
        SourceEntityKind::DataProperty => "DataProperty",
        SourceEntityKind::AnnotationProperty => "AnnotationProperty",
        SourceEntityKind::NamedIndividual => "NamedIndividual",
    }
}

#[test]
fn all_six_entity_kinds_keep_their_keyword_and_exact_iri() {
    for keyword in [
        "Class",
        "Datatype",
        "ObjectProperty",
        "DataProperty",
        "AnnotationProperty",
        "NamedIndividual",
    ] {
        let source = format!(
            "Prefix(ex:=<https://example.org/plant#>) Ontology(Declaration({keyword}(ex:Pump)))"
        );
        let (declaration, remaining) = ready(&source, &limits(1, 10, 100));
        assert_eq!(kind_name(declaration.entity.kind), keyword);
        let entity = &declaration.entity;
        assert_eq!(&source[entity.keyword.start..entity.keyword.end], keyword);
        assert_eq!(entity.iri.value, b"https://example.org/plant#Pump");
        assert_eq!(
            &source[entity.iri.token.start..entity.iri.token.end],
            "ex:Pump"
        );
        assert!(matches!(
            declaration.keyword.terminal,
            Terminal::Keyword(Keyword::Declaration)
        ));
        assert!(declaration.annotations.is_empty());
        match remaining {
            Tokens::Cons { token, next } => {
                assert!(matches!(token.terminal, Terminal::Close));
                assert!(matches!(*next, Tokens::Empty));
            }
            Tokens::Empty => panic!("the ontology closing token must remain"),
        }
    }
}

#[test]
fn axiom_annotations_are_read_with_the_annotation_contract() {
    let source = "Ontology(Declaration(Annotation(Annotation(rdfs:comment \"checked\") \
        rdfs:label \"Pumpe\"@de) Annotation(rdfs:seeAlso _:sheet) Class(<urn:pump>)) \
        Declaration(Class(<urn:motor>)))";
    let (declaration, remaining) = ready(source, &limits(2, 10, 100));
    assert_eq!(declaration.annotations.len(), 2);
    assert_eq!(declaration.annotations[0].annotations.len(), 1);
    assert!(matches!(
        &declaration.annotations[1].value,
        SourceAnnotationValue::Anonymous { label, .. } if label == b"sheet"
    ));
    assert!(matches!(declaration.entity.kind, SourceEntityKind::Class));
    assert_eq!(declaration.entity.iri.value, b"urn:pump");
    match remaining {
        Tokens::Cons { token, .. } => {
            assert!(matches!(
                token.terminal,
                Terminal::Keyword(Keyword::Declaration)
            ));
            assert_eq!(token.start, source.rfind("Declaration").expect("second"));
        }
        Tokens::Empty => panic!("the next axiom must remain unparsed"),
    }
    // Annotation limits apply to axiom annotations too.
    let nested = source.match_indices("Annotation").nth(1).expect("nested").0;
    assert!(matches!(
        read(source, &limits(1, 10, 100)),
        Err(DeclarationError::Annotation(AnnotationError::DepthLimit { offset })) if offset == nested
    ));
    let second = source
        .match_indices("Annotation(")
        .nth(2)
        .expect("second annotation")
        .0;
    assert!(matches!(
        read(source, &limits(2, 1, 100)),
        Err(DeclarationError::Annotation(AnnotationError::CountLimit { offset })) if offset == second
    ));
}

#[test]
fn syntax_errors_report_the_first_missing_or_wrong_terminal() {
    let cases = [
        (
            "Ontology(SubClassOf(<urn:a> <urn:b>))",
            "declaration",
            "SubClassOf",
        ),
        ("Ontology(Declaration Class(<urn:a>)))", "open", "Class"),
        ("Ontology(Declaration(<urn:a>))", "entity", "<urn:a>"),
        (
            "Ontology(Declaration(ObjectInverseOf(<urn:a>)))",
            "entity",
            "ObjectInverseOf",
        ),
        ("Ontology(Declaration(owl:Thing))", "entity", "owl:Thing"),
        ("Ontology(Declaration(Class <urn:a>))", "open", "<urn:a>"),
        ("Ontology(Declaration(Class(_:a)))", "iri", "_:a"),
        ("Ontology(Declaration(Class(\"a\")))", "iri", "\"a\""),
        (
            "Ontology(Declaration(Class(<urn:a> <urn:b>)))",
            "close",
            "<urn:b>",
        ),
        (
            "Ontology(Declaration(Class(<urn:a>) <urn:b>))",
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
        ("Ontology(Declaration", "open"),
        ("Ontology(Declaration(", "entity"),
        ("Ontology(Declaration(Class", "open"),
        ("Ontology(Declaration(Class(", "iri"),
        ("Ontology(Declaration(Class(<urn:a>", "close"),
        ("Ontology(Declaration(Class(<urn:a>)", "close"),
    ] {
        assert_eq!(
            expected(read(source, &limits(1, 10, 100))),
            (kind, source.len()),
            "{source}"
        );
    }
    let table_rows = Vec::new();
    let table = match check(&table_rows) {
        Check::Ready(table) => table,
        _ => panic!("empty table"),
    };
    assert_eq!(
        expected(read_declaration(
            &table,
            &Vec::new(),
            Tokens::Empty,
            &limits(1, 1, 10)
        )),
        ("declaration", 0)
    );
}

#[test]
fn entity_iri_resolution_and_budget_failures_keep_their_typed_phase() {
    let undeclared = "Ontology(Declaration(Class(nope:Pump)))";
    assert!(matches!(
        read(undeclared, &limits(1, 10, 100)),
        Err(DeclarationError::Iri(SourceIriError::UndeclaredPrefix { offset }))
            if offset == undeclared.find("nope").expect("entity IRI")
    ));
    let full = "Ontology(Declaration(Class(<urn:longer>)))";
    assert!(matches!(
        read(full, &limits(1, 10, 5)),
        Err(DeclarationError::Iri(SourceIriError::Name(NameError::ResourceLimit { offset })))
            if offset == full.find("<urn").expect("full IRI") + 1
    ));
    assert!(read(full, &limits(1, 10, 10)).is_ok());
    // Source order: the IRI is resolved before the missing closing tokens.
    assert!(matches!(
        read("Ontology(Declaration(Class(nope:Pump", &limits(1, 10, 100)),
        Err(DeclarationError::Iri(
            SourceIriError::UndeclaredPrefix { .. }
        ))
    ));
    // Annotation failures come before any entity syntax.
    let annotated = "Ontology(Declaration(Annotation(nope:p \"x\") Class <urn:a>))";
    assert!(matches!(
        read(annotated, &limits(1, 10, 100)),
        Err(DeclarationError::Annotation(AnnotationError::Property(
            SourceIriError::UndeclaredPrefix { .. }
        )))
    ));
}

#[test]
fn reserved_and_punned_names_are_read_without_typing_checks() {
    // Declaration typing, punning and reserved vocabulary are later checks;
    // the reader only constructs the exact source declaration.
    for source in [
        "Ontology(Declaration(ObjectProperty(owl:Thing)))",
        "Ontology(Declaration(Class(<urn:x>)) Declaration(NamedIndividual(<urn:x>)))",
    ] {
        let (declaration, _) = ready(source, &limits(1, 10, 100));
        assert!(!declaration.entity.iri.value.is_empty());
    }
}

#[test]
fn declaration_tokens_and_multibyte_offsets_are_original() {
    let source = "Prefix(設備:=<https://example.org/設備#>) Ontology(\
        Declaration(Annotation(rdfs:label \"ポンプ\"@ja) Class(設備:ポンプ)))";
    let (declaration, _) = ready(source, &limits(1, 10, 100));
    assert_eq!(
        declaration.entity.iri.value,
        "https://example.org/設備#ポンプ".as_bytes()
    );
    assert_eq!(
        &source[declaration.keyword.start..declaration.keyword.end],
        "Declaration"
    );
    let bytes = source.as_bytes().to_vec();
    let tokens = match lex(&bytes, 100) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("fixture must lex"),
    };
    // Not at a declaration position: the first token is `Prefix`.
    let table_rows = Vec::new();
    let table = match check(&table_rows) {
        Check::Ready(table) => table,
        _ => panic!("empty table"),
    };
    assert_eq!(
        expected(read_declaration(
            &table,
            &bytes,
            tokens,
            &limits(1, 10, 100)
        )),
        ("declaration", 0)
    );
}
