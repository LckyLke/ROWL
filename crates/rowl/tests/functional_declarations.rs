use rowl::experimental::functional::{Keyword, Terminal};
use rowl::experimental::functional_annotations::{read_annotations, AnnotationLimits};
use rowl::experimental::functional_declarations::{
    read_declaration, DeclarationError, SourceDeclaration, SourceEntityKind,
};
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_iris::SourceIriError;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

const LIMITS: AnnotationLimits = AnnotationLimits {
    depth: 2,
    count: 10,
    iri: 100,
    lexical: 100,
};
fn starts_declaration(tokens: &Tokens) -> bool {
    match tokens {
        Tokens::Cons { token, .. } => {
            matches!(token.terminal, Terminal::Keyword(Keyword::Declaration))
        }
        Tokens::Empty => false,
    }
}
/// Read every leading declaration after the ontology annotations of a source.
fn declarations(bytes: &Vec<u8>) -> Result<(Vec<SourceDeclaration>, Tokens), DeclarationError> {
    let prefix = read_prefix_header(bytes, 200, 10, 100)
        .unwrap_or_else(|_| panic!("original prefix syntax"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("source table"),
    };
    let header = read_header_tail(&table, bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    let ontology = read_annotations(&table, bytes, header.remaining, &LIMITS)
        .unwrap_or_else(|_| panic!("ontology annotations"));
    let mut tokens = ontology.remaining;
    let mut found = Vec::new();
    while starts_declaration(&tokens) {
        let (declaration, rest) = read_declaration(&table, bytes, tokens, &LIMITS)?;
        found.push(declaration);
        tokens = rest;
    }
    Ok((found, tokens))
}
#[test]
fn public_reader_returns_every_maintenance_declaration_in_source_order() {
    let bytes = include_bytes!("../../../examples/maintenance-declarations.ofn").to_vec();
    let (found, remaining) = declarations(&bytes).unwrap_or_else(|_| panic!("declarations"));
    let summary: Vec<(&str, &[u8], usize)> = found
        .iter()
        .map(|declaration| {
            let kind = match declaration.entity.kind {
                SourceEntityKind::Class => "class",
                SourceEntityKind::Datatype => "datatype",
                SourceEntityKind::ObjectProperty => "object",
                SourceEntityKind::DataProperty => "data",
                SourceEntityKind::AnnotationProperty => "annotation",
                SourceEntityKind::NamedIndividual => "individual",
            };
            (
                kind,
                declaration.entity.iri.value.as_slice(),
                declaration.annotations.len(),
            )
        })
        .collect();
    assert_eq!(
        summary,
        vec![
            (
                "class",
                b"https://example.org/maintenance/Machine".as_slice(),
                0
            ),
            ("class", b"https://example.org/maintenance/FaultyPart", 0),
            ("object", b"https://example.org/maintenance/hasPart", 0),
            ("data", b"https://example.org/maintenance/faultCode", 0),
            ("individual", b"https://example.org/maintenance/pump1", 0),
            ("individual", b"https://example.org/maintenance/motor1", 1),
            (
                "annotation",
                b"https://example.org/maintenance/inspectedBy",
                0
            ),
        ]
    );
    match remaining {
        Tokens::Cons { token, next } => {
            assert!(matches!(token.terminal, Terminal::Close));
            assert!(matches!(*next, Tokens::Empty));
        }
        Tokens::Empty => panic!("the ontology closing token must remain"),
    }
}
#[test]
fn public_reader_reports_an_undeclared_entity_prefix() {
    let bytes = b"Ontology(Declaration(Class(nope:Pump)))".to_vec();
    assert!(matches!(
        declarations(&bytes),
        Err(DeclarationError::Iri(SourceIriError::UndeclaredPrefix {
            offset: 27
        }))
    ));
}
