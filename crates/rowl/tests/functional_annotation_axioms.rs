use rowl::experimental::functional::{Keyword, Terminal};
use rowl::experimental::functional_annotation_axioms::{
    read_annotation_axiom, AnnotationAxiomError, SourceAnnotationAxiom, SourceAnnotationAxiomBody,
    SourceAnnotationSubject,
};
use rowl::experimental::functional_annotations::{
    read_annotations, AnnotationLimits, SourceAnnotationValue,
};
use rowl::experimental::functional_declarations::read_declaration;
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

const LIMITS: AnnotationLimits = AnnotationLimits {
    depth: 2,
    count: 10,
    iri: 100,
    lexical: 100,
};
fn keyword(tokens: &Tokens) -> Option<Keyword> {
    match tokens {
        Tokens::Cons { token, .. } => match token.terminal {
            Terminal::Keyword(keyword) => Some(keyword),
            _ => None,
        },
        Tokens::Empty => None,
    }
}
/// Skip the leading declarations, then read every annotation axiom that follows.
fn annotation_axioms(
    bytes: &Vec<u8>,
) -> Result<(Vec<SourceAnnotationAxiom>, Tokens), AnnotationAxiomError> {
    let prefix = read_prefix_header(bytes, 300, 10, 100)
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
    while matches!(keyword(&tokens), Some(Keyword::Declaration)) {
        tokens = read_declaration(&table, bytes, tokens, &LIMITS)
            .unwrap_or_else(|_| panic!("declaration"))
            .1;
    }
    let mut found = Vec::new();
    while matches!(
        keyword(&tokens),
        Some(
            Keyword::AnnotationAssertion
                | Keyword::SubAnnotationPropertyOf
                | Keyword::AnnotationPropertyDomain
                | Keyword::AnnotationPropertyRange
        )
    ) {
        let (axiom, rest) = read_annotation_axiom(&table, bytes, tokens, &LIMITS)?;
        found.push(axiom);
        tokens = rest;
    }
    Ok((found, tokens))
}
#[test]
fn public_reader_returns_the_maintenance_annotation_axioms_in_source_order() {
    let bytes = include_bytes!("../../../examples/maintenance-vocabulary.ofn").to_vec();
    let (found, remaining) =
        annotation_axioms(&bytes).unwrap_or_else(|_| panic!("annotation axioms"));
    assert_eq!(found.len(), 6);
    assert!(matches!(
        &found[0].body,
        SourceAnnotationAxiomBody::SubProperty { super_property, .. }
            if super_property.value == b"http://www.w3.org/2000/01/rdf-schema#label"
    ));
    assert!(matches!(
        &found[1].body,
        SourceAnnotationAxiomBody::Domain { domain, .. }
            if domain.value == b"https://example.org/maintenance/Machine"
    ));
    assert!(matches!(
        &found[2].body,
        SourceAnnotationAxiomBody::Range { range, .. }
            if range.value == b"http://www.w3.org/2001/XMLSchema#integer"
    ));
    match &found[4].body {
        SourceAnnotationAxiomBody::Assertion { subject, value, .. } => {
            assert!(matches!(
                subject,
                SourceAnnotationSubject::Iri(iri) if iri.value == b"https://example.org/maintenance/pump1"
            ));
            assert!(matches!(
                value,
                SourceAnnotationValue::Anonymous { label, .. } if label == b"inspector"
            ));
        }
        _ => panic!("inspection assertion"),
    }
    assert_eq!(found[4].annotations.len(), 1);
    match remaining {
        Tokens::Cons { token, next } => {
            assert!(matches!(token.terminal, Terminal::Close));
            assert!(matches!(*next, Tokens::Empty));
        }
        Tokens::Empty => panic!("the ontology closing token must remain"),
    }
}
#[test]
fn public_reader_rejects_a_literal_annotation_subject() {
    let bytes = b"Ontology(AnnotationAssertion(rdfs:label \"x\" \"y\"))".to_vec();
    assert!(matches!(
        annotation_axioms(&bytes),
        Err(AnnotationAxiomError::Expected { offset: 40, .. })
    ));
}
