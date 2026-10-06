use rowl::experimental::functional::{Keyword, Terminal};
use rowl::experimental::functional_annotations::{read_annotations, AnnotationLimits};
use rowl::experimental::functional_class_axioms::{read_class_axiom, SourceClassAxiomBody};
use rowl::experimental::functional_classes::ClassLimits;
use rowl::experimental::functional_declarations::read_declaration;
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

const ANNOTATIONS: AnnotationLimits = AnnotationLimits {
    depth: 2,
    count: 10,
    iri: 100,
    lexical: 100,
};
const CLASSES: ClassLimits = ClassLimits {
    depth: 10,
    count: 10,
    iri: 100,
};
fn first_terminal(tokens: &Tokens) -> Option<Terminal> {
    match tokens {
        Tokens::Cons { token, .. } => Some(token.terminal),
        Tokens::Empty => None,
    }
}

#[test]
fn every_maintenance_axiom_reads_in_source_order() {
    let bytes = include_bytes!("../../../examples/maintenance-classes.ofn").to_vec();
    let prefix = read_prefix_header(&bytes, 400, 10, 100)
        .unwrap_or_else(|_| panic!("original prefix syntax"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("source table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    let ontology = read_annotations(&table, &bytes, header.remaining, &ANNOTATIONS)
        .unwrap_or_else(|_| panic!("ontology annotations"));
    let mut tokens = ontology.remaining;
    let mut summary = Vec::new();
    loop {
        match first_terminal(&tokens) {
            Some(Terminal::Keyword(Keyword::Declaration)) => {
                let (_, rest) = read_declaration(&table, &bytes, tokens, &ANNOTATIONS)
                    .unwrap_or_else(|_| panic!("declaration"));
                summary.push("declaration");
                tokens = rest;
            }
            Some(Terminal::Close) => break,
            _ => {
                let (axiom, rest) =
                    read_class_axiom(&table, &bytes, tokens, &ANNOTATIONS, &CLASSES)
                        .unwrap_or_else(|_| panic!("class axiom"));
                summary.push(match axiom.body {
                    SourceClassAxiomBody::SubClassOf { .. } => "subclass",
                    SourceClassAxiomBody::EquivalentClasses(_) => "equivalent",
                    SourceClassAxiomBody::DisjointClasses(_) => "disjoint",
                    SourceClassAxiomBody::DisjointUnion { .. } => "union",
                    SourceClassAxiomBody::ObjectPropertyDomain { .. } => "domain",
                    SourceClassAxiomBody::ObjectPropertyRange { .. } => "range",
                });
                tokens = rest;
            }
        }
    }
    assert_eq!(
        summary,
        [
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "declaration",
            "subclass",
            "subclass",
            "range",
            "domain",
            "disjoint",
            "union",
            "equivalent",
            "subclass"
        ]
    );
}
