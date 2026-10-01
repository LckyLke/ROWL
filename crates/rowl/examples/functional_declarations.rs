//! Entity declarations, with their axiom annotations, from original source bytes.
use rowl::experimental::functional::{Keyword, Terminal};
use rowl::experimental::functional_annotations::{read_annotations, AnnotationLimits};
use rowl::experimental::functional_declarations::{read_declaration, SourceEntityKind};
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

fn kind(kind: SourceEntityKind) -> &'static str {
    match kind {
        SourceEntityKind::Class => "class",
        SourceEntityKind::Datatype => "datatype",
        SourceEntityKind::ObjectProperty => "object property",
        SourceEntityKind::DataProperty => "data property",
        SourceEntityKind::AnnotationProperty => "annotation property",
        SourceEntityKind::NamedIndividual => "named individual",
    }
}
fn at_declaration(tokens: &Tokens) -> bool {
    match tokens {
        Tokens::Cons { token, .. } => {
            matches!(token.terminal, Terminal::Keyword(Keyword::Declaration))
        }
        Tokens::Empty => false,
    }
}
fn main() {
    let bytes = include_bytes!("../../../examples/maintenance-declarations.ofn").to_vec();
    let prefix =
        read_prefix_header(&bytes, 200, 10, 100).unwrap_or_else(|_| panic!("source prefixes"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    let limits = AnnotationLimits {
        depth: 2,
        count: 10,
        iri: 100,
        lexical: 100,
    };
    let ontology = read_annotations(&table, &bytes, header.remaining, &limits)
        .unwrap_or_else(|_| panic!("ontology annotations"));
    // This loop selects declaration positions for the demo; the verified axiom
    // loop over all axiom forms is a later stage.
    let mut tokens = ontology.remaining;
    while at_declaration(&tokens) {
        let (declaration, rest) = read_declaration(&table, &bytes, tokens, &limits)
            .unwrap_or_else(|_| panic!("declaration"));
        println!(
            "Declares {} {} ({} axiom annotation(s))",
            kind(declaration.entity.kind),
            String::from_utf8_lossy(&declaration.entity.iri.value),
            declaration.annotations.len()
        );
        tokens = rest;
    }
    if let Tokens::Cons { token, .. } = tokens {
        println!(
            "Stopped at '{}', the ontology's closing token.",
            String::from_utf8_lossy(&bytes[token.start..token.end])
        );
    }
    println!("Declaration typing, the other axiom forms, the full axiom loop and OWL reasoning are separate stages.");
}
