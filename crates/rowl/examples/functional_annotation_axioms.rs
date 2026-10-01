//! Declarations and annotation axioms from original source bytes.
use rowl::experimental::functional::{Keyword, Terminal};
use rowl::experimental::functional_annotation_axioms::{
    read_annotation_axiom, SourceAnnotationAxiomBody, SourceAnnotationSubject,
};
use rowl::experimental::functional_annotations::{
    read_annotations, AnnotationLimits, SourceAnnotationValue,
};
use rowl::experimental::functional_declarations::read_declaration;
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}
fn subject(subject: &SourceAnnotationSubject) -> String {
    match subject {
        SourceAnnotationSubject::Iri(iri) => text(&iri.value),
        SourceAnnotationSubject::Anonymous { label, .. } => format!("_:{}", text(label)),
    }
}
fn value(value: &SourceAnnotationValue) -> String {
    match value {
        SourceAnnotationValue::Iri(iri) => text(&iri.value),
        SourceAnnotationValue::Anonymous { label, .. } => format!("_:{}", text(label)),
        SourceAnnotationValue::Literal(literal) => format!(
            "\"{}\"^^{}",
            text(&literal.lexical),
            text(&literal.datatype)
        ),
    }
}
/// The kind of axiom the next token starts, for this demo's dispatch only.
enum Next {
    Declaration,
    AnnotationAxiom,
    Other,
}
fn next(tokens: &Tokens) -> Next {
    match tokens {
        Tokens::Cons { token, .. } => match token.terminal {
            Terminal::Keyword(Keyword::Declaration) => Next::Declaration,
            Terminal::Keyword(
                Keyword::AnnotationAssertion
                | Keyword::SubAnnotationPropertyOf
                | Keyword::AnnotationPropertyDomain
                | Keyword::AnnotationPropertyRange,
            ) => Next::AnnotationAxiom,
            _ => Next::Other,
        },
        Tokens::Empty => Next::Other,
    }
}
fn main() {
    let bytes = include_bytes!("../../../examples/maintenance-vocabulary.ofn").to_vec();
    let prefix =
        read_prefix_header(&bytes, 300, 10, 100).unwrap_or_else(|_| panic!("source prefixes"));
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
    // This loop selects axiom positions for the demo; the verified axiom loop
    // over all axiom forms is a later stage.
    let mut tokens = ontology.remaining;
    loop {
        match next(&tokens) {
            Next::Declaration => {
                let (declaration, rest) = read_declaration(&table, &bytes, tokens, &limits)
                    .unwrap_or_else(|_| panic!("declaration"));
                println!("Declaration of {}", text(&declaration.entity.iri.value));
                tokens = rest;
            }
            Next::AnnotationAxiom => {
                let (axiom, rest) = read_annotation_axiom(&table, &bytes, tokens, &limits)
                    .unwrap_or_else(|_| panic!("annotation axiom"));
                let line = match &axiom.body {
                    SourceAnnotationAxiomBody::Assertion {
                        property,
                        subject: target,
                        value: object,
                    } => format!(
                        "Assertion: {} {} {}",
                        subject(target),
                        text(&property.value),
                        value(object)
                    ),
                    SourceAnnotationAxiomBody::SubProperty {
                        sub_property,
                        super_property,
                    } => format!(
                        "Subproperty: {} below {}",
                        text(&sub_property.value),
                        text(&super_property.value)
                    ),
                    SourceAnnotationAxiomBody::Domain { property, domain } => format!(
                        "Domain: {} on {}",
                        text(&property.value),
                        text(&domain.value)
                    ),
                    SourceAnnotationAxiomBody::Range { property, range } => {
                        format!("Range: {} to {}", text(&property.value), text(&range.value))
                    }
                };
                println!("{line} ({} axiom annotation(s))", axiom.annotations.len());
                tokens = rest;
            }
            Next::Other => break,
        }
    }
    if let Tokens::Cons { token, .. } = tokens {
        println!(
            "Stopped at '{}', the ontology's closing token.",
            text(&bytes[token.start..token.end])
        );
    }
    println!("Logical axioms, the verified axiom loop and OWL reasoning are separate stages.");
}
