//! Ontology annotations, including a nested annotation, from original source bytes.
use rowl::experimental::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotation, SourceAnnotationValue,
    SourceAnnotations,
};
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}
fn ontology_annotations(
    bytes: &Vec<u8>,
    limits: &AnnotationLimits,
) -> Result<SourceAnnotations, AnnotationError> {
    let prefix =
        read_prefix_header(bytes, 200, 10, 100).unwrap_or_else(|_| panic!("source prefixes"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("prefix table"),
    };
    let header = read_header_tail(&table, bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    read_annotations(&table, bytes, header.remaining, limits)
}
fn show(annotation: &SourceAnnotation, level: usize) {
    let value = match &annotation.value {
        SourceAnnotationValue::Iri(iri) => format!("IRI {}", text(&iri.value)),
        SourceAnnotationValue::Anonymous { label, .. } => {
            format!("anonymous individual _:{}", text(label))
        }
        SourceAnnotationValue::Literal(literal) => format!(
            "literal {} with datatype {}",
            text(&literal.lexical),
            text(&literal.datatype)
        ),
    };
    println!(
        "{}{} -> {}",
        "  ".repeat(level),
        text(&annotation.property.value),
        value
    );
    for nested in &annotation.annotations {
        show(nested, level + 1);
    }
}
fn main() {
    let bytes = include_bytes!("../../../examples/maintenance-annotations.ofn").to_vec();
    let limits = AnnotationLimits {
        depth: 2,
        count: 10,
        iri: 100,
        lexical: 100,
    };
    let output =
        ontology_annotations(&bytes, &limits).unwrap_or_else(|_| panic!("ontology annotations"));
    for annotation in &output.annotations {
        show(annotation, 0);
    }
    let shallow = AnnotationLimits { depth: 1, ..limits };
    if let Err(AnnotationError::DepthLimit { offset }) = ontology_annotations(&bytes, &shallow) {
        println!("With nesting depth 1, the nested annotation at byte {offset} is rejected.");
    }
    println!("The demo reads ontology annotations only; axioms, the closing token, anonymous-individual scopes and OWL reasoning remain pending.");
}
