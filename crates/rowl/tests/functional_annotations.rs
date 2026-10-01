use rowl::experimental::functional::{Keyword, Terminal};
use rowl::experimental::functional_annotations::{
    read_annotations, AnnotationError, AnnotationLimits, SourceAnnotationValue, SourceAnnotations,
};
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

fn maintenance(limits: &AnnotationLimits) -> Result<SourceAnnotations, AnnotationError> {
    let bytes = include_bytes!("../../../examples/maintenance-annotations.ofn").to_vec();
    let prefix = read_prefix_header(&bytes, 200, 10, 100)
        .unwrap_or_else(|_| panic!("original prefix syntax"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("source table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    read_annotations(&table, &bytes, header.remaining, limits)
}
#[test]
fn public_reader_returns_the_maintenance_ontology_annotations() {
    let limits = AnnotationLimits {
        depth: 2,
        count: 3,
        iri: 100,
        lexical: 100,
    };
    let output = maintenance(&limits).unwrap_or_else(|_| panic!("ontology annotations"));
    assert_eq!(output.annotations.len(), 3);
    let inspected = &output.annotations[1];
    assert_eq!(
        inspected.property.value,
        b"https://example.org/maintenance/inspectedBy"
    );
    assert!(matches!(
        &inspected.value,
        SourceAnnotationValue::Anonymous { label, .. } if label == b"inspector"
    ));
    assert_eq!(inspected.annotations.len(), 1);
    match &inspected.annotations[0].value {
        SourceAnnotationValue::Literal(literal) => {
            assert_eq!(literal.lexical, b"Recorded during the 2026 inspection@");
        }
        _ => panic!("nested comment literal"),
    }
    match &output.annotations[2].value {
        SourceAnnotationValue::Literal(literal) => {
            assert_eq!(literal.lexical, b"007");
            assert_eq!(
                literal.datatype,
                b"http://www.w3.org/2001/XMLSchema#integer"
            );
        }
        _ => panic!("typed literal"),
    }
    match output.remaining {
        Tokens::Cons { token, .. } => assert!(matches!(
            token.terminal,
            Terminal::Keyword(Keyword::Declaration)
        )),
        Tokens::Empty => panic!("declarations remain for the axiom stage"),
    }
}
#[test]
fn public_reader_reports_limits_without_a_partial_result() {
    let shallow = AnnotationLimits {
        depth: 1,
        count: 3,
        iri: 100,
        lexical: 100,
    };
    assert!(matches!(
        maintenance(&shallow),
        Err(AnnotationError::DepthLimit { .. })
    ));
    let few = AnnotationLimits {
        depth: 2,
        count: 2,
        iri: 100,
        lexical: 100,
    };
    assert!(matches!(
        maintenance(&few),
        Err(AnnotationError::CountLimit { .. })
    ));
}
