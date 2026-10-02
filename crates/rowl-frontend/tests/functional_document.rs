use rowl_frontend::functional_annotations::AnnotationLimits;
use rowl_frontend::functional_classes::ClassLimits;
use rowl_frontend::functional_document::{
    read_document, DocumentError, DocumentExpected, DocumentLimits, SourceAxiom, SourceDocument,
    TableError,
};
use rowl_frontend::functional_prefixes::PrefixReadError;

fn limits(axioms: usize) -> DocumentLimits {
    DocumentLimits {
        tokens: 2000,
        prefixes: 10,
        prefix_value: 100,
        imports: 10,
        iri: 100,
        axioms,
        annotations: AnnotationLimits {
            depth: 2,
            count: 10,
            iri: 100,
            lexical: 100,
        },
        classes: ClassLimits {
            depth: 10,
            count: 10,
            iri: 100,
        },
    }
}
fn read(source: &str, axioms: usize) -> (Vec<u8>, Result<SourceDocument, DocumentError>) {
    let bytes = source.as_bytes().to_vec();
    let result = read_document(&bytes, &limits(axioms));
    (bytes, result)
}
fn families(document: &SourceDocument) -> Vec<&'static str> {
    document
        .tail
        .axioms
        .iter()
        .map(|axiom| match axiom {
            SourceAxiom::Declaration(_) => "declaration",
            SourceAxiom::Annotation(_) => "annotation",
            SourceAxiom::Class(_) => "class",
            SourceAxiom::Assertion(_) => "assertion",
        })
        .collect()
}
fn offset(bytes: &[u8], needle: &str) -> usize {
    (0..bytes.len())
        .find(|&start| bytes[start..].starts_with(needle.as_bytes()))
        .expect("fixture text must occur")
}

#[test]
fn every_example_document_reads_completely() {
    let cases: [(&[u8], usize); 5] = [
        (
            include_bytes!("../../../examples/maintenance-annotations.ofn"),
            2,
        ),
        (
            include_bytes!("../../../examples/maintenance-declarations.ofn"),
            7,
        ),
        (
            include_bytes!("../../../examples/maintenance-literals.ofn"),
            1,
        ),
        (
            include_bytes!("../../../examples/maintenance-vocabulary.ofn"),
            10,
        ),
        (
            include_bytes!("../../../examples/maintenance-classes.ofn"),
            12,
        ),
    ];
    for (bytes, count) in cases {
        let document = read_document(&bytes.to_vec(), &limits(100))
            .unwrap_or_else(|_| panic!("example documents read completely"));
        assert_eq!(document.tail.axioms.len(), count);
        assert_eq!(document.prefixes.len(), 1);
    }
}

#[test]
fn axioms_keep_their_family_and_order() {
    let (_, result) = read(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n Annotation(rdfs:label \"o\")\n Declaration(Class(:A))\n SubClassOf(:A :B)\n AnnotationAssertion(rdfs:label :A \"A\")\n DisjointClasses(:A :C)\n)\n",
        10,
    );
    let document = result.unwrap_or_else(|_| panic!("fixture document"));
    assert_eq!(
        families(&document),
        ["declaration", "class", "annotation", "class"]
    );
    assert_eq!(document.tail.annotations.len(), 1);
}

#[test]
fn errors_report_the_first_failing_stage() {
    // An axiom form this stage does not read yet.
    let (bytes, result) = read(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A :B)\n SubObjectPropertyOf(:p :q)\n)",
        10,
    );
    match result {
        Err(DocumentError::UnsupportedAxiom { offset: at }) => {
            assert_eq!(at, offset(&bytes, "SubObjectPropertyOf"))
        }
        _ => panic!("the other logical axioms are reported as unsupported"),
    }
    // A missing closing parenthesis.
    let (bytes, result) = read(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A :B)\n",
        10,
    );
    match result {
        Err(DocumentError::Expected {
            expected: DocumentExpected::Close,
            offset: at,
        }) => assert_eq!(at, bytes.len()),
        _ => panic!("the end of the source before `)` is reported"),
    }
    // Content after the closing parenthesis.
    let (bytes, result) = read(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n)\nSubClassOf(:A :B)",
        10,
    );
    match result {
        Err(DocumentError::Expected {
            expected: DocumentExpected::End,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, "SubClassOf")),
        _ => panic!("trailing content is reported"),
    }
    // A token that cannot start an axiom.
    let (bytes, result) = read(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n Prefix(x:=<https://example.org/x#>)\n)",
        10,
    );
    match result {
        Err(DocumentError::Expected {
            expected: DocumentExpected::Axiom,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, " Prefix(x") + 1),
        _ => panic!("a non-axiom token is reported"),
    }
    // The axiom count.
    let (bytes, result) = read(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A :B)\n SubClassOf(:B :C)\n)",
        1,
    );
    match result {
        Err(DocumentError::AxiomLimit { offset: at }) => {
            assert_eq!(at, offset(&bytes, "SubClassOf(:B"))
        }
        _ => panic!("axioms beyond the count are reported"),
    }
    // A duplicate prefix declaration.
    let (_, result) = read(
        "Prefix(:=<https://example.org/>)\nPrefix(:=<https://example.org/other#>)\nOntology(<https://example.org/o>\n)",
        10,
    );
    assert!(matches!(
        result,
        Err(DocumentError::Table(TableError::Duplicate))
    ));
    // A source without an ontology.
    let (_, result) = read("Prefix(:=<https://example.org/>)\n", 10);
    assert!(matches!(
        result,
        Err(DocumentError::Prefix(PrefixReadError::Syntax(_)))
    ));
    // An error inside an axiom keeps its stage.
    let (_, result) = read(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A)\n)",
        10,
    );
    assert!(matches!(result, Err(DocumentError::ClassAxiom(_))));
}
