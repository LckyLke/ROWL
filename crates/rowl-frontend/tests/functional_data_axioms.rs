use rowl_frontend::functional_annotations::{read_annotations, AnnotationLimits};
use rowl_frontend::functional_classes::{ClassLimits, SourceClass, SourceObjectProperty};
use rowl_frontend::functional_data_axioms::{
    read_data_axiom, DataAxiomError, DataAxiomExpected, SourceDataAxiom, SourceDataAxiomBody,
};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::functional_ranges::{RangeError, SourceDataRange};
use rowl_frontend::prefixes::{check, Check};

const EX: &str = "https://example.org/lab/";
const ANNOTATIONS: AnnotationLimits = AnnotationLimits {
    depth: 2,
    count: 10,
    iri: 100,
    lexical: 100,
};
const CLASSES: ClassLimits = ClassLimits {
    depth: 5,
    count: 3,
    iri: 100,
};

/// Read one data axiom at the first axiom position of a source document.
fn read(body: &str) -> (Vec<u8>, Result<(SourceDataAxiom, Tokens), DataAxiomError>) {
    let source = format!(
        "Prefix(:=<{EX}>)\nOntology(<https://example.org/lab> <https://example.org/lab/1>\n{body}"
    );
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 400, 10, 100)
        .unwrap_or_else(|_| panic!("fixture prefix syntax must be complete"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("fixture declarations must form a normative prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("fixture header must be accepted"));
    let ontology = read_annotations(&table, &bytes, header.remaining, &ANNOTATIONS)
        .unwrap_or_else(|_| panic!("fixture ontology annotations must be accepted"));
    let result = read_data_axiom(&table, &bytes, ontology.remaining, &ANNOTATIONS, &CLASSES);
    (bytes, result)
}
fn ready(body: &str) -> SourceDataAxiom {
    read(body)
        .1
        .unwrap_or_else(|_| panic!("fixture data axiom must be accepted"))
        .0
}
fn offset(bytes: &[u8], needle: &str) -> usize {
    (0..bytes.len())
        .find(|&start| bytes[start..].starts_with(needle.as_bytes()))
        .expect("fixture text must occur")
}
fn name(iri: &[u8]) -> String {
    let text = String::from_utf8(iri.to_vec()).expect("IRIs are UTF-8");
    if let Some(local) = text.strip_prefix("http://www.w3.org/2001/XMLSchema#") {
        return format!("xsd:{local}");
    }
    text.strip_prefix(EX).unwrap_or(&text).to_string()
}
fn class(class: &SourceClass) -> String {
    match class {
        SourceClass::Named(iri) => name(&iri.value),
        _ => "expression".to_string(),
    }
}
fn range(range: &SourceDataRange) -> String {
    match range {
        SourceDataRange::Datatype(iri) => name(&iri.value),
        _ => "range".to_string(),
    }
}
fn object(property: &SourceObjectProperty) -> String {
    match property {
        SourceObjectProperty::Named(iri) => name(&iri.value),
        SourceObjectProperty::Inverse { property, .. } => format!("inv({})", name(&property.value)),
    }
}
fn shape(axiom: &SourceDataAxiom) -> String {
    let list = |members: &Vec<rowl_frontend::functional_header::HeaderIri>| {
        members
            .iter()
            .map(|iri| name(&iri.value))
            .collect::<Vec<_>>()
            .join(",")
    };
    match &axiom.body {
        SourceDataAxiomBody::SubDataPropertyOf { sub, sup } => {
            format!("sub({},{})", name(&sub.value), name(&sup.value))
        }
        SourceDataAxiomBody::EquivalentDataProperties(members) => {
            format!("equivalent({})", list(members))
        }
        SourceDataAxiomBody::DisjointDataProperties(members) => {
            format!("disjoint({})", list(members))
        }
        SourceDataAxiomBody::DataPropertyDomain { property, domain } => {
            format!("domain({},{})", name(&property.value), class(domain))
        }
        SourceDataAxiomBody::DataPropertyRange {
            property,
            range: value,
        } => format!("range({},{})", name(&property.value), range(value)),
        SourceDataAxiomBody::FunctionalDataProperty(property) => {
            format!("functional({})", name(&property.value))
        }
        SourceDataAxiomBody::DatatypeDefinition {
            datatype,
            range: value,
        } => format!("definition({},{})", name(&datatype.value), range(value)),
        SourceDataAxiomBody::HasKey {
            class: key,
            objects,
            data,
        } => format!(
            "key({},[{}],[{}])",
            class(key),
            objects.iter().map(object).collect::<Vec<_>>().join(","),
            list(data)
        ),
    }
}
fn expected(result: Result<(SourceDataAxiom, Tokens), DataAxiomError>) -> (&'static str, usize) {
    match result {
        Err(DataAxiomError::Expected { expected, offset }) => {
            let kind = match expected {
                DataAxiomExpected::Axiom => "axiom",
                DataAxiomExpected::Open => "open",
                DataAxiomExpected::Iri => "iri",
                DataAxiomExpected::Close => "close",
            };
            (kind, offset)
        }
        _ => panic!("expected a source syntax failure"),
    }
}

#[test]
fn all_eight_axiom_forms_keep_their_shape() {
    let cases = [
        ("SubDataPropertyOf(:dose :amount))", "sub(dose,amount)"),
        (
            "EquivalentDataProperties(:dose :dosage :amount))",
            "equivalent(dose,dosage,amount)",
        ),
        (
            "DisjointDataProperties(:dose :code))",
            "disjoint(dose,code)",
        ),
        (
            "DataPropertyDomain(:dose :Prescription))",
            "domain(dose,Prescription)",
        ),
        (
            "DataPropertyRange(:dose xsd:integer))",
            "range(dose,xsd:integer)",
        ),
        ("FunctionalDataProperty(:dose))", "functional(dose)"),
        (
            "DatatypeDefinition(:Dose DataComplementOf(xsd:string)))",
            "definition(Dose,range)",
        ),
        (
            "HasKey(:Patient (:hasDoctor ObjectInverseOf(:treats)) (:recordNumber)))",
            "key(Patient,[hasDoctor,inv(treats)],[recordNumber])",
        ),
        ("HasKey(:Patient () ()))", "key(Patient,[],[])"),
    ];
    for (body, shape_text) in cases {
        assert_eq!(shape(&ready(body)), shape_text, "{body}");
    }
    let annotated = ready("FunctionalDataProperty(Annotation(rdfs:comment \"one\") :dose))");
    assert_eq!(annotated.annotations.len(), 1);
    assert_eq!(annotated.keyword.start, {
        let (bytes, _) = read("FunctionalDataProperty(Annotation(rdfs:comment \"one\") :dose))");
        offset(&bytes, "FunctionalDataProperty")
    });
}

#[test]
fn errors_follow_source_order() {
    let (bytes, result) = read("EquivalentDataProperties(:dose))");
    assert_eq!(expected(result), ("iri", offset(&bytes, "))")));
    let (bytes, result) = read("SubDataPropertyOf(:dose ObjectInverseOf(:p)))");
    assert_eq!(expected(result), ("iri", offset(&bytes, "ObjectInverseOf")));
    let (bytes, result) = read("FunctionalDataProperty(:dose :code))");
    assert_eq!(expected(result), ("close", offset(&bytes, ":code")));
    let (bytes, result) = read("HasKey(:Patient :hasDoctor ())");
    assert_eq!(expected(result), ("open", offset(&bytes, ":hasDoctor")));
    let (bytes, result) = read("HasKey(:Patient () (:a :b :c :d)))");
    match result {
        Err(DataAxiomError::CountLimit { offset: at }) => assert_eq!(at, offset(&bytes, ":d")),
        _ => panic!("key lists share the count limit"),
    }
    let (bytes, result) = read("DisjointDataProperties(:a undeclared:b))");
    match result {
        Err(DataAxiomError::Iri(SourceIriError::UndeclaredPrefix { offset: at })) => {
            assert_eq!(at, offset(&bytes, "undeclared:b"))
        }
        _ => panic!("data properties resolve through the prefix table"),
    }
    let (_, result) = read("DataPropertyRange(:dose DataOneOf()))");
    assert!(matches!(
        result,
        Err(DataAxiomError::Range(RangeError::Expected { .. }))
    ));
    let (_, result) = read("DataPropertyDomain(:dose ObjectUnionOf(:A)))");
    assert!(matches!(result, Err(DataAxiomError::Class(_))));
    let (bytes, result) = read("SubClassOf(:A :B))");
    assert_eq!(expected(result), ("axiom", offset(&bytes, "SubClassOf")));
}
