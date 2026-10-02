use rowl_frontend::functional_annotations::{read_annotations, AnnotationLimits};
use rowl_frontend::functional_classes::{ClassError, ClassLimits, SourceObjectProperty};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::functional_property_axioms::{
    read_property_axiom, PropertyAxiomError, PropertyAxiomExpected, PropertyCharacteristic,
    SourcePropertyAxiom, SourcePropertyAxiomBody, SourceSubProperty,
};
use rowl_frontend::prefixes::{check, Check};

const EX: &str = "https://example.org/maintenance/";
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

/// Read one property axiom at the first axiom position of a source document.
fn read(
    body: &str,
) -> (
    Vec<u8>,
    Result<(SourcePropertyAxiom, Tokens), PropertyAxiomError>,
) {
    let source = format!("Prefix(:=<{EX}>)\nOntology(<https://example.org/maintenance>\n{body}");
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
    let result = read_property_axiom(&table, &bytes, ontology.remaining, &ANNOTATIONS, &CLASSES);
    (bytes, result)
}
fn ready(body: &str) -> SourcePropertyAxiom {
    read(body)
        .1
        .unwrap_or_else(|_| panic!("fixture property axiom must be accepted"))
        .0
}
fn offset(bytes: &[u8], needle: &str) -> usize {
    (0..bytes.len())
        .find(|&start| bytes[start..].starts_with(needle.as_bytes()))
        .expect("fixture text must occur")
}
fn name(iri: &[u8]) -> String {
    let text = String::from_utf8(iri.to_vec()).expect("IRIs are UTF-8");
    text.strip_prefix(EX).unwrap_or(&text).to_string()
}
fn property(property: &SourceObjectProperty) -> String {
    match property {
        SourceObjectProperty::Named(iri) => name(&iri.value),
        SourceObjectProperty::Inverse { property, .. } => {
            format!("inverse({})", name(&property.value))
        }
    }
}
fn list(members: &[SourceObjectProperty]) -> String {
    members.iter().map(property).collect::<Vec<_>>().join(",")
}
fn shape(axiom: &SourcePropertyAxiom) -> String {
    match &axiom.body {
        SourcePropertyAxiomBody::SubObjectPropertyOf { sub, sup } => match sub {
            SourceSubProperty::Single(sub) => format!("{} < {}", property(sub), property(sup)),
            SourceSubProperty::Chain { members, .. } => {
                format!("chain({}) < {}", list(members), property(sup))
            }
        },
        SourcePropertyAxiomBody::EquivalentObjectProperties(members) => {
            format!("equivalent({})", list(members))
        }
        SourcePropertyAxiomBody::DisjointObjectProperties(members) => {
            format!("disjoint({})", list(members))
        }
        SourcePropertyAxiomBody::InverseObjectProperties { first, second } => {
            format!("inverse {} {}", property(first), property(second))
        }
        SourcePropertyAxiomBody::Characteristic {
            characteristic,
            property: value,
        } => {
            let kind = match characteristic {
                PropertyCharacteristic::Functional => "functional",
                PropertyCharacteristic::InverseFunctional => "inverse-functional",
                PropertyCharacteristic::Reflexive => "reflexive",
                PropertyCharacteristic::Irreflexive => "irreflexive",
                PropertyCharacteristic::Symmetric => "symmetric",
                PropertyCharacteristic::Asymmetric => "asymmetric",
                PropertyCharacteristic::Transitive => "transitive",
            };
            format!("{kind}({})", property(value))
        }
    }
}

#[test]
fn every_property_axiom_form_reads_its_properties_in_order() {
    let cases = [
        ("SubObjectPropertyOf(:hasComponent :hasPart))", "hasComponent < hasPart"),
        (
            "SubObjectPropertyOf(ObjectPropertyChain(:hasPart ObjectInverseOf(:hasPart)) :sibling))",
            "chain(hasPart,inverse(hasPart)) < sibling",
        ),
        (
            "EquivalentObjectProperties(:hasPart :contains :includes))",
            "equivalent(hasPart,contains,includes)",
        ),
        (
            "DisjointObjectProperties(:hasPart :partOf))",
            "disjoint(hasPart,partOf)",
        ),
        (
            "InverseObjectProperties(:hasPart :partOf))",
            "inverse hasPart partOf",
        ),
        ("FunctionalObjectProperty(:serial))", "functional(serial)"),
        (
            "InverseFunctionalObjectProperty(:serial))",
            "inverse-functional(serial)",
        ),
        ("ReflexiveObjectProperty(:near))", "reflexive(near)"),
        ("IrreflexiveObjectProperty(:hasPart))", "irreflexive(hasPart)"),
        ("SymmetricObjectProperty(:near))", "symmetric(near)"),
        ("AsymmetricObjectProperty(:hasPart))", "asymmetric(hasPart)"),
        (
            "TransitiveObjectProperty(ObjectInverseOf(:hasPart)))",
            "transitive(inverse(hasPart))",
        ),
    ];
    for (body, expected) in cases {
        assert_eq!(shape(&ready(body)), expected, "{body}");
    }
    let annotated =
        ready("TransitiveObjectProperty(Annotation(rdfs:comment \"parts of parts\") :hasPart))");
    assert_eq!(annotated.annotations.len(), 1);
    assert_eq!(shape(&annotated), "transitive(hasPart)");
}

#[test]
fn the_remaining_tokens_follow_the_closing_parenthesis() {
    let (bytes, result) =
        read("TransitiveObjectProperty(:hasPart) SymmetricObjectProperty(:near))");
    let (_, rest) = result.unwrap_or_else(|_| panic!("first property axiom"));
    match rest {
        Tokens::Cons { token, .. } => {
            assert_eq!(token.start, offset(&bytes, "SymmetricObjectProperty"))
        }
        Tokens::Empty => panic!("the second axiom remains"),
    }
}

#[test]
fn errors_report_the_first_failing_step() {
    // A member list needs two members.
    let (bytes, result) = read("EquivalentObjectProperties(:hasPart))");
    match result {
        Err(PropertyAxiomError::Expected {
            expected: PropertyAxiomExpected::Property,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, "))")),
        _ => panic!("a one-member list is reported where the second member belongs"),
    }
    // So does a chain.
    let (bytes, result) = read("SubObjectPropertyOf(ObjectPropertyChain(:hasPart) :sibling))");
    match result {
        Err(PropertyAxiomError::Expected {
            expected: PropertyAxiomExpected::Property,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, ") :sibling")),
        _ => panic!("a one-member chain is reported"),
    }
    // A list longer than the count.
    let (bytes, result) = read("DisjointObjectProperties(:a :b :c :d))");
    match result {
        Err(PropertyAxiomError::CountLimit { offset: at }) => {
            assert_eq!(at, offset(&bytes, ":d"))
        }
        _ => panic!("a list beyond the count is reported at the first extra member"),
    }
    // A chain is no super-property.
    let (_, result) = read("SubObjectPropertyOf(:hasPart ObjectPropertyChain(:a :b)))");
    assert!(matches!(
        result,
        Err(PropertyAxiomError::Class(ClassError::Expected { .. }))
    ));
    // A missing second property of an inverse pair.
    let (bytes, result) = read("InverseObjectProperties(:hasPart))");
    match result {
        Err(PropertyAxiomError::Class(ClassError::Expected { offset: at, .. })) => {
            assert_eq!(at, offset(&bytes, "))"))
        }
        _ => panic!("the missing property is reported at the closing parenthesis"),
    }
    // Content after the property of a characteristic.
    let (bytes, result) = read("TransitiveObjectProperty(:hasPart :partOf))");
    match result {
        Err(PropertyAxiomError::Expected {
            expected: PropertyAxiomExpected::Close,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, ":partOf")),
        _ => panic!("a second property is reported where `)` belongs"),
    }
    // A keyword of another axiom form.
    let (bytes, result) = read("SubClassOf(:Pump :Machine))");
    match result {
        Err(PropertyAxiomError::Expected {
            expected: PropertyAxiomExpected::Axiom,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, "SubClassOf")),
        _ => panic!("only property axiom keywords start a property axiom"),
    }
}
