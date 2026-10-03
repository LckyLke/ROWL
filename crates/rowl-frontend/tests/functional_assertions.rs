use rowl_frontend::functional_annotations::{read_annotations, AnnotationLimits};
use rowl_frontend::functional_assertions::{
    read_assertion, AssertionError, AssertionExpected, SourceAssertion, SourceAssertionBody,
};
use rowl_frontend::functional_classes::{
    ClassError, ClassLimits, SourceClass, SourceObjectProperty,
};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_individuals::{IndividualError, SourceIndividual};
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_prefixes::read_prefix_header;
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
    count: 10,
    iri: 100,
};

/// Read one assertion at the first axiom position of a source document.
fn read(body: &str) -> (Vec<u8>, Result<(SourceAssertion, Tokens), AssertionError>) {
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
    let result = read_assertion(&table, &bytes, ontology.remaining, &ANNOTATIONS, &CLASSES);
    (bytes, result)
}
fn ready(body: &str) -> SourceAssertion {
    read(body)
        .1
        .unwrap_or_else(|_| panic!("fixture assertion must be accepted"))
        .0
}
fn offset(bytes: &[u8], needle: &str, occurrence: usize) -> usize {
    let mut found = 0;
    for start in 0..bytes.len() {
        if bytes[start..].starts_with(needle.as_bytes()) {
            if found == occurrence {
                return start;
            }
            found += 1;
        }
    }
    panic!("fixture text must occur")
}
fn name(iri: &[u8]) -> String {
    let text = String::from_utf8(iri.to_vec()).expect("IRIs are UTF-8");
    text.strip_prefix(EX).unwrap_or(&text).to_string()
}
fn individual(individual: &SourceIndividual) -> String {
    match individual {
        SourceIndividual::Named(iri) => name(&iri.value),
        SourceIndividual::Anonymous { label, .. } => {
            format!(
                "_:{}",
                String::from_utf8(label.clone()).expect("labels are UTF-8")
            )
        }
    }
}
fn property(property: &SourceObjectProperty) -> String {
    match property {
        SourceObjectProperty::Named(iri) => name(&iri.value),
        SourceObjectProperty::Inverse { property, .. } => {
            format!("inverse({})", name(&property.value))
        }
    }
}
fn class(class: &SourceClass) -> String {
    match class {
        SourceClass::Named(iri) => name(&iri.value),
        SourceClass::ComplementOf { operand, .. } => format!("not({})", self::class(operand)),
        SourceClass::SomeValuesFrom {
            property, filler, ..
        } => format!("some({},{})", self::property(property), self::class(filler)),
        _ => "other".to_string(),
    }
}
fn individuals(members: &[SourceIndividual]) -> String {
    members.iter().map(individual).collect::<Vec<_>>().join(",")
}
fn shape(assertion: &SourceAssertion) -> String {
    match &assertion.body {
        SourceAssertionBody::SameIndividual(members) => format!("same({})", individuals(members)),
        SourceAssertionBody::DifferentIndividuals(members) => {
            format!("different({})", individuals(members))
        }
        SourceAssertionBody::ClassAssertion {
            class: value,
            individual: member,
        } => format!("{}({})", class(value), individual(member)),
        SourceAssertionBody::ObjectPropertyAssertion {
            property: role,
            source,
            target,
        } => format!(
            "{}({},{})",
            property(role),
            individual(source),
            individual(target)
        ),
        SourceAssertionBody::NegativeObjectPropertyAssertion {
            property: role,
            source,
            target,
        } => format!(
            "not {}({},{})",
            property(role),
            individual(source),
            individual(target)
        ),
    }
}

#[test]
fn every_assertion_form_reads_its_individuals_in_order() {
    let cases = [
        ("ClassAssertion(:Pump :pump1))", "Pump(pump1)"),
        (
            "ClassAssertion(ObjectSomeValuesFrom(:hasPart :FaultyPart) _:unit7))",
            "some(hasPart,FaultyPart)(_:unit7)",
        ),
        (
            "ObjectPropertyAssertion(:hasPart :pump1 :motor1))",
            "hasPart(pump1,motor1)",
        ),
        (
            "ObjectPropertyAssertion(ObjectInverseOf(:hasPart) _:m <https://example.org/maintenance/p>))",
            "inverse(hasPart)(_:m,p)",
        ),
        (
            "NegativeObjectPropertyAssertion(:hasPart :motor1 :pump1))",
            "not hasPart(motor1,pump1)",
        ),
        ("SameIndividual(:pump1 :p1))", "same(pump1,p1)"),
        (
            "DifferentIndividuals(:pump1 _:spare :pump2))",
            "different(pump1,_:spare,pump2)",
        ),
    ];
    for (body, expected) in cases {
        assert_eq!(shape(&ready(body)), expected, "{body}");
    }
    let annotated = ready("ClassAssertion(Annotation(rdfs:comment \"seen\") :Pump :pump1))");
    assert_eq!(annotated.annotations.len(), 1);
    assert_eq!(shape(&annotated), "Pump(pump1)");
}

#[test]
fn the_remaining_tokens_follow_the_closing_parenthesis() {
    let (bytes, result) = read("ClassAssertion(:Pump :pump1) ClassAssertion(:Pump :pump2))");
    let (_, rest) = result.unwrap_or_else(|_| panic!("first assertion"));
    match rest {
        Tokens::Cons { token, .. } => assert_eq!(token.start, offset(&bytes, "ClassAssertion", 1)),
        Tokens::Empty => panic!("the second assertion remains"),
    }
}

#[test]
fn errors_report_the_first_failing_step() {
    // A missing individual.
    let (bytes, result) = read("ClassAssertion(:Pump))");
    match result {
        Err(AssertionError::Individual(IndividualError::Expected { offset: at })) => {
            assert_eq!(at, offset(&bytes, "))", 0))
        }
        _ => panic!("a missing individual is reported at the closing parenthesis"),
    }
    // A literal where the target individual belongs.
    let (bytes, result) = read("ObjectPropertyAssertion(:hasPart :pump1 \"motor\"))");
    match result {
        Err(AssertionError::Individual(IndividualError::Expected { offset: at })) => {
            assert_eq!(at, offset(&bytes, "\"motor\"", 0))
        }
        _ => panic!("a literal is not an individual"),
    }
    // An undeclared prefix in an individual.
    let (_, result) = read("ClassAssertion(:Pump other:pump1))");
    assert!(matches!(
        result,
        Err(AssertionError::Individual(IndividualError::Iri(
            SourceIriError::UndeclaredPrefix { .. }
        )))
    ));
    // An equality needs two individuals and stops before `)`.
    let (bytes, result) = read("SameIndividual(:pump1))");
    match result {
        Err(AssertionError::Individual(IndividualError::Expected { offset: at })) => {
            assert_eq!(at, offset(&bytes, "))", 0))
        }
        _ => panic!("a second individual is expected"),
    }
    let (bytes, result) = read("DifferentIndividuals(:a :b :c :d :e :f :g :h :i :j :k))");
    match result {
        Err(AssertionError::Individual(IndividualError::CountLimit { offset: at })) => {
            assert_eq!(at, offset(&bytes, ":k", 0))
        }
        _ => panic!("individuals beyond the count are reported"),
    }
    let (bytes, result) = read("SameIndividual(:pump1 :Pump(:p)))");
    match result {
        Err(AssertionError::Individual(IndividualError::Expected { offset: at })) => {
            assert_eq!(at, offset(&bytes, "(:p)", 0))
        }
        _ => panic!("only individuals belong in the list"),
    }
    // A class expression error keeps the class stage.
    let (_, result) = read("ClassAssertion(ObjectHasSelf(:p) :pump1))");
    assert!(matches!(
        result,
        Err(AssertionError::Class(ClassError::Unsupported { .. }))
    ));
    // Content after the target individual.
    let (bytes, result) = read("ObjectPropertyAssertion(:hasPart :pump1 :motor1 :extra))");
    match result {
        Err(AssertionError::Expected {
            expected: AssertionExpected::Close,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, ":extra", 0)),
        _ => panic!("a third individual is reported where `)` belongs"),
    }
    // A keyword of another axiom form.
    let (bytes, result) = read("SubClassOf(:Pump :Machine))");
    match result {
        Err(AssertionError::Expected {
            expected: AssertionExpected::Axiom,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, "SubClassOf", 0)),
        _ => panic!("only assertion keywords start an assertion"),
    }
}
