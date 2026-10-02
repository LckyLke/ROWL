use rowl_frontend::functional::{Keyword, Terminal};
use rowl_frontend::functional_annotations::{read_annotations, AnnotationError, AnnotationLimits};
use rowl_frontend::functional_class_axioms::{
    read_class_axiom, ClassAxiomError, ClassAxiomExpected, SourceClassAxiom, SourceClassAxiomBody,
};
use rowl_frontend::functional_classes::{
    ClassError, ClassExpected, ClassLimits, SourceClass, SourceObjectProperty,
};
use rowl_frontend::functional_header::read_header_tail;
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

/// Read one class axiom at the first axiom position of a source document.
fn read(body: &str) -> (Vec<u8>, Result<(SourceClassAxiom, Tokens), ClassAxiomError>) {
    let source = format!(
        "Prefix(:=<{EX}>)\nOntology(<https://example.org/maintenance> <https://example.org/maintenance/1>\n{body}"
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
    let result = read_class_axiom(&table, &bytes, ontology.remaining, &ANNOTATIONS, &CLASSES);
    (bytes, result)
}
fn ready(body: &str) -> SourceClassAxiom {
    read(body)
        .1
        .unwrap_or_else(|_| panic!("fixture axiom must be accepted"))
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
fn class(class: &SourceClass) -> String {
    match class {
        SourceClass::Named(iri) => name(&iri.value),
        SourceClass::IntersectionOf { members, .. } => format!("and{}", list(members)),
        SourceClass::UnionOf { members, .. } => format!("or{}", list(members)),
        SourceClass::ComplementOf { operand, .. } => format!("not({})", self::class(operand)),
        SourceClass::SomeValuesFrom {
            property, filler, ..
        } => format!("some({},{})", self::property(property), self::class(filler)),
        SourceClass::AllValuesFrom {
            property, filler, ..
        } => format!("all({},{})", self::property(property), self::class(filler)),
    }
}
fn list(members: &[SourceClass]) -> String {
    format!(
        "({})",
        members.iter().map(class).collect::<Vec<_>>().join(",")
    )
}
fn property(property: &SourceObjectProperty) -> String {
    match property {
        SourceObjectProperty::Named(iri) => name(&iri.value),
        SourceObjectProperty::Inverse { property, .. } => format!("inv({})", name(&property.value)),
    }
}
fn body(axiom: &SourceClassAxiom) -> String {
    match &axiom.body {
        SourceClassAxiomBody::SubClassOf { sub, sup } => {
            format!("sub({},{})", class(sub), class(sup))
        }
        SourceClassAxiomBody::EquivalentClasses(members) => format!("equivalent{}", list(members)),
        SourceClassAxiomBody::DisjointClasses(members) => format!("disjoint{}", list(members)),
        SourceClassAxiomBody::DisjointUnion { class, members } => {
            format!("union({},{})", name(&class.value), list(members))
        }
        SourceClassAxiomBody::ObjectPropertyDomain { property, domain } => {
            format!("domain({},{})", self::property(property), class(domain))
        }
        SourceClassAxiomBody::ObjectPropertyRange { property, range } => {
            format!("range({},{})", self::property(property), class(range))
        }
    }
}
fn expected(result: Result<(SourceClassAxiom, Tokens), ClassAxiomError>) -> (&'static str, usize) {
    match result {
        Err(ClassAxiomError::Expected { expected, offset }) => {
            let kind = match expected {
                ClassAxiomExpected::Axiom => "axiom",
                ClassAxiomExpected::Open => "open",
                ClassAxiomExpected::Iri => "iri",
                ClassAxiomExpected::Close => "close",
            };
            (kind, offset)
        }
        Err(ClassAxiomError::Class(ClassError::Expected { expected, offset })) => {
            let kind = match expected {
                ClassExpected::Class => "class",
                ClassExpected::Open => "class open",
                ClassExpected::Property => "property",
                ClassExpected::Iri => "class iri",
                ClassExpected::Close => "class close",
            };
            (kind, offset)
        }
        _ => panic!("expected a source syntax failure"),
    }
}

#[test]
fn all_six_axiom_forms_keep_their_shape() {
    let cases = [
        (
            "SubClassOf(:Pump ObjectIntersectionOf(:Machine ObjectSomeValuesFrom(:hasPart :Part)))",
            "sub(Pump,and(Machine,some(hasPart,Part)))",
        ),
        (
            "EquivalentClasses(:A :B ObjectComplementOf(:C))",
            "equivalent(A,B,not(C))",
        ),
        ("DisjointClasses(:A :B)", "disjoint(A,B)"),
        (
            "DisjointUnion(:Part :Motor :Valve :Seal)",
            "union(Part,(Motor,Valve,Seal))",
        ),
        (
            "ObjectPropertyDomain(:hasPart :Machine)",
            "domain(hasPart,Machine)",
        ),
        (
            "ObjectPropertyRange(ObjectInverseOf(:hasPart) ObjectAllValuesFrom(:partOf :Machine))",
            "range(inv(hasPart),all(partOf,Machine))",
        ),
    ];
    for (source, shape) in cases {
        let axiom = ready(&format!("{source}\n)"));
        assert_eq!(body(&axiom), shape);
    }
}

#[test]
fn axiom_annotations_and_tokens_are_kept() {
    let (bytes, result) = read(
        "SubClassOf(Annotation(rdfs:comment \"pumps\") Annotation(rdfs:label \"p\") :Pump :Machine)\n)",
    );
    let (axiom, remaining) = result.unwrap_or_else(|_| panic!("annotated axiom"));
    assert!(matches!(
        axiom.keyword.terminal,
        Terminal::Keyword(Keyword::SubClassOf)
    ));
    assert_eq!(axiom.keyword.start, offset(&bytes, "SubClassOf", 0));
    assert_eq!(axiom.annotations.len(), 2);
    assert_eq!(body(&axiom), "sub(Pump,Machine)");
    match remaining {
        Tokens::Cons { token, .. } => assert!(matches!(token.terminal, Terminal::Close)),
        Tokens::Empty => panic!("the ontology's closing parenthesis remains"),
    }
}

#[test]
fn errors_follow_source_order() {
    let (bytes, result) = read("Declaration(Class(:A))");
    assert_eq!(
        expected(result),
        ("axiom", offset(&bytes, "Declaration", 0))
    );
    let (bytes, result) = read("SubClassOf :A :B)");
    assert_eq!(expected(result), ("open", offset(&bytes, ":A", 0)));
    let (_, result) = read("SubClassOf(Annotation(:p) :A :B)");
    assert!(matches!(
        result,
        Err(ClassAxiomError::Annotation(
            AnnotationError::Expected { .. }
        ))
    ));
    let (bytes, result) = read("SubClassOf(:A)");
    assert_eq!(expected(result), ("class", offset(&bytes, ")", 1)));
    let (bytes, result) = read("EquivalentClasses(:A)");
    assert_eq!(expected(result), ("class", offset(&bytes, ")", 1)));
    let (bytes, result) = read("DisjointUnion(ObjectComplementOf(:A) :B :C)");
    assert_eq!(
        expected(result),
        ("iri", offset(&bytes, "ObjectComplementOf", 0))
    );
    let (bytes, result) = read("DisjointUnion(:A :B)");
    assert_eq!(expected(result), ("class", offset(&bytes, ")", 1)));
    let (bytes, result) = read("ObjectPropertyRange(ObjectComplementOf(:A) :B)");
    assert_eq!(
        expected(result),
        ("property", offset(&bytes, "ObjectComplementOf", 0))
    );
    let (bytes, result) = read("SubClassOf(:A :B :C)");
    assert_eq!(expected(result), ("close", offset(&bytes, ":C", 0)));
    let (bytes, result) = read("DisjointUnion(undeclared:A :B :C)");
    match result {
        Err(ClassAxiomError::Iri(SourceIriError::UndeclaredPrefix { offset: at })) => {
            assert_eq!(at, offset(&bytes, "undeclared:A", 0))
        }
        _ => panic!("the union class IRI resolves through the prefix table"),
    }
    let (bytes, result) = read("SubClassOf(:A ObjectHasSelf(:p))");
    match result {
        Err(ClassAxiomError::Class(ClassError::Unsupported { offset: at })) => {
            assert_eq!(at, offset(&bytes, "ObjectHasSelf", 0))
        }
        _ => panic!("the other class-expression forms are not read yet"),
    }
}
