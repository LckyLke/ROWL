//! Questions about original Functional Syntax source, answered end to end by
//! the verified pipeline: the document reader, the mapping into the kernel's
//! OWL model and the ALC reasoner.
use rowl::experimental::functional_annotations::AnnotationLimits;
use rowl::experimental::functional_class_axioms::SourceClassAxiomBody;
use rowl::experimental::functional_classes::ClassLimits;
use rowl::experimental::functional_document::{
    read_document, DocumentError, DocumentLimits, SourceAxiom,
};
use rowl::experimental::model::*;
use rowl::experimental::source_reasoning::{
    source_class_satisfiable, source_consistent, source_subsumed,
};

const EX: &str = "https://example.org/maintenance/";

fn iri(value: &[u8]) -> Iri {
    Iri {
        spelling: value.to_vec(),
    }
}
fn named(local: &str) -> ClassExpression {
    ClassExpression::Class(Class {
        iri: iri(format!("{EX}{local}").as_bytes()),
    })
}
fn both(first: ClassExpression, second: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first,
        second,
        rest: Vec::new(),
    }))
}
fn some_part(filler: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri(format!("{EX}hasPart").as_bytes()),
        }),
        Box::new(filler),
    )
}
fn show(question: &str, answer: Result<Option<bool>, DocumentError>) {
    match answer {
        Ok(Some(answer)) => println!("{question}: {answer}"),
        Ok(None) => println!("{question}: outside the supported fragment"),
        Err(_) => println!("{question}: the document was rejected"),
    }
}
fn main() {
    let bytes = include_bytes!("../../../examples/maintenance-classes.ofn").to_vec();
    let limits = DocumentLimits {
        tokens: 400,
        prefixes: 10,
        prefix_value: 100,
        imports: 10,
        iri: 100,
        axioms: 100,
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
    };
    let document = read_document(&bytes, &limits).unwrap_or_else(|_| panic!("document"));
    for item in &document.tail.axioms {
        if let SourceAxiom::Class(source) = item {
            println!(
                "Read {} with {} axiom annotation(s)",
                match source.body {
                    SourceClassAxiomBody::SubClassOf { .. } => "SubClassOf",
                    SourceClassAxiomBody::EquivalentClasses(_) => "EquivalentClasses",
                    SourceClassAxiomBody::DisjointClasses(_) => "DisjointClasses",
                    SourceClassAxiomBody::DisjointUnion { .. } => "DisjointUnion",
                    SourceClassAxiomBody::ObjectPropertyDomain { .. } => "ObjectPropertyDomain",
                    SourceClassAxiomBody::ObjectPropertyRange { .. } => "ObjectPropertyRange",
                },
                source.annotations.len()
            );
        }
    }
    // Node IDs in the document would become anonymous individuals of this scope.
    let scope = b"maintenance-classes".to_vec();
    show(
        "The axioms are consistent",
        source_consistent(&bytes, &limits, &scope),
    );
    show(
        "A pump has some part",
        source_subsumed(
            &bytes,
            &limits,
            &scope,
            &named("Pump"),
            &some_part(named("Part")),
        ),
    );
    show(
        "A pump with a faulty part is out of service",
        source_subsumed(
            &bytes,
            &limits,
            &scope,
            &both(named("Pump"), some_part(named("FaultyPart"))),
            &ClassExpression::ObjectComplementOf(Box::new(named("InService"))),
        ),
    );
    show(
        "A motor that is also a valve can exist",
        source_class_satisfiable(
            &bytes,
            &limits,
            &scope,
            &both(named("Motor"), named("Valve")),
        ),
    );
    show(
        "Every machine needs inspection",
        source_subsumed(
            &bytes,
            &limits,
            &scope,
            &named("Machine"),
            &named("NeedsInspection"),
        ),
    );
    println!("Each answer is proved end to end: from the original bytes, through the document reader and the mapping into the OWL model, to the OWL 2 Direct Semantics of the read axioms.");
}
