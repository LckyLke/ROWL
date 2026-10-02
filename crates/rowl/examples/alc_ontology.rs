//! Verified ontology-level answers for a small maintenance ontology in ALC.
use rowl::experimental::alc_ontology::{class_satisfiable, consistent, instance_of, subsumed};
use rowl::experimental::model::*;

const EX: &str = "https://example.org/maintenance/";

fn iri(name: &str) -> Iri {
    Iri {
        spelling: format!("{EX}{name}").into_bytes(),
    }
}
fn class(name: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(name) })
}
fn has_part() -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty {
        iri: iri("hasPart"),
    })
}
fn two(first: ClassExpression, second: ClassExpression) -> AtLeastTwo<ClassExpression> {
    AtLeastTwo {
        first,
        second,
        rest: Vec::new(),
    }
}
fn not(e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(e))
}
fn both(first: ClassExpression, second: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(two(first, second)))
}
fn some_part(e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(has_part(), Box::new(e))
}
fn axiom(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: Vec::new(),
        axiom,
    }
}
fn show(question: &str, answer: Option<bool>) {
    match answer {
        Some(answer) => println!("{question}: {answer}"),
        None => println!("{question}: outside the supported fragment"),
    }
}
fn main() {
    let axioms = vec![
        axiom(Axiom::Declaration(Entity::Class(Class {
            iri: iri("Pump"),
        }))),
        // A pump is a machine; every machine has a part; whatever is a part is a Part.
        axiom(Axiom::SubClassOf(class("Pump"), class("Machine"))),
        axiom(Axiom::SubClassOf(
            class("Machine"),
            some_part(class("Part")),
        )),
        axiom(Axiom::ObjectPropertyRange(has_part(), class("Part"))),
        axiom(Axiom::DisjointClasses(two(class("Machine"), class("Part")))),
        // Every part is exactly one of motor, valve or seal.
        axiom(Axiom::DisjointUnion(
            Class { iri: iri("Part") },
            AtLeastTwo {
                first: class("Motor"),
                second: class("Valve"),
                rest: vec![class("Seal")],
            },
        )),
        // Needing inspection means having a faulty part, and stops service.
        axiom(Axiom::EquivalentClasses(two(
            class("NeedsInspection"),
            some_part(class("FaultyPart")),
        ))),
        axiom(Axiom::SubClassOf(
            class("NeedsInspection"),
            not(class("InService")),
        )),
    ];
    show("The axioms are consistent", consistent(&axioms));
    show(
        "A pump has some part",
        subsumed(&axioms, &class("Pump"), &some_part(class("Part"))),
    );
    show(
        "A pump with a faulty part is out of service",
        subsumed(
            &axioms,
            &both(class("Pump"), some_part(class("FaultyPart"))),
            &not(class("InService")),
        ),
    );
    show(
        "Something with a motor has a part",
        subsumed(
            &axioms,
            &some_part(class("Motor")),
            &some_part(class("Part")),
        ),
    );
    show(
        "Every pump needs inspection",
        subsumed(&axioms, &class("Pump"), &class("NeedsInspection")),
    );
    show(
        "A motor that is also a valve can exist",
        class_satisfiable(&axioms, &both(class("Motor"), class("Valve"))),
    );
    show(
        "A machine that is also a part can exist",
        class_satisfiable(&axioms, &both(class("Machine"), class("Part"))),
    );
    let mut with_individual = axioms;
    with_individual.push(axiom(Axiom::ClassAssertion(
        class("Pump"),
        Individual::Named(NamedIndividual { iri: iri("pump1") }),
    )));
    show(
        "With an individual pump1 that is a pump, the axioms are consistent",
        consistent(&with_individual),
    );
    show(
        "pump1 is a machine",
        instance_of(
            &with_individual,
            &NamedIndividual { iri: iri("pump1") },
            &class("Machine"),
        ),
    );
    println!("Each answer is proved to coincide with the OWL 2 Direct Semantics definition of consistency, class satisfiability, subsumption or instance checking for these axioms; satisfiable answers come with an actual OWL model.");
    println!("The other axiom forms are later stages; reading these axioms from Functional Syntax is shown in the functional_class_axioms and source_individuals examples.");
}
