//! Verified SHI answers on the completion graph tableau: inverse and symmetric
//! properties, a transitive property, and definitions unfolded where their class
//! holds.
use rowl::experimental::model::*;
use rowl::experimental::shi_ontology::{consistent, instance_of, subsumed};

const EX: &str = "https://example.org/family/";

fn iri(name: &str) -> Iri {
    Iri {
        spelling: format!("{EX}{name}").into_bytes(),
    }
}
fn class(name: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(name) })
}
fn thing() -> ClassExpression {
    ClassExpression::Class(Class {
        iri: Iri {
            spelling: b"http://www.w3.org/2002/07/owl#Thing".to_vec(),
        },
    })
}
fn property(name: &str) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(name) })
}
fn inverse(name: &str) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(name) })
}
fn some(role: ObjectPropertyExpression, filler: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(role, Box::new(filler))
}
fn all(role: ObjectPropertyExpression, filler: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectAllValuesFrom(role, Box::new(filler))
}
fn person(name: &str) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(name) })
}
fn named(name: &str) -> NamedIndividual {
    NamedIndividual { iri: iri(name) }
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
        // hasParent is the inverse of hasChild; ancestors are transitive and
        // include parents; siblings are symmetric.
        axiom(Axiom::InverseObjectProperties(
            property("hasParent"),
            property("hasChild"),
        )),
        axiom(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Single(property("hasParent")),
            property("hasAncestor"),
        )),
        axiom(Axiom::TransitiveObjectProperty(property("hasAncestor"))),
        axiom(Axiom::SymmetricObjectProperty(property("hasSibling"))),
        // Whoever has a parent is a child; every descendant of a founder is an heir.
        axiom(Axiom::SubClassOf(
            some(property("hasParent"), class("Person")),
            class("Child"),
        )),
        axiom(Axiom::SubClassOf(
            class("Founder"),
            all(inverse("hasAncestor"), class("Heir")),
        )),
        axiom(Axiom::ClassAssertion(class("Founder"), person("ada"))),
        axiom(Axiom::ClassAssertion(class("Person"), person("ada"))),
        axiom(Axiom::ObjectPropertyAssertion(
            property("hasChild"),
            person("ada"),
            person("ben"),
        )),
        axiom(Axiom::ObjectPropertyAssertion(
            property("hasParent"),
            person("cy"),
            person("ben"),
        )),
        axiom(Axiom::ObjectPropertyAssertion(
            property("hasSibling"),
            person("dee"),
            person("cy"),
        )),
    ];
    show("The family records are consistent", consistent(&axioms));
    show(
        "ben is a child (his parent ada is recorded only as having him)",
        instance_of(&axioms, &named("ben"), &class("Child")),
    );
    show(
        "cy is an heir of the founder ada (two generations down)",
        instance_of(&axioms, &named("cy"), &class("Heir")),
    );
    show(
        "cy has a sibling (recorded only from dee's side)",
        instance_of(
            &axioms,
            &named("cy"),
            &some(property("hasSibling"), thing()),
        ),
    );
    show(
        "every grandchild of a founder is an heir",
        subsumed(
            &axioms,
            &some(
                property("hasParent"),
                some(property("hasParent"), class("Founder")),
            ),
            &class("Heir"),
        ),
    );
    println!("Each answer is proved exact against the OWL 2 Direct Semantics of the axioms.");
}
