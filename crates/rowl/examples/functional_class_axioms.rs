//! Class axioms read from original Functional Syntax source, then answered by the
//! verified reasoner.
use rowl::experimental::alc_ontology::{class_satisfiable, consistent, subsumed};
use rowl::experimental::functional_annotations::AnnotationLimits;
use rowl::experimental::functional_class_axioms::{SourceClassAxiom, SourceClassAxiomBody};
use rowl::experimental::functional_classes::{ClassLimits, SourceClass, SourceObjectProperty};
use rowl::experimental::functional_declarations::{SourceDeclaration, SourceEntityKind};
use rowl::experimental::functional_document::{read_document, DocumentLimits, SourceAxiom};
use rowl::experimental::model::*;

const EX: &str = "https://example.org/maintenance/";

fn iri(value: &[u8]) -> Iri {
    Iri {
        spelling: value.to_vec(),
    }
}
// The conversion from source records to the kernel's ontology model below is
// example code; the verified document construction is a later stage.
fn class(source: &SourceClass) -> ClassExpression {
    match source {
        SourceClass::Named(name) => ClassExpression::Class(Class {
            iri: iri(&name.value),
        }),
        SourceClass::IntersectionOf { members, .. } => {
            ClassExpression::ObjectIntersectionOf(Box::new(members_of(members)))
        }
        SourceClass::UnionOf { members, .. } => {
            ClassExpression::ObjectUnionOf(Box::new(members_of(members)))
        }
        SourceClass::ComplementOf { operand, .. } => {
            ClassExpression::ObjectComplementOf(Box::new(class(operand)))
        }
        SourceClass::SomeValuesFrom {
            property, filler, ..
        } => {
            ClassExpression::ObjectSomeValuesFrom(self::property(property), Box::new(class(filler)))
        }
        SourceClass::AllValuesFrom {
            property, filler, ..
        } => {
            ClassExpression::ObjectAllValuesFrom(self::property(property), Box::new(class(filler)))
        }
    }
}
fn members_of(members: &[SourceClass]) -> AtLeastTwo<ClassExpression> {
    AtLeastTwo {
        first: class(&members[0]),
        second: class(&members[1]),
        rest: members[2..].iter().map(class).collect(),
    }
}
fn property(source: &SourceObjectProperty) -> ObjectPropertyExpression {
    match source {
        SourceObjectProperty::Named(name) => ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri(&name.value),
        }),
        SourceObjectProperty::Inverse { property, .. } => {
            ObjectPropertyExpression::Inverse(ObjectProperty {
                iri: iri(&property.value),
            })
        }
    }
}
/// Axiom annotations are dropped here: they impose nothing on reasoning.
fn declaration(source: &SourceDeclaration) -> Axiom {
    let name = iri(&source.entity.iri.value);
    Axiom::Declaration(match source.entity.kind {
        SourceEntityKind::Class => Entity::Class(Class { iri: name }),
        SourceEntityKind::Datatype => Entity::Datatype(Datatype { iri: name }),
        SourceEntityKind::ObjectProperty => Entity::ObjectProperty(ObjectProperty { iri: name }),
        SourceEntityKind::DataProperty => Entity::DataProperty(DataProperty { iri: name }),
        SourceEntityKind::AnnotationProperty => {
            Entity::AnnotationProperty(AnnotationProperty { iri: name })
        }
        SourceEntityKind::NamedIndividual => Entity::NamedIndividual(NamedIndividual { iri: name }),
    })
}
fn class_axiom(source: &SourceClassAxiom) -> Axiom {
    match &source.body {
        SourceClassAxiomBody::SubClassOf { sub, sup } => Axiom::SubClassOf(class(sub), class(sup)),
        SourceClassAxiomBody::EquivalentClasses(members) => {
            Axiom::EquivalentClasses(members_of(members))
        }
        SourceClassAxiomBody::DisjointClasses(members) => {
            Axiom::DisjointClasses(members_of(members))
        }
        SourceClassAxiomBody::DisjointUnion {
            class: name,
            members,
        } => Axiom::DisjointUnion(
            Class {
                iri: iri(&name.value),
            },
            members_of(members),
        ),
        SourceClassAxiomBody::ObjectPropertyDomain { property, domain } => {
            Axiom::ObjectPropertyDomain(self::property(property), class(domain))
        }
        SourceClassAxiomBody::ObjectPropertyRange { property, range } => {
            Axiom::ObjectPropertyRange(self::property(property), class(range))
        }
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
fn show(question: &str, answer: Option<bool>) {
    match answer {
        Some(answer) => println!("{question}: {answer}"),
        None => println!("{question}: outside the supported fragment"),
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
    let mut axioms = Vec::new();
    for item in &document.tail.axioms {
        match item {
            SourceAxiom::Declaration(source) => axioms.push(declaration(source)),
            SourceAxiom::Annotation(_) => {}
            SourceAxiom::Class(source) => {
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
                axioms.push(class_axiom(source));
            }
        }
    }
    let axioms: Vec<AnnotatedAxiom> = axioms
        .into_iter()
        .map(|axiom| AnnotatedAxiom {
            annotations: Vec::new(),
            axiom,
        })
        .collect();
    show("The axioms are consistent", consistent(&axioms));
    show(
        "A pump has some part",
        subsumed(&axioms, &named("Pump"), &some_part(named("Part"))),
    );
    show(
        "A pump with a faulty part is out of service",
        subsumed(
            &axioms,
            &both(named("Pump"), some_part(named("FaultyPart"))),
            &ClassExpression::ObjectComplementOf(Box::new(named("InService"))),
        ),
    );
    show(
        "A motor that is also a valve can exist",
        class_satisfiable(&axioms, &both(named("Motor"), named("Valve"))),
    );
    show(
        "Every machine needs inspection",
        subsumed(&axioms, &named("Machine"), &named("NeedsInspection")),
    );
    println!("Reading the whole document is proved exact against the Functional Syntax grammar, and each answer is proved against the OWL 2 Direct Semantics; the conversion between them in this example is not yet a verified step.");
}
