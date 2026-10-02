//! Class axioms read from original Functional Syntax source, then answered by the
//! verified reasoner.
use rowl::experimental::alc_ontology::{class_satisfiable, consistent, subsumed};
use rowl::experimental::functional::{Keyword, Terminal};
use rowl::experimental::functional_annotations::{read_annotations, AnnotationLimits};
use rowl::experimental::functional_class_axioms::{
    read_class_axiom, SourceClassAxiom, SourceClassAxiomBody,
};
use rowl::experimental::functional_classes::{ClassLimits, SourceClass, SourceObjectProperty};
use rowl::experimental::functional_declarations::{
    read_declaration, SourceDeclaration, SourceEntityKind,
};
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::model::*;
use rowl::experimental::prefixes::{check, Check};

const EX: &str = "https://example.org/maintenance/";

fn first_terminal(tokens: &Tokens) -> Option<Terminal> {
    match tokens {
        Tokens::Cons { token, .. } => Some(token.terminal),
        Tokens::Empty => None,
    }
}
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
    let prefix =
        read_prefix_header(&bytes, 400, 10, 100).unwrap_or_else(|_| panic!("source prefixes"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    let annotations = AnnotationLimits {
        depth: 2,
        count: 10,
        iri: 100,
        lexical: 100,
    };
    let classes = ClassLimits {
        depth: 10,
        count: 10,
        iri: 100,
    };
    let ontology = read_annotations(&table, &bytes, header.remaining, &annotations)
        .unwrap_or_else(|_| panic!("ontology annotations"));
    // This loop selects axiom positions for the demo; the verified axiom loop is
    // a later stage.
    let mut tokens = ontology.remaining;
    let mut axioms = Vec::new();
    loop {
        match first_terminal(&tokens) {
            Some(Terminal::Keyword(Keyword::Declaration)) => {
                let (source, rest) = read_declaration(&table, &bytes, tokens, &annotations)
                    .unwrap_or_else(|_| panic!("declaration"));
                axioms.push(declaration(&source));
                tokens = rest;
            }
            Some(Terminal::Close) | None => break,
            _ => {
                let (source, rest) =
                    read_class_axiom(&table, &bytes, tokens, &annotations, &classes)
                        .unwrap_or_else(|_| panic!("class axiom"));
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
                axioms.push(class_axiom(&source));
                tokens = rest;
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
    println!("Reading each axiom is proved exact against the Functional Syntax grammar, and each answer is proved against the OWL 2 Direct Semantics; the conversion between them in this example, the axiom loop and document construction are not yet verified steps.");
}
