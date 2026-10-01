//! Negation normal form of maintenance class expressions, the tableau's input.
use rowl::experimental::model::*;
use rowl::experimental::nnf::{nnf, NnfConcept};
use rowl::experimental::Natural;

const EX: &str = "https://example.org/maintenance/";

fn iri(local: &str) -> Iri {
    Iri {
        spelling: format!("{EX}{local}").into_bytes(),
    }
}
fn class(local: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(local) })
}
fn property(local: &str) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(local) })
}
fn not(e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(e))
}
fn both(first: ClassExpression, second: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first,
        second,
        rest: Vec::new(),
    }))
}
fn some(p: &str, e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(property(p), Box::new(e))
}
fn short(spelling: &[u8]) -> String {
    let text = String::from_utf8_lossy(spelling).into_owned();
    text.strip_prefix(EX)
        .map(|local| format!("ex:{local}"))
        .unwrap_or(text)
}
fn show(c: &NnfConcept) -> String {
    match c {
        NnfConcept::Top => "⊤".into(),
        NnfConcept::Bottom => "⊥".into(),
        NnfConcept::Atom(class) => short(&class.iri.spelling),
        NnfConcept::NotAtom(class) => format!("¬{}", short(&class.iri.spelling)),
        NnfConcept::And(a, b) => format!("({} ⊓ {})", show(a), show(b)),
        NnfConcept::Or(a, b) => format!("({} ⊔ {})", show(a), show(b)),
        NnfConcept::Exists(p, c) => format!("∃{}.{}", short(&p.iri.spelling), show(c)),
        NnfConcept::Forall(p, c) => format!("∀{}.{}", short(&p.iri.spelling), show(c)),
    }
}
fn main() {
    let cases = [
        (
            "Machines with a faulty part",
            both(class("Machine"), some("hasPart", class("FaultyPart"))),
        ),
        (
            "Not (machine with a faulty part)",
            not(both(class("Machine"), some("hasPart", class("FaultyPart")))),
        ),
        (
            "Not (some part is not owl:Nothing)",
            not(some(
                "hasPart",
                not(ClassExpression::Class(Class {
                    iri: Iri {
                        spelling: b"http://www.w3.org/2002/07/owl#Nothing".to_vec(),
                    },
                })),
            )),
        ),
        (
            "At least one part (a cardinality)",
            ClassExpression::ObjectMinCardinality(
                Natural::Succ(Box::new(Natural::Zero)),
                property("hasPart"),
                None,
            ),
        ),
    ];
    for (title, expression) in cases {
        match nnf(&expression, true) {
            Some(concept) => println!("{title}: {}", show(&concept)),
            None => println!("{title}: outside the ALC fragment (a later reasoner stage)"),
        }
    }
    println!("Negation only remains on named classes. The tableau that decides these concepts is the next reasoner stage.");
}
