//! The verified ALC tableau answering maintenance satisfiability and subsumption questions.
use rowl::experimental::model::*;
use rowl::experimental::nnf::nnf;
use rowl::experimental::tableau::satisfiable;

const EX: &str = "https://example.org/maintenance/";
const NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

fn class(name: &str) -> ClassExpression {
    let spelling = if name.starts_with("http") {
        name.as_bytes().to_vec()
    } else {
        format!("{EX}{name}").into_bytes()
    };
    ClassExpression::Class(Class {
        iri: Iri { spelling },
    })
}
fn property(name: &str) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty {
        iri: Iri {
            spelling: format!("{EX}{name}").into_bytes(),
        },
    })
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
fn only(p: &str, e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectAllValuesFrom(property(p), Box::new(e))
}
fn decide(e: &ClassExpression) -> bool {
    satisfiable(&nnf(e, true).expect("inside the ALC fragment"))
}
/// `sub` is subsumed by `sup` exactly when `sub` and not `sup` cannot hold together.
fn subsumed(sub: ClassExpression, sup: ClassExpression) -> bool {
    !decide(&both(sub, not(sup)))
}
fn main() {
    let faulty_machine = || both(class("Machine"), some("hasPart", class("FaultyPart")));
    println!(
        "Machine with a faulty part is satisfiable: {}",
        decide(&faulty_machine())
    );
    println!(
        "...and is subsumed by 'has some faulty part': {}",
        subsumed(faulty_machine(), some("hasPart", class("FaultyPart")))
    );
    println!(
        "...but not by 'every part is faulty': {}",
        subsumed(faulty_machine(), only("hasPart", class("FaultyPart")))
    );
    let impossible = both(
        some("hasPart", class("FaultyPart")),
        only("hasPart", not(class("FaultyPart"))),
    );
    println!(
        "A faulty part with only non-faulty parts is satisfiable: {}",
        decide(&impossible)
    );
    println!(
        "owl:Nothing is subsumed by every class: {}",
        subsumed(class(NOTHING), class("Machine"))
    );
    println!("Satisfiable answers (and failed subsumptions) come with a tree model of the concept; unsatisfiable answers (and subsumptions) are proved to hold in every OWL interpretation.");
    println!("Ontology axioms (a TBox, such as 'machines with faulty parts need inspection') need blocking; the tbox example answers questions under them.");
}
