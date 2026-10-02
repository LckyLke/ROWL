//! The verified ALC tableau with blocking answering maintenance questions under ontology axioms.
use rowl::experimental::model::*;
use rowl::experimental::nnf::{nnf, NnfConcept};
use rowl::experimental::tbox::satisfiable_in;

const EX: &str = "https://example.org/maintenance/";

fn class(name: &str) -> ClassExpression {
    ClassExpression::Class(Class {
        iri: Iri {
            spelling: format!("{EX}{name}").into_bytes(),
        },
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
fn either(first: ClassExpression, second: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectUnionOf(Box::new(AtLeastTwo {
        first,
        second,
        rest: Vec::new(),
    }))
}
fn some(p: &str, e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(property(p), Box::new(e))
}
/// `sub ⊑ sup` holds in an interpretation exactly when every element is in `¬sub ⊔ sup`.
fn below(sub: ClassExpression, sup: ClassExpression) -> ClassExpression {
    either(not(sub), sup)
}
fn translate(e: &ClassExpression) -> NnfConcept {
    nnf(e, true).expect("inside the ALC fragment")
}
/// `sub` is subsumed by `sup` under the axioms exactly when `sub` and not `sup` cannot hold together.
fn subsumed(axioms: &NnfConcept, sub: ClassExpression, sup: ClassExpression) -> bool {
    !satisfiable_in(&translate(&both(sub, not(sup))), axioms)
}
fn main() {
    // Every machine has a part, every part has a part (an infinite chain that
    // blocking cuts off), anything with a faulty part needs inspection, and
    // nothing that needs inspection is in service.
    let axioms = translate(&both(
        both(
            below(class("Machine"), some("hasPart", class("Part"))),
            below(class("Part"), some("hasPart", class("Part"))),
        ),
        both(
            below(
                some("hasPart", class("FaultyPart")),
                class("NeedsInspection"),
            ),
            below(class("NeedsInspection"), not(class("InService"))),
        ),
    ));
    let faulty_machine = || both(class("Machine"), some("hasPart", class("FaultyPart")));
    println!(
        "Machine is satisfiable under the axioms: {}",
        satisfiable_in(&translate(&class("Machine")), &axioms)
    );
    println!(
        "Machine with a faulty part needs inspection: {}",
        subsumed(&axioms, faulty_machine(), class("NeedsInspection"))
    );
    println!(
        "...and is therefore not in service: {}",
        subsumed(&axioms, faulty_machine(), not(class("InService")))
    );
    println!(
        "Every machine needs inspection: {}",
        subsumed(&axioms, class("Machine"), class("NeedsInspection"))
    );
    println!(
        "A machine in service with a faulty part is satisfiable: {}",
        satisfiable_in(
            &translate(&both(class("InService"), faulty_machine())),
            &axioms
        )
    );
    println!("Satisfiable answers (and failed subsumptions) come with a model of the translated concept in which every element satisfies the translated axioms; unsatisfiable answers (and subsumptions) are proved for every OWL interpretation in which every element is in the axiom expression.");
    println!("The axioms are written here as one class expression by hand; reading SubClassOf axioms from an ontology into it is not yet a verified step.");
}
