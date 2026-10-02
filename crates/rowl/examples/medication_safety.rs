//! Allergy checking for prescriptions, answered end to end from the original
//! Functional Syntax bytes by the verified pipeline. alice is allergic to
//! penicillins and receives a combination pack; a capsule in the pack has
//! amoxicillin, a penicillin, as an active ingredient. The alert follows because
//! `contains` is transitive and every active ingredient is contained. bob
//! receives the same pack without a recorded allergy. carol has the same allergy
//! and receives a tablet with azithromycin, a macrolide; macrolides and
//! penicillins are disjoint, so the tablet's active ingredient is provably no
//! penicillin. The document is read and prepared once, and every question is
//! asked of the prepared records. An illustration of allergy checking, not
//! clinical guidance.
use rowl::experimental::functional_annotations::AnnotationLimits;
use rowl::experimental::functional_classes::ClassLimits;
use rowl::experimental::functional_document::DocumentLimits;
use rowl::experimental::model::*;
use rowl::experimental::shi_ontology::{prepared_consistent, prepared_instance_of};
use rowl::experimental::source_reasoning::source_prepared;

const EX: &str = "https://example.org/medication/";

fn iri(local: &str) -> Iri {
    Iri {
        spelling: format!("{EX}{local}").into_bytes(),
    }
}
fn class(local: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(local) })
}
fn individual(local: &str) -> NamedIndividual {
    NamedIndividual { iri: iri(local) }
}
fn show(question: &str, answer: Option<bool>) {
    match answer {
        Some(answer) => println!("{question}: {answer}"),
        None => println!("{question}: outside the supported fragment"),
    }
}
fn main() {
    let bytes = include_bytes!("../../../examples/medication-safety.ofn").to_vec();
    let limits = DocumentLimits {
        tokens: 1000,
        prefixes: 10,
        prefix_value: 100,
        imports: 10,
        iri: 100,
        axioms: 100,
        annotations: AnnotationLimits {
            depth: 2,
            count: 10,
            iri: 100,
            lexical: 200,
        },
        classes: ClassLimits {
            depth: 10,
            count: 10,
            iri: 100,
        },
    };
    let scope = b"records".to_vec();
    let records = match source_prepared(&bytes, &limits, &scope) {
        Ok(Some(records)) => records,
        Ok(None) => {
            println!("The records are outside the supported fragment");
            return;
        }
        Err(_) => {
            println!("The document was rejected");
            return;
        }
    };
    show("The records are consistent", prepared_consistent(&records));
    for patient in ["alice", "bob", "carol"] {
        show(
            &format!("{patient} needs an allergy alert"),
            prepared_instance_of(&records, &individual(patient), &class("AllergyAlert")),
        );
    }
    let no_penicillin = ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri("hasActiveIngredient"),
        }),
        Box::new(ClassExpression::ObjectComplementOf(Box::new(class(
            "Penicillin",
        )))),
    );
    show(
        "carol's tablet has an active ingredient that is no penicillin",
        prepared_instance_of(&records, &individual("tablet"), &no_penicillin),
    );
    println!("alice's alert follows in every model of the records: the amoxicillin sits in a capsule inside the pack, and contains is transitive. bob has no recorded allergy, and carol's azithromycin is a macrolide, which is no penicillin; for them the alert does not follow. false means not entailed by the records, not proved safe. Each answer is proved end to end against the OWL 2 Direct Semantics of the read axioms.");
}
