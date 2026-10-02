//! Allergy checking for prescriptions, answered end to end from the original
//! Functional Syntax bytes by the verified pipeline. alice is allergic to
//! penicillins and receives a combination pack; a capsule in the pack has
//! amoxicillin, a penicillin, as an active ingredient. The alert follows because
//! `contains` is transitive and every active ingredient is contained. bob
//! receives the same pack without a recorded allergy. carol has the same allergy
//! and receives a tablet with azithromycin, a macrolide; macrolides and
//! penicillins are disjoint, so the tablet's active ingredient is provably no
//! penicillin. An illustration of allergy checking, not clinical guidance.
use rowl::experimental::functional_annotations::AnnotationLimits;
use rowl::experimental::functional_classes::ClassLimits;
use rowl::experimental::functional_document::{DocumentError, DocumentLimits};
use rowl::experimental::model::*;
use rowl::experimental::source_reasoning::{source_consistent, source_instance_of};

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
fn show(question: &str, answer: Result<Option<bool>, DocumentError>) {
    match answer {
        Ok(Some(answer)) => println!("{question}: {answer}"),
        Ok(None) => println!("{question}: outside the supported fragment"),
        Err(_) => println!("{question}: the document was rejected"),
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
    show(
        "The records are consistent",
        source_consistent(&bytes, &limits, &scope),
    );
    for patient in ["alice", "bob", "carol"] {
        show(
            &format!("{patient} needs an allergy alert"),
            source_instance_of(
                &bytes,
                &limits,
                &scope,
                &individual(patient),
                &class("AllergyAlert"),
            ),
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
        source_instance_of(
            &bytes,
            &limits,
            &scope,
            &individual("tablet"),
            &no_penicillin,
        ),
    );
    println!("alice's alert follows in every model of the records: the amoxicillin sits in a capsule inside the pack, and contains is transitive. bob has no recorded allergy, and carol's azithromycin is a macrolide, which is no penicillin; for them the alert does not follow. false means not entailed by the records, not proved safe. Each answer is proved end to end against the OWL 2 Direct Semantics of the read axioms.");
}
