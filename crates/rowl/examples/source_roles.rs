//! Questions about a part hierarchy in original Functional Syntax source,
//! answered end to end by the verified pipeline: hasComponent is a sub-property
//! of the transitive hasPart, so a component of a component is a part.
use rowl::experimental::functional_annotations::AnnotationLimits;
use rowl::experimental::functional_classes::ClassLimits;
use rowl::experimental::functional_document::{DocumentError, DocumentLimits};
use rowl::experimental::model::*;
use rowl::experimental::source_reasoning::{source_consistent, source_instance_of};

const EX: &str = "https://example.org/maintenance/";

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
    let bytes = include_bytes!("../../../examples/maintenance-roles.ofn").to_vec();
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
    let scope = b"plant".to_vec();
    show(
        "The plant's axioms are consistent",
        source_consistent(&bytes, &limits, &scope),
    );
    for machine in ["pump1", "motor1"] {
        show(
            &format!("{machine} needs inspection"),
            source_instance_of(
                &bytes,
                &limits,
                &scope,
                &individual(machine),
                &class("NeedsInspection"),
            ),
        );
    }
    println!("pump1 needs inspection because bearing1, a component of its component motor1, is a faulty part: hasComponent is included in the transitive hasPart. Each answer is proved end to end against the OWL 2 Direct Semantics of the read axioms.");
}
