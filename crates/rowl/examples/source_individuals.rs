//! Questions about named individuals in original Functional Syntax source,
//! answered end to end by the verified pipeline: the document reader, the
//! mapping into the kernel's OWL model and the ALC reasoner with assertions.
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
    let bytes = include_bytes!("../../../examples/maintenance-individuals.ofn").to_vec();
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
    // The node ID _:seal becomes an anonymous individual of this scope.
    let scope = b"fleet".to_vec();
    show(
        "The fleet's axioms are consistent",
        source_consistent(&bytes, &limits, &scope),
    );
    for pump in ["pump1", "pump2"] {
        show(
            &format!("{pump} needs inspection"),
            source_instance_of(
                &bytes,
                &limits,
                &scope,
                &individual(pump),
                &class("NeedsInspection"),
            ),
        );
    }
    show(
        "pump2 is a machine",
        source_instance_of(
            &bytes,
            &limits,
            &scope,
            &individual("pump2"),
            &class("Machine"),
        ),
    );
    println!("Each answer is proved end to end: from the original bytes, through the document reader and the mapping into the OWL model, to the OWL 2 Direct Semantics of the read axioms and assertions.");
}
