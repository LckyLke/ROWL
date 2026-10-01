//! Composed OWL 2 §11.2 datatype definition availability and dependency order.
//! Requires the complete raw axiom closure. The structural composition also
//! checks defined-datatype positions; lexical/facet/value validity remains separate.
use crate::datatype_definitions::{check_definitions, DefinitionCheck};
use crate::datatype_order::{check_acyclic, DependencyCheck};
use crate::datatype_positions::{check_ontology_positions, PositionCheck};
use crate::model::{AnnotatedAxiom, Annotation, Iri, RawOntology};

pub enum DatatypeDefinitionCheck<'a> {
    Allowed,
    MissingDefinition(&'a Iri),
    PredefinedRedefined(&'a AnnotatedAxiom),
    MultipleDefinitions {
        first: &'a AnnotatedAxiom,
        second: &'a AnnotatedAxiom,
    },
    Cycle {
        smaller: &'a Iri,
        larger: &'a Iri,
    },
}

/// Availability failures precede circular-definition diagnostics. A cycle failure
/// certifies successful definition availability/uniqueness before the order check.
pub fn check_definition_rules(ontology: &RawOntology) -> DatatypeDefinitionCheck<'_> {
    match check_definitions(ontology) {
        DefinitionCheck::MissingDefinition(iri) => DatatypeDefinitionCheck::MissingDefinition(iri),
        DefinitionCheck::PredefinedRedefined(item) => {
            DatatypeDefinitionCheck::PredefinedRedefined(item)
        }
        DefinitionCheck::MultipleDefinitions { first, second } => {
            DatatypeDefinitionCheck::MultipleDefinitions { first, second }
        }
        DefinitionCheck::Allowed => match check_acyclic(&ontology.axioms) {
            DependencyCheck::Acyclic => DatatypeDefinitionCheck::Allowed,
            DependencyCheck::Cycle { smaller, larger } => {
                DatatypeDefinitionCheck::Cycle { smaller, larger }
            }
        },
    }
}

pub enum StructuralDatatypeCheck<'a> {
    Allowed,
    MissingDefinition(&'a Iri),
    PredefinedRedefined(&'a AnnotatedAxiom),
    MultipleDefinitions {
        first: &'a AnnotatedAxiom,
        second: &'a AnnotatedAxiom,
    },
    Cycle {
        smaller: &'a Iri,
        larger: &'a Iri,
    },
    ForbiddenOntologyAnnotation(&'a Annotation),
    ForbiddenAxiomPosition(&'a AnnotatedAxiom),
}

/// Definition availability/order followed by every defined-datatype positional
/// restriction in the supplied closure and ontology annotations. Literal lexical
/// validity, facet admissibility, value spaces and full DL validity are separate.
pub fn check_structural_datatypes(ontology: &RawOntology) -> StructuralDatatypeCheck<'_> {
    match check_definition_rules(ontology) {
        DatatypeDefinitionCheck::MissingDefinition(iri) => {
            StructuralDatatypeCheck::MissingDefinition(iri)
        }
        DatatypeDefinitionCheck::PredefinedRedefined(item) => {
            StructuralDatatypeCheck::PredefinedRedefined(item)
        }
        DatatypeDefinitionCheck::MultipleDefinitions { first, second } => {
            StructuralDatatypeCheck::MultipleDefinitions { first, second }
        }
        DatatypeDefinitionCheck::Cycle { smaller, larger } => {
            StructuralDatatypeCheck::Cycle { smaller, larger }
        }
        DatatypeDefinitionCheck::Allowed => match check_ontology_positions(ontology) {
            PositionCheck::Allowed => StructuralDatatypeCheck::Allowed,
            PositionCheck::OntologyAnnotation(item) => {
                StructuralDatatypeCheck::ForbiddenOntologyAnnotation(item)
            }
            PositionCheck::Axiom(item) => StructuralDatatypeCheck::ForbiddenAxiomPosition(item),
        },
    }
}
