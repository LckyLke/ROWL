//! Definition availability and uniqueness for OWL 2 §11.2 datatypes.
//! Acyclic dependencies and lexical/facet/value validation are separate checks.
#![allow(clippy::ptr_arg)]
use crate::builtins::builtin_kind;
use crate::collection::{axiom_closure_entities, EntityUses};
use crate::model::{AnnotatedAxiom, Axiom, Iri, RawOntology};
use crate::range_equality::same_definition;
use crate::symbols::same_spelling;
use crate::typing::EntityKind;

pub enum DefinitionCheck<'a> {
    Allowed,
    MissingDefinition(&'a Iri),
    PredefinedRedefined(&'a AnnotatedAxiom),
    MultipleDefinitions {
        first: &'a AnnotatedAxiom,
        second: &'a AnnotatedAxiom,
    },
}

/// Exactly rdfs:Literal and the reviewed 2012 OWL datatype vocabulary.
/// This recognizes names; it does not implement their value spaces.
pub fn predefined(datatype: &Iri) -> bool {
    matches!(builtin_kind(&datatype.spelling), Some(EntityKind::Datatype))
}

pub fn defines(item: &AnnotatedAxiom, datatype: &Iri) -> bool {
    match &item.axiom {
        Axiom::DatatypeDefinition(d, _) => same_spelling(&d.iri.spelling, &datatype.spelling),
        _ => false,
    }
}

fn first_from<'a>(
    axioms: &'a Vec<AnnotatedAxiom>,
    datatype: &Iri,
    index: usize,
) -> Option<&'a AnnotatedAxiom> {
    if index < axioms.len() {
        let item = &axioms[index];
        if defines(item, datatype) {
            Some(item)
        } else {
            first_from(axioms, datatype, index + 1)
        }
    } else {
        None
    }
}

fn distinct_from<'a>(
    axioms: &'a Vec<AnnotatedAxiom>,
    datatype: &Iri,
    first: &AnnotatedAxiom,
    index: usize,
) -> Option<&'a AnnotatedAxiom> {
    if index < axioms.len() {
        let second = &axioms[index];
        if defines(second, datatype) && !same_definition(first, second) {
            Some(second)
        } else {
            distinct_from(axioms, datatype, first, index + 1)
        }
    } else {
        None
    }
}

fn check_one<'a>(axioms: &'a Vec<AnnotatedAxiom>, datatype: &'a Iri) -> DefinitionCheck<'a> {
    let built_in = predefined(datatype);
    match first_from(axioms, datatype, 0) {
        None => {
            if built_in {
                DefinitionCheck::Allowed
            } else {
                DefinitionCheck::MissingDefinition(datatype)
            }
        }
        Some(first) => {
            if built_in {
                DefinitionCheck::PredefinedRedefined(first)
            } else {
                match distinct_from(axioms, datatype, first, 0) {
                    None => DefinitionCheck::Allowed,
                    Some(second) => DefinitionCheck::MultipleDefinitions { first, second },
                }
            }
        }
    }
}

fn check_uses<'a>(axioms: &'a Vec<AnnotatedAxiom>, uses: EntityUses<'a>) -> DefinitionCheck<'a> {
    match uses {
        EntityUses::Empty => DefinitionCheck::Allowed,
        EntityUses::Entry {
            iri,
            kind: EntityKind::Datatype,
            next,
        } => match check_one(axioms, iri) {
            DefinitionCheck::Allowed => check_uses(axioms, *next),
            failure => failure,
        },
        EntityUses::Entry { next, .. } => check_uses(axioms, *next),
    }
}

/// Check every explicit typed datatype occurrence, including literal datatypes
/// in recursive annotations and facets, from the actual supplied raw closure.
/// Custom datatypes need one structurally distinct annotated definition; predefined
/// datatypes permit no defining axiom. Equivalent raw copies count once.
pub fn check_definitions(ontology: &RawOntology) -> DefinitionCheck<'_> {
    check_uses(&ontology.axioms, axiom_closure_entities(ontology).uses)
}
