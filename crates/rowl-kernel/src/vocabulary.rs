//! OWL 2 DL reserved-vocabulary restrictions on headers and entity positions.
//!
//! This check is separate from declaration typing: ordinary allowed punning
//! cannot authorize an OWL/XSD/RDF/RDFS reserved IRI in the wrong role. Raw
//! byte spellings, datatype lexical spaces, facet usage and global restrictions
//! remain separate obligations. A `Valid` here is not full DL validity.

#![allow(clippy::ptr_arg)]

use crate::builtins::builtin_kind;
use crate::collection::{ontology_entities, EntityUses};
use crate::model::{Iri, OntologyIdentity, RawOntology};
use crate::typing::EntityKind;

pub enum VocabularyResult<'a> {
    Valid,
    ReservedOntologyIri(&'a Iri),
    ReservedVersionIri(&'a Iri),
    ForbiddenEntity { iri: &'a Iri, kind: EntityKind },
}

fn prefix_from(key: &Vec<u8>, prefix: &[u8], index: usize) -> bool {
    if index >= prefix.len() {
        true
    } else if index >= key.len() {
        false
    } else if key[index] == prefix[index] {
        prefix_from(key, prefix, index + 1)
    } else {
        false
    }
}

/// Four exact namespace prefixes from the 2012 specification, Table 2.
pub fn reserved_iri(key: &Vec<u8>) -> bool {
    prefix_from(key, b"http://www.w3.org/1999/02/22-rdf-syntax-ns#", 0)
        || prefix_from(key, b"http://www.w3.org/2000/01/rdf-schema#", 0)
        || prefix_from(key, b"http://www.w3.org/2001/XMLSchema#", 0)
        || prefix_from(key, b"http://www.w3.org/2002/07/owl#", 0)
}

/// Custom names are allowed. Reserved names must have precisely their built-in
/// entity role; no reserved IRI can name an OWL 2 DL named individual.
pub fn entity_iri_allowed(iri: &Iri, kind: &EntityKind) -> bool {
    if !reserved_iri(&iri.spelling) {
        return true;
    }
    match builtin_kind(&iri.spelling) {
        Some(role) => matches!(
            (role, kind),
            (EntityKind::Class, EntityKind::Class)
                | (EntityKind::Datatype, EntityKind::Datatype)
                | (EntityKind::ObjectProperty, EntityKind::ObjectProperty)
                | (EntityKind::DataProperty, EntityKind::DataProperty)
                | (
                    EntityKind::AnnotationProperty,
                    EntityKind::AnnotationProperty
                )
                | (EntityKind::NamedIndividual, EntityKind::NamedIndividual)
        ),
        None => false,
    }
}

fn check_uses(uses: EntityUses<'_>) -> VocabularyResult<'_> {
    match uses {
        EntityUses::Empty => VocabularyResult::Valid,
        EntityUses::Entry { iri, kind, next } => {
            if entity_iri_allowed(iri, &kind) {
                check_uses(*next)
            } else {
                VocabularyResult::ForbiddenEntity { iri, kind }
            }
        }
    }
}

/// Check the supplied ontology, including ontology-level and nested annotations.
/// Untyped annotation IRI values, imports and facet IRIs are not entity positions.
/// Headers are checked first, then the first forbidden collected occurrence.
pub fn check_reserved_vocabulary(ontology: &RawOntology) -> VocabularyResult<'_> {
    if let OntologyIdentity::Named { ontology, version } = &ontology.identity {
        if reserved_iri(&ontology.spelling) {
            return VocabularyResult::ReservedOntologyIri(ontology);
        }
        if let Some(version) = version {
            if reserved_iri(&version.spelling) {
                return VocabularyResult::ReservedVersionIri(version);
            }
        }
    }
    let collected = ontology_entities(ontology);
    check_uses(collected.uses)
}
