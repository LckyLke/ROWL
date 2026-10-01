//! OWL 2 structural specification §11.2 top-data-property restriction.
//!
//! This checks typed data-property occurrences in a supplied complete axiom
//! closure. Only a SubDataPropertyOf superproperty position admits the built-in
//! top data property. Other global restrictions are checked separately.
#![allow(clippy::ptr_arg)] // Stay in the checked Vec/index extraction subset.

use crate::collection::{axiom_entities, EntityUses};
use crate::model::{AnnotatedAxiom, Axiom};
use crate::typing::EntityKind;

fn equal_from(key: &Vec<u8>, pattern: &[u8], index: usize) -> bool {
    if index < key.len() {
        key[index] == pattern[index] && equal_from(key, pattern, index + 1)
    } else {
        true
    }
}
fn same_pattern(key: &Vec<u8>, pattern: &[u8]) -> bool {
    key.len() == pattern.len() && equal_from(key, pattern, 0)
}
fn is_top(key: &Vec<u8>) -> bool {
    same_pattern(key, b"http://www.w3.org/2002/07/owl#topDataProperty")
}
fn uses_allowed(values: EntityUses<'_>) -> bool {
    match values {
        EntityUses::Empty => true,
        EntityUses::Entry { iri, kind, next } => match kind {
            EntityKind::DataProperty => !is_top(&iri.spelling) && uses_allowed(*next),
            _ => uses_allowed(*next),
        },
    }
}

/// Check all typed occurrences, including properties nested in class
/// expressions and key lists. Annotation IRI values are not property uses.
pub fn axiom_allowed(item: &AnnotatedAxiom) -> bool {
    match &item.axiom {
        Axiom::SubDataPropertyOf(sub, _) => !is_top(&sub.iri.spelling),
        _ => uses_allowed(axiom_entities(item)),
    }
}
fn axioms_from(values: &Vec<AnnotatedAxiom>, index: usize) -> Option<&AnnotatedAxiom> {
    if index < values.len() {
        let item = &values[index];
        if axiom_allowed(item) {
            axioms_from(values, index + 1)
        } else {
            Some(item)
        }
    } else {
        None
    }
}

/// Return the exact first offending annotated axiom, or None iff every
/// supplied axiom obeys this restriction. Success is not full DL validity.
pub fn check_axioms(axioms: &Vec<AnnotatedAxiom>) -> Option<&AnnotatedAxiom> {
    axioms_from(axioms, 0)
}
