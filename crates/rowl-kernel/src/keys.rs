//! OWL 2 Structural Specification §9.5 nonempty key-property requirement.
//! Checks supplied raw axioms, preserving the original first failing occurrence.
//! This is a structural check; it neither validates all DL constraints nor
//! performs named-individual key reasoning.
#![allow(clippy::ptr_arg)] // Checked indexed Vec operations.
use crate::model::{AnnotatedAxiom, Axiom};

#[allow(clippy::len_zero)] // Vec::is_empty lacks a model in the pinned extraction.
pub fn axiom_allowed(item: &AnnotatedAxiom) -> bool {
    match &item.axiom {
        Axiom::HasKey(_, objects, data) => objects.len() != 0 || data.len() != 0,
        _ => true,
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
/// None iff every HasKey in the supplied complete closure uses at least one
/// object or data property; otherwise the exact original first invalid axiom.
pub fn check_keys(axioms: &Vec<AnnotatedAxiom>) -> Option<&AnnotatedAxiom> {
    axioms_from(axioms, 0)
}
