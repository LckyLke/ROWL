//! Distinct annotated-assertion multiplicity in the anonymous graph.
//!
//! This operates on raw occurrence vectors: structurally equivalent copies are
//! one axiom-set member. It does not count bytes, occurrences or logical meanings.
#![allow(clippy::ptr_arg)] // Pinned extraction covers the indexed Vec operations.
use crate::anonymous_graph::same_individual;
use crate::assertion_equality::same_object_assertion;
use crate::model::{AnnotatedAxiom, Axiom, Individual};

pub enum MultiplicityCheck<'a> {
    Allowed,
    MultipleAssertions {
        first: &'a AnnotatedAxiom,
        second: &'a AnnotatedAxiom,
    },
}

/// Whether two positive assertions connect the same anonymous endpoint pair.
pub fn same_pair(left: &AnnotatedAxiom, right: &AnnotatedAxiom) -> bool {
    match (&left.axiom, &right.axiom) {
        (
            Axiom::ObjectPropertyAssertion(_, Individual::Anonymous(a), Individual::Anonymous(b)),
            Axiom::ObjectPropertyAssertion(_, Individual::Anonymous(c), Individual::Anonymous(d)),
        ) => {
            (same_individual(a, c) && same_individual(b, d))
                || (same_individual(a, d) && same_individual(b, c))
        }
        _ => false,
    }
}

fn against_from<'a>(
    axioms: &'a Vec<AnnotatedAxiom>,
    first: &AnnotatedAxiom,
    index: usize,
) -> Option<&'a AnnotatedAxiom> {
    if index < axioms.len() {
        let second = &axioms[index];
        if same_pair(first, second) && !same_object_assertion(first, second) {
            Some(second)
        } else {
            against_from(axioms, first, index + 1)
        }
    } else {
        None
    }
}

fn check_from(axioms: &Vec<AnnotatedAxiom>, index: usize) -> MultiplicityCheck<'_> {
    if index < axioms.len() {
        let first = &axioms[index];
        match against_from(axioms, first, 0) {
            Some(second) => MultiplicityCheck::MultipleAssertions { first, second },
            None => check_from(axioms, index + 1),
        }
    } else {
        MultiplicityCheck::Allowed
    }
}

/// Accept iff every anonymous pair has at most one structurally distinct positive
/// object assertion, including annotations. Return the original conflicting axioms.
/// Forests, named boundaries and complete OWL DL validity are separate conditions.
pub fn check_multiplicity(axioms: &Vec<AnnotatedAxiom>) -> MultiplicityCheck<'_> {
    check_from(axioms, 0)
}
