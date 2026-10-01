//! All anonymous-individual restrictions of OWL 2 §11.2 on a supplied closure.
//! Parsing, standardization apart, other DL restrictions and reasoning are separate.
#![allow(clippy::ptr_arg)]
use crate::anonymous::check_positions;
use crate::anonymous_boundary::{check_boundary, BoundaryCheck};
use crate::anonymous_graph::{check_forest, ForestCheck};
use crate::anonymous_multiplicity::{check_multiplicity, MultiplicityCheck};
use crate::model::{AnnotatedAxiom, AnonymousIndividual};

pub enum AnonymousCheck<'a> {
    Allowed,
    ForbiddenPosition(&'a AnnotatedAxiom),
    SelfLoop(&'a AnonymousIndividual),
    Cycle {
        left: &'a AnonymousIndividual,
        right: &'a AnonymousIndividual,
    },
    MultipleAssertions {
        first: &'a AnnotatedAxiom,
        second: &'a AnnotatedAxiom,
    },
    NoBoundaryRoot(&'a AnonymousIndividual),
}

/// Accept exactly all anonymous positional and assertion-graph restrictions.
/// Failure priority is positions, forest, multiplicity, then named boundary.
/// The input must be the complete, standardized-apart raw closure. Run this
/// before semantic assertion normalization, which changes structural identity.
pub fn check_anonymous(axioms: &Vec<AnnotatedAxiom>) -> AnonymousCheck<'_> {
    if let Some(item) = check_positions(axioms) {
        return AnonymousCheck::ForbiddenPosition(item);
    }
    match check_forest(axioms) {
        ForestCheck::SelfLoop(vertex) => return AnonymousCheck::SelfLoop(vertex),
        ForestCheck::Cycle { left, right } => return AnonymousCheck::Cycle { left, right },
        ForestCheck::Forest => {}
    }
    if let MultiplicityCheck::MultipleAssertions { first, second } = check_multiplicity(axioms) {
        return AnonymousCheck::MultipleAssertions { first, second };
    }
    if let BoundaryCheck::NoRoot(vertex) = check_boundary(axioms) {
        return AnonymousCheck::NoBoundaryRoot(vertex);
    }
    AnonymousCheck::Allowed
}
