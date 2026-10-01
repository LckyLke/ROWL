//! Validated outer axiom-set view with every original occurrence retained.
//!
//! The complete caller-supplied closure must already be standardized apart.
//! Origin tokens are caller metadata, not proved parser locations. Every raw
//! axiom passes arity checking before any structural copies are grouped. This
//! does not materialize duplicate-free nested associations or validate full DL.
#![allow(clippy::ptr_arg)] // Indexed Vec operations in the pinned extraction subset.
use crate::arity::axiom_allowed;
use crate::axiom_equality::same_axiom;
use crate::batch::AxiomOrigin;
use crate::model::AnnotatedAxiom;

pub struct AxiomOccurrence {
    pub origin: AxiomOrigin,
    pub axiom: AnnotatedAxiom,
}

/// Constructed only by build; original source objects are borrowed unchanged.
pub struct AxiomSet<'a> {
    source: &'a Vec<AxiomOccurrence>,
    representative_of: Vec<usize>,
    representatives: Vec<usize>,
}

pub enum BuildResult<'a> {
    InvalidArity(&'a AxiomOccurrence),
    Set(AxiomSet<'a>),
}

fn first_forbidden_from(source: &Vec<AxiomOccurrence>, index: usize) -> Option<&AxiomOccurrence> {
    if index < source.len() {
        if axiom_allowed(&source[index].axiom) {
            first_forbidden_from(source, index + 1)
        } else {
            Some(&source[index])
        }
    } else {
        None
    }
}

fn first_match_from(
    source: &Vec<AxiomOccurrence>,
    sought: &AnnotatedAxiom,
    end: usize,
    index: usize,
) -> usize {
    if index < end {
        if same_axiom(&source[index].axiom, sought) {
            index
        } else {
            first_match_from(source, sought, end, index + 1)
        }
    } else {
        end
    }
}

fn build_from(
    source: &Vec<AxiomOccurrence>,
    index: usize,
    mut representative_of: Vec<usize>,
    mut representatives: Vec<usize>,
) -> AxiomSet<'_> {
    if index < source.len() {
        let representative = first_match_from(source, &source[index].axiom, index, 0);
        representative_of.push(representative);
        if representative == index {
            representatives.push(index);
        }
        build_from(source, index + 1, representative_of, representatives)
    } else {
        AxiomSet {
            source,
            representative_of,
            representatives,
        }
    }
}

/// Validate all original arities first, then choose stable first representatives.
/// Invalid input returns the first original occurrence, including its metadata.
pub fn build(source: &Vec<AxiomOccurrence>) -> BuildResult<'_> {
    match first_forbidden_from(source, 0) {
        Some(item) => BuildResult::InvalidArity(item),
        None => BuildResult::Set(build_from(source, 0, Vec::new(), Vec::new())),
    }
}

/// Every original source occurrence survives, including equivalent copies.
pub fn originals<'a>(set: &AxiomSet<'a>) -> &'a Vec<AxiomOccurrence> {
    set.source
}

/// Source indices of unique representatives, in first-occurrence order.
pub fn representatives<'view>(set: &'view AxiomSet<'_>) -> &'view Vec<usize> {
    &set.representatives
}

/// Exact per-occurrence map to its first equivalent original source index.
pub fn representative_indices<'view>(set: &'view AxiomSet<'_>) -> &'view Vec<usize> {
    &set.representative_of
}

pub fn occurrence<'a>(set: &AxiomSet<'a>, index: usize) -> Option<&'a AxiomOccurrence> {
    if index < set.source.len() {
        Some(&set.source[index])
    } else {
        None
    }
}

/// Resolve any original occurrence to the original representative object.
pub fn representative_of<'a>(set: &AxiomSet<'a>, index: usize) -> Option<&'a AxiomOccurrence> {
    if index < set.representative_of.len() {
        let representative = set.representative_of[index];
        Some(&set.source[representative])
    } else {
        None
    }
}
