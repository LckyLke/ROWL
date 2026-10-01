//! Structural equality of the complete OWL 2 data-range language.
//! Unordered associations are compared as sets recursively, retaining nesting,
//! constructor kinds, exact datatype/facet IRIs and literal spellings.
//! This does not compare denotations, validate facets or canonicalize raw syntax.
#![allow(clippy::ptr_arg)] // Indexed operations covered by the pinned extraction.
use crate::assertion_equality::{same_annotation_set, same_literal};
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, DataRange, FacetRestriction, Literal, NonEmpty,
};
use crate::symbols::same_spelling;

pub fn same_facet(left: &FacetRestriction, right: &FacetRestriction) -> bool {
    same_spelling(&left.facet.spelling, &right.facet.spelling)
        && same_literal(&left.value, &right.value)
}

fn literal_contains_from(values: &Vec<Literal>, sought: &Literal, index: usize) -> bool {
    if index < values.len() {
        same_literal(sought, &values[index]) || literal_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn literal_member(sought: &Literal, values: &NonEmpty<Literal>) -> bool {
    same_literal(sought, &values.first) || literal_contains_from(&values.rest, sought, 0)
}
fn literal_subset_from(left: &Vec<Literal>, right: &NonEmpty<Literal>, index: usize) -> bool {
    if index < left.len() {
        literal_member(&left[index], right) && literal_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn literal_subset(left: &NonEmpty<Literal>, right: &NonEmpty<Literal>) -> bool {
    literal_member(&left.first, right) && literal_subset_from(&left.rest, right, 0)
}
pub fn same_literal_set(left: &NonEmpty<Literal>, right: &NonEmpty<Literal>) -> bool {
    literal_subset(left, right) && literal_subset(right, left)
}

fn facet_contains_from(
    values: &Vec<FacetRestriction>,
    sought: &FacetRestriction,
    index: usize,
) -> bool {
    if index < values.len() {
        same_facet(sought, &values[index]) || facet_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn facet_member(sought: &FacetRestriction, values: &NonEmpty<FacetRestriction>) -> bool {
    same_facet(sought, &values.first) || facet_contains_from(&values.rest, sought, 0)
}
fn facet_subset_from(
    left: &Vec<FacetRestriction>,
    right: &NonEmpty<FacetRestriction>,
    index: usize,
) -> bool {
    if index < left.len() {
        facet_member(&left[index], right) && facet_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn facet_subset(left: &NonEmpty<FacetRestriction>, right: &NonEmpty<FacetRestriction>) -> bool {
    facet_member(&left.first, right) && facet_subset_from(&left.rest, right, 0)
}
pub fn same_facet_set(
    left: &NonEmpty<FacetRestriction>,
    right: &NonEmpty<FacetRestriction>,
) -> bool {
    facet_subset(left, right) && facet_subset(right, left)
}

fn range_contains_from(values: &Vec<DataRange>, sought: &DataRange, index: usize) -> bool {
    if index < values.len() {
        same_range(sought, &values[index]) || range_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn range_member(sought: &DataRange, values: &AtLeastTwo<DataRange>) -> bool {
    same_range(sought, &values.first)
        || same_range(sought, &values.second)
        || range_contains_from(&values.rest, sought, 0)
}
fn range_subset_from(left: &Vec<DataRange>, right: &AtLeastTwo<DataRange>, index: usize) -> bool {
    if index < left.len() {
        range_member(&left[index], right) && range_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn range_subset(left: &AtLeastTwo<DataRange>, right: &AtLeastTwo<DataRange>) -> bool {
    range_member(&left.first, right)
        && range_member(&left.second, right)
        && range_subset_from(&left.rest, right, 0)
}
pub fn same_range_set(left: &AtLeastTwo<DataRange>, right: &AtLeastTwo<DataRange>) -> bool {
    range_subset(left, right) && range_subset(right, left)
}

/// Exact structural equality on all six data-range forms; no logical simplification.
pub fn same_range(left: &DataRange, right: &DataRange) -> bool {
    match (left, right) {
        (DataRange::Datatype(a), DataRange::Datatype(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (DataRange::Intersection(a), DataRange::Intersection(b))
        | (DataRange::Union(a), DataRange::Union(b)) => same_range_set(a, b),
        (DataRange::Complement(a), DataRange::Complement(b)) => same_range(a, b),
        (DataRange::OneOf(a), DataRange::OneOf(b)) => same_literal_set(a, b),
        (DataRange::Restriction(a, xs), DataRange::Restriction(b, ys)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling) && same_facet_set(xs, ys)
        }
        _ => false,
    }
}

/// Two datatype definitions are structural axiom-set copies exactly when their
/// defined datatype, recursive data range and nested annotation sets agree.
/// Returns false for every other axiom type, even when compared with itself.
pub fn same_definition(left: &AnnotatedAxiom, right: &AnnotatedAxiom) -> bool {
    match (&left.axiom, &right.axiom) {
        (Axiom::DatatypeDefinition(a, x), Axiom::DatatypeDefinition(b, y)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
                && same_range(x, y)
                && same_annotation_set(&left.annotations, &right.annotations)
        }
        _ => false,
    }
}
