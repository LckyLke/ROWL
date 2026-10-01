//! Structural comparison of all eighteen standard OWL 2 class-expression forms.
//! Unordered associations use recursive set membership; cardinality omissions
//! use the normative owl:Thing/rdfs:Literal defaults. Constructors and nesting
//! remain significant. This performs no logical simplification or DL validation.
#![allow(clippy::ptr_arg)] // Indexed operations in the pinned extraction subset.
use crate::assertion_equality::{same_individual_value, same_literal, same_property};
use crate::model::{AtLeastTwo, ClassExpression, DataRange, Individual, NonEmpty};
use crate::probes::Natural;
use crate::range_equality::same_range;
use crate::symbols::same_spelling;

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
/// Compare exact unbounded cardinality values without machine arithmetic.
pub fn same_natural(left: &Natural, right: &Natural) -> bool {
    match (left, right) {
        (Natural::Zero, Natural::Zero) => true,
        (Natural::Succ(a), Natural::Succ(b)) => same_natural(a, b),
        _ => false,
    }
}
/// Only the exact named built-in class qualifies as the omitted object filler.
pub fn is_thing(value: &ClassExpression) -> bool {
    match value {
        ClassExpression::Class(c) => {
            same_pattern(&c.iri.spelling, b"http://www.w3.org/2002/07/owl#Thing")
        }
        _ => false,
    }
}
/// Only the exact named top data range qualifies as the omitted data filler.
pub fn is_literal(value: &DataRange) -> bool {
    match value {
        DataRange::Datatype(d) => same_pattern(
            &d.iri.spelling,
            b"http://www.w3.org/2000/01/rdf-schema#Literal",
        ),
        _ => false,
    }
}
pub fn same_optional_range(left: &Option<DataRange>, right: &Option<DataRange>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(a), Some(b)) => same_range(a, b),
        (None, Some(value)) | (Some(value), None) => is_literal(value),
    }
}
pub fn same_optional_class(
    left: &Option<Box<ClassExpression>>,
    right: &Option<Box<ClassExpression>>,
) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(a), Some(b)) => same_class(a, b),
        (None, Some(value)) | (Some(value), None) => is_thing(value),
    }
}

fn individual_contains_from(values: &Vec<Individual>, sought: &Individual, index: usize) -> bool {
    if index < values.len() {
        same_individual_value(sought, &values[index])
            || individual_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn individual_member(sought: &Individual, values: &NonEmpty<Individual>) -> bool {
    same_individual_value(sought, &values.first)
        || individual_contains_from(&values.rest, sought, 0)
}
fn individual_subset_from(
    left: &Vec<Individual>,
    right: &NonEmpty<Individual>,
    index: usize,
) -> bool {
    if index < left.len() {
        individual_member(&left[index], right) && individual_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn individual_subset(left: &NonEmpty<Individual>, right: &NonEmpty<Individual>) -> bool {
    individual_member(&left.first, right) && individual_subset_from(&left.rest, right, 0)
}
pub fn same_individual_set(left: &NonEmpty<Individual>, right: &NonEmpty<Individual>) -> bool {
    individual_subset(left, right) && individual_subset(right, left)
}
fn class_contains_from(
    values: &Vec<ClassExpression>,
    sought: &ClassExpression,
    index: usize,
) -> bool {
    if index < values.len() {
        same_class(sought, &values[index]) || class_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn class_member(sought: &ClassExpression, values: &AtLeastTwo<ClassExpression>) -> bool {
    same_class(sought, &values.first)
        || same_class(sought, &values.second)
        || class_contains_from(&values.rest, sought, 0)
}
fn class_subset_from(
    left: &Vec<ClassExpression>,
    right: &AtLeastTwo<ClassExpression>,
    index: usize,
) -> bool {
    if index < left.len() {
        class_member(&left[index], right) && class_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn class_subset(left: &AtLeastTwo<ClassExpression>, right: &AtLeastTwo<ClassExpression>) -> bool {
    class_member(&left.first, right)
        && class_member(&left.second, right)
        && class_subset_from(&left.rest, right, 0)
}
pub fn same_class_set(
    left: &AtLeastTwo<ClassExpression>,
    right: &AtLeastTwo<ClassExpression>,
) -> bool {
    class_subset(left, right) && class_subset(right, left)
}
/// Exact recursive structure after expanding omitted cardinality qualifiers.
/// Semantically equivalent but differently constructed expressions stay distinct.
pub fn same_class(left: &ClassExpression, right: &ClassExpression) -> bool {
    match (left, right) {
        (ClassExpression::Class(a), ClassExpression::Class(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (ClassExpression::ObjectIntersectionOf(a), ClassExpression::ObjectIntersectionOf(b))
        | (ClassExpression::ObjectUnionOf(a), ClassExpression::ObjectUnionOf(b)) => {
            same_class_set(a, b)
        }
        (ClassExpression::ObjectComplementOf(a), ClassExpression::ObjectComplementOf(b)) => {
            same_class(a, b)
        }
        (ClassExpression::ObjectOneOf(a), ClassExpression::ObjectOneOf(b)) => {
            same_individual_set(a, b)
        }
        (
            ClassExpression::ObjectSomeValuesFrom(p, a),
            ClassExpression::ObjectSomeValuesFrom(q, b),
        )
        | (
            ClassExpression::ObjectAllValuesFrom(p, a),
            ClassExpression::ObjectAllValuesFrom(q, b),
        ) => same_property(p, q) && same_class(a, b),
        (ClassExpression::ObjectHasValue(p, a), ClassExpression::ObjectHasValue(q, b)) => {
            same_property(p, q) && same_individual_value(a, b)
        }
        (ClassExpression::ObjectHasSelf(p), ClassExpression::ObjectHasSelf(q)) => {
            same_property(p, q)
        }
        (
            ClassExpression::ObjectMinCardinality(n, p, a),
            ClassExpression::ObjectMinCardinality(m, q, b),
        ) => same_natural(n, m) && same_property(p, q) && same_optional_class(a, b),
        (
            ClassExpression::ObjectMaxCardinality(n, p, a),
            ClassExpression::ObjectMaxCardinality(m, q, b),
        ) => same_natural(n, m) && same_property(p, q) && same_optional_class(a, b),
        (
            ClassExpression::ObjectExactCardinality(n, p, a),
            ClassExpression::ObjectExactCardinality(m, q, b),
        ) => same_natural(n, m) && same_property(p, q) && same_optional_class(a, b),
        (ClassExpression::DataSomeValuesFrom(p, a), ClassExpression::DataSomeValuesFrom(q, b))
        | (ClassExpression::DataAllValuesFrom(p, a), ClassExpression::DataAllValuesFrom(q, b)) => {
            same_spelling(&p.iri.spelling, &q.iri.spelling) && same_range(a, b)
        }
        (ClassExpression::DataHasValue(p, a), ClassExpression::DataHasValue(q, b)) => {
            same_spelling(&p.iri.spelling, &q.iri.spelling) && same_literal(a, b)
        }
        (
            ClassExpression::DataMinCardinality(n, p, a),
            ClassExpression::DataMinCardinality(m, q, b),
        ) => {
            same_natural(n, m)
                && same_spelling(&p.iri.spelling, &q.iri.spelling)
                && same_optional_range(a, b)
        }
        (
            ClassExpression::DataMaxCardinality(n, p, a),
            ClassExpression::DataMaxCardinality(m, q, b),
        ) => {
            same_natural(n, m)
                && same_spelling(&p.iri.spelling, &q.iri.spelling)
                && same_optional_range(a, b)
        }
        (
            ClassExpression::DataExactCardinality(n, p, a),
            ClassExpression::DataExactCardinality(m, q, b),
        ) => {
            same_natural(n, m)
                && same_spelling(&p.iri.spelling, &q.iri.spelling)
                && same_optional_range(a, b)
        }
        _ => false,
    }
}
