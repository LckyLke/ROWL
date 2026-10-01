//! Structural equality needed for OWL assertion-set restrictions.
//!
//! Annotation associations are sets at every nesting level: order and repeated
//! equivalent members do not matter. Literal equality uses lexical bytes and
//! datatype spelling, never datatype-value equality. The complete
//! axiom comparison composes these operations in `axiom_equality`.
#![allow(clippy::ptr_arg)] // Vec/index operations are covered by pinned extraction.
use crate::anonymous_graph::same_individual;
use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationValue, Axiom, Individual, Literal,
    ObjectPropertyExpression,
};
use crate::symbols::same_spelling;

pub fn same_literal(left: &Literal, right: &Literal) -> bool {
    same_spelling(&left.lexical, &right.lexical)
        && same_spelling(&left.datatype.iri.spelling, &right.datatype.iri.spelling)
}

pub fn same_annotation_value(left: &AnnotationValue, right: &AnnotationValue) -> bool {
    match (left, right) {
        (AnnotationValue::Iri(a), AnnotationValue::Iri(b)) => {
            same_spelling(&a.spelling, &b.spelling)
        }
        (AnnotationValue::Anonymous(a), AnnotationValue::Anonymous(b)) => same_individual(a, b),
        (AnnotationValue::Literal(a), AnnotationValue::Literal(b)) => same_literal(a, b),
        _ => false,
    }
}

pub fn same_individual_value(left: &Individual, right: &Individual) -> bool {
    match (left, right) {
        (Individual::Named(a), Individual::Named(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (Individual::Anonymous(a), Individual::Anonymous(b)) => same_individual(a, b),
        _ => false,
    }
}

pub fn same_property(left: &ObjectPropertyExpression, right: &ObjectPropertyExpression) -> bool {
    match (left, right) {
        (ObjectPropertyExpression::Property(a), ObjectPropertyExpression::Property(b))
        | (ObjectPropertyExpression::Inverse(a), ObjectPropertyExpression::Inverse(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        _ => false,
    }
}

fn contains_from(values: &Vec<Annotation>, sought: &Annotation, index: usize) -> bool {
    if index < values.len() {
        if same_annotation(sought, &values[index]) {
            true
        } else {
            contains_from(values, sought, index + 1)
        }
    } else {
        false
    }
}

fn subset_from(left: &Vec<Annotation>, right: &Vec<Annotation>, index: usize) -> bool {
    if index < left.len() {
        if contains_from(right, &left[index], 0) {
            subset_from(left, right, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Extensional equality of recursively structured annotation sets.
pub fn same_annotation_set(left: &Vec<Annotation>, right: &Vec<Annotation>) -> bool {
    subset_from(left, right, 0) && subset_from(right, left, 0)
}

/// Preserve annotation nesting; flattening nested metadata would be incorrect.
pub fn same_annotation(left: &Annotation, right: &Annotation) -> bool {
    same_spelling(&left.property.iri.spelling, &right.property.iri.spelling)
        && same_annotation_value(&left.value, &right.value)
        && same_annotation_set(&left.annotations, &right.annotations)
}

/// Compare only two positive object assertions, including their annotation sets.
/// Different axiom types return false even if their other fields happen to agree.
pub fn same_object_assertion(left: &AnnotatedAxiom, right: &AnnotatedAxiom) -> bool {
    match (&left.axiom, &right.axiom) {
        (Axiom::ObjectPropertyAssertion(p, a, b), Axiom::ObjectPropertyAssertion(q, c, d)) => {
            same_property(p, q)
                && same_individual_value(a, c)
                && same_individual_value(b, d)
                && same_annotation_set(&left.annotations, &right.annotations)
        }
        _ => false,
    }
}
