//! Full OWL 2 axiom structural comparison, including nested annotations.
//! Unordered associations ignore order and equivalent repetitions. Property
//! chains and distinct association fields retain their order; no semantic
//! simplification, canonical output or ontology validity is established here.
#![allow(clippy::ptr_arg)] // Indexed Vec operations in the pinned extraction subset.
use crate::anonymous_graph::same_individual;
use crate::arity::same_data_property;
use crate::assertion_equality::{
    same_annotation_set, same_annotation_value, same_individual_value, same_literal, same_property,
};
use crate::class_equality::{same_class, same_class_set};
use crate::model::*;
use crate::range_equality::same_range;
use crate::symbols::same_spelling;

pub fn same_entity(left: &Entity, right: &Entity) -> bool {
    match (left, right) {
        (Entity::Class(a), Entity::Class(b)) => same_spelling(&a.iri.spelling, &b.iri.spelling),
        (Entity::Datatype(a), Entity::Datatype(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (Entity::ObjectProperty(a), Entity::ObjectProperty(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (Entity::DataProperty(a), Entity::DataProperty(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (Entity::AnnotationProperty(a), Entity::AnnotationProperty(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (Entity::NamedIndividual(a), Entity::NamedIndividual(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        _ => false,
    }
}
pub fn same_subject(left: &AnnotationSubject, right: &AnnotationSubject) -> bool {
    match (left, right) {
        (AnnotationSubject::Iri(a), AnnotationSubject::Iri(b)) => {
            same_spelling(&a.spelling, &b.spelling)
        }
        (AnnotationSubject::Anonymous(a), AnnotationSubject::Anonymous(b)) => same_individual(a, b),
        _ => false,
    }
}

fn properties_contains_from(
    values: &Vec<ObjectPropertyExpression>,
    sought: &ObjectPropertyExpression,
    index: usize,
) -> bool {
    if index < values.len() {
        same_property(sought, &values[index]) || properties_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn properties_subset_from(
    left: &Vec<ObjectPropertyExpression>,
    right: &Vec<ObjectPropertyExpression>,
    index: usize,
) -> bool {
    if index < left.len() {
        properties_contains_from(right, &left[index], 0)
            && properties_subset_from(left, right, index + 1)
    } else {
        true
    }
}
pub fn same_properties_set(
    left: &Vec<ObjectPropertyExpression>,
    right: &Vec<ObjectPropertyExpression>,
) -> bool {
    properties_subset_from(left, right, 0) && properties_subset_from(right, left, 0)
}
fn properties_member(
    sought: &ObjectPropertyExpression,
    values: &AtLeastTwo<ObjectPropertyExpression>,
) -> bool {
    same_property(sought, &values.first)
        || same_property(sought, &values.second)
        || properties_contains_from(&values.rest, sought, 0)
}
fn properties_association_subset_from(
    left: &Vec<ObjectPropertyExpression>,
    right: &AtLeastTwo<ObjectPropertyExpression>,
    index: usize,
) -> bool {
    if index < left.len() {
        properties_member(&left[index], right)
            && properties_association_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn properties_association_subset(
    left: &AtLeastTwo<ObjectPropertyExpression>,
    right: &AtLeastTwo<ObjectPropertyExpression>,
) -> bool {
    properties_member(&left.first, right)
        && properties_member(&left.second, right)
        && properties_association_subset_from(&left.rest, right, 0)
}
pub fn same_properties_association(
    left: &AtLeastTwo<ObjectPropertyExpression>,
    right: &AtLeastTwo<ObjectPropertyExpression>,
) -> bool {
    properties_association_subset(left, right) && properties_association_subset(right, left)
}

fn data_properties_contains_from(
    values: &Vec<DataProperty>,
    sought: &DataProperty,
    index: usize,
) -> bool {
    if index < values.len() {
        same_data_property(sought, &values[index])
            || data_properties_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn data_properties_subset_from(
    left: &Vec<DataProperty>,
    right: &Vec<DataProperty>,
    index: usize,
) -> bool {
    if index < left.len() {
        data_properties_contains_from(right, &left[index], 0)
            && data_properties_subset_from(left, right, index + 1)
    } else {
        true
    }
}
pub fn same_data_properties_set(left: &Vec<DataProperty>, right: &Vec<DataProperty>) -> bool {
    data_properties_subset_from(left, right, 0) && data_properties_subset_from(right, left, 0)
}
fn data_properties_member(sought: &DataProperty, values: &AtLeastTwo<DataProperty>) -> bool {
    same_data_property(sought, &values.first)
        || same_data_property(sought, &values.second)
        || data_properties_contains_from(&values.rest, sought, 0)
}
fn data_properties_association_subset_from(
    left: &Vec<DataProperty>,
    right: &AtLeastTwo<DataProperty>,
    index: usize,
) -> bool {
    if index < left.len() {
        data_properties_member(&left[index], right)
            && data_properties_association_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn data_properties_association_subset(
    left: &AtLeastTwo<DataProperty>,
    right: &AtLeastTwo<DataProperty>,
) -> bool {
    data_properties_member(&left.first, right)
        && data_properties_member(&left.second, right)
        && data_properties_association_subset_from(&left.rest, right, 0)
}
pub fn same_data_properties_association(
    left: &AtLeastTwo<DataProperty>,
    right: &AtLeastTwo<DataProperty>,
) -> bool {
    data_properties_association_subset(left, right)
        && data_properties_association_subset(right, left)
}

fn individuals_contains_from(values: &Vec<Individual>, sought: &Individual, index: usize) -> bool {
    if index < values.len() {
        same_individual_value(sought, &values[index])
            || individuals_contains_from(values, sought, index + 1)
    } else {
        false
    }
}
fn individuals_member(sought: &Individual, values: &AtLeastTwo<Individual>) -> bool {
    same_individual_value(sought, &values.first)
        || same_individual_value(sought, &values.second)
        || individuals_contains_from(&values.rest, sought, 0)
}
fn individuals_association_subset_from(
    left: &Vec<Individual>,
    right: &AtLeastTwo<Individual>,
    index: usize,
) -> bool {
    if index < left.len() {
        individuals_member(&left[index], right)
            && individuals_association_subset_from(left, right, index + 1)
    } else {
        true
    }
}
fn individuals_association_subset(
    left: &AtLeastTwo<Individual>,
    right: &AtLeastTwo<Individual>,
) -> bool {
    individuals_member(&left.first, right)
        && individuals_member(&left.second, right)
        && individuals_association_subset_from(&left.rest, right, 0)
}
pub fn same_individuals_association(
    left: &AtLeastTwo<Individual>,
    right: &AtLeastTwo<Individual>,
) -> bool {
    individuals_association_subset(left, right) && individuals_association_subset(right, left)
}

fn chain_equal_from(
    left: &Vec<ObjectPropertyExpression>,
    right: &Vec<ObjectPropertyExpression>,
    index: usize,
) -> bool {
    if index < left.len() {
        same_property(&left[index], &right[index]) && chain_equal_from(left, right, index + 1)
    } else {
        true
    }
}
/// Chains are ordered and retain repeated members.
pub fn same_chain(
    left: &AtLeastTwo<ObjectPropertyExpression>,
    right: &AtLeastTwo<ObjectPropertyExpression>,
) -> bool {
    same_property(&left.first, &right.first)
        && same_property(&left.second, &right.second)
        && left.rest.len() == right.rest.len()
        && chain_equal_from(&left.rest, &right.rest, 0)
}
pub fn same_sub_property(
    left: &SubObjectPropertyExpression,
    right: &SubObjectPropertyExpression,
) -> bool {
    match (left, right) {
        (SubObjectPropertyExpression::Single(a), SubObjectPropertyExpression::Single(b)) => {
            same_property(a, b)
        }
        (SubObjectPropertyExpression::Chain(a), SubObjectPropertyExpression::Chain(b)) => {
            same_chain(a, b)
        }
        _ => false,
    }
}
/// Compare logical structure only; use same_axiom to include axiom metadata.
pub fn same_body(left: &Axiom, right: &Axiom) -> bool {
    match (left, right) {
        (Axiom::Declaration(a), Axiom::Declaration(x)) => same_entity(a, x),
        (Axiom::SubClassOf(a, b), Axiom::SubClassOf(x, y)) => same_class(a, x) && same_class(b, y),
        (Axiom::EquivalentClasses(a), Axiom::EquivalentClasses(x)) => same_class_set(a, x),
        (Axiom::DisjointClasses(a), Axiom::DisjointClasses(x)) => same_class_set(a, x),
        (Axiom::DisjointUnion(a, b), Axiom::DisjointUnion(x, y)) => {
            same_spelling(&a.iri.spelling, &x.iri.spelling) && same_class_set(b, y)
        }
        (Axiom::SubObjectPropertyOf(a, b), Axiom::SubObjectPropertyOf(x, y)) => {
            same_sub_property(a, x) && same_property(b, y)
        }
        (Axiom::EquivalentObjectProperties(a), Axiom::EquivalentObjectProperties(x)) => {
            same_properties_association(a, x)
        }
        (Axiom::DisjointObjectProperties(a), Axiom::DisjointObjectProperties(x)) => {
            same_properties_association(a, x)
        }
        (Axiom::InverseObjectProperties(a, b), Axiom::InverseObjectProperties(x, y)) => {
            same_property(a, x) && same_property(b, y)
        }
        (Axiom::ObjectPropertyDomain(a, b), Axiom::ObjectPropertyDomain(x, y)) => {
            same_property(a, x) && same_class(b, y)
        }
        (Axiom::ObjectPropertyRange(a, b), Axiom::ObjectPropertyRange(x, y)) => {
            same_property(a, x) && same_class(b, y)
        }
        (Axiom::FunctionalObjectProperty(a), Axiom::FunctionalObjectProperty(x)) => {
            same_property(a, x)
        }
        (Axiom::InverseFunctionalObjectProperty(a), Axiom::InverseFunctionalObjectProperty(x)) => {
            same_property(a, x)
        }
        (Axiom::ReflexiveObjectProperty(a), Axiom::ReflexiveObjectProperty(x)) => {
            same_property(a, x)
        }
        (Axiom::IrreflexiveObjectProperty(a), Axiom::IrreflexiveObjectProperty(x)) => {
            same_property(a, x)
        }
        (Axiom::SymmetricObjectProperty(a), Axiom::SymmetricObjectProperty(x)) => {
            same_property(a, x)
        }
        (Axiom::AsymmetricObjectProperty(a), Axiom::AsymmetricObjectProperty(x)) => {
            same_property(a, x)
        }
        (Axiom::TransitiveObjectProperty(a), Axiom::TransitiveObjectProperty(x)) => {
            same_property(a, x)
        }
        (Axiom::SubDataPropertyOf(a, b), Axiom::SubDataPropertyOf(x, y)) => {
            same_data_property(a, x) && same_data_property(b, y)
        }
        (Axiom::EquivalentDataProperties(a), Axiom::EquivalentDataProperties(x)) => {
            same_data_properties_association(a, x)
        }
        (Axiom::DisjointDataProperties(a), Axiom::DisjointDataProperties(x)) => {
            same_data_properties_association(a, x)
        }
        (Axiom::DataPropertyDomain(a, b), Axiom::DataPropertyDomain(x, y)) => {
            same_data_property(a, x) && same_class(b, y)
        }
        (Axiom::DataPropertyRange(a, b), Axiom::DataPropertyRange(x, y)) => {
            same_data_property(a, x) && same_range(b, y)
        }
        (Axiom::FunctionalDataProperty(a), Axiom::FunctionalDataProperty(x)) => {
            same_data_property(a, x)
        }
        (Axiom::DatatypeDefinition(a, b), Axiom::DatatypeDefinition(x, y)) => {
            same_spelling(&a.iri.spelling, &x.iri.spelling) && same_range(b, y)
        }
        (Axiom::HasKey(a, b, c), Axiom::HasKey(x, y, z)) => {
            same_class(a, x) && same_properties_set(b, y) && same_data_properties_set(c, z)
        }
        (Axiom::SameIndividual(a), Axiom::SameIndividual(x)) => same_individuals_association(a, x),
        (Axiom::DifferentIndividuals(a), Axiom::DifferentIndividuals(x)) => {
            same_individuals_association(a, x)
        }
        (Axiom::ClassAssertion(a, b), Axiom::ClassAssertion(x, y)) => {
            same_class(a, x) && same_individual_value(b, y)
        }
        (Axiom::ObjectPropertyAssertion(a, b, c), Axiom::ObjectPropertyAssertion(x, y, z)) => {
            same_property(a, x) && same_individual_value(b, y) && same_individual_value(c, z)
        }
        (
            Axiom::NegativeObjectPropertyAssertion(a, b, c),
            Axiom::NegativeObjectPropertyAssertion(x, y, z),
        ) => same_property(a, x) && same_individual_value(b, y) && same_individual_value(c, z),
        (Axiom::DataPropertyAssertion(a, b, c), Axiom::DataPropertyAssertion(x, y, z)) => {
            same_data_property(a, x) && same_individual_value(b, y) && same_literal(c, z)
        }
        (
            Axiom::NegativeDataPropertyAssertion(a, b, c),
            Axiom::NegativeDataPropertyAssertion(x, y, z),
        ) => same_data_property(a, x) && same_individual_value(b, y) && same_literal(c, z),
        (Axiom::AnnotationAssertion(a, b, c), Axiom::AnnotationAssertion(x, y, z)) => {
            same_spelling(&a.iri.spelling, &x.iri.spelling)
                && same_subject(b, y)
                && same_annotation_value(c, z)
        }
        (Axiom::SubAnnotationPropertyOf(a, b), Axiom::SubAnnotationPropertyOf(x, y)) => {
            same_spelling(&a.iri.spelling, &x.iri.spelling)
                && same_spelling(&b.iri.spelling, &y.iri.spelling)
        }
        (Axiom::AnnotationPropertyDomain(a, b), Axiom::AnnotationPropertyDomain(x, y)) => {
            same_spelling(&a.iri.spelling, &x.iri.spelling)
                && same_spelling(&b.spelling, &y.spelling)
        }
        (Axiom::AnnotationPropertyRange(a, b), Axiom::AnnotationPropertyRange(x, y)) => {
            same_spelling(&a.iri.spelling, &x.iri.spelling)
                && same_spelling(&b.spelling, &y.spelling)
        }
        _ => false,
    }
}
/// Axiom identity includes the complete unordered nested annotation association.
pub fn same_axiom(left: &AnnotatedAxiom, right: &AnnotatedAxiom) -> bool {
    same_body(&left.axiom, &right.axiom)
        && same_annotation_set(&left.annotations, &right.annotations)
}
