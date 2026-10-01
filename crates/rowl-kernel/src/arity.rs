//! Structural arity checking on the complete standard OWL 2 raw language.
//! Unordered associations count structural equivalence classes. The documented
//! duplicate-disjointness compatibility rule rejects repetitions before any
//! canonicalization. Ordered property chains retain repetitions. No lexical,
//! datatype-value, declaration, global DL or logical consistency claim is made.
#![allow(clippy::ptr_arg)] // Supported indexed Vec operations.
use crate::assertion_equality::{same_individual_value, same_property};
use crate::class_equality::same_class;
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, ClassExpression, DataProperty, DataRange, Individual,
    ObjectPropertyExpression,
};
use crate::range_equality::same_range;
use crate::symbols::same_spelling;

pub fn same_data_property(left: &DataProperty, right: &DataProperty) -> bool {
    same_spelling(&left.iri.spelling, &right.iri.spelling)
}

fn other_ranges_from(values: &Vec<DataRange>, sought: &DataRange, index: usize) -> bool {
    if index < values.len() {
        !same_range(sought, &values[index]) || other_ranges_from(values, sought, index + 1)
    } else {
        false
    }
}
/// At least two structural equivalence classes; raw repetitions may remain.
pub fn has_two_ranges(values: &AtLeastTwo<DataRange>) -> bool {
    !same_range(&values.first, &values.second) || other_ranges_from(&values.rest, &values.first, 0)
}

fn other_classes_from(
    values: &Vec<ClassExpression>,
    sought: &ClassExpression,
    index: usize,
) -> bool {
    if index < values.len() {
        !same_class(sought, &values[index]) || other_classes_from(values, sought, index + 1)
    } else {
        false
    }
}
/// At least two structural equivalence classes; raw repetitions may remain.
pub fn has_two_classes(values: &AtLeastTwo<ClassExpression>) -> bool {
    !same_class(&values.first, &values.second) || other_classes_from(&values.rest, &values.first, 0)
}

fn different_classes_from(
    values: &Vec<ClassExpression>,
    sought: &ClassExpression,
    index: usize,
) -> bool {
    if index < values.len() {
        !same_class(sought, &values[index]) && different_classes_from(values, sought, index + 1)
    } else {
        true
    }
}
fn unique_classes_from(values: &Vec<ClassExpression>, index: usize) -> bool {
    if index < values.len() {
        different_classes_from(values, &values[index], index + 1)
            && unique_classes_from(values, index + 1)
    } else {
        true
    }
}
/// Pairwise structural distinctness of the original raw occurrences.
pub fn unique_classes(values: &AtLeastTwo<ClassExpression>) -> bool {
    !same_class(&values.first, &values.second)
        && different_classes_from(&values.rest, &values.first, 0)
        && different_classes_from(&values.rest, &values.second, 0)
        && unique_classes_from(&values.rest, 0)
}

fn other_properties_from(
    values: &Vec<ObjectPropertyExpression>,
    sought: &ObjectPropertyExpression,
    index: usize,
) -> bool {
    if index < values.len() {
        !same_property(sought, &values[index]) || other_properties_from(values, sought, index + 1)
    } else {
        false
    }
}
/// At least two structural equivalence classes; raw repetitions may remain.
pub fn has_two_properties(values: &AtLeastTwo<ObjectPropertyExpression>) -> bool {
    !same_property(&values.first, &values.second)
        || other_properties_from(&values.rest, &values.first, 0)
}

fn different_properties_from(
    values: &Vec<ObjectPropertyExpression>,
    sought: &ObjectPropertyExpression,
    index: usize,
) -> bool {
    if index < values.len() {
        !same_property(sought, &values[index])
            && different_properties_from(values, sought, index + 1)
    } else {
        true
    }
}
fn unique_properties_from(values: &Vec<ObjectPropertyExpression>, index: usize) -> bool {
    if index < values.len() {
        different_properties_from(values, &values[index], index + 1)
            && unique_properties_from(values, index + 1)
    } else {
        true
    }
}
/// Pairwise structural distinctness of the original raw occurrences.
pub fn unique_properties(values: &AtLeastTwo<ObjectPropertyExpression>) -> bool {
    !same_property(&values.first, &values.second)
        && different_properties_from(&values.rest, &values.first, 0)
        && different_properties_from(&values.rest, &values.second, 0)
        && unique_properties_from(&values.rest, 0)
}

fn other_data_properties_from(
    values: &Vec<DataProperty>,
    sought: &DataProperty,
    index: usize,
) -> bool {
    if index < values.len() {
        !same_data_property(sought, &values[index])
            || other_data_properties_from(values, sought, index + 1)
    } else {
        false
    }
}
/// At least two structural equivalence classes; raw repetitions may remain.
pub fn has_two_data_properties(values: &AtLeastTwo<DataProperty>) -> bool {
    !same_data_property(&values.first, &values.second)
        || other_data_properties_from(&values.rest, &values.first, 0)
}

fn different_data_properties_from(
    values: &Vec<DataProperty>,
    sought: &DataProperty,
    index: usize,
) -> bool {
    if index < values.len() {
        !same_data_property(sought, &values[index])
            && different_data_properties_from(values, sought, index + 1)
    } else {
        true
    }
}
fn unique_data_properties_from(values: &Vec<DataProperty>, index: usize) -> bool {
    if index < values.len() {
        different_data_properties_from(values, &values[index], index + 1)
            && unique_data_properties_from(values, index + 1)
    } else {
        true
    }
}
/// Pairwise structural distinctness of the original raw occurrences.
pub fn unique_data_properties(values: &AtLeastTwo<DataProperty>) -> bool {
    !same_data_property(&values.first, &values.second)
        && different_data_properties_from(&values.rest, &values.first, 0)
        && different_data_properties_from(&values.rest, &values.second, 0)
        && unique_data_properties_from(&values.rest, 0)
}

fn other_individuals_from(values: &Vec<Individual>, sought: &Individual, index: usize) -> bool {
    if index < values.len() {
        !same_individual_value(sought, &values[index])
            || other_individuals_from(values, sought, index + 1)
    } else {
        false
    }
}
/// At least two structural equivalence classes; raw repetitions may remain.
pub fn has_two_individuals(values: &AtLeastTwo<Individual>) -> bool {
    !same_individual_value(&values.first, &values.second)
        || other_individuals_from(&values.rest, &values.first, 0)
}

fn different_individuals_from(values: &Vec<Individual>, sought: &Individual, index: usize) -> bool {
    if index < values.len() {
        !same_individual_value(sought, &values[index])
            && different_individuals_from(values, sought, index + 1)
    } else {
        true
    }
}
fn unique_individuals_from(values: &Vec<Individual>, index: usize) -> bool {
    if index < values.len() {
        different_individuals_from(values, &values[index], index + 1)
            && unique_individuals_from(values, index + 1)
    } else {
        true
    }
}
/// Pairwise structural distinctness of the original raw occurrences.
pub fn unique_individuals(values: &AtLeastTwo<Individual>) -> bool {
    !same_individual_value(&values.first, &values.second)
        && different_individuals_from(&values.rest, &values.first, 0)
        && different_individuals_from(&values.rest, &values.second, 0)
        && unique_individuals_from(&values.rest, 0)
}

fn ranges_from(values: &Vec<DataRange>, index: usize) -> bool {
    if index < values.len() {
        if range_allowed(&values[index]) {
            ranges_from(values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// All data-range association arities, including recursively nested members.
pub fn range_allowed(value: &DataRange) -> bool {
    match value {
        DataRange::Datatype(_) | DataRange::OneOf(_) | DataRange::Restriction(_, _) => true,
        DataRange::Intersection(xs) | DataRange::Union(xs) => {
            has_two_ranges(xs)
                && range_allowed(&xs.first)
                && range_allowed(&xs.second)
                && ranges_from(&xs.rest, 0)
        }
        DataRange::Complement(x) => range_allowed(x),
    }
}
fn classes_from(values: &Vec<ClassExpression>, index: usize) -> bool {
    if index < values.len() {
        if class_allowed(&values[index]) {
            classes_from(values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// All eighteen class forms, including data ranges and optional fillers.
pub fn class_allowed(value: &ClassExpression) -> bool {
    match value {
        ClassExpression::Class(_)
        | ClassExpression::ObjectOneOf(_)
        | ClassExpression::ObjectHasValue(_, _)
        | ClassExpression::ObjectHasSelf(_)
        | ClassExpression::DataHasValue(_, _) => true,
        ClassExpression::ObjectIntersectionOf(xs) | ClassExpression::ObjectUnionOf(xs) => {
            has_two_classes(xs)
                && class_allowed(&xs.first)
                && class_allowed(&xs.second)
                && classes_from(&xs.rest, 0)
        }
        ClassExpression::ObjectComplementOf(x)
        | ClassExpression::ObjectSomeValuesFrom(_, x)
        | ClassExpression::ObjectAllValuesFrom(_, x) => class_allowed(x),
        ClassExpression::ObjectMinCardinality(_, _, x)
        | ClassExpression::ObjectMaxCardinality(_, _, x)
        | ClassExpression::ObjectExactCardinality(_, _, x) => match x {
            None => true,
            Some(x) => class_allowed(x),
        },
        ClassExpression::DataSomeValuesFrom(_, r) | ClassExpression::DataAllValuesFrom(_, r) => {
            range_allowed(r)
        }
        ClassExpression::DataMinCardinality(_, _, r)
        | ClassExpression::DataMaxCardinality(_, _, r)
        | ClassExpression::DataExactCardinality(_, _, r) => match r {
            None => true,
            Some(r) => range_allowed(r),
        },
    }
}
pub fn axiom_allowed(item: &AnnotatedAxiom) -> bool {
    match &item.axiom {
        Axiom::SubClassOf(a, b) => class_allowed(a) && class_allowed(b),
        Axiom::EquivalentClasses(xs) => {
            has_two_classes(xs)
                && class_allowed(&xs.first)
                && class_allowed(&xs.second)
                && classes_from(&xs.rest, 0)
        }
        Axiom::DisjointClasses(xs) | Axiom::DisjointUnion(_, xs) => {
            unique_classes(xs)
                && class_allowed(&xs.first)
                && class_allowed(&xs.second)
                && classes_from(&xs.rest, 0)
        }
        Axiom::EquivalentObjectProperties(xs) => has_two_properties(xs),
        Axiom::DisjointObjectProperties(xs) => unique_properties(xs),
        Axiom::EquivalentDataProperties(xs) => has_two_data_properties(xs),
        Axiom::DisjointDataProperties(xs) => unique_data_properties(xs),
        Axiom::SameIndividual(xs) => has_two_individuals(xs),
        Axiom::DifferentIndividuals(xs) => unique_individuals(xs),
        Axiom::ObjectPropertyDomain(_, c)
        | Axiom::ObjectPropertyRange(_, c)
        | Axiom::DataPropertyDomain(_, c)
        | Axiom::ClassAssertion(c, _) => class_allowed(c),
        Axiom::DataPropertyRange(_, r) | Axiom::DatatypeDefinition(_, r) => range_allowed(r),
        Axiom::HasKey(c, _, _) => class_allowed(c) && crate::keys::axiom_allowed(item),
        Axiom::Declaration(_)
        | Axiom::SubObjectPropertyOf(_, _)
        | Axiom::InverseObjectProperties(_, _)
        | Axiom::FunctionalObjectProperty(_)
        | Axiom::InverseFunctionalObjectProperty(_)
        | Axiom::ReflexiveObjectProperty(_)
        | Axiom::IrreflexiveObjectProperty(_)
        | Axiom::SymmetricObjectProperty(_)
        | Axiom::AsymmetricObjectProperty(_)
        | Axiom::TransitiveObjectProperty(_)
        | Axiom::SubDataPropertyOf(_, _)
        | Axiom::FunctionalDataProperty(_)
        | Axiom::ObjectPropertyAssertion(_, _, _)
        | Axiom::NegativeObjectPropertyAssertion(_, _, _)
        | Axiom::DataPropertyAssertion(_, _, _)
        | Axiom::NegativeDataPropertyAssertion(_, _, _)
        | Axiom::AnnotationAssertion(_, _, _)
        | Axiom::SubAnnotationPropertyOf(_, _)
        | Axiom::AnnotationPropertyDomain(_, _)
        | Axiom::AnnotationPropertyRange(_, _) => true,
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
/// Exact first original annotated arity/duplicate-disjointness failure, or None
/// iff every supplied axiom obeys this structural rule. Full DL validity is separate.
pub fn check_arities(axioms: &Vec<AnnotatedAxiom>) -> Option<&AnnotatedAxiom> {
    axioms_from(axioms, 0)
}
