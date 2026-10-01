//! OWL 2 structural specification §11.2 anonymous-individual positions.
//!
//! This traverses the supplied axiom closure, including nested class
//! expressions. It does not establish the separate anonymous graph forest,
//! edge uniqueness or named-boundary conditions.

use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationValue, Axiom, ClassExpression, Individual,
};

fn annotations_from(values: &Vec<Annotation>, index: usize) -> bool {
    if index < values.len() {
        if annotation_has_no_anonymous(&values[index]) {
            annotations_from(values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Anonymous occurrences in annotations include recursively nested annotations.
pub fn annotation_has_no_anonymous(annotation: &Annotation) -> bool {
    match &annotation.value {
        AnnotationValue::Anonymous(_) => false,
        AnnotationValue::Iri(_) | AnnotationValue::Literal(_) => {
            annotations_from(&annotation.annotations, 0)
        }
    }
}

fn named(individual: &Individual) -> bool {
    match individual {
        Individual::Named(_) => true,
        Individual::Anonymous(_) => false,
    }
}
fn individuals_from(values: &Vec<Individual>, index: usize) -> bool {
    if index < values.len() {
        if named(&values[index]) {
            individuals_from(values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn classes_from(values: &Vec<ClassExpression>, index: usize) -> bool {
    if index < values.len() {
        if class_positions_allowed(&values[index]) {
            classes_from(values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Check every nested `ObjectOneOf` and `ObjectHasValue` position.
pub fn class_positions_allowed(expression: &ClassExpression) -> bool {
    match expression {
        ClassExpression::Class(_) => true,
        ClassExpression::ObjectIntersectionOf(values) | ClassExpression::ObjectUnionOf(values) => {
            class_positions_allowed(&values.first)
                && class_positions_allowed(&values.second)
                && classes_from(&values.rest, 0)
        }
        ClassExpression::ObjectComplementOf(inner)
        | ClassExpression::ObjectSomeValuesFrom(_, inner)
        | ClassExpression::ObjectAllValuesFrom(_, inner) => class_positions_allowed(inner),
        ClassExpression::ObjectOneOf(values) => {
            named(&values.first) && individuals_from(&values.rest, 0)
        }
        ClassExpression::ObjectHasValue(_, individual) => named(individual),
        ClassExpression::ObjectHasSelf(_) => true,
        ClassExpression::ObjectMinCardinality(_, _, filler)
        | ClassExpression::ObjectMaxCardinality(_, _, filler)
        | ClassExpression::ObjectExactCardinality(_, _, filler) => match filler {
            None => true,
            Some(inner) => class_positions_allowed(inner),
        },
        ClassExpression::DataSomeValuesFrom(_, _)
        | ClassExpression::DataAllValuesFrom(_, _)
        | ClassExpression::DataHasValue(_, _)
        | ClassExpression::DataMinCardinality(_, _, _)
        | ClassExpression::DataMaxCardinality(_, _, _)
        | ClassExpression::DataExactCardinality(_, _, _) => true,
    }
}

/// Check positional constraints in the logical axiom body. This operation
/// does not inspect enclosing axiom annotations. Positive assertions may use
/// anonymous individuals subject to the separate anonymous graph restrictions.
pub fn axiom_positions_allowed(axiom: &Axiom) -> bool {
    match axiom {
        Axiom::SubClassOf(a, b) => class_positions_allowed(a) && class_positions_allowed(b),
        Axiom::EquivalentClasses(values)
        | Axiom::DisjointClasses(values)
        | Axiom::DisjointUnion(_, values) => {
            class_positions_allowed(&values.first)
                && class_positions_allowed(&values.second)
                && classes_from(&values.rest, 0)
        }
        Axiom::ObjectPropertyDomain(_, expression)
        | Axiom::ObjectPropertyRange(_, expression)
        | Axiom::DataPropertyDomain(_, expression)
        | Axiom::HasKey(expression, _, _)
        | Axiom::ClassAssertion(expression, _) => class_positions_allowed(expression),
        Axiom::SameIndividual(values) | Axiom::DifferentIndividuals(values) => {
            named(&values.first) && named(&values.second) && individuals_from(&values.rest, 0)
        }
        Axiom::NegativeObjectPropertyAssertion(_, a, b) => named(a) && named(b),
        Axiom::NegativeDataPropertyAssertion(_, individual, _) => named(individual),
        Axiom::Declaration(_)
        | Axiom::SubObjectPropertyOf(_, _)
        | Axiom::EquivalentObjectProperties(_)
        | Axiom::DisjointObjectProperties(_)
        | Axiom::InverseObjectProperties(_, _)
        | Axiom::FunctionalObjectProperty(_)
        | Axiom::InverseFunctionalObjectProperty(_)
        | Axiom::ReflexiveObjectProperty(_)
        | Axiom::IrreflexiveObjectProperty(_)
        | Axiom::SymmetricObjectProperty(_)
        | Axiom::AsymmetricObjectProperty(_)
        | Axiom::TransitiveObjectProperty(_)
        | Axiom::SubDataPropertyOf(_, _)
        | Axiom::EquivalentDataProperties(_)
        | Axiom::DisjointDataProperties(_)
        | Axiom::DataPropertyRange(_, _)
        | Axiom::FunctionalDataProperty(_)
        | Axiom::DatatypeDefinition(_, _)
        | Axiom::ObjectPropertyAssertion(_, _, _)
        | Axiom::DataPropertyAssertion(_, _, _)
        | Axiom::AnnotationAssertion(_, _, _)
        | Axiom::SubAnnotationPropertyOf(_, _)
        | Axiom::AnnotationPropertyDomain(_, _)
        | Axiom::AnnotationPropertyRange(_, _) => true,
    }
}

/// Section 11.2 forbids an anonymous occurrence anywhere in these four axiom
/// types. Their enclosing annotations are therefore checked as well as their
/// logical arguments. Other axiom types may have anonymous annotation values.
pub fn annotated_axiom_positions_allowed(item: &AnnotatedAxiom) -> bool {
    if axiom_positions_allowed(&item.axiom) {
        match &item.axiom {
            Axiom::SameIndividual(_)
            | Axiom::DifferentIndividuals(_)
            | Axiom::NegativeObjectPropertyAssertion(_, _, _)
            | Axiom::NegativeDataPropertyAssertion(_, _, _) => {
                annotations_from(&item.annotations, 0)
            }
            _ => true,
        }
    } else {
        false
    }
}

fn axioms_from(values: &Vec<AnnotatedAxiom>, index: usize) -> Option<&AnnotatedAxiom> {
    if index < values.len() {
        let item = &values[index];
        if annotated_axiom_positions_allowed(item) {
            axioms_from(values, index + 1)
        } else {
            Some(item)
        }
    } else {
        None
    }
}

/// Return the first axiom with a forbidden anonymous position, or `None` iff
/// every axiom in the supplied complete closure satisfies these positions.
#[allow(clippy::ptr_arg)]
pub fn check_positions(axioms: &Vec<AnnotatedAxiom>) -> Option<&AnnotatedAxiom> {
    axioms_from(axioms, 0)
}
