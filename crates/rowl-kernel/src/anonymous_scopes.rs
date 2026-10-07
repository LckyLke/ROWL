//! Whether every anonymous individual of an ontology has one scope.
//!
//! An import closure reads every document with a scope of its own, so that the
//! anonymous individuals of different documents stay apart (OWL 2 Structural
//! Specification §5.6.2). These checks visit every individual of every class
//! expression, axiom, axiom annotation and ontology annotation, nested ones
//! included, and accept exactly when each anonymous individual has the scope.
#![allow(clippy::ptr_arg)]

use crate::dl_validity::same_bytes;
use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationSubject, AnnotationValue, AnonymousIndividual, Axiom,
    ClassExpression, Individual, RawOntology,
};

fn scoped_anonymous(scope: &Vec<u8>, individual: &AnonymousIndividual) -> bool {
    same_bytes(&individual.scope, scope)
}

fn scoped_individual(scope: &Vec<u8>, individual: &Individual) -> bool {
    match individual {
        Individual::Named(_) => true,
        Individual::Anonymous(anonymous) => scoped_anonymous(scope, anonymous),
    }
}

fn individuals_from(scope: &Vec<u8>, values: &Vec<Individual>, index: usize) -> bool {
    if index < values.len() {
        if scoped_individual(scope, &values[index]) {
            individuals_from(scope, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

fn classes_from(scope: &Vec<u8>, values: &Vec<ClassExpression>, index: usize) -> bool {
    if index < values.len() {
        if scoped_class(scope, &values[index]) {
            classes_from(scope, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether every individual of an enumeration or value restriction in the
/// class expression, nested ones included, is named or has the scope.
pub fn scoped_class(scope: &Vec<u8>, expression: &ClassExpression) -> bool {
    match expression {
        ClassExpression::Class(_) => true,
        ClassExpression::ObjectIntersectionOf(values) | ClassExpression::ObjectUnionOf(values) => {
            scoped_class(scope, &values.first)
                && scoped_class(scope, &values.second)
                && classes_from(scope, &values.rest, 0)
        }
        ClassExpression::ObjectComplementOf(inner)
        | ClassExpression::ObjectSomeValuesFrom(_, inner)
        | ClassExpression::ObjectAllValuesFrom(_, inner) => scoped_class(scope, inner),
        ClassExpression::ObjectOneOf(values) => {
            scoped_individual(scope, &values.first) && individuals_from(scope, &values.rest, 0)
        }
        ClassExpression::ObjectHasValue(_, individual) => scoped_individual(scope, individual),
        ClassExpression::ObjectHasSelf(_) => true,
        ClassExpression::ObjectMinCardinality(_, _, filler)
        | ClassExpression::ObjectMaxCardinality(_, _, filler)
        | ClassExpression::ObjectExactCardinality(_, _, filler) => match filler {
            None => true,
            Some(inner) => scoped_class(scope, inner),
        },
        ClassExpression::DataSomeValuesFrom(_, _)
        | ClassExpression::DataAllValuesFrom(_, _)
        | ClassExpression::DataHasValue(_, _)
        | ClassExpression::DataMinCardinality(_, _, _)
        | ClassExpression::DataMaxCardinality(_, _, _)
        | ClassExpression::DataExactCardinality(_, _, _) => true,
    }
}

fn scoped_value(scope: &Vec<u8>, value: &AnnotationValue) -> bool {
    match value {
        AnnotationValue::Anonymous(anonymous) => scoped_anonymous(scope, anonymous),
        AnnotationValue::Iri(_) | AnnotationValue::Literal(_) => true,
    }
}

fn scoped_subject(scope: &Vec<u8>, subject: &AnnotationSubject) -> bool {
    match subject {
        AnnotationSubject::Anonymous(anonymous) => scoped_anonymous(scope, anonymous),
        AnnotationSubject::Iri(_) => true,
    }
}

fn annotations_from(scope: &Vec<u8>, values: &Vec<Annotation>, index: usize) -> bool {
    if index < values.len() {
        if scoped_annotation(scope, &values[index]) {
            annotations_from(scope, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether the annotation's value and those of its nested annotations are
/// IRIs, literals or anonymous individuals of the scope.
pub fn scoped_annotation(scope: &Vec<u8>, annotation: &Annotation) -> bool {
    if scoped_value(scope, &annotation.value) {
        annotations_from(scope, &annotation.annotations, 0)
    } else {
        false
    }
}

/// Whether every individual of the axiom is named or has the scope.
pub fn scoped_axiom(scope: &Vec<u8>, axiom: &Axiom) -> bool {
    match axiom {
        Axiom::SubClassOf(sub, sup) => scoped_class(scope, sub) && scoped_class(scope, sup),
        Axiom::EquivalentClasses(values)
        | Axiom::DisjointClasses(values)
        | Axiom::DisjointUnion(_, values) => {
            scoped_class(scope, &values.first)
                && scoped_class(scope, &values.second)
                && classes_from(scope, &values.rest, 0)
        }
        Axiom::ObjectPropertyDomain(_, expression)
        | Axiom::ObjectPropertyRange(_, expression)
        | Axiom::DataPropertyDomain(_, expression)
        | Axiom::HasKey(expression, _, _) => scoped_class(scope, expression),
        Axiom::SameIndividual(values) | Axiom::DifferentIndividuals(values) => {
            scoped_individual(scope, &values.first)
                && scoped_individual(scope, &values.second)
                && individuals_from(scope, &values.rest, 0)
        }
        Axiom::ClassAssertion(expression, individual) => {
            scoped_class(scope, expression) && scoped_individual(scope, individual)
        }
        Axiom::ObjectPropertyAssertion(_, source, target)
        | Axiom::NegativeObjectPropertyAssertion(_, source, target) => {
            scoped_individual(scope, source) && scoped_individual(scope, target)
        }
        Axiom::DataPropertyAssertion(_, source, _)
        | Axiom::NegativeDataPropertyAssertion(_, source, _) => scoped_individual(scope, source),
        Axiom::AnnotationAssertion(_, subject, value) => {
            scoped_subject(scope, subject) && scoped_value(scope, value)
        }
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
        | Axiom::SubAnnotationPropertyOf(_, _)
        | Axiom::AnnotationPropertyDomain(_, _)
        | Axiom::AnnotationPropertyRange(_, _) => true,
    }
}

/// Whether every individual of the axiom and of its annotations is named or
/// has the scope.
pub fn scoped_annotated(scope: &Vec<u8>, item: &AnnotatedAxiom) -> bool {
    if annotations_from(scope, &item.annotations, 0) {
        scoped_axiom(scope, &item.axiom)
    } else {
        false
    }
}

fn axioms_from(scope: &Vec<u8>, values: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < values.len() {
        if scoped_annotated(scope, &values[index]) {
            axioms_from(scope, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Whether every anonymous individual of the ontology's annotations and axioms
/// has the scope.
pub fn scoped_ontology(scope: &Vec<u8>, ontology: &RawOntology) -> bool {
    if annotations_from(scope, &ontology.annotations, 0) {
        axioms_from(scope, &ontology.axioms, 0)
    } else {
        false
    }
}
