//! OWL 2 §9.4 positions of datatypes defined by axioms in a supplied closure.
//! Defined datatype names may occur as ranges, but not as literal datatypes or
//! DatatypeRestriction bases. This is separate from lexical/facet/value validation.
#![allow(clippy::ptr_arg)]
use crate::datatype_definitions::defines;
use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationValue, Axiom, ClassExpression, DataRange,
    FacetRestriction, Iri, Literal, RawOntology,
};

fn defined_from(axioms: &Vec<AnnotatedAxiom>, datatype: &Iri, index: usize) -> bool {
    if index < axioms.len() {
        defines(&axioms[index], datatype) || defined_from(axioms, datatype, index + 1)
    } else {
        false
    }
}
/// Exactly whether an actual defining axiom names this datatype. Metadata,
/// duplicate definitions and unrelated IRI roles do not affect this predicate.
pub fn defined_datatype(axioms: &Vec<AnnotatedAxiom>, datatype: &Iri) -> bool {
    defined_from(axioms, datatype, 0)
}
pub fn literal_allowed(axioms: &Vec<AnnotatedAxiom>, literal: &Literal) -> bool {
    !defined_datatype(axioms, &literal.datatype.iri)
}
fn facet_allowed(axioms: &Vec<AnnotatedAxiom>, facet: &FacetRestriction) -> bool {
    literal_allowed(axioms, &facet.value)
}
fn literals_from(axioms: &Vec<AnnotatedAxiom>, values: &Vec<Literal>, index: usize) -> bool {
    if index < values.len() {
        if literal_allowed(axioms, &values[index]) {
            literals_from(axioms, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn facets_from(axioms: &Vec<AnnotatedAxiom>, values: &Vec<FacetRestriction>, index: usize) -> bool {
    if index < values.len() {
        if facet_allowed(axioms, &values[index]) {
            facets_from(axioms, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn ranges_from(axioms: &Vec<AnnotatedAxiom>, values: &Vec<DataRange>, index: usize) -> bool {
    if index < values.len() {
        if range_allowed(axioms, &values[index]) {
            ranges_from(axioms, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn classes_from(axioms: &Vec<AnnotatedAxiom>, values: &Vec<ClassExpression>, index: usize) -> bool {
    if index < values.len() {
        if class_allowed(axioms, &values[index]) {
            classes_from(axioms, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn annotations_from(axioms: &Vec<AnnotatedAxiom>, values: &Vec<Annotation>, index: usize) -> bool {
    if index < values.len() {
        if annotation_allowed(axioms, &values[index]) {
            annotations_from(axioms, values, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// All six range constructors, including enumeration and facet literals.
pub fn range_allowed(axioms: &Vec<AnnotatedAxiom>, range: &DataRange) -> bool {
    match range {
        DataRange::Datatype(_) => true,
        DataRange::Intersection(xs) | DataRange::Union(xs) => {
            range_allowed(axioms, &xs.first)
                && range_allowed(axioms, &xs.second)
                && ranges_from(axioms, &xs.rest, 0)
        }
        DataRange::Complement(inner) => range_allowed(axioms, inner),
        DataRange::OneOf(xs) => {
            literal_allowed(axioms, &xs.first) && literals_from(axioms, &xs.rest, 0)
        }
        DataRange::Restriction(datatype, xs) => {
            !defined_datatype(axioms, &datatype.iri)
                && facet_allowed(axioms, &xs.first)
                && facets_from(axioms, &xs.rest, 0)
        }
    }
}
/// All eighteen class-expression forms and optional cardinality fillers.
pub fn class_allowed(axioms: &Vec<AnnotatedAxiom>, expression: &ClassExpression) -> bool {
    match expression {
        ClassExpression::Class(_)
        | ClassExpression::ObjectOneOf(_)
        | ClassExpression::ObjectHasValue(_, _)
        | ClassExpression::ObjectHasSelf(_) => true,
        ClassExpression::ObjectIntersectionOf(xs) | ClassExpression::ObjectUnionOf(xs) => {
            class_allowed(axioms, &xs.first)
                && class_allowed(axioms, &xs.second)
                && classes_from(axioms, &xs.rest, 0)
        }
        ClassExpression::ObjectComplementOf(inner)
        | ClassExpression::ObjectSomeValuesFrom(_, inner)
        | ClassExpression::ObjectAllValuesFrom(_, inner) => class_allowed(axioms, inner),
        ClassExpression::ObjectMinCardinality(_, _, filler)
        | ClassExpression::ObjectMaxCardinality(_, _, filler)
        | ClassExpression::ObjectExactCardinality(_, _, filler) => match filler {
            None => true,
            Some(inner) => class_allowed(axioms, inner),
        },
        ClassExpression::DataSomeValuesFrom(_, range)
        | ClassExpression::DataAllValuesFrom(_, range) => range_allowed(axioms, range),
        ClassExpression::DataHasValue(_, literal) => literal_allowed(axioms, literal),
        ClassExpression::DataMinCardinality(_, _, filler)
        | ClassExpression::DataMaxCardinality(_, _, filler)
        | ClassExpression::DataExactCardinality(_, _, filler) => match filler {
            None => true,
            Some(range) => range_allowed(axioms, range),
        },
    }
}
fn value_allowed(axioms: &Vec<AnnotatedAxiom>, value: &AnnotationValue) -> bool {
    match value {
        AnnotationValue::Literal(literal) => literal_allowed(axioms, literal),
        AnnotationValue::Iri(_) | AnnotationValue::Anonymous(_) => true,
    }
}
/// Literal values in the entire recursively nested annotation tree.
pub fn annotation_allowed(axioms: &Vec<AnnotatedAxiom>, annotation: &Annotation) -> bool {
    value_allowed(axioms, &annotation.value) && annotations_from(axioms, &annotation.annotations, 0)
}
pub fn body_allowed(axioms: &Vec<AnnotatedAxiom>, body: &Axiom) -> bool {
    match body {
        Axiom::SubClassOf(a, b) => class_allowed(axioms, a) && class_allowed(axioms, b),
        Axiom::EquivalentClasses(xs) | Axiom::DisjointClasses(xs) | Axiom::DisjointUnion(_, xs) => {
            class_allowed(axioms, &xs.first)
                && class_allowed(axioms, &xs.second)
                && classes_from(axioms, &xs.rest, 0)
        }
        Axiom::ObjectPropertyDomain(_, e)
        | Axiom::ObjectPropertyRange(_, e)
        | Axiom::DataPropertyDomain(_, e)
        | Axiom::HasKey(e, _, _)
        | Axiom::ClassAssertion(e, _) => class_allowed(axioms, e),
        Axiom::DataPropertyRange(_, range) | Axiom::DatatypeDefinition(_, range) => {
            range_allowed(axioms, range)
        }
        Axiom::DataPropertyAssertion(_, _, literal)
        | Axiom::NegativeDataPropertyAssertion(_, _, literal) => literal_allowed(axioms, literal),
        Axiom::AnnotationAssertion(_, _, value) => value_allowed(axioms, value),
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
        | Axiom::FunctionalDataProperty(_)
        | Axiom::SameIndividual(_)
        | Axiom::DifferentIndividuals(_)
        | Axiom::ObjectPropertyAssertion(_, _, _)
        | Axiom::NegativeObjectPropertyAssertion(_, _, _)
        | Axiom::SubAnnotationPropertyOf(_, _)
        | Axiom::AnnotationPropertyDomain(_, _)
        | Axiom::AnnotationPropertyRange(_, _) => true,
    }
}
/// All body positions and enclosing annotations, preserving the original axiom.
pub fn axiom_allowed(axioms: &Vec<AnnotatedAxiom>, item: &AnnotatedAxiom) -> bool {
    body_allowed(axioms, &item.axiom) && annotations_from(axioms, &item.annotations, 0)
}
fn axioms_from(axioms: &Vec<AnnotatedAxiom>, index: usize) -> Option<&AnnotatedAxiom> {
    if index < axioms.len() {
        let item = &axioms[index];
        if axiom_allowed(axioms, item) {
            axioms_from(axioms, index + 1)
        } else {
            Some(item)
        }
    } else {
        None
    }
}
/// The original first forbidden axiom, or None iff the complete supplied closure
/// has no defined datatype in a forbidden literal/restriction-base position.
pub fn check_positions(axioms: &Vec<AnnotatedAxiom>) -> Option<&AnnotatedAxiom> {
    axioms_from(axioms, 0)
}
fn first_annotation<'a>(
    axioms: &Vec<AnnotatedAxiom>,
    annotations: &'a Vec<Annotation>,
    index: usize,
) -> Option<&'a Annotation> {
    if index < annotations.len() {
        let item = &annotations[index];
        if annotation_allowed(axioms, item) {
            first_annotation(axioms, annotations, index + 1)
        } else {
            Some(item)
        }
    } else {
        None
    }
}
pub enum PositionCheck<'a> {
    Allowed,
    OntologyAnnotation(&'a Annotation),
    Axiom(&'a AnnotatedAxiom),
}
/// Supplied ontology annotations precede closure axioms. Definitions come from
/// the supplied complete axiom closure. Imported ontology annotations must be
/// supplied separately and checked against the same complete definition closure;
/// canonical import/annotation assembly remains a frontend obligation.
pub fn check_ontology_positions(ontology: &RawOntology) -> PositionCheck<'_> {
    match first_annotation(&ontology.axioms, &ontology.annotations, 0) {
        Some(annotation) => PositionCheck::OntologyAnnotation(annotation),
        None => match check_positions(&ontology.axioms) {
            Some(item) => PositionCheck::Axiom(item),
            None => PositionCheck::Allowed,
        },
    }
}
