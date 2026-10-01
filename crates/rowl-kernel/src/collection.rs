//! Explicit entity occurrences in the raw OWL structural model.
//!
//! IRI spellings are borrowed verbatim, with duplicates and traversal order
//! retained. Headers/import IRIs, annotation IRI values, facets and anonymous
//! identifiers are not entity occurrences. Implicit built-ins and IRI interning
//! remain separate stages. This is not a complete OWL DL validity check.
#![allow(clippy::ptr_arg)] // Keep Vec/index operations inside the proved extraction subset.

use crate::model::*;
use crate::typing::EntityKind;

pub enum EntityUses<'a> {
    Empty,
    Entry {
        iri: &'a Iri,
        kind: EntityKind,
        next: Box<EntityUses<'a>>,
    },
}

pub struct CollectedEntities<'a> {
    pub declarations: EntityUses<'a>,
    pub uses: EntityUses<'a>,
}

fn entry<'a>(iri: &'a Iri, kind: EntityKind, next: EntityUses<'a>) -> EntityUses<'a> {
    EntityUses::Entry {
        iri,
        kind,
        next: Box::new(next),
    }
}

fn visit_entity<'a>(entity: &'a Entity, tail: EntityUses<'a>) -> EntityUses<'a> {
    match entity {
        Entity::Class(c) => entry(&c.iri, EntityKind::Class, tail),
        Entity::Datatype(d) => entry(&d.iri, EntityKind::Datatype, tail),
        Entity::ObjectProperty(p) => entry(&p.iri, EntityKind::ObjectProperty, tail),
        Entity::DataProperty(p) => entry(&p.iri, EntityKind::DataProperty, tail),
        Entity::AnnotationProperty(p) => entry(&p.iri, EntityKind::AnnotationProperty, tail),
        Entity::NamedIndividual(i) => entry(&i.iri, EntityKind::NamedIndividual, tail),
    }
}
fn visit_object<'a>(
    property: &'a ObjectPropertyExpression,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    match property {
        ObjectPropertyExpression::Property(p) | ObjectPropertyExpression::Inverse(p) => {
            entry(&p.iri, EntityKind::ObjectProperty, tail)
        }
    }
}
fn visit_data<'a>(property: &'a DataProperty, tail: EntityUses<'a>) -> EntityUses<'a> {
    entry(&property.iri, EntityKind::DataProperty, tail)
}
fn visit_individual<'a>(individual: &'a Individual, tail: EntityUses<'a>) -> EntityUses<'a> {
    match individual {
        Individual::Named(i) => entry(&i.iri, EntityKind::NamedIndividual, tail),
        Individual::Anonymous(_) => tail,
    }
}
fn visit_literal<'a>(literal: &'a Literal, tail: EntityUses<'a>) -> EntityUses<'a> {
    entry(&literal.datatype.iri, EntityKind::Datatype, tail)
}
fn visit_facet<'a>(facet: &'a FacetRestriction, tail: EntityUses<'a>) -> EntityUses<'a> {
    visit_literal(&facet.value, tail)
}
fn visit_value<'a>(value: &'a AnnotationValue, tail: EntityUses<'a>) -> EntityUses<'a> {
    match value {
        AnnotationValue::Literal(literal) => visit_literal(literal, tail),
        AnnotationValue::Iri(_) | AnnotationValue::Anonymous(_) => tail,
    }
}

fn visit_objects<'a>(
    values: &'a Vec<ObjectPropertyExpression>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_objects(values, index + 1, tail);
        visit_object(&values[index], tail)
    } else {
        tail
    }
}

fn visit_datas<'a>(
    values: &'a Vec<DataProperty>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_datas(values, index + 1, tail);
        visit_data(&values[index], tail)
    } else {
        tail
    }
}

fn visit_individuals<'a>(
    values: &'a Vec<Individual>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_individuals(values, index + 1, tail);
        visit_individual(&values[index], tail)
    } else {
        tail
    }
}

fn visit_literals<'a>(
    values: &'a Vec<Literal>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_literals(values, index + 1, tail);
        visit_literal(&values[index], tail)
    } else {
        tail
    }
}

fn visit_facets<'a>(
    values: &'a Vec<FacetRestriction>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_facets(values, index + 1, tail);
        visit_facet(&values[index], tail)
    } else {
        tail
    }
}

fn visit_ranges<'a>(
    values: &'a Vec<DataRange>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_ranges(values, index + 1, tail);
        visit_range(&values[index], tail)
    } else {
        tail
    }
}

fn visit_classes<'a>(
    values: &'a Vec<ClassExpression>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_classes(values, index + 1, tail);
        visit_class(&values[index], tail)
    } else {
        tail
    }
}

fn visit_annotations<'a>(
    values: &'a Vec<Annotation>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_annotations(values, index + 1, tail);
        visit_annotation(&values[index], tail)
    } else {
        tail
    }
}

fn visit_axioms<'a>(
    values: &'a Vec<AnnotatedAxiom>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < values.len() {
        let tail = visit_axioms(values, index + 1, tail);
        visit_annotated(&values[index], tail)
    } else {
        tail
    }
}

fn visit_range<'a>(range: &'a DataRange, tail: EntityUses<'a>) -> EntityUses<'a> {
    match range {
        DataRange::Datatype(d) => entry(&d.iri, EntityKind::Datatype, tail),
        DataRange::Intersection(xs) | DataRange::Union(xs) => {
            let tail = visit_ranges(&xs.rest, 0, tail);
            let tail = visit_range(&xs.second, tail);
            visit_range(&xs.first, tail)
        }
        DataRange::Complement(e) => visit_range(e, tail),
        DataRange::OneOf(xs) => {
            let tail = visit_literals(&xs.rest, 0, tail);
            visit_literal(&xs.first, tail)
        }
        DataRange::Restriction(d, xs) => {
            let tail = visit_facets(&xs.rest, 0, tail);
            let tail = visit_facet(&xs.first, tail);
            entry(&d.iri, EntityKind::Datatype, tail)
        }
    }
}
fn visit_class<'a>(expression: &'a ClassExpression, tail: EntityUses<'a>) -> EntityUses<'a> {
    match expression {
        ClassExpression::Class(c) => entry(&c.iri, EntityKind::Class, tail),
        ClassExpression::ObjectIntersectionOf(xs) | ClassExpression::ObjectUnionOf(xs) => {
            let tail = visit_classes(&xs.rest, 0, tail);
            let tail = visit_class(&xs.second, tail);
            visit_class(&xs.first, tail)
        }
        ClassExpression::ObjectComplementOf(e) => visit_class(e, tail),
        ClassExpression::ObjectOneOf(xs) => {
            let tail = visit_individuals(&xs.rest, 0, tail);
            visit_individual(&xs.first, tail)
        }
        ClassExpression::ObjectSomeValuesFrom(p, e)
        | ClassExpression::ObjectAllValuesFrom(p, e) => {
            let tail = visit_class(e, tail);
            visit_object(p, tail)
        }
        ClassExpression::ObjectHasValue(p, i) => {
            let tail = visit_individual(i, tail);
            visit_object(p, tail)
        }
        ClassExpression::ObjectHasSelf(p) => visit_object(p, tail),
        ClassExpression::ObjectMinCardinality(_, p, e)
        | ClassExpression::ObjectMaxCardinality(_, p, e)
        | ClassExpression::ObjectExactCardinality(_, p, e) => {
            let tail = match e {
                Some(e) => visit_class(e, tail),
                None => tail,
            };
            visit_object(p, tail)
        }
        ClassExpression::DataSomeValuesFrom(p, r) | ClassExpression::DataAllValuesFrom(p, r) => {
            let tail = visit_range(r, tail);
            visit_data(p, tail)
        }
        ClassExpression::DataHasValue(p, l) => {
            let tail = visit_literal(l, tail);
            visit_data(p, tail)
        }
        ClassExpression::DataMinCardinality(_, p, r)
        | ClassExpression::DataMaxCardinality(_, p, r)
        | ClassExpression::DataExactCardinality(_, p, r) => {
            let tail = match r {
                Some(r) => visit_range(r, tail),
                None => tail,
            };
            visit_data(p, tail)
        }
    }
}
fn visit_annotation<'a>(annotation: &'a Annotation, tail: EntityUses<'a>) -> EntityUses<'a> {
    let tail = visit_value(&annotation.value, tail);
    let tail = entry(
        &annotation.property.iri,
        EntityKind::AnnotationProperty,
        tail,
    );
    visit_annotations(&annotation.annotations, 0, tail)
}
fn visit_sub_object<'a>(
    sub: &'a SubObjectPropertyExpression,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    match sub {
        SubObjectPropertyExpression::Single(p) => visit_object(p, tail),
        SubObjectPropertyExpression::Chain(xs) => {
            let tail = visit_objects(&xs.rest, 0, tail);
            let tail = visit_object(&xs.second, tail);
            visit_object(&xs.first, tail)
        }
    }
}
fn visit_axiom<'a>(axiom: &'a Axiom, tail: EntityUses<'a>) -> EntityUses<'a> {
    match axiom {
        Axiom::Declaration(e) => visit_entity(e, tail),
        Axiom::SubClassOf(a, b) => {
            let tail = visit_class(b, tail);
            visit_class(a, tail)
        }
        Axiom::EquivalentClasses(xs) | Axiom::DisjointClasses(xs) => {
            let tail = visit_classes(&xs.rest, 0, tail);
            let tail = visit_class(&xs.second, tail);
            visit_class(&xs.first, tail)
        }
        Axiom::DisjointUnion(c, xs) => {
            let tail = visit_classes(&xs.rest, 0, tail);
            let tail = visit_class(&xs.second, tail);
            let tail = visit_class(&xs.first, tail);
            entry(&c.iri, EntityKind::Class, tail)
        }
        Axiom::SubObjectPropertyOf(a, b) => {
            let tail = visit_object(b, tail);
            visit_sub_object(a, tail)
        }
        Axiom::EquivalentObjectProperties(xs) | Axiom::DisjointObjectProperties(xs) => {
            let tail = visit_objects(&xs.rest, 0, tail);
            let tail = visit_object(&xs.second, tail);
            visit_object(&xs.first, tail)
        }
        Axiom::InverseObjectProperties(a, b) => {
            let tail = visit_object(b, tail);
            visit_object(a, tail)
        }
        Axiom::ObjectPropertyDomain(p, c) | Axiom::ObjectPropertyRange(p, c) => {
            let tail = visit_class(c, tail);
            visit_object(p, tail)
        }
        Axiom::FunctionalObjectProperty(p)
        | Axiom::InverseFunctionalObjectProperty(p)
        | Axiom::ReflexiveObjectProperty(p)
        | Axiom::IrreflexiveObjectProperty(p)
        | Axiom::SymmetricObjectProperty(p)
        | Axiom::AsymmetricObjectProperty(p)
        | Axiom::TransitiveObjectProperty(p) => visit_object(p, tail),
        Axiom::SubDataPropertyOf(a, b) => {
            let tail = visit_data(b, tail);
            visit_data(a, tail)
        }
        Axiom::EquivalentDataProperties(xs) | Axiom::DisjointDataProperties(xs) => {
            let tail = visit_datas(&xs.rest, 0, tail);
            let tail = visit_data(&xs.second, tail);
            visit_data(&xs.first, tail)
        }
        Axiom::DataPropertyDomain(p, c) => {
            let tail = visit_class(c, tail);
            visit_data(p, tail)
        }
        Axiom::DataPropertyRange(p, r) => {
            let tail = visit_range(r, tail);
            visit_data(p, tail)
        }
        Axiom::FunctionalDataProperty(p) => visit_data(p, tail),
        Axiom::DatatypeDefinition(d, r) => {
            let tail = visit_range(r, tail);
            entry(&d.iri, EntityKind::Datatype, tail)
        }
        Axiom::HasKey(c, objects, datas) => {
            let tail = visit_datas(datas, 0, tail);
            let tail = visit_objects(objects, 0, tail);
            visit_class(c, tail)
        }
        Axiom::SameIndividual(xs) | Axiom::DifferentIndividuals(xs) => {
            let tail = visit_individuals(&xs.rest, 0, tail);
            let tail = visit_individual(&xs.second, tail);
            visit_individual(&xs.first, tail)
        }
        Axiom::ClassAssertion(c, i) => {
            let tail = visit_individual(i, tail);
            visit_class(c, tail)
        }
        Axiom::ObjectPropertyAssertion(p, a, b)
        | Axiom::NegativeObjectPropertyAssertion(p, a, b) => {
            let tail = visit_individual(b, tail);
            let tail = visit_individual(a, tail);
            visit_object(p, tail)
        }
        Axiom::DataPropertyAssertion(p, i, l) | Axiom::NegativeDataPropertyAssertion(p, i, l) => {
            let tail = visit_literal(l, tail);
            let tail = visit_individual(i, tail);
            visit_data(p, tail)
        }
        Axiom::AnnotationAssertion(p, _, v) => {
            let tail = visit_value(v, tail);
            entry(&p.iri, EntityKind::AnnotationProperty, tail)
        }
        Axiom::SubAnnotationPropertyOf(a, b) => {
            let tail = entry(&b.iri, EntityKind::AnnotationProperty, tail);
            entry(&a.iri, EntityKind::AnnotationProperty, tail)
        }
        Axiom::AnnotationPropertyDomain(p, _) | Axiom::AnnotationPropertyRange(p, _) => {
            entry(&p.iri, EntityKind::AnnotationProperty, tail)
        }
    }
}
fn visit_annotated<'a>(axiom: &'a AnnotatedAxiom, tail: EntityUses<'a>) -> EntityUses<'a> {
    let tail = visit_axiom(&axiom.axiom, tail);
    visit_annotations(&axiom.annotations, 0, tail)
}
fn visit_declarations<'a>(
    axioms: &'a Vec<AnnotatedAxiom>,
    index: usize,
    tail: EntityUses<'a>,
) -> EntityUses<'a> {
    if index < axioms.len() {
        let tail = visit_declarations(axioms, index + 1, tail);
        match &axioms[index].axiom {
            Axiom::Declaration(e) => visit_entity(e, tail),
            _ => tail,
        }
    } else {
        tail
    }
}

/// Every explicit entity in a class expression, in structural traversal order.
pub fn class_entities(expression: &ClassExpression) -> EntityUses<'_> {
    visit_class(expression, EntityUses::Empty)
}
/// Every explicit datatype in a data range and its literal/facet values.
pub fn range_entities(range: &DataRange) -> EntityUses<'_> {
    visit_range(range, EntityUses::Empty)
}
/// An entity declaration is also an explicit entity occurrence.
pub fn entity_entities(entity: &Entity) -> EntityUses<'_> {
    visit_entity(entity, EntityUses::Empty)
}
/// Nested annotations precede their property's/value's entity occurrences.
pub fn annotation_entities(annotation: &Annotation) -> EntityUses<'_> {
    visit_annotation(annotation, EntityUses::Empty)
}
/// Collect all explicit roles, including recursively nested axiom annotations.
pub fn axiom_entities(axiom: &AnnotatedAxiom) -> EntityUses<'_> {
    visit_annotated(axiom, EntityUses::Empty)
}
/// Collect explicit declarations and all explicit entity occurrences. Ontology
/// annotations precede axiom occurrences; headers/imports are not entity uses.
pub fn ontology_entities(ontology: &RawOntology) -> CollectedEntities<'_> {
    let uses = visit_axioms(&ontology.axioms, 0, EntityUses::Empty);
    let uses = visit_annotations(&ontology.annotations, 0, uses);
    let declarations = visit_declarations(&ontology.axioms, 0, EntityUses::Empty);
    CollectedEntities { declarations, uses }
}

/// Entity occurrences for the supplied axiom list, including axiom annotations.
/// Ontology annotations remain structural metadata outside the axiom closure.
/// Import assembly and anonymous standardization apart are separate stages.
pub fn axiom_closure_entities(ontology: &RawOntology) -> CollectedEntities<'_> {
    let uses = visit_axioms(&ontology.axioms, 0, EntityUses::Empty);
    let declarations = visit_declarations(&ontology.axioms, 0, EntityUses::Empty);
    CollectedEntities { declarations, uses }
}
