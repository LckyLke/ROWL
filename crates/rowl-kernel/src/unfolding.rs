//! Datatype definitions (OWL 2 Structural Specification §9.4) unfolded for the
//! data queries. A defined datatype stands for the data range of its
//! definition, so each use of one in a data range of an axiom or of a question
//! becomes that data range, unfolded in turn, and the definitions go: what
//! remains names only datatypes without a definition, and it has a model
//! exactly when the closure has one, under every datatype map that supports
//! none of the defined datatypes (`Rowl.Unfolding`).
//!
//! `None` means that a datatype has two definitions, that a predefined
//! datatype or `rdfs:Literal` is defined, that a defined datatype is
//! restricted by facets, that the definitions are cyclic, or that a structure
//! would exceed the `usize` range.
#![allow(
    clippy::ptr_arg,
    clippy::manual_map,
    clippy::match_like_matches_macro,
    clippy::redundant_pattern_matching,
    clippy::question_mark
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::components::{
    copy_class_name, copy_data_list, copy_data_members, copy_data_property, copy_datatype,
    copy_facet, copy_facets, copy_individual_members, copy_individuals, copy_literal,
    copy_literals, copy_natural, copy_range, copy_role_members, copy_roles, copy_sub_role,
};
use crate::concepts::{copy_individual, copy_role};
use crate::datatype_definitions::predefined;
use crate::model::{
    AnnotatedAxiom, AnnotationProperty, AtLeastTwo, Axiom, ClassExpression, DataRange, Datatype,
    Entity, NamedIndividual, NonEmpty, ObjectProperty,
};
use crate::nnf::copy_iri;
use crate::symbols::same_spelling;

/// Whether `items[index..]` has a datatype definition.
pub fn has_definitions(items: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::DatatypeDefinition(_, _) => true,
            _ => has_definitions(items, index + 1),
        }
    } else {
        false
    }
}
/// The data range of the first definition of `datatype` in
/// `definitions[index..]`.
fn definition_from<'a>(
    definitions: &'a Vec<AnnotatedAxiom>,
    datatype: &Datatype,
    index: usize,
) -> Option<&'a DataRange> {
    if index < definitions.len() {
        match &definitions[index].axiom {
            Axiom::DatatypeDefinition(defined, range) => {
                if same_spelling(&defined.iri.spelling, &datatype.iri.spelling) {
                    Some(range)
                } else {
                    definition_from(definitions, datatype, index + 1)
                }
            }
            _ => definition_from(definitions, datatype, index + 1),
        }
    } else {
        None
    }
}
/// Whether every definition in `definitions[index..]` defines a datatype
/// that is not predefined and that no later definition defines again.
fn definitions_proper(definitions: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < definitions.len() {
        match &definitions[index].axiom {
            Axiom::DatatypeDefinition(defined, _) => {
                if predefined(&defined.iri) {
                    false
                } else {
                    match definition_from(definitions, defined, index + 1) {
                        Some(_) => false,
                        None => definitions_proper(definitions, index + 1),
                    }
                }
            }
            _ => definitions_proper(definitions, index + 1),
        }
    } else {
        true
    }
}

// ---------------------------------------------------------------------------
// Data ranges
// ---------------------------------------------------------------------------

/// The data range with each defined datatype replaced by its definition,
/// unfolded with at most `fuel` definitions on the way.
fn unfold_range(
    definitions: &Vec<AnnotatedAxiom>,
    range: &DataRange,
    fuel: usize,
) -> Option<DataRange> {
    match range {
        DataRange::Datatype(datatype) => match definition_from(definitions, datatype, 0) {
            Some(definition) => {
                if 0 < fuel {
                    unfold_range(definitions, definition, fuel - 1)
                } else {
                    None
                }
            }
            None => Some(DataRange::Datatype(copy_datatype(datatype))),
        },
        DataRange::Intersection(members) => {
            match unfold_range_members(definitions, members, fuel) {
                Some(members) => Some(DataRange::Intersection(Box::new(members))),
                None => None,
            }
        }
        DataRange::Union(members) => match unfold_range_members(definitions, members, fuel) {
            Some(members) => Some(DataRange::Union(Box::new(members))),
            None => None,
        },
        DataRange::Complement(inner) => match unfold_range(definitions, inner, fuel) {
            Some(inner) => Some(DataRange::Complement(Box::new(inner))),
            None => None,
        },
        DataRange::OneOf(literals) => Some(DataRange::OneOf(NonEmpty {
            first: copy_literal(&literals.first),
            rest: copy_literals(&literals.rest, 0, Vec::new()),
        })),
        DataRange::Restriction(datatype, facets) => match definition_from(definitions, datatype, 0)
        {
            Some(_) => None,
            None => Some(DataRange::Restriction(
                copy_datatype(datatype),
                NonEmpty {
                    first: copy_facet(&facets.first),
                    rest: copy_facets(&facets.rest, 0, Vec::new()),
                },
            )),
        },
    }
}
/// `out` with the data ranges of `ranges[index..]` unfolded.
fn unfold_range_list(
    definitions: &Vec<AnnotatedAxiom>,
    ranges: &Vec<DataRange>,
    fuel: usize,
    index: usize,
    mut out: Vec<DataRange>,
) -> Option<Vec<DataRange>> {
    if index < ranges.len() {
        if out.len() < usize::MAX {
            match unfold_range(definitions, &ranges[index], fuel) {
                Some(range) => {
                    out.push(range);
                    unfold_range_list(definitions, ranges, fuel, index + 1, out)
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        Some(out)
    }
}
fn unfold_range_members(
    definitions: &Vec<AnnotatedAxiom>,
    members: &AtLeastTwo<DataRange>,
    fuel: usize,
) -> Option<AtLeastTwo<DataRange>> {
    match (
        unfold_range(definitions, &members.first, fuel),
        unfold_range(definitions, &members.second, fuel),
        unfold_range_list(definitions, &members.rest, fuel, 0, Vec::new()),
    ) {
        (Some(first), Some(second), Some(rest)) => Some(AtLeastTwo {
            first,
            second,
            rest,
        }),
        _ => None,
    }
}
fn unfold_range_filler(
    definitions: &Vec<AnnotatedAxiom>,
    filler: &Option<DataRange>,
    fuel: usize,
) -> Option<Option<DataRange>> {
    match filler {
        Some(range) => match unfold_range(definitions, range, fuel) {
            Some(range) => Some(Some(range)),
            None => None,
        },
        None => Some(None),
    }
}

// ---------------------------------------------------------------------------
// Class expressions
// ---------------------------------------------------------------------------

/// The class expression with the data ranges of its data restrictions
/// unfolded.
fn unfold_class(
    definitions: &Vec<AnnotatedAxiom>,
    expression: &ClassExpression,
    fuel: usize,
) -> Option<ClassExpression> {
    match expression {
        ClassExpression::Class(name) => Some(ClassExpression::Class(copy_class_name(name))),
        ClassExpression::ObjectIntersectionOf(members) => {
            match unfold_class_members(definitions, members, fuel) {
                Some(members) => Some(ClassExpression::ObjectIntersectionOf(Box::new(members))),
                None => None,
            }
        }
        ClassExpression::ObjectUnionOf(members) => {
            match unfold_class_members(definitions, members, fuel) {
                Some(members) => Some(ClassExpression::ObjectUnionOf(Box::new(members))),
                None => None,
            }
        }
        ClassExpression::ObjectComplementOf(inner) => {
            match unfold_class(definitions, inner, fuel) {
                Some(inner) => Some(ClassExpression::ObjectComplementOf(Box::new(inner))),
                None => None,
            }
        }
        ClassExpression::ObjectOneOf(individuals) => Some(ClassExpression::ObjectOneOf(NonEmpty {
            first: copy_individual(&individuals.first),
            rest: copy_individuals(&individuals.rest, 0, Vec::new()),
        })),
        ClassExpression::ObjectSomeValuesFrom(role, filler) => {
            match unfold_class(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::ObjectSomeValuesFrom(
                    copy_role(role),
                    Box::new(filler),
                )),
                None => None,
            }
        }
        ClassExpression::ObjectAllValuesFrom(role, filler) => {
            match unfold_class(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::ObjectAllValuesFrom(
                    copy_role(role),
                    Box::new(filler),
                )),
                None => None,
            }
        }
        ClassExpression::ObjectHasValue(role, individual) => Some(ClassExpression::ObjectHasValue(
            copy_role(role),
            copy_individual(individual),
        )),
        ClassExpression::ObjectHasSelf(role) => {
            Some(ClassExpression::ObjectHasSelf(copy_role(role)))
        }
        ClassExpression::ObjectMinCardinality(count, role, filler) => {
            match unfold_class_filler(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::ObjectMinCardinality(
                    copy_natural(count),
                    copy_role(role),
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::ObjectMaxCardinality(count, role, filler) => {
            match unfold_class_filler(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::ObjectMaxCardinality(
                    copy_natural(count),
                    copy_role(role),
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::ObjectExactCardinality(count, role, filler) => {
            match unfold_class_filler(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::ObjectExactCardinality(
                    copy_natural(count),
                    copy_role(role),
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::DataSomeValuesFrom(property, range) => {
            match unfold_range(definitions, range, fuel) {
                Some(range) => Some(ClassExpression::DataSomeValuesFrom(
                    copy_data_property(property),
                    range,
                )),
                None => None,
            }
        }
        ClassExpression::DataAllValuesFrom(property, range) => {
            match unfold_range(definitions, range, fuel) {
                Some(range) => Some(ClassExpression::DataAllValuesFrom(
                    copy_data_property(property),
                    range,
                )),
                None => None,
            }
        }
        ClassExpression::DataHasValue(property, literal) => Some(ClassExpression::DataHasValue(
            copy_data_property(property),
            copy_literal(literal),
        )),
        ClassExpression::DataMinCardinality(count, property, filler) => {
            match unfold_range_filler(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::DataMinCardinality(
                    copy_natural(count),
                    copy_data_property(property),
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::DataMaxCardinality(count, property, filler) => {
            match unfold_range_filler(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::DataMaxCardinality(
                    copy_natural(count),
                    copy_data_property(property),
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::DataExactCardinality(count, property, filler) => {
            match unfold_range_filler(definitions, filler, fuel) {
                Some(filler) => Some(ClassExpression::DataExactCardinality(
                    copy_natural(count),
                    copy_data_property(property),
                    filler,
                )),
                None => None,
            }
        }
    }
}
fn unfold_class_filler(
    definitions: &Vec<AnnotatedAxiom>,
    filler: &Option<Box<ClassExpression>>,
    fuel: usize,
) -> Option<Option<Box<ClassExpression>>> {
    match filler {
        Some(expression) => match unfold_class(definitions, expression, fuel) {
            Some(expression) => Some(Some(Box::new(expression))),
            None => None,
        },
        None => Some(None),
    }
}
/// `out` with the class expressions of `classes[index..]` unfolded.
fn unfold_class_list(
    definitions: &Vec<AnnotatedAxiom>,
    classes: &Vec<ClassExpression>,
    fuel: usize,
    index: usize,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < classes.len() {
        if out.len() < usize::MAX {
            match unfold_class(definitions, &classes[index], fuel) {
                Some(expression) => {
                    out.push(expression);
                    unfold_class_list(definitions, classes, fuel, index + 1, out)
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        Some(out)
    }
}
fn unfold_class_members(
    definitions: &Vec<AnnotatedAxiom>,
    members: &AtLeastTwo<ClassExpression>,
    fuel: usize,
) -> Option<AtLeastTwo<ClassExpression>> {
    match (
        unfold_class(definitions, &members.first, fuel),
        unfold_class(definitions, &members.second, fuel),
        unfold_class_list(definitions, &members.rest, fuel, 0, Vec::new()),
    ) {
        (Some(first), Some(second), Some(rest)) => Some(AtLeastTwo {
            first,
            second,
            rest,
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Axioms
// ---------------------------------------------------------------------------

fn copy_entity(entity: &Entity) -> Entity {
    match entity {
        Entity::Class(name) => Entity::Class(copy_class_name(name)),
        Entity::Datatype(datatype) => Entity::Datatype(copy_datatype(datatype)),
        Entity::ObjectProperty(property) => Entity::ObjectProperty(ObjectProperty {
            iri: copy_iri(&property.iri),
        }),
        Entity::DataProperty(property) => Entity::DataProperty(copy_data_property(property)),
        Entity::AnnotationProperty(property) => Entity::AnnotationProperty(AnnotationProperty {
            iri: copy_iri(&property.iri),
        }),
        Entity::NamedIndividual(individual) => Entity::NamedIndividual(NamedIndividual {
            iri: copy_iri(&individual.iri),
        }),
    }
}

fn unfold_pair(
    definitions: &Vec<AnnotatedAxiom>,
    left: &ClassExpression,
    right: &ClassExpression,
    fuel: usize,
) -> Option<(ClassExpression, ClassExpression)> {
    match (
        unfold_class(definitions, left, fuel),
        unfold_class(definitions, right, fuel),
    ) {
        (Some(left), Some(right)) => Some((left, right)),
        _ => None,
    }
}
/// The axiom with its data ranges unfolded: `Some(None)` for a datatype
/// definition or an annotation axiom, which goes.
fn unfold_axiom(
    definitions: &Vec<AnnotatedAxiom>,
    axiom: &Axiom,
    fuel: usize,
) -> Option<Option<Axiom>> {
    match axiom {
        Axiom::Declaration(entity) => Some(Some(Axiom::Declaration(copy_entity(entity)))),
        Axiom::SubClassOf(sub, sup) => match unfold_pair(definitions, sub, sup, fuel) {
            Some((sub, sup)) => Some(Some(Axiom::SubClassOf(sub, sup))),
            None => None,
        },
        Axiom::EquivalentClasses(members) => match unfold_class_members(definitions, members, fuel)
        {
            Some(members) => Some(Some(Axiom::EquivalentClasses(members))),
            None => None,
        },
        Axiom::DisjointClasses(members) => match unfold_class_members(definitions, members, fuel) {
            Some(members) => Some(Some(Axiom::DisjointClasses(members))),
            None => None,
        },
        Axiom::DisjointUnion(name, members) => {
            match unfold_class_members(definitions, members, fuel) {
                Some(members) => Some(Some(Axiom::DisjointUnion(copy_class_name(name), members))),
                None => None,
            }
        }
        Axiom::SubObjectPropertyOf(sub, sup) => Some(Some(Axiom::SubObjectPropertyOf(
            copy_sub_role(sub),
            copy_role(sup),
        ))),
        Axiom::EquivalentObjectProperties(roles) => Some(Some(Axiom::EquivalentObjectProperties(
            copy_role_members(roles),
        ))),
        Axiom::DisjointObjectProperties(roles) => Some(Some(Axiom::DisjointObjectProperties(
            copy_role_members(roles),
        ))),
        Axiom::InverseObjectProperties(first, second) => Some(Some(
            Axiom::InverseObjectProperties(copy_role(first), copy_role(second)),
        )),
        Axiom::ObjectPropertyDomain(role, expression) => {
            match unfold_class(definitions, expression, fuel) {
                Some(expression) => Some(Some(Axiom::ObjectPropertyDomain(
                    copy_role(role),
                    expression,
                ))),
                None => None,
            }
        }
        Axiom::ObjectPropertyRange(role, expression) => {
            match unfold_class(definitions, expression, fuel) {
                Some(expression) => Some(Some(Axiom::ObjectPropertyRange(
                    copy_role(role),
                    expression,
                ))),
                None => None,
            }
        }
        Axiom::FunctionalObjectProperty(role) => {
            Some(Some(Axiom::FunctionalObjectProperty(copy_role(role))))
        }
        Axiom::InverseFunctionalObjectProperty(role) => Some(Some(
            Axiom::InverseFunctionalObjectProperty(copy_role(role)),
        )),
        Axiom::ReflexiveObjectProperty(role) => {
            Some(Some(Axiom::ReflexiveObjectProperty(copy_role(role))))
        }
        Axiom::IrreflexiveObjectProperty(role) => {
            Some(Some(Axiom::IrreflexiveObjectProperty(copy_role(role))))
        }
        Axiom::SymmetricObjectProperty(role) => {
            Some(Some(Axiom::SymmetricObjectProperty(copy_role(role))))
        }
        Axiom::AsymmetricObjectProperty(role) => {
            Some(Some(Axiom::AsymmetricObjectProperty(copy_role(role))))
        }
        Axiom::TransitiveObjectProperty(role) => {
            Some(Some(Axiom::TransitiveObjectProperty(copy_role(role))))
        }
        Axiom::SubDataPropertyOf(sub, sup) => Some(Some(Axiom::SubDataPropertyOf(
            copy_data_property(sub),
            copy_data_property(sup),
        ))),
        Axiom::EquivalentDataProperties(properties) => Some(Some(Axiom::EquivalentDataProperties(
            copy_data_members(properties),
        ))),
        Axiom::DisjointDataProperties(properties) => Some(Some(Axiom::DisjointDataProperties(
            copy_data_members(properties),
        ))),
        Axiom::DataPropertyDomain(property, expression) => {
            match unfold_class(definitions, expression, fuel) {
                Some(expression) => Some(Some(Axiom::DataPropertyDomain(
                    copy_data_property(property),
                    expression,
                ))),
                None => None,
            }
        }
        Axiom::DataPropertyRange(property, range) => match unfold_range(definitions, range, fuel) {
            Some(range) => Some(Some(Axiom::DataPropertyRange(
                copy_data_property(property),
                range,
            ))),
            None => None,
        },
        Axiom::FunctionalDataProperty(property) => Some(Some(Axiom::FunctionalDataProperty(
            copy_data_property(property),
        ))),
        Axiom::DatatypeDefinition(_, range) => match unfold_range(definitions, range, fuel) {
            Some(_) => Some(None),
            None => None,
        },
        Axiom::HasKey(expression, roles, properties) => {
            match unfold_class(definitions, expression, fuel) {
                Some(expression) => Some(Some(Axiom::HasKey(
                    expression,
                    copy_roles(roles, 0, Vec::new()),
                    copy_data_list(properties, 0, Vec::new()),
                ))),
                None => None,
            }
        }
        Axiom::SameIndividual(individuals) => Some(Some(Axiom::SameIndividual(
            copy_individual_members(individuals),
        ))),
        Axiom::DifferentIndividuals(individuals) => Some(Some(Axiom::DifferentIndividuals(
            copy_individual_members(individuals),
        ))),
        Axiom::ClassAssertion(expression, individual) => {
            match unfold_class(definitions, expression, fuel) {
                Some(expression) => Some(Some(Axiom::ClassAssertion(
                    expression,
                    copy_individual(individual),
                ))),
                None => None,
            }
        }
        Axiom::ObjectPropertyAssertion(role, source, target) => {
            Some(Some(Axiom::ObjectPropertyAssertion(
                copy_role(role),
                copy_individual(source),
                copy_individual(target),
            )))
        }
        Axiom::NegativeObjectPropertyAssertion(role, source, target) => {
            Some(Some(Axiom::NegativeObjectPropertyAssertion(
                copy_role(role),
                copy_individual(source),
                copy_individual(target),
            )))
        }
        Axiom::DataPropertyAssertion(property, source, literal) => {
            Some(Some(Axiom::DataPropertyAssertion(
                copy_data_property(property),
                copy_individual(source),
                copy_literal(literal),
            )))
        }
        Axiom::NegativeDataPropertyAssertion(property, source, literal) => {
            Some(Some(Axiom::NegativeDataPropertyAssertion(
                copy_data_property(property),
                copy_individual(source),
                copy_literal(literal),
            )))
        }
        Axiom::AnnotationAssertion(_, _, _)
        | Axiom::SubAnnotationPropertyOf(_, _)
        | Axiom::AnnotationPropertyDomain(_, _)
        | Axiom::AnnotationPropertyRange(_, _) => Some(None),
    }
}
/// `out` with the axioms of `items[index..]` unfolded, without their
/// annotations, and without the datatype definitions, whose data ranges must
/// unfold, and annotation axioms.
fn unfold_from(
    definitions: &Vec<AnnotatedAxiom>,
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    mut out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < items.len() {
        match unfold_axiom(definitions, &items[index].axiom, definitions.len()) {
            Some(Some(axiom)) => {
                if out.len() < usize::MAX {
                    out.push(AnnotatedAxiom {
                        annotations: Vec::new(),
                        axiom,
                    });
                    unfold_from(definitions, items, index + 1, out)
                } else {
                    None
                }
            }
            Some(None) => unfold_from(definitions, items, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The closure with the datatype definitions `definitions` (its own,
/// `definitions(items)`) unfolded, when every defined datatype has one
/// definition, is not predefined and unfolds.
pub fn unfold_items(
    definitions: &Vec<AnnotatedAxiom>,
    items: &Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if definitions_proper(definitions, 0) {
        unfold_from(definitions, items, 0, Vec::new())
    } else {
        None
    }
}
/// A question's class expression with the closure's definitions unfolded.
pub fn unfold_question(
    definitions: &Vec<AnnotatedAxiom>,
    expression: &ClassExpression,
) -> Option<ClassExpression> {
    unfold_class(definitions, expression, definitions.len())
}
/// `out` with copies of the datatype definitions of `items[index..]`, which
/// unfold a question as the closure does.
fn definitions_from(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    mut out: Vec<AnnotatedAxiom>,
) -> Vec<AnnotatedAxiom> {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::DatatypeDefinition(defined, range) => {
                if out.len() < usize::MAX {
                    out.push(AnnotatedAxiom {
                        annotations: Vec::new(),
                        axiom: Axiom::DatatypeDefinition(copy_datatype(defined), copy_range(range)),
                    });
                    definitions_from(items, index + 1, out)
                } else {
                    out
                }
            }
            _ => definitions_from(items, index + 1, out),
        }
    } else {
        out
    }
}
/// The datatype definitions of the closure, copied.
pub fn definitions(items: &Vec<AnnotatedAxiom>) -> Vec<AnnotatedAxiom> {
    definitions_from(items, 0, Vec::new())
}
