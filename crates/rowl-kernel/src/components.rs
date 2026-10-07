//! The part of a closure that an instance question about one named
//! individual needs.
//!
//! An assertion states something about individuals: a class assertion, an
//! object or data property assertion or its negation, or an equality or
//! inequality of individuals. Declarations and annotation axioms mean nothing
//! in a model. Every other axiom is plain when it names no individual, uses
//! neither top property, defines no datatype, gives a key an object property,
//! and uses only the datatypes, literals and range facets that the data
//! queries know (`datatypes`); an assertion is plain when its class expression
//! uses neither top property and its data are of that kind too. In a closure
//! of plain axioms and assertions, a model of some of the assertions and a
//! model of the others combine into a model of all of them whenever the two
//! groups share no individual (`Rowl.Partition.instance_part`).
//!
//! The component of a named individual is the group of assertions that shared
//! individuals connect to it, found in rounds over the assertions until a
//! round adds no individual, and then checked: every assertion that names one
//! of its individuals names only its individuals. The part of the closure for
//! the individual is its plain axioms and its component, copied without their
//! annotations. When the
//! closure has a model, an instance question about the individual with a plain
//! class expression that names no individual has the same answer for the part
//! as for the closure (`Rowl.Components.part_instance_correct`), and the part
//! of an individual among independent records is small. Without any
//! assertion, the part answers satisfiability and subsumption questions with
//! such class expressions as the closure does (`tbox_closure`).
//!
//! `closure_parts` finds all components once, each with its part, for a
//! reasoner that asks many instance questions.
//!
//! `None` means that the closure has an axiom or an assertion that is not
//! plain, that the component takes more than `ROUNDS` rounds or grows beyond
//! `MEMBERS` individuals, or that a structure would exceed the `usize` range.
#![allow(
    clippy::ptr_arg,
    clippy::needless_return,
    clippy::match_like_matches_macro,
    clippy::manual_map,
    clippy::collapsible_else_if,
    clippy::collapsible_match,
    clippy::redundant_pattern_matching,
    clippy::len_zero,
    clippy::if_same_then_else,
    clippy::question_mark,
    clippy::collapsible_if
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::alc_ontology::{intern, position};
use crate::concepts::{copy_individual, copy_role};
use crate::data_ontology::{axiom_individuals, consistent, is_literal, is_top_data, universal};
use crate::datatypes::{facet_of, kind_of, literal_value, numeric};
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, Class, ClassExpression, DataProperty, DataRange, Datatype,
    FacetRestriction, Individual, Literal, NamedIndividual, NonEmpty, ObjectPropertyExpression,
    SubObjectPropertyExpression,
};
use crate::nnf::{copy_bytes, copy_iri};
use crate::probes::Natural;

/// The most rounds that finding a component may take.
pub const ROUNDS: usize = 64;
/// The most individuals a component may have.
pub const MEMBERS: usize = 4096;

// ---------------------------------------------------------------------------
// Plain axioms
// ---------------------------------------------------------------------------

/// Whether the axiom states something about individuals.
fn assertion(axiom: &Axiom) -> bool {
    match axiom {
        Axiom::ClassAssertion(_, _) => true,
        Axiom::ObjectPropertyAssertion(_, _, _) => true,
        Axiom::NegativeObjectPropertyAssertion(_, _, _) => true,
        Axiom::DataPropertyAssertion(_, _, _) => true,
        Axiom::NegativeDataPropertyAssertion(_, _, _) => true,
        Axiom::SameIndividual(_) => true,
        Axiom::DifferentIndividuals(_) => true,
        _ => false,
    }
}
/// Whether the axiom means nothing in a model: a declaration or an annotation
/// axiom.
fn meaningless(axiom: &Axiom) -> bool {
    match axiom {
        Axiom::Declaration(_) => true,
        Axiom::AnnotationAssertion(_, _, _) => true,
        Axiom::SubAnnotationPropertyOf(_, _) => true,
        Axiom::AnnotationPropertyDomain(_, _) => true,
        Axiom::AnnotationPropertyRange(_, _) => true,
        _ => false,
    }
}
/// Whether the role is neither the top object property nor its inverse.
fn plain_role(role: &ObjectPropertyExpression) -> bool {
    !universal(role)
}
fn plain_roles(roles: &Vec<ObjectPropertyExpression>, index: usize) -> bool {
    if index < roles.len() {
        if plain_role(&roles[index]) {
            plain_roles(roles, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn plain_role_members(roles: &AtLeastTwo<ObjectPropertyExpression>) -> bool {
    if plain_role(&roles.first) {
        if plain_role(&roles.second) {
            plain_roles(&roles.rest, 0)
        } else {
            false
        }
    } else {
        false
    }
}
/// Whether the data property is not the top one.
fn plain_data(property: &DataProperty) -> bool {
    !is_top_data(property)
}
fn plain_data_list(properties: &Vec<DataProperty>, index: usize) -> bool {
    if index < properties.len() {
        if plain_data(&properties[index]) {
            plain_data_list(properties, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn plain_data_members(properties: &AtLeastTwo<DataProperty>) -> bool {
    if plain_data(&properties.first) {
        if plain_data(&properties.second) {
            plain_data_list(&properties.rest, 0)
        } else {
            false
        }
    } else {
        false
    }
}
/// Whether the datatype is one that the data queries know, or `rdfs:Literal`.
fn known_datatype(datatype: &Datatype) -> bool {
    match kind_of(datatype) {
        Some(_) => true,
        None => is_literal(datatype),
    }
}
/// Whether the literal is in the lexical space of a datatype that the data
/// queries know.
fn known_literal(literal: &Literal) -> bool {
    match literal_value(literal) {
        Some(_) => true,
        None => false,
    }
}
fn known_literals(literals: &Vec<Literal>, index: usize) -> bool {
    if index < literals.len() {
        if known_literal(&literals[index]) {
            known_literals(literals, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the facet restriction is a range facet with a number.
fn range_facet(facet: &FacetRestriction) -> bool {
    match facet_of(&facet.facet) {
        Some(_) => match literal_value(&facet.value) {
            Some(value) => numeric(&value),
            None => false,
        },
        None => false,
    }
}
fn range_facets(facets: &Vec<FacetRestriction>, index: usize) -> bool {
    if index < facets.len() {
        if range_facet(&facets[index]) {
            range_facets(facets, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the data range uses only the datatypes, literals and range facets
/// that the data queries know.
fn standard_range(range: &DataRange) -> bool {
    match range {
        DataRange::Datatype(datatype) => known_datatype(datatype),
        DataRange::Intersection(members) => standard_members(members),
        DataRange::Union(members) => standard_members(members),
        DataRange::Complement(inner) => standard_range(inner),
        DataRange::OneOf(literals) => {
            if known_literal(&literals.first) {
                known_literals(&literals.rest, 0)
            } else {
                false
            }
        }
        DataRange::Restriction(datatype, facets) => match kind_of(datatype) {
            Some(_) => {
                if range_facet(&facets.first) {
                    range_facets(&facets.rest, 0)
                } else {
                    false
                }
            }
            None => false,
        },
    }
}
fn standard_list(ranges: &Vec<DataRange>, index: usize) -> bool {
    if index < ranges.len() {
        if standard_range(&ranges[index]) {
            standard_list(ranges, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
fn standard_members(members: &AtLeastTwo<DataRange>) -> bool {
    if standard_range(&members.first) {
        if standard_range(&members.second) {
            standard_list(&members.rest, 0)
        } else {
            false
        }
    } else {
        false
    }
}
fn standard_filler(filler: &Option<DataRange>) -> bool {
    match filler {
        Some(range) => standard_range(range),
        None => true,
    }
}
/// Whether the class expression uses neither top property and has only
/// standard data; with `nominals` false, also whether it names no individual.
fn plain_class(expression: &ClassExpression, nominals: bool) -> bool {
    match expression {
        ClassExpression::Class(_) => true,
        ClassExpression::ObjectIntersectionOf(members) => plain_members(members, nominals),
        ClassExpression::ObjectUnionOf(members) => plain_members(members, nominals),
        ClassExpression::ObjectComplementOf(inner) => plain_class(inner, nominals),
        ClassExpression::ObjectOneOf(_) => nominals,
        ClassExpression::ObjectSomeValuesFrom(role, filler) => {
            if plain_role(role) {
                plain_class(filler, nominals)
            } else {
                false
            }
        }
        ClassExpression::ObjectAllValuesFrom(role, filler) => {
            if plain_role(role) {
                plain_class(filler, nominals)
            } else {
                false
            }
        }
        ClassExpression::ObjectHasValue(role, _) => {
            if plain_role(role) {
                nominals
            } else {
                false
            }
        }
        ClassExpression::ObjectHasSelf(role) => plain_role(role),
        ClassExpression::ObjectMinCardinality(_, role, filler) => {
            plain_counted(role, filler, nominals)
        }
        ClassExpression::ObjectMaxCardinality(_, role, filler) => {
            plain_counted(role, filler, nominals)
        }
        ClassExpression::ObjectExactCardinality(_, role, filler) => {
            plain_counted(role, filler, nominals)
        }
        ClassExpression::DataSomeValuesFrom(property, range) => {
            if plain_data(property) {
                standard_range(range)
            } else {
                false
            }
        }
        ClassExpression::DataAllValuesFrom(property, range) => {
            if plain_data(property) {
                standard_range(range)
            } else {
                false
            }
        }
        ClassExpression::DataHasValue(property, literal) => {
            if plain_data(property) {
                known_literal(literal)
            } else {
                false
            }
        }
        ClassExpression::DataMinCardinality(_, property, filler) => {
            if plain_data(property) {
                standard_filler(filler)
            } else {
                false
            }
        }
        ClassExpression::DataMaxCardinality(_, property, filler) => {
            if plain_data(property) {
                standard_filler(filler)
            } else {
                false
            }
        }
        ClassExpression::DataExactCardinality(_, property, filler) => {
            if plain_data(property) {
                standard_filler(filler)
            } else {
                false
            }
        }
    }
}
fn plain_counted(
    role: &ObjectPropertyExpression,
    filler: &Option<Box<ClassExpression>>,
    nominals: bool,
) -> bool {
    if plain_role(role) {
        match filler {
            Some(filler) => plain_class(filler, nominals),
            None => true,
        }
    } else {
        false
    }
}
fn plain_list(classes: &Vec<ClassExpression>, index: usize, nominals: bool) -> bool {
    if index < classes.len() {
        if plain_class(&classes[index], nominals) {
            plain_list(classes, index + 1, nominals)
        } else {
            false
        }
    } else {
        true
    }
}
fn plain_members(members: &AtLeastTwo<ClassExpression>, nominals: bool) -> bool {
    if plain_class(&members.first, nominals) {
        if plain_class(&members.second, nominals) {
            plain_list(&members.rest, 0, nominals)
        } else {
            false
        }
    } else {
        false
    }
}
fn plain_sub_role(sub: &SubObjectPropertyExpression) -> bool {
    match sub {
        SubObjectPropertyExpression::Single(role) => plain_role(role),
        SubObjectPropertyExpression::Chain(roles) => plain_role_members(roles),
    }
}
/// Whether an axiom that is no assertion and means something is plain.
fn plain_axiom(axiom: &Axiom) -> bool {
    match axiom {
        Axiom::SubClassOf(sub, sup) => {
            if plain_class(sub, false) {
                plain_class(sup, false)
            } else {
                false
            }
        }
        Axiom::EquivalentClasses(members) => plain_members(members, false),
        Axiom::DisjointClasses(members) => plain_members(members, false),
        Axiom::DisjointUnion(_, members) => plain_members(members, false),
        Axiom::SubObjectPropertyOf(sub, sup) => {
            if plain_sub_role(sub) {
                plain_role(sup)
            } else {
                false
            }
        }
        Axiom::EquivalentObjectProperties(roles) => plain_role_members(roles),
        Axiom::DisjointObjectProperties(roles) => plain_role_members(roles),
        Axiom::InverseObjectProperties(first, second) => {
            if plain_role(first) {
                plain_role(second)
            } else {
                false
            }
        }
        Axiom::ObjectPropertyDomain(role, expression) => {
            if plain_role(role) {
                plain_class(expression, false)
            } else {
                false
            }
        }
        Axiom::ObjectPropertyRange(role, expression) => {
            if plain_role(role) {
                plain_class(expression, false)
            } else {
                false
            }
        }
        Axiom::FunctionalObjectProperty(role) => plain_role(role),
        Axiom::InverseFunctionalObjectProperty(role) => plain_role(role),
        Axiom::ReflexiveObjectProperty(role) => plain_role(role),
        Axiom::IrreflexiveObjectProperty(role) => plain_role(role),
        Axiom::SymmetricObjectProperty(role) => plain_role(role),
        Axiom::AsymmetricObjectProperty(role) => plain_role(role),
        Axiom::TransitiveObjectProperty(role) => plain_role(role),
        Axiom::SubDataPropertyOf(sub, sup) => {
            if plain_data(sub) {
                plain_data(sup)
            } else {
                false
            }
        }
        Axiom::EquivalentDataProperties(properties) => plain_data_members(properties),
        Axiom::DisjointDataProperties(properties) => plain_data_members(properties),
        Axiom::DataPropertyDomain(property, expression) => {
            if plain_data(property) {
                plain_class(expression, false)
            } else {
                false
            }
        }
        Axiom::DataPropertyRange(property, range) => {
            if plain_data(property) {
                standard_range(range)
            } else {
                false
            }
        }
        Axiom::FunctionalDataProperty(property) => plain_data(property),
        Axiom::HasKey(expression, roles, properties) => {
            if 0 < roles.len() {
                if plain_class(expression, false) {
                    if plain_roles(roles, 0) {
                        plain_data_list(properties, 0)
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}
/// Whether an assertion is plain.
fn plain_assertion(axiom: &Axiom) -> bool {
    match axiom {
        Axiom::ClassAssertion(expression, _) => plain_class(expression, true),
        Axiom::DataPropertyAssertion(_, _, literal) => known_literal(literal),
        Axiom::NegativeDataPropertyAssertion(_, _, literal) => known_literal(literal),
        _ => true,
    }
}
/// Whether every axiom of `items[index..]` is plain, an assertion that is plain
/// or meaningless.
fn plain_items(items: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < items.len() {
        let item = &items[index].axiom;
        let plain = if assertion(item) {
            plain_assertion(item)
        } else if meaningless(item) {
            true
        } else {
            plain_axiom(item)
        };
        if plain {
            plain_items(items, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the class expression of an instance question is plain and names no
/// individual, so that the question can be asked of a part.
pub fn plain_question(expression: &ClassExpression) -> bool {
    plain_class(expression, false)
}

// ---------------------------------------------------------------------------
// The component
// ---------------------------------------------------------------------------

/// Whether some individual of `named[index..]` is a member.
fn any_member(members: &Vec<Individual>, named: &Vec<Individual>, index: usize) -> bool {
    if index < named.len() {
        if position(members, &named[index], 0) != 0 {
            true
        } else {
            any_member(members, named, index + 1)
        }
    } else {
        false
    }
}
/// `members` with every individual of `named[index..]`; `None` when there is
/// no room.
fn add_all(
    members: Vec<Individual>,
    named: &Vec<Individual>,
    index: usize,
) -> Option<Vec<Individual>> {
    if index < named.len() {
        match intern(members, &named[index]) {
            Some(members) => add_all(members, named, index + 1),
            None => None,
        }
    } else {
        Some(members)
    }
}
/// `out` with the individuals of each axiom of `items[index..]`: those it
/// names when it is an assertion, and none otherwise; `None` when there is no
/// room.
fn individual_table(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    mut out: Vec<Vec<Individual>>,
) -> Option<Vec<Vec<Individual>>> {
    if index < items.len() {
        let named = if assertion(&items[index].axiom) {
            match axiom_individuals(Vec::new(), &items[index].axiom) {
                Some(named) => named,
                None => return None,
            }
        } else {
            Vec::new()
        };
        if out.len() < usize::MAX {
            out.push(named);
            individual_table(items, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// Whether the axiom at `index` names a member, by the table.
fn names_member(table: &Vec<Vec<Individual>>, index: usize, members: &Vec<Individual>) -> bool {
    if index < table.len() {
        any_member(members, &table[index], 0)
    } else {
        false
    }
}
/// `members` with the individuals of every axiom of `table[index..]` that
/// names a member; `None` when there is no room.
fn grow(
    table: &Vec<Vec<Individual>>,
    index: usize,
    members: Vec<Individual>,
) -> Option<Vec<Individual>> {
    if index < table.len() {
        if any_member(&members, &table[index], 0) {
            match add_all(members, &table[index], 0) {
                Some(members) => grow(table, index + 1, members),
                None => None,
            }
        } else {
            grow(table, index + 1, members)
        }
    } else {
        Some(members)
    }
}
/// The members, grown in rounds over the table until a round adds no
/// individual, within `rounds` more rounds and `MEMBERS` individuals.
fn component(
    table: &Vec<Vec<Individual>>,
    members: Vec<Individual>,
    rounds: usize,
) -> Option<Vec<Individual>> {
    let before = members.len();
    match grow(table, 0, members) {
        Some(members) => {
            if members.len() == before {
                Some(members)
            } else if rounds == 0 {
                None
            } else if MEMBERS < members.len() {
                None
            } else {
                component(table, members, rounds - 1)
            }
        }
        None => None,
    }
}
/// Whether every individual of `named[index..]` is a member.
fn all_members(members: &Vec<Individual>, named: &Vec<Individual>, index: usize) -> bool {
    if index < named.len() {
        if position(members, &named[index], 0) != 0 {
            all_members(members, named, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether every axiom of `table[index..]` that names a member names only
/// members.
fn closed(table: &Vec<Vec<Individual>>, index: usize, members: &Vec<Individual>) -> bool {
    if index < table.len() {
        if any_member(members, &table[index], 0) {
            if all_members(members, &table[index], 0) {
                closed(table, index + 1, members)
            } else {
                false
            }
        } else {
            closed(table, index + 1, members)
        }
    } else {
        true
    }
}
/// The component of `start`, checked: it holds `start`, and every axiom of
/// the table that names a member names only members.
fn members_of(table: &Vec<Vec<Individual>>, start: &Individual) -> Option<Vec<Individual>> {
    let mut first = Vec::new();
    first.push(copy_individual(start));
    match component(table, first, ROUNDS) {
        Some(members) => {
            if position(&members, start, 0) != 0 {
                if closed(table, 0, &members) {
                    Some(members)
                } else {
                    None
                }
            } else {
                None
            }
        }
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Copies
// ---------------------------------------------------------------------------

fn copy_natural(value: &Natural) -> Natural {
    match value {
        Natural::Zero => Natural::Zero,
        Natural::Succ(inner) => Natural::Succ(Box::new(copy_natural(inner))),
    }
}
fn copy_class_name(expression: &Class) -> Class {
    Class {
        iri: copy_iri(&expression.iri),
    }
}
fn copy_datatype(datatype: &Datatype) -> Datatype {
    Datatype {
        iri: copy_iri(&datatype.iri),
    }
}
fn copy_data_property(property: &DataProperty) -> DataProperty {
    DataProperty {
        iri: copy_iri(&property.iri),
    }
}
fn copy_literal(literal: &Literal) -> Literal {
    Literal {
        lexical: copy_bytes(&literal.lexical),
        datatype: copy_datatype(&literal.datatype),
    }
}
fn copy_facet(facet: &FacetRestriction) -> FacetRestriction {
    FacetRestriction {
        facet: copy_iri(&facet.facet),
        value: copy_literal(&facet.value),
    }
}
fn copy_literals(literals: &Vec<Literal>, index: usize, mut out: Vec<Literal>) -> Vec<Literal> {
    if index < literals.len() {
        if out.len() < usize::MAX {
            out.push(copy_literal(&literals[index]));
            copy_literals(literals, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
fn copy_facets(
    facets: &Vec<FacetRestriction>,
    index: usize,
    mut out: Vec<FacetRestriction>,
) -> Vec<FacetRestriction> {
    if index < facets.len() {
        if out.len() < usize::MAX {
            out.push(copy_facet(&facets[index]));
            copy_facets(facets, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
fn copy_individuals(
    individuals: &Vec<Individual>,
    index: usize,
    mut out: Vec<Individual>,
) -> Vec<Individual> {
    if index < individuals.len() {
        if out.len() < usize::MAX {
            out.push(copy_individual(&individuals[index]));
            copy_individuals(individuals, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
fn copy_roles(
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Vec<ObjectPropertyExpression> {
    if index < roles.len() {
        if out.len() < usize::MAX {
            out.push(copy_role(&roles[index]));
            copy_roles(roles, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
fn copy_data_list(
    properties: &Vec<DataProperty>,
    index: usize,
    mut out: Vec<DataProperty>,
) -> Vec<DataProperty> {
    if index < properties.len() {
        if out.len() < usize::MAX {
            out.push(copy_data_property(&properties[index]));
            copy_data_list(properties, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
fn copy_range(range: &DataRange) -> DataRange {
    match range {
        DataRange::Datatype(datatype) => DataRange::Datatype(copy_datatype(datatype)),
        DataRange::Intersection(members) => {
            DataRange::Intersection(Box::new(copy_range_members(members)))
        }
        DataRange::Union(members) => DataRange::Union(Box::new(copy_range_members(members))),
        DataRange::Complement(inner) => DataRange::Complement(Box::new(copy_range(inner))),
        DataRange::OneOf(literals) => DataRange::OneOf(NonEmpty {
            first: copy_literal(&literals.first),
            rest: copy_literals(&literals.rest, 0, Vec::new()),
        }),
        DataRange::Restriction(datatype, facets) => DataRange::Restriction(
            copy_datatype(datatype),
            NonEmpty {
                first: copy_facet(&facets.first),
                rest: copy_facets(&facets.rest, 0, Vec::new()),
            },
        ),
    }
}
fn copy_range_list(
    ranges: &Vec<DataRange>,
    index: usize,
    mut out: Vec<DataRange>,
) -> Vec<DataRange> {
    if index < ranges.len() {
        if out.len() < usize::MAX {
            out.push(copy_range(&ranges[index]));
            copy_range_list(ranges, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
fn copy_range_members(members: &AtLeastTwo<DataRange>) -> AtLeastTwo<DataRange> {
    AtLeastTwo {
        first: copy_range(&members.first),
        second: copy_range(&members.second),
        rest: copy_range_list(&members.rest, 0, Vec::new()),
    }
}
fn copy_range_filler(filler: &Option<DataRange>) -> Option<DataRange> {
    match filler {
        Some(range) => Some(copy_range(range)),
        None => None,
    }
}
fn copy_class(expression: &ClassExpression) -> ClassExpression {
    match expression {
        ClassExpression::Class(name) => ClassExpression::Class(copy_class_name(name)),
        ClassExpression::ObjectIntersectionOf(members) => {
            ClassExpression::ObjectIntersectionOf(Box::new(copy_class_members(members)))
        }
        ClassExpression::ObjectUnionOf(members) => {
            ClassExpression::ObjectUnionOf(Box::new(copy_class_members(members)))
        }
        ClassExpression::ObjectComplementOf(inner) => {
            ClassExpression::ObjectComplementOf(Box::new(copy_class(inner)))
        }
        ClassExpression::ObjectOneOf(individuals) => ClassExpression::ObjectOneOf(NonEmpty {
            first: copy_individual(&individuals.first),
            rest: copy_individuals(&individuals.rest, 0, Vec::new()),
        }),
        ClassExpression::ObjectSomeValuesFrom(role, filler) => {
            ClassExpression::ObjectSomeValuesFrom(copy_role(role), Box::new(copy_class(filler)))
        }
        ClassExpression::ObjectAllValuesFrom(role, filler) => {
            ClassExpression::ObjectAllValuesFrom(copy_role(role), Box::new(copy_class(filler)))
        }
        ClassExpression::ObjectHasValue(role, individual) => {
            ClassExpression::ObjectHasValue(copy_role(role), copy_individual(individual))
        }
        ClassExpression::ObjectHasSelf(role) => ClassExpression::ObjectHasSelf(copy_role(role)),
        ClassExpression::ObjectMinCardinality(count, role, filler) => {
            ClassExpression::ObjectMinCardinality(
                copy_natural(count),
                copy_role(role),
                copy_class_filler(filler),
            )
        }
        ClassExpression::ObjectMaxCardinality(count, role, filler) => {
            ClassExpression::ObjectMaxCardinality(
                copy_natural(count),
                copy_role(role),
                copy_class_filler(filler),
            )
        }
        ClassExpression::ObjectExactCardinality(count, role, filler) => {
            ClassExpression::ObjectExactCardinality(
                copy_natural(count),
                copy_role(role),
                copy_class_filler(filler),
            )
        }
        ClassExpression::DataSomeValuesFrom(property, range) => {
            ClassExpression::DataSomeValuesFrom(copy_data_property(property), copy_range(range))
        }
        ClassExpression::DataAllValuesFrom(property, range) => {
            ClassExpression::DataAllValuesFrom(copy_data_property(property), copy_range(range))
        }
        ClassExpression::DataHasValue(property, literal) => {
            ClassExpression::DataHasValue(copy_data_property(property), copy_literal(literal))
        }
        ClassExpression::DataMinCardinality(count, property, filler) => {
            ClassExpression::DataMinCardinality(
                copy_natural(count),
                copy_data_property(property),
                copy_range_filler(filler),
            )
        }
        ClassExpression::DataMaxCardinality(count, property, filler) => {
            ClassExpression::DataMaxCardinality(
                copy_natural(count),
                copy_data_property(property),
                copy_range_filler(filler),
            )
        }
        ClassExpression::DataExactCardinality(count, property, filler) => {
            ClassExpression::DataExactCardinality(
                copy_natural(count),
                copy_data_property(property),
                copy_range_filler(filler),
            )
        }
    }
}
fn copy_class_filler(filler: &Option<Box<ClassExpression>>) -> Option<Box<ClassExpression>> {
    match filler {
        Some(expression) => Some(Box::new(copy_class(expression))),
        None => None,
    }
}
fn copy_class_list(
    classes: &Vec<ClassExpression>,
    index: usize,
    mut out: Vec<ClassExpression>,
) -> Vec<ClassExpression> {
    if index < classes.len() {
        if out.len() < usize::MAX {
            out.push(copy_class(&classes[index]));
            copy_class_list(classes, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
fn copy_class_members(members: &AtLeastTwo<ClassExpression>) -> AtLeastTwo<ClassExpression> {
    AtLeastTwo {
        first: copy_class(&members.first),
        second: copy_class(&members.second),
        rest: copy_class_list(&members.rest, 0, Vec::new()),
    }
}
fn copy_role_members(
    roles: &AtLeastTwo<ObjectPropertyExpression>,
) -> AtLeastTwo<ObjectPropertyExpression> {
    AtLeastTwo {
        first: copy_role(&roles.first),
        second: copy_role(&roles.second),
        rest: copy_roles(&roles.rest, 0, Vec::new()),
    }
}
fn copy_data_members(properties: &AtLeastTwo<DataProperty>) -> AtLeastTwo<DataProperty> {
    AtLeastTwo {
        first: copy_data_property(&properties.first),
        second: copy_data_property(&properties.second),
        rest: copy_data_list(&properties.rest, 0, Vec::new()),
    }
}
fn copy_individual_members(individuals: &AtLeastTwo<Individual>) -> AtLeastTwo<Individual> {
    AtLeastTwo {
        first: copy_individual(&individuals.first),
        second: copy_individual(&individuals.second),
        rest: copy_individuals(&individuals.rest, 0, Vec::new()),
    }
}
fn copy_sub_role(sub: &SubObjectPropertyExpression) -> SubObjectPropertyExpression {
    match sub {
        SubObjectPropertyExpression::Single(role) => {
            SubObjectPropertyExpression::Single(copy_role(role))
        }
        SubObjectPropertyExpression::Chain(roles) => {
            SubObjectPropertyExpression::Chain(copy_role_members(roles))
        }
    }
}
/// A copy of a logical axiom; `None` for a declaration, an annotation axiom or
/// a datatype definition, which no part has.
fn copy_axiom(axiom: &Axiom) -> Option<Axiom> {
    match axiom {
        Axiom::SubClassOf(sub, sup) => Some(Axiom::SubClassOf(copy_class(sub), copy_class(sup))),
        Axiom::EquivalentClasses(members) => {
            Some(Axiom::EquivalentClasses(copy_class_members(members)))
        }
        Axiom::DisjointClasses(members) => {
            Some(Axiom::DisjointClasses(copy_class_members(members)))
        }
        Axiom::DisjointUnion(name, members) => Some(Axiom::DisjointUnion(
            copy_class_name(name),
            copy_class_members(members),
        )),
        Axiom::SubObjectPropertyOf(sub, sup) => Some(Axiom::SubObjectPropertyOf(
            copy_sub_role(sub),
            copy_role(sup),
        )),
        Axiom::EquivalentObjectProperties(roles) => {
            Some(Axiom::EquivalentObjectProperties(copy_role_members(roles)))
        }
        Axiom::DisjointObjectProperties(roles) => {
            Some(Axiom::DisjointObjectProperties(copy_role_members(roles)))
        }
        Axiom::InverseObjectProperties(first, second) => Some(Axiom::InverseObjectProperties(
            copy_role(first),
            copy_role(second),
        )),
        Axiom::ObjectPropertyDomain(role, expression) => Some(Axiom::ObjectPropertyDomain(
            copy_role(role),
            copy_class(expression),
        )),
        Axiom::ObjectPropertyRange(role, expression) => Some(Axiom::ObjectPropertyRange(
            copy_role(role),
            copy_class(expression),
        )),
        Axiom::FunctionalObjectProperty(role) => {
            Some(Axiom::FunctionalObjectProperty(copy_role(role)))
        }
        Axiom::InverseFunctionalObjectProperty(role) => {
            Some(Axiom::InverseFunctionalObjectProperty(copy_role(role)))
        }
        Axiom::ReflexiveObjectProperty(role) => {
            Some(Axiom::ReflexiveObjectProperty(copy_role(role)))
        }
        Axiom::IrreflexiveObjectProperty(role) => {
            Some(Axiom::IrreflexiveObjectProperty(copy_role(role)))
        }
        Axiom::SymmetricObjectProperty(role) => {
            Some(Axiom::SymmetricObjectProperty(copy_role(role)))
        }
        Axiom::AsymmetricObjectProperty(role) => {
            Some(Axiom::AsymmetricObjectProperty(copy_role(role)))
        }
        Axiom::TransitiveObjectProperty(role) => {
            Some(Axiom::TransitiveObjectProperty(copy_role(role)))
        }
        Axiom::SubDataPropertyOf(sub, sup) => Some(Axiom::SubDataPropertyOf(
            copy_data_property(sub),
            copy_data_property(sup),
        )),
        Axiom::EquivalentDataProperties(properties) => Some(Axiom::EquivalentDataProperties(
            copy_data_members(properties),
        )),
        Axiom::DisjointDataProperties(properties) => {
            Some(Axiom::DisjointDataProperties(copy_data_members(properties)))
        }
        Axiom::DataPropertyDomain(property, expression) => Some(Axiom::DataPropertyDomain(
            copy_data_property(property),
            copy_class(expression),
        )),
        Axiom::DataPropertyRange(property, range) => Some(Axiom::DataPropertyRange(
            copy_data_property(property),
            copy_range(range),
        )),
        Axiom::FunctionalDataProperty(property) => {
            Some(Axiom::FunctionalDataProperty(copy_data_property(property)))
        }
        Axiom::HasKey(expression, roles, properties) => Some(Axiom::HasKey(
            copy_class(expression),
            copy_roles(roles, 0, Vec::new()),
            copy_data_list(properties, 0, Vec::new()),
        )),
        Axiom::SameIndividual(individuals) => {
            Some(Axiom::SameIndividual(copy_individual_members(individuals)))
        }
        Axiom::DifferentIndividuals(individuals) => Some(Axiom::DifferentIndividuals(
            copy_individual_members(individuals),
        )),
        Axiom::ClassAssertion(expression, individual) => Some(Axiom::ClassAssertion(
            copy_class(expression),
            copy_individual(individual),
        )),
        Axiom::ObjectPropertyAssertion(role, source, target) => {
            Some(Axiom::ObjectPropertyAssertion(
                copy_role(role),
                copy_individual(source),
                copy_individual(target),
            ))
        }
        Axiom::NegativeObjectPropertyAssertion(role, source, target) => {
            Some(Axiom::NegativeObjectPropertyAssertion(
                copy_role(role),
                copy_individual(source),
                copy_individual(target),
            ))
        }
        Axiom::DataPropertyAssertion(property, source, literal) => {
            Some(Axiom::DataPropertyAssertion(
                copy_data_property(property),
                copy_individual(source),
                copy_literal(literal),
            ))
        }
        Axiom::NegativeDataPropertyAssertion(property, source, literal) => {
            Some(Axiom::NegativeDataPropertyAssertion(
                copy_data_property(property),
                copy_individual(source),
                copy_literal(literal),
            ))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The part
// ---------------------------------------------------------------------------

/// Whether a part keeps the axiom at `index`: a meaningful axiom that is no
/// assertion, or an assertion that names a member.
fn kept(
    items: &Vec<AnnotatedAxiom>,
    table: &Vec<Vec<Individual>>,
    index: usize,
    members: &Vec<Individual>,
) -> bool {
    if assertion(&items[index].axiom) {
        names_member(table, index, members)
    } else {
        !meaningless(&items[index].axiom)
    }
}
/// `out` with copies of the axioms of `items[index..]` that a part keeps.
fn select(
    items: &Vec<AnnotatedAxiom>,
    table: &Vec<Vec<Individual>>,
    index: usize,
    members: &Vec<Individual>,
    mut out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < items.len() {
        if kept(items, table, index, members) {
            match copy_axiom(&items[index].axiom) {
                Some(copied) => {
                    if out.len() < usize::MAX {
                        out.push(AnnotatedAxiom {
                            annotations: Vec::new(),
                            axiom: copied,
                        });
                        select(items, table, index + 1, members, out)
                    } else {
                        None
                    }
                }
                None => None,
            }
        } else {
            select(items, table, index + 1, members, out)
        }
    } else {
        Some(out)
    }
}
/// The part of the closure for an instance question about `individual`: the
/// plain axioms and the component of the individual, copied without
/// annotations.
pub fn component_closure(
    items: &Vec<AnnotatedAxiom>,
    individual: &NamedIndividual,
) -> Option<Vec<AnnotatedAxiom>> {
    if plain_items(items, 0) {
        match individual_table(items, 0, Vec::new()) {
            Some(table) => {
                let start = Individual::Named(NamedIndividual {
                    iri: copy_iri(&individual.iri),
                });
                match members_of(&table, &start) {
                    Some(members) => select(items, &table, 0, &members, Vec::new()),
                    None => None,
                }
            }
            None => None,
        }
    } else {
        None
    }
}
/// The axioms of the closure that mean something and are no assertion, copied
/// without annotations, when every axiom is plain, a plain assertion or
/// without meaning. When the closure has a model, a satisfiability or
/// subsumption question with class expressions that `plain_question` accepts
/// has the same answer for them as for the closure.
pub fn tbox_closure(items: &Vec<AnnotatedAxiom>) -> Option<Vec<AnnotatedAxiom>> {
    if plain_items(items, 0) {
        match individual_table(items, 0, Vec::new()) {
            Some(table) => {
                let members = Vec::new();
                select(items, &table, 0, &members, Vec::new())
            }
            None => None,
        }
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Consistency part by part
// ---------------------------------------------------------------------------

/// `out` with `count` more flags that are false.
fn falses(count: usize, mut out: Vec<bool>) -> Vec<bool> {
    if 0 < count {
        if out.len() < usize::MAX {
            out.push(false);
            falses(count - 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
/// The first index of `table[index..]` of an axiom that names an individual
/// and is not done.
fn open_from(table: &Vec<Vec<Individual>>, index: usize, done: &Vec<bool>) -> Option<usize> {
    if index < table.len() {
        if 0 < table[index].len() {
            if index < done.len() {
                if done[index] {
                    open_from(table, index + 1, done)
                } else {
                    Some(index)
                }
            } else {
                Some(index)
            }
        } else {
            open_from(table, index + 1, done)
        }
    } else {
        None
    }
}
/// `done` with every axiom of `table[index..]` that names a member done;
/// `None` when one of them is done already.
fn mark(
    table: &Vec<Vec<Individual>>,
    index: usize,
    members: &Vec<Individual>,
    mut done: Vec<bool>,
) -> Option<Vec<bool>> {
    if index < table.len() {
        if any_member(members, &table[index], 0) {
            if index < done.len() {
                if done[index] {
                    None
                } else {
                    done[index] = true;
                    mark(table, index + 1, members, done)
                }
            } else {
                mark(table, index + 1, members, done)
            }
        } else {
            mark(table, index + 1, members, done)
        }
    } else {
        Some(done)
    }
}
/// Whether a closure of plain axioms, plain assertions and axioms without
/// meaning has a model, given that its axioms other than assertions together
/// with its assertions that are done have one: the part of the component of
/// the first assertion that is not done, then the next, within `rounds`
/// parts.
fn parts_from(
    items: &Vec<AnnotatedAxiom>,
    table: &Vec<Vec<Individual>>,
    done: Vec<bool>,
    rounds: usize,
) -> Option<bool> {
    match open_from(table, 0, &done) {
        Some(open) => match members_of(table, &table[open][0]) {
            Some(members) => match select(items, table, 0, &members, Vec::new()) {
                Some(part) => match consistent(&part) {
                    Some(true) => {
                        if 0 < rounds {
                            match mark(table, 0, &members, done) {
                                Some(done) => parts_from(items, table, done, rounds - 1),
                                None => None,
                            }
                        } else {
                            None
                        }
                    }
                    Some(false) => Some(false),
                    None => None,
                },
                None => None,
            },
            None => None,
        },
        None => Some(true),
    }
}
/// Whether the closure has a model, decided part by part when every axiom is
/// plain, a plain assertion or without meaning: first its axioms other than
/// assertions, then the part of each component of assertions, which holds
/// those axioms too.
pub fn consistent_by_parts(items: &Vec<AnnotatedAxiom>) -> Option<bool> {
    if plain_items(items, 0) {
        match individual_table(items, 0, Vec::new()) {
            Some(table) => {
                let members = Vec::new();
                match select(items, &table, 0, &members, Vec::new()) {
                    Some(tbox) => match consistent(&tbox) {
                        Some(true) => {
                            parts_from(items, &table, falses(items.len(), Vec::new()), items.len())
                        }
                        Some(false) => Some(false),
                        None => None,
                    },
                    None => None,
                }
            }
            None => None,
        }
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// The parts of a closure
// ---------------------------------------------------------------------------

/// A component of assertions: its individuals, and the part of the closure for
/// an instance question about any of them.
pub struct Component {
    pub members: Vec<Individual>,
    pub part: Vec<AnnotatedAxiom>,
}
/// The parts of a closure for instance questions.
pub struct Parts {
    /// The axioms that mean something and are no assertion, copied without
    /// annotations: the part for an individual that no assertion names.
    pub tbox: Vec<AnnotatedAxiom>,
    /// The components of assertions, each with its part.
    pub components: Vec<Component>,
}
/// `out` with the component of the first assertion that is not done and its
/// part, then the next, within `rounds` components.
fn components_from(
    items: &Vec<AnnotatedAxiom>,
    table: &Vec<Vec<Individual>>,
    done: Vec<bool>,
    rounds: usize,
    mut out: Vec<Component>,
) -> Option<Vec<Component>> {
    match open_from(table, 0, &done) {
        Some(open) => {
            if 0 < rounds {
                match members_of(table, &table[open][0]) {
                    Some(members) => match select(items, table, 0, &members, Vec::new()) {
                        Some(part) => match mark(table, 0, &members, done) {
                            Some(done) => {
                                if out.len() < usize::MAX {
                                    out.push(Component { members, part });
                                    components_from(items, table, done, rounds - 1, out)
                                } else {
                                    None
                                }
                            }
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                }
            } else {
                None
            }
        }
        None => Some(out),
    }
}
/// The parts of the closure for instance questions, when every axiom is
/// plain, a plain assertion or without meaning: the axioms other than
/// assertions, and each component of assertions with its part. When the
/// closure has a model, an instance question about a member of a component,
/// with a class expression that `plain_question` accepts, has the same answer
/// for the part of the component as for the closure, and one about an
/// individual that no component holds has the same answer for the axioms other
/// than assertions (`Rowl.Components.parts_instance_correct`).
pub fn closure_parts(items: &Vec<AnnotatedAxiom>) -> Option<Parts> {
    if plain_items(items, 0) {
        match individual_table(items, 0, Vec::new()) {
            Some(table) => {
                let members = Vec::new();
                match select(items, &table, 0, &members, Vec::new()) {
                    Some(tbox) => match components_from(
                        items,
                        &table,
                        falses(items.len(), Vec::new()),
                        items.len(),
                        Vec::new(),
                    ) {
                        Some(components) => Some(Parts { tbox, components }),
                        None => None,
                    },
                    None => None,
                }
            }
            None => None,
        }
    } else {
        None
    }
}
