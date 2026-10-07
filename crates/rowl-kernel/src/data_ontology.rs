//! Data properties, literals, the datatypes of `datatypes` and the range facets
//! in the ontology queries, by an encoding into classes, object properties and
//! named individuals that the SROIQ queries of `shi_ontology` decide.
//!
//! The data values of a model become further elements, the data nodes, which
//! the class `D` marks:
//!
//! - every data property `p` becomes an object property `p'` from elements
//!   that are no data nodes to data nodes (`owl:bottomDataProperty` becomes
//!   `owl:bottomObjectProperty`), and its axioms the same axioms on `p'`;
//! - every distinct literal value becomes a named individual, a data node
//!   whose classes say which of the datatypes in use it is in, with a pattern
//!   of bit classes that tells it apart from every other literal value;
//! - every datatype of a data range becomes a class `A`, with the inclusions of
//!   the datatypes (integers are decimals, decimals rationals, rationals reals,
//!   strings plain literals) and their disjointness, and the booleans are the
//!   individuals of `true` and `false`; `rdfs:Literal` is every data node;
//! - when a datatype restriction or a subtype of `xsd:integer` is in use, the
//!   numbers of the closure become cuts of the real line (`regions`), each with
//!   a class of the numbers at or above it (closed) or above it (open): a
//!   numeric literal value both its cuts, a range facet one, and a subtype the
//!   closed cut of its lower bound and the open cut of its upper bound. The
//!   classes are chained in the order of the cuts; a number with both cuts is a
//!   literal value whose individual is alone between them; a facet becomes its
//!   cut's class or that class's complement, and a subtype the integers between
//!   its bounds' classes. When the integers are in use, the integers between
//!   two neighbouring cuts of different numbers are none, a few (fewer than a
//!   capacity that bounds the counts of the data restrictions of the closure
//!   and its questions, and at most that many at any element along a role `U`
//!   above every data property) or treated as infinitely many;
//! - every object property relates only elements that are no data nodes, and
//!   the individuals are no data nodes; a class expression that a data node
//!   could satisfy, on the left of an inclusion or in a list of equivalent or
//!   disjoint classes, is conjoined with the complement of `D`, and so is the
//!   filler of an existential restriction along the universal role, while the
//!   filler of a universal restriction along it is joined with `D`.
//!
//! The context of the encoding (`Context`) lists the distinct literal values,
//! the datatypes in use, the object properties, the data properties and the
//! cuts; the encoding gives no answer for anything outside it, so a context
//! prepared from a closure also encodes the questions about it. A model of the encoding has,
//! at every element that is no data node, a value for each of finitely many
//! data nodes it is related to, with the values of the literal individuals and
//! distinct values for distinct data nodes, which the infinitely many values of
//! every region of numbers outside the literals allow, and every bounded run of
//! integers too, since its bound or the counts of all data restrictions limit
//! how many data nodes need values from it; and every OWL model, with its data
//! values as data nodes, is a model of the encoding.
//!
//! A closure with keys is encoded by `key_ontology`, which adds the keys to
//! this encoding of its other axioms.
//!
//! `None` means that the closure or the question uses a datatype restriction
//! other than one of the four range facets with a numeric bound on a numeric
//! datatype, a datatype definition, a key that `key_ontology` declines, another
//! datatype, a literal outside its lexical space, `owl:topDataProperty` outside
//! an inclusion into it, `owl:Thing` as a disjoint union, a number restriction
//! along the universal role, the universal role included in another role (alone
//! or in a chain), equivalent or inverse to a role, functional or inverse
//! functional, or a name starting with the byte 0; that the data restrictions of
//! the closure, with the room for a question's, count `usize::MAX / 16` values
//! or more; that a question names an individual that is anonymous or that the
//! closure does not mention, or, for a closure with keys, asks whether such an
//! individual is an instance, or counts more values than a prepared closure has
//! room for; or that the queries give no answer.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::manual_map,
    clippy::needless_return,
    clippy::too_many_arguments,
    clippy::vec_init_then_push,
    clippy::len_zero,
    clippy::match_like_matches_macro,
    clippy::collapsible_else_if,
    clippy::if_same_then_else
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::alc_ontology::{intern, position};
use crate::concepts::copy_individual;
use crate::datatypes::{
    facet_of, in_kind, kind_of, literal_value, lower_bound, numeric, same_value, upper_bound,
    DataValue, Facet, Kind,
};
use crate::key_ontology;
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, Class, ClassExpression, DataProperty, DataRange,
    FacetRestriction, Individual, Iri, Literal, NamedIndividual, NonEmpty, ObjectProperty,
    ObjectPropertyExpression, SubObjectPropertyExpression,
};
use crate::nnf::copy_bytes;
use crate::probes::Natural;
use crate::regions::{
    add_cut, copy_value, cut_index, cut_order, cuts_fit, fits, in_cut, run_size, Cut,
};
use crate::shi_ontology;

/// The datatypes in use, and whether numbers are ordered: a datatype
/// restriction or a subtype of `xsd:integer` is in use.
pub struct Kinds {
    pub integer: bool,
    pub decimal: bool,
    pub string: bool,
    pub plain: bool,
    pub boolean: bool,
    pub real: bool,
    pub rational: bool,
    pub ordered: bool,
}
/// What the encoding of a closure and its questions knows: the distinct
/// literal values, the datatypes in use, the named object properties other than
/// the universal role, the data properties other than the top and bottom
/// ones, and the cuts of the numbers that facets, bounds of datatypes and
/// literal values make.
pub struct Context {
    pub values: Vec<DataValue>,
    pub kinds: Kinds,
    pub roles: Vec<ObjectProperty>,
    pub data: Vec<DataProperty>,
    pub cuts: Vec<Cut>,
}

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
fn same_from(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> bool {
    if index < left.len() && index < right.len() {
        left[index] == right[index] && same_from(left, right, index + 1)
    } else {
        true
    }
}
fn same_bytes(left: &Vec<u8>, right: &Vec<u8>) -> bool {
    left.len() == right.len() && same_from(left, right, 0)
}
/// `out` followed by the bytes of `pattern[index..]`.
fn pattern_from(pattern: &[u8], index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < pattern.len() {
        out.push(pattern[index]);
        pattern_from(pattern, index + 1, out)
    } else {
        out
    }
}
/// Whether the spelling starts with the byte 0, as the encoding's own names do.
fn reserved(spelling: &Vec<u8>) -> bool {
    if 0 < spelling.len() {
        spelling[0] == 0
    } else {
        false
    }
}
fn is_top_object(property: &ObjectProperty) -> bool {
    same_pattern(
        &property.iri.spelling,
        b"http://www.w3.org/2002/07/owl#topObjectProperty",
    )
}
pub(crate) fn is_top_data(property: &DataProperty) -> bool {
    same_pattern(
        &property.iri.spelling,
        b"http://www.w3.org/2002/07/owl#topDataProperty",
    )
}
fn is_bottom_data(property: &DataProperty) -> bool {
    same_pattern(
        &property.iri.spelling,
        b"http://www.w3.org/2002/07/owl#bottomDataProperty",
    )
}
fn is_thing(class: &Class) -> bool {
    same_pattern(&class.iri.spelling, b"http://www.w3.org/2002/07/owl#Thing")
}
pub(crate) fn is_literal(datatype: &crate::model::Datatype) -> bool {
    same_pattern(
        &datatype.iri.spelling,
        b"http://www.w3.org/2000/01/rdf-schema#Literal",
    )
}
/// The named property of an object property expression.
fn named(role: &ObjectPropertyExpression) -> &ObjectProperty {
    match role {
        ObjectPropertyExpression::Property(property) => property,
        ObjectPropertyExpression::Inverse(property) => property,
    }
}
/// Whether the role is the universal role or its inverse.
pub(crate) fn universal(role: &ObjectPropertyExpression) -> bool {
    is_top_object(named(role))
}

// ---------------------------------------------------------------------------
// The encoding's own names
// ---------------------------------------------------------------------------

/// The eight bytes of `value`, least significant first, after `out`.
/// Whether the universal role is one of `roles[index..]`.
fn any_universal(roles: &Vec<ObjectPropertyExpression>, index: usize) -> bool {
    if index < roles.len() {
        if universal(&roles[index]) {
            true
        } else {
            any_universal(roles, index + 1)
        }
    } else {
        false
    }
}
/// Whether the universal role is one of the roles.
fn members_universal(roles: &AtLeastTwo<ObjectPropertyExpression>) -> bool {
    universal(&roles.first) || universal(&roles.second) || any_universal(&roles.rest, 0)
}
/// Whether the universal role is the role or a role of the chain.
fn sub_universal(sub: &SubObjectPropertyExpression) -> bool {
    match sub {
        SubObjectPropertyExpression::Single(role) => universal(role),
        SubObjectPropertyExpression::Chain(roles) => members_universal(roles),
    }
}
fn bytes(value: usize, count: usize, mut out: Vec<u8>) -> Vec<u8> {
    if count < 8 {
        out.push((value % 256) as u8);
        bytes(value / 256, count + 1, out)
    } else {
        out
    }
}
/// The byte 0, a tag and `rest`.
pub(crate) fn tagged_name(tag: u8, rest: Vec<u8>) -> Vec<u8> {
    let mut spelling = Vec::new();
    spelling.push(0);
    spelling.push(tag);
    copy_after(&rest, 0, spelling)
}
/// `out` followed by `source[index..]`.
pub(crate) fn copy_after(source: &Vec<u8>, index: usize, mut out: Vec<u8>) -> Vec<u8> {
    if index < source.len() {
        out.push(source[index]);
        copy_after(source, index + 1, out)
    } else {
        out
    }
}
fn class_named(spelling: Vec<u8>) -> ClassExpression {
    ClassExpression::Class(Class {
        iri: Iri { spelling },
    })
}
/// The class `D` of the data nodes.
fn data_class() -> ClassExpression {
    class_named(tagged_name(b'D', Vec::new()))
}
/// The complement of `D`.
pub(crate) fn object_class() -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(data_class()))
}
/// The index of a kind: integer 0, decimal 1, string 2, plain literal 3,
/// boolean 4, and the further datatypes from 5 on.
fn kind_index(kind: Kind) -> u8 {
    match kind {
        Kind::Integer => 0,
        Kind::Decimal => 1,
        Kind::String => 2,
        Kind::Plain => 3,
        Kind::Boolean => 4,
        Kind::Real => 5,
        Kind::Rational => 6,
        Kind::NonNegativeInteger => 7,
        Kind::NonPositiveInteger => 8,
        Kind::PositiveInteger => 9,
        Kind::NegativeInteger => 10,
        Kind::Long => 11,
        Kind::Int => 12,
        Kind::Short => 13,
        Kind::Byte => 14,
        Kind::UnsignedLong => 15,
        Kind::UnsignedInt => 16,
        Kind::UnsignedShort => 17,
        Kind::UnsignedByte => 18,
    }
}
/// The class of a kind.
fn kind_class(kind: Kind) -> ClassExpression {
    let mut rest = Vec::new();
    rest.push(kind_index(kind));
    class_named(tagged_name(b'A', rest))
}
/// The bit class at `position`.
fn bit_class(position: usize) -> ClassExpression {
    class_named(tagged_name(b'B', bytes(position, 0, Vec::new())))
}
/// The individual of the literal value at `index`.
fn value_individual(index: usize) -> Individual {
    Individual::Named(NamedIndividual {
        iri: Iri {
            spelling: tagged_name(b'L', bytes(index, 0, Vec::new())),
        },
    })
}
/// The class `G` of the numbers in the cut at `index`.
fn cut_class(index: usize) -> ClassExpression {
    class_named(tagged_name(b'G', bytes(index, 0, Vec::new())))
}
/// The role `U` above every data property's role.
fn data_super() -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty {
        iri: Iri {
            spelling: tagged_name(b'U', Vec::new()),
        },
    })
}
/// The further individual that is no data node.
fn object_individual() -> Individual {
    Individual::Named(NamedIndividual {
        iri: Iri {
            spelling: tagged_name(b'O', Vec::new()),
        },
    })
}
fn thing() -> ClassExpression {
    class_named(pattern_from(
        b"http://www.w3.org/2002/07/owl#Thing",
        0,
        Vec::new(),
    ))
}

// ---------------------------------------------------------------------------
// The context
// ---------------------------------------------------------------------------

fn no_kinds() -> Kinds {
    Kinds {
        integer: false,
        decimal: false,
        string: false,
        plain: false,
        boolean: false,
        real: false,
        rational: false,
        ordered: false,
    }
}
/// Whether the kind is in use.
fn used(kinds: &Kinds, kind: Kind) -> bool {
    match kind {
        Kind::Integer => kinds.integer,
        Kind::Decimal => kinds.decimal,
        Kind::String => kinds.string,
        Kind::Plain => kinds.plain,
        Kind::Boolean => kinds.boolean,
        Kind::Real => kinds.real,
        Kind::Rational => kinds.rational,
        _ => false,
    }
}
/// Whether the kind is a subtype of `xsd:integer` with bounds.
fn bounded(kind: Kind) -> bool {
    match kind {
        Kind::Integer => false,
        Kind::Decimal => false,
        Kind::String => false,
        Kind::Plain => false,
        Kind::Boolean => false,
        Kind::Real => false,
        Kind::Rational => false,
        _ => true,
    }
}
/// Whether the kind is a numeric datatype.
fn numeric_kind(kind: Kind) -> bool {
    match kind {
        Kind::String => false,
        Kind::Plain => false,
        Kind::Boolean => false,
        _ => true,
    }
}
/// The kinds with `kind` in use too.
fn with_kind(kinds: Kinds, kind: Kind) -> Kinds {
    match kind {
        Kind::Integer => Kinds {
            integer: true,
            ..kinds
        },
        Kind::Decimal => Kinds {
            decimal: true,
            ..kinds
        },
        Kind::String => Kinds {
            string: true,
            ..kinds
        },
        Kind::Plain => Kinds {
            plain: true,
            ..kinds
        },
        Kind::Boolean => Kinds {
            boolean: true,
            ..kinds
        },
        Kind::Real => Kinds {
            real: true,
            ..kinds
        },
        Kind::Rational => Kinds {
            rational: true,
            ..kinds
        },
        _ => Kinds {
            integer: true,
            real: true,
            ordered: true,
            ..kinds
        },
    }
}
/// The kinds with ordered numbers.
fn with_order(kinds: Kinds) -> Kinds {
    Kinds {
        real: true,
        ordered: true,
        ..kinds
    }
}
/// The index of the value in `values[index..]`.
fn value_index(values: &Vec<DataValue>, value: &DataValue, index: usize) -> Option<usize> {
    if index < values.len() {
        if same_value(&values[index], value) {
            Some(index)
        } else {
            value_index(values, value, index + 1)
        }
    } else {
        None
    }
}
/// The values with `value` too, once.
fn add_value(mut values: Vec<DataValue>, value: DataValue) -> Vec<DataValue> {
    match value_index(&values, &value, 0) {
        Some(_) => values,
        None => {
            if values.len() < usize::MAX {
                values.push(value);
            }
            values
        }
    }
}
fn has_role(roles: &Vec<ObjectProperty>, property: &ObjectProperty, index: usize) -> bool {
    if index < roles.len() {
        if same_bytes(&roles[index].iri.spelling, &property.iri.spelling) {
            true
        } else {
            has_role(roles, property, index + 1)
        }
    } else {
        false
    }
}
fn has_data(data: &Vec<DataProperty>, property: &DataProperty, index: usize) -> bool {
    if index < data.len() {
        if same_bytes(&data[index].iri.spelling, &property.iri.spelling) {
            true
        } else {
            has_data(data, property, index + 1)
        }
    } else {
        false
    }
}
fn add_role(mut context: Context, role: &ObjectPropertyExpression) -> Context {
    let property = named(role);
    if is_top_object(property)
        || reserved(&property.iri.spelling)
        || has_role(&context.roles, property, 0)
        || context.roles.len() == usize::MAX
    {
        context
    } else {
        context.roles.push(ObjectProperty {
            iri: Iri {
                spelling: copy_bytes(&property.iri.spelling),
            },
        });
        context
    }
}
fn add_data(mut context: Context, property: &DataProperty) -> Context {
    if is_top_data(property)
        || is_bottom_data(property)
        || has_data(&context.data, property, 0)
        || context.data.len() == usize::MAX
    {
        context
    } else {
        context.data.push(DataProperty {
            iri: Iri {
                spelling: copy_bytes(&property.iri.spelling),
            },
        });
        context
    }
}
/// The context with a literal's value, and the two cuts of a numeric one.
fn add_literal(mut context: Context, literal: &Literal) -> Context {
    match literal_value(literal) {
        Some(value) => {
            context.values = add_value(context.values, value);
            context
        }
        None => context,
    }
}
fn literals_context(context: Context, literals: &Vec<Literal>, index: usize) -> Context {
    if index < literals.len() {
        literals_context(add_literal(context, &literals[index]), literals, index + 1)
    } else {
        context
    }
}
/// The cuts with the cut of a bound, if any.
fn add_bound(cuts: Vec<Cut>, bound: Option<DataValue>, open: bool) -> Vec<Cut> {
    match bound {
        Some(value) => add_cut(cuts, &value, open),
        None => cuts,
    }
}
/// The context with the datatype of the kind in use, and the cuts of the
/// bounds of a subtype of `xsd:integer`: at or above its lower bound, and above
/// its upper bound.
fn kind_context(mut context: Context, kind: Kind) -> Context {
    context.kinds = with_kind(context.kinds, kind);
    context.cuts = add_bound(context.cuts, lower_bound(kind), false);
    context.cuts = add_bound(context.cuts, upper_bound(kind), true);
    context
}
/// The side of the cut of a range facet: open for `xsd:minExclusive` and
/// `xsd:maxInclusive`.
fn facet_open(facet: Facet) -> bool {
    match facet {
        Facet::MinInclusive => false,
        Facet::MinExclusive => true,
        Facet::MaxInclusive => true,
        Facet::MaxExclusive => false,
    }
}
/// The context with the cut of a range facet with a numeric bound.
fn facet_context(mut context: Context, restriction: &FacetRestriction) -> Context {
    match (
        facet_of(&restriction.facet),
        literal_value(&restriction.value),
    ) {
        (Some(facet), Some(value)) => {
            if numeric(&value) {
                context.cuts = add_cut(context.cuts, &value, facet_open(facet));
            }
            context
        }
        _ => context,
    }
}
/// The context with the cuts of the facet restrictions `restrictions[index..]`.
fn facets_context(context: Context, restrictions: &Vec<FacetRestriction>, index: usize) -> Context {
    if index < restrictions.len() {
        facets_context(
            facet_context(context, &restrictions[index]),
            restrictions,
            index + 1,
        )
    } else {
        context
    }
}
fn range_context(mut context: Context, range: &DataRange) -> Context {
    match range {
        DataRange::Datatype(datatype) => match kind_of(datatype) {
            Some(kind) => kind_context(context, kind),
            None => context,
        },
        DataRange::Intersection(members) | DataRange::Union(members) => {
            let context = range_context(context, &members.first);
            let context = range_context(context, &members.second);
            ranges_context(context, &members.rest, 0)
        }
        DataRange::Complement(inner) => range_context(context, inner),
        DataRange::OneOf(literals) => {
            let context = add_literal(context, &literals.first);
            literals_context(context, &literals.rest, 0)
        }
        DataRange::Restriction(datatype, restrictions) => {
            context.kinds = with_order(context.kinds);
            let context = match kind_of(datatype) {
                Some(kind) => kind_context(context, kind),
                None => context,
            };
            let context = facet_context(context, &restrictions.first);
            facets_context(context, &restrictions.rest, 0)
        }
    }
}
fn ranges_context(context: Context, ranges: &Vec<DataRange>, index: usize) -> Context {
    if index < ranges.len() {
        ranges_context(range_context(context, &ranges[index]), ranges, index + 1)
    } else {
        context
    }
}
fn optional_range_context(context: Context, range: &Option<DataRange>) -> Context {
    match range {
        Some(range) => range_context(context, range),
        None => context,
    }
}
pub(crate) fn class_context(context: Context, class: &ClassExpression) -> Context {
    match class {
        ClassExpression::Class(_) => context,
        ClassExpression::ObjectIntersectionOf(members)
        | ClassExpression::ObjectUnionOf(members) => members_context(context, members),
        ClassExpression::ObjectComplementOf(inner) => class_context(context, inner),
        ClassExpression::ObjectOneOf(_) => context,
        ClassExpression::ObjectSomeValuesFrom(role, filler)
        | ClassExpression::ObjectAllValuesFrom(role, filler) => {
            class_context(add_role(context, role), filler)
        }
        ClassExpression::ObjectHasValue(role, _) => add_role(context, role),
        ClassExpression::ObjectHasSelf(role) => add_role(context, role),
        ClassExpression::ObjectMinCardinality(_, role, filler)
        | ClassExpression::ObjectMaxCardinality(_, role, filler)
        | ClassExpression::ObjectExactCardinality(_, role, filler) => {
            let context = add_role(context, role);
            match filler {
                Some(filler) => class_context(context, filler),
                None => context,
            }
        }
        ClassExpression::DataSomeValuesFrom(property, range)
        | ClassExpression::DataAllValuesFrom(property, range) => {
            range_context(add_data(context, property), range)
        }
        ClassExpression::DataHasValue(property, literal) => {
            add_literal(add_data(context, property), literal)
        }
        ClassExpression::DataMinCardinality(_, property, range)
        | ClassExpression::DataMaxCardinality(_, property, range)
        | ClassExpression::DataExactCardinality(_, property, range) => {
            optional_range_context(add_data(context, property), range)
        }
    }
}
fn classes_context(context: Context, classes: &Vec<ClassExpression>, index: usize) -> Context {
    if index < classes.len() {
        classes_context(class_context(context, &classes[index]), classes, index + 1)
    } else {
        context
    }
}
fn members_context(context: Context, members: &AtLeastTwo<ClassExpression>) -> Context {
    let context = class_context(context, &members.first);
    let context = class_context(context, &members.second);
    classes_context(context, &members.rest, 0)
}
pub(crate) fn roles_context(
    context: Context,
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
) -> Context {
    if index < roles.len() {
        roles_context(add_role(context, &roles[index]), roles, index + 1)
    } else {
        context
    }
}
fn role_members_context(context: Context, roles: &AtLeastTwo<ObjectPropertyExpression>) -> Context {
    let context = add_role(context, &roles.first);
    let context = add_role(context, &roles.second);
    roles_context(context, &roles.rest, 0)
}
pub(crate) fn data_list_context(
    context: Context,
    data: &Vec<DataProperty>,
    index: usize,
) -> Context {
    if index < data.len() {
        data_list_context(add_data(context, &data[index]), data, index + 1)
    } else {
        context
    }
}
fn axiom_context(context: Context, axiom: &Axiom) -> Context {
    match axiom {
        Axiom::SubClassOf(sub, sup) => class_context(class_context(context, sub), sup),
        Axiom::EquivalentClasses(members)
        | Axiom::DisjointClasses(members)
        | Axiom::DisjointUnion(_, members) => members_context(context, members),
        Axiom::SubObjectPropertyOf(sub, sup) => {
            let context = match sub {
                SubObjectPropertyExpression::Single(role) => add_role(context, role),
                SubObjectPropertyExpression::Chain(roles) => role_members_context(context, roles),
            };
            add_role(context, sup)
        }
        Axiom::EquivalentObjectProperties(roles) | Axiom::DisjointObjectProperties(roles) => {
            role_members_context(context, roles)
        }
        Axiom::InverseObjectProperties(first, second) => add_role(add_role(context, first), second),
        Axiom::ObjectPropertyDomain(role, class) | Axiom::ObjectPropertyRange(role, class) => {
            class_context(add_role(context, role), class)
        }
        Axiom::FunctionalObjectProperty(role)
        | Axiom::InverseFunctionalObjectProperty(role)
        | Axiom::ReflexiveObjectProperty(role)
        | Axiom::IrreflexiveObjectProperty(role)
        | Axiom::SymmetricObjectProperty(role)
        | Axiom::AsymmetricObjectProperty(role)
        | Axiom::TransitiveObjectProperty(role) => add_role(context, role),
        Axiom::SubDataPropertyOf(sub, sup) => add_data(add_data(context, sub), sup),
        Axiom::EquivalentDataProperties(data) | Axiom::DisjointDataProperties(data) => {
            let context = add_data(context, &data.first);
            let context = add_data(context, &data.second);
            data_list_context(context, &data.rest, 0)
        }
        Axiom::DataPropertyDomain(property, class) => {
            class_context(add_data(context, property), class)
        }
        Axiom::DataPropertyRange(property, range) => {
            range_context(add_data(context, property), range)
        }
        Axiom::FunctionalDataProperty(property) => add_data(context, property),
        Axiom::ClassAssertion(class, _) => class_context(context, class),
        Axiom::ObjectPropertyAssertion(role, _, _)
        | Axiom::NegativeObjectPropertyAssertion(role, _, _) => add_role(context, role),
        Axiom::DataPropertyAssertion(property, _, literal)
        | Axiom::NegativeDataPropertyAssertion(property, _, literal) => {
            add_literal(add_data(context, property), literal)
        }
        _ => context,
    }
}
fn items_context(context: Context, items: &Vec<AnnotatedAxiom>, index: usize) -> Context {
    if index < items.len() {
        items_context(
            axiom_context(context, &items[index].axiom),
            items,
            index + 1,
        )
    } else {
        context
    }
}
/// The context of a closure.
fn closure_context(items: &Vec<AnnotatedAxiom>) -> Context {
    items_context(
        Context {
            values: Vec::new(),
            kinds: no_kinds(),
            roles: Vec::new(),
            data: Vec::new(),
            cuts: Vec::new(),
        },
        items,
        0,
    )
}
/// The context with both truth values among the literal values when the
/// booleans are in use.
pub(crate) fn with_truths(mut context: Context) -> Context {
    if context.kinds.boolean {
        context.values = add_value(context.values, DataValue::Truth(true));
        context.values = add_value(context.values, DataValue::Truth(false));
    }
    context
}
/// The values with the number of every cut of `cuts[index..]` whose number has
/// both cuts.
fn points_from(cuts: &Vec<Cut>, index: usize, values: Vec<DataValue>) -> Vec<DataValue> {
    if index < cuts.len() {
        let open = !cuts[index].open;
        match cut_index(cuts, &cuts[index].value, open, 0) {
            Some(_) => points_from(
                cuts,
                index + 1,
                add_value(values, copy_value(&cuts[index].value)),
            ),
            None => points_from(cuts, index + 1, values),
        }
    } else {
        values
    }
}
/// The context finished for the encoding: both truth values among the literal
/// values when the booleans are in use, and every number with both cuts
/// among the literal values too.
pub(crate) fn finished(context: Context) -> Context {
    let mut context = with_truths(context);
    context.values = points_from(&context.cuts, 0, context.values);
    context
}

// ---------------------------------------------------------------------------
// Class expressions and data ranges
// ---------------------------------------------------------------------------

fn copy_natural(value: &Natural) -> Natural {
    match value {
        Natural::Zero => Natural::Zero,
        Natural::Succ(inner) => Natural::Succ(Box::new(copy_natural(inner))),
    }
}
fn positive(value: &Natural) -> bool {
    match value {
        Natural::Zero => false,
        Natural::Succ(_) => true,
    }
}
pub(crate) fn and(left: ClassExpression, right: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first: left,
        second: right,
        rest: Vec::new(),
    }))
}
pub(crate) fn or(left: ClassExpression, right: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectUnionOf(Box::new(AtLeastTwo {
        first: left,
        second: right,
        rest: Vec::new(),
    }))
}
/// A copy of an object property expression of the context, or of the
/// universal role.
pub(crate) fn object_role(
    context: &Context,
    role: &ObjectPropertyExpression,
) -> Option<ObjectPropertyExpression> {
    let property = named(role);
    if reserved(&property.iri.spelling) {
        return None;
    }
    if !(is_top_object(property) || has_role(&context.roles, property, 0)) {
        return None;
    }
    let copy = ObjectProperty {
        iri: Iri {
            spelling: copy_bytes(&property.iri.spelling),
        },
    };
    match role {
        ObjectPropertyExpression::Property(_) => Some(ObjectPropertyExpression::Property(copy)),
        ObjectPropertyExpression::Inverse(_) => Some(ObjectPropertyExpression::Inverse(copy)),
    }
}
/// A copy of an individual whose name is not the encoding's.
pub(crate) fn object_individual_of(individual: &Individual) -> Option<Individual> {
    match individual {
        Individual::Named(named) => {
            if reserved(&named.iri.spelling) {
                None
            } else {
                Some(copy_individual(individual))
            }
        }
        Individual::Anonymous(_) => Some(copy_individual(individual)),
    }
}
fn individuals_from(
    individuals: &Vec<Individual>,
    index: usize,
    mut out: Vec<Individual>,
) -> Option<Vec<Individual>> {
    if index < individuals.len() {
        match object_individual_of(&individuals[index]) {
            Some(copy) => {
                out.push(copy);
                individuals_from(individuals, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The object property of a data property of the context, or of
/// `owl:bottomDataProperty`.
fn data_role(context: &Context, property: &DataProperty) -> Option<ObjectPropertyExpression> {
    if is_bottom_data(property) {
        Some(ObjectPropertyExpression::Property(ObjectProperty {
            iri: Iri {
                spelling: pattern_from(
                    b"http://www.w3.org/2002/07/owl#bottomObjectProperty",
                    0,
                    Vec::new(),
                ),
            },
        }))
    } else if has_data(&context.data, property, 0)
        && !reserved(&property.iri.spelling)
        && property.iri.spelling.len() < usize::MAX - 1
    {
        Some(ObjectPropertyExpression::Property(ObjectProperty {
            iri: Iri {
                spelling: tagged_name(b'P', copy_bytes(&property.iri.spelling)),
            },
        }))
    } else {
        None
    }
}
/// The individual of a literal's value in the context.
fn literal_individual(context: &Context, literal: &Literal) -> Option<Individual> {
    match literal_value(literal) {
        Some(value) => match value_index(&context.values, &value, 0) {
            Some(index) => Some(value_individual(index)),
            None => None,
        },
        None => None,
    }
}
fn literal_individuals(
    context: &Context,
    literals: &Vec<Literal>,
    index: usize,
    mut out: Vec<Individual>,
) -> Option<Vec<Individual>> {
    if index < literals.len() {
        match literal_individual(context, &literals[index]) {
            Some(individual) => {
                out.push(individual);
                literal_individuals(context, literals, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The complement of a class expression.
fn not(class: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(class))
}
/// The intersection of three class expressions.
fn and3(
    first: ClassExpression,
    second: ClassExpression,
    third: ClassExpression,
) -> ClassExpression {
    let mut rest = Vec::new();
    rest.push(third);
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first,
        second,
        rest,
    }))
}
/// The class of the cut of a bound on the side `open`, complemented when
/// `outside`, and `owl:Thing` without a bound.
fn bound_class(
    context: &Context,
    bound: Option<DataValue>,
    open: bool,
    outside: bool,
) -> Option<ClassExpression> {
    match bound {
        Some(value) => match cut_index(&context.cuts, &value, open, 0) {
            Some(index) => {
                if outside {
                    Some(not(cut_class(index)))
                } else {
                    Some(cut_class(index))
                }
            }
            None => None,
        },
        None => Some(thing()),
    }
}
/// The class expression of a subtype of `xsd:integer`: the integers at or
/// above its lower bound and not above its upper bound.
fn subtype_range(context: &Context, kind: Kind) -> Option<ClassExpression> {
    if used(&context.kinds, Kind::Integer) & context.kinds.ordered {
        match (
            bound_class(context, lower_bound(kind), false, false),
            bound_class(context, upper_bound(kind), true, true),
        ) {
            (Some(lower), Some(upper)) => Some(and3(kind_class(Kind::Integer), lower, upper)),
            _ => None,
        }
    } else {
        None
    }
}
/// The class expression of a datatype of a kind in use.
fn kind_range(context: &Context, kind: Kind) -> Option<ClassExpression> {
    if bounded(kind) {
        subtype_range(context, kind)
    } else if used(&context.kinds, kind) {
        Some(kind_class(kind))
    } else {
        None
    }
}
/// Whether a range facet bounds the numbers from above: its values are
/// outside its cut.
fn facet_outside(facet: Facet) -> bool {
    match facet {
        Facet::MinInclusive => false,
        Facet::MinExclusive => false,
        Facet::MaxInclusive => true,
        Facet::MaxExclusive => true,
    }
}
/// The class expression of a facet restriction: a range facet with a numeric
/// bound, whose cut is in the context.
fn facet_class(context: &Context, restriction: &FacetRestriction) -> Option<ClassExpression> {
    match (
        facet_of(&restriction.facet),
        literal_value(&restriction.value),
    ) {
        (Some(facet), Some(value)) => {
            if numeric(&value) {
                bound_class(
                    context,
                    Some(value),
                    facet_open(facet),
                    facet_outside(facet),
                )
            } else {
                None
            }
        }
        _ => None,
    }
}
fn facet_classes(
    context: &Context,
    restrictions: &Vec<FacetRestriction>,
    index: usize,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < restrictions.len() {
        match facet_class(context, &restrictions[index]) {
            Some(class) => {
                if out.len() < usize::MAX {
                    out.push(class);
                }
                facet_classes(context, restrictions, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The class expression of a datatype restriction of a numeric datatype.
fn restriction_range(
    context: &Context,
    kind: Kind,
    restrictions: &NonEmpty<FacetRestriction>,
) -> Option<ClassExpression> {
    if numeric_kind(kind) & context.kinds.ordered {
        match (
            kind_range(context, kind),
            facet_class(context, &restrictions.first),
            facet_classes(context, &restrictions.rest, 0, Vec::new()),
        ) {
            (Some(base), Some(first), Some(rest)) => Some(ClassExpression::ObjectIntersectionOf(
                Box::new(AtLeastTwo {
                    first: base,
                    second: first,
                    rest,
                }),
            )),
            _ => None,
        }
    } else {
        None
    }
}
/// The class expression a data range becomes at data nodes.
pub fn encode_range(context: &Context, range: &DataRange) -> Option<ClassExpression> {
    match range {
        DataRange::Datatype(datatype) => {
            if is_literal(datatype) {
                Some(thing())
            } else {
                match kind_of(datatype) {
                    Some(kind) => kind_range(context, kind),
                    None => None,
                }
            }
        }
        DataRange::Intersection(members) => match encode_ranges(context, members) {
            Some(members) => Some(ClassExpression::ObjectIntersectionOf(Box::new(members))),
            None => None,
        },
        DataRange::Union(members) => match encode_ranges(context, members) {
            Some(members) => Some(ClassExpression::ObjectUnionOf(Box::new(members))),
            None => None,
        },
        DataRange::Complement(inner) => match encode_range(context, inner) {
            Some(inner) => Some(ClassExpression::ObjectComplementOf(Box::new(inner))),
            None => None,
        },
        DataRange::OneOf(literals) => match literal_individual(context, &literals.first) {
            Some(first) => match literal_individuals(context, &literals.rest, 0, Vec::new()) {
                Some(rest) => Some(ClassExpression::ObjectOneOf(NonEmpty { first, rest })),
                None => None,
            },
            None => None,
        },
        DataRange::Restriction(datatype, restrictions) => match kind_of(datatype) {
            Some(kind) => restriction_range(context, kind, restrictions),
            None => None,
        },
    }
}
fn encode_range_list(
    context: &Context,
    ranges: &Vec<DataRange>,
    index: usize,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < ranges.len() {
        match encode_range(context, &ranges[index]) {
            Some(class) => {
                out.push(class);
                encode_range_list(context, ranges, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn encode_ranges(
    context: &Context,
    members: &AtLeastTwo<DataRange>,
) -> Option<AtLeastTwo<ClassExpression>> {
    match encode_range(context, &members.first) {
        Some(first) => match encode_range(context, &members.second) {
            Some(second) => match encode_range_list(context, &members.rest, 0, Vec::new()) {
                Some(rest) => Some(AtLeastTwo {
                    first,
                    second,
                    rest,
                }),
                None => None,
            },
            None => None,
        },
        None => None,
    }
}
fn encode_optional_range(
    context: &Context,
    range: &Option<DataRange>,
) -> Option<Option<Box<ClassExpression>>> {
    match range {
        Some(range) => match encode_range(context, range) {
            Some(class) => Some(Some(Box::new(class))),
            None => None,
        },
        None => Some(None),
    }
}
/// The role and filler of an object number restriction, which may not count
/// along the universal role.
fn encode_counted(
    context: &Context,
    role: &ObjectPropertyExpression,
    filler: &Option<Box<ClassExpression>>,
) -> Option<(ObjectPropertyExpression, Option<Box<ClassExpression>>)> {
    if universal(role) {
        return None;
    }
    match object_role(context, role) {
        Some(copy) => match filler {
            Some(filler) => match encode_class(context, filler) {
                Some(filler) => Some((copy, Some(Box::new(filler)))),
                None => None,
            },
            None => Some((copy, None)),
        },
        None => None,
    }
}
/// The class expression an OWL class expression becomes at elements that are
/// no data nodes.
pub fn encode_class(context: &Context, class: &ClassExpression) -> Option<ClassExpression> {
    match class {
        ClassExpression::Class(named) => {
            if reserved(&named.iri.spelling) {
                None
            } else {
                Some(class_named(copy_bytes(&named.iri.spelling)))
            }
        }
        ClassExpression::ObjectIntersectionOf(members) => match encode_members(context, members) {
            Some(members) => Some(ClassExpression::ObjectIntersectionOf(Box::new(members))),
            None => None,
        },
        ClassExpression::ObjectUnionOf(members) => match encode_members(context, members) {
            Some(members) => Some(ClassExpression::ObjectUnionOf(Box::new(members))),
            None => None,
        },
        ClassExpression::ObjectComplementOf(inner) => match encode_class(context, inner) {
            Some(inner) => Some(ClassExpression::ObjectComplementOf(Box::new(inner))),
            None => None,
        },
        ClassExpression::ObjectOneOf(individuals) => match object_individual_of(&individuals.first)
        {
            Some(first) => match individuals_from(&individuals.rest, 0, Vec::new()) {
                Some(rest) => Some(ClassExpression::ObjectOneOf(NonEmpty { first, rest })),
                None => None,
            },
            None => None,
        },
        ClassExpression::ObjectSomeValuesFrom(role, filler) => {
            match (object_role(context, role), encode_class(context, filler)) {
                (Some(copy), Some(filler)) => {
                    if universal(role) {
                        Some(ClassExpression::ObjectSomeValuesFrom(
                            copy,
                            Box::new(and(filler, object_class())),
                        ))
                    } else {
                        Some(ClassExpression::ObjectSomeValuesFrom(
                            copy,
                            Box::new(filler),
                        ))
                    }
                }
                _ => None,
            }
        }
        ClassExpression::ObjectAllValuesFrom(role, filler) => {
            match (object_role(context, role), encode_class(context, filler)) {
                (Some(copy), Some(filler)) => {
                    if universal(role) {
                        Some(ClassExpression::ObjectAllValuesFrom(
                            copy,
                            Box::new(or(filler, data_class())),
                        ))
                    } else {
                        Some(ClassExpression::ObjectAllValuesFrom(copy, Box::new(filler)))
                    }
                }
                _ => None,
            }
        }
        ClassExpression::ObjectHasValue(role, individual) => {
            match (object_role(context, role), object_individual_of(individual)) {
                (Some(role), Some(individual)) => {
                    Some(ClassExpression::ObjectHasValue(role, individual))
                }
                _ => None,
            }
        }
        ClassExpression::ObjectHasSelf(role) => match object_role(context, role) {
            Some(role) => Some(ClassExpression::ObjectHasSelf(role)),
            None => None,
        },
        ClassExpression::ObjectMinCardinality(count, role, filler) => {
            match encode_counted(context, role, filler) {
                Some((role, filler)) => Some(ClassExpression::ObjectMinCardinality(
                    copy_natural(count),
                    role,
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::ObjectMaxCardinality(count, role, filler) => {
            match encode_counted(context, role, filler) {
                Some((role, filler)) => Some(ClassExpression::ObjectMaxCardinality(
                    copy_natural(count),
                    role,
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::ObjectExactCardinality(count, role, filler) => {
            match encode_counted(context, role, filler) {
                Some((role, filler)) => Some(ClassExpression::ObjectExactCardinality(
                    copy_natural(count),
                    role,
                    filler,
                )),
                None => None,
            }
        }
        ClassExpression::DataSomeValuesFrom(property, range) => {
            match (data_role(context, property), encode_range(context, range)) {
                (Some(role), Some(filler)) => Some(ClassExpression::ObjectSomeValuesFrom(
                    role,
                    Box::new(filler),
                )),
                _ => None,
            }
        }
        ClassExpression::DataAllValuesFrom(property, range) => {
            match (data_role(context, property), encode_range(context, range)) {
                (Some(role), Some(filler)) => {
                    Some(ClassExpression::ObjectAllValuesFrom(role, Box::new(filler)))
                }
                _ => None,
            }
        }
        ClassExpression::DataHasValue(property, literal) => {
            match (
                data_role(context, property),
                literal_individual(context, literal),
            ) {
                (Some(role), Some(individual)) => {
                    Some(ClassExpression::ObjectHasValue(role, individual))
                }
                _ => None,
            }
        }
        ClassExpression::DataMinCardinality(count, property, range) => {
            match (
                data_role(context, property),
                encode_optional_range(context, range),
            ) {
                (Some(role), Some(filler)) => Some(ClassExpression::ObjectMinCardinality(
                    copy_natural(count),
                    role,
                    filler,
                )),
                _ => None,
            }
        }
        ClassExpression::DataMaxCardinality(count, property, range) => {
            match (
                data_role(context, property),
                encode_optional_range(context, range),
            ) {
                (Some(role), Some(filler)) => Some(ClassExpression::ObjectMaxCardinality(
                    copy_natural(count),
                    role,
                    filler,
                )),
                _ => None,
            }
        }
        ClassExpression::DataExactCardinality(count, property, range) => {
            match (
                data_role(context, property),
                encode_optional_range(context, range),
            ) {
                (Some(role), Some(filler)) => Some(ClassExpression::ObjectExactCardinality(
                    copy_natural(count),
                    role,
                    filler,
                )),
                _ => None,
            }
        }
    }
}
fn encode_class_list(
    context: &Context,
    classes: &Vec<ClassExpression>,
    index: usize,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < classes.len() {
        match encode_class(context, &classes[index]) {
            Some(class) => {
                out.push(class);
                encode_class_list(context, classes, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn encode_members(
    context: &Context,
    members: &AtLeastTwo<ClassExpression>,
) -> Option<AtLeastTwo<ClassExpression>> {
    match encode_class(context, &members.first) {
        Some(first) => match encode_class(context, &members.second) {
            Some(second) => match encode_class_list(context, &members.rest, 0, Vec::new()) {
                Some(rest) => Some(AtLeastTwo {
                    first,
                    second,
                    rest,
                }),
                None => None,
            },
            None => None,
        },
        None => None,
    }
}
/// Whether no data node satisfies the encoding of the class expression in the
/// model whose data nodes are the data values: a named class other than
/// `owl:Thing`, an enumeration of individuals, a restriction that needs a
/// neighbour along an object property other than the universal role or along a
/// data property, or an intersection with such a member or a union of them.
pub fn guarded(class: &ClassExpression) -> bool {
    match class {
        ClassExpression::Class(named) => !is_thing(named),
        ClassExpression::ObjectIntersectionOf(members) => {
            guarded(&members.first) || guarded(&members.second) || any_guarded(&members.rest, 0)
        }
        ClassExpression::ObjectUnionOf(members) => {
            guarded(&members.first) && guarded(&members.second) && all_guarded(&members.rest, 0)
        }
        ClassExpression::ObjectComplementOf(_) => false,
        ClassExpression::ObjectOneOf(_) => true,
        ClassExpression::ObjectSomeValuesFrom(role, _) => !universal(role),
        ClassExpression::ObjectAllValuesFrom(_, _) => false,
        ClassExpression::ObjectHasValue(role, _) => !universal(role),
        ClassExpression::ObjectHasSelf(role) => !universal(role),
        ClassExpression::ObjectMinCardinality(count, role, _) => {
            positive(count) && !universal(role)
        }
        ClassExpression::ObjectMaxCardinality(_, _, _) => false,
        ClassExpression::ObjectExactCardinality(count, role, _) => {
            positive(count) && !universal(role)
        }
        ClassExpression::DataSomeValuesFrom(_, _) => true,
        ClassExpression::DataAllValuesFrom(_, _) => false,
        ClassExpression::DataHasValue(_, _) => true,
        ClassExpression::DataMinCardinality(count, _, _) => positive(count),
        ClassExpression::DataMaxCardinality(_, _, _) => false,
        ClassExpression::DataExactCardinality(count, _, _) => positive(count),
    }
}
fn any_guarded(classes: &Vec<ClassExpression>, index: usize) -> bool {
    if index < classes.len() {
        if guarded(&classes[index]) {
            true
        } else {
            any_guarded(classes, index + 1)
        }
    } else {
        false
    }
}
fn all_guarded(classes: &Vec<ClassExpression>, index: usize) -> bool {
    if index < classes.len() {
        if guarded(&classes[index]) {
            all_guarded(classes, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// The encoding of a class expression conjoined with the complement of `D`
/// unless it is guarded: no data node satisfies it.
fn encode_object(context: &Context, class: &ClassExpression) -> Option<ClassExpression> {
    match encode_class(context, class) {
        Some(encoded) => {
            if guarded(class) {
                Some(encoded)
            } else {
                Some(and(encoded, object_class()))
            }
        }
        None => None,
    }
}
fn encode_object_list(
    context: &Context,
    classes: &Vec<ClassExpression>,
    index: usize,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < classes.len() {
        match encode_object(context, &classes[index]) {
            Some(class) => {
                out.push(class);
                encode_object_list(context, classes, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn encode_object_members(
    context: &Context,
    members: &AtLeastTwo<ClassExpression>,
) -> Option<AtLeastTwo<ClassExpression>> {
    match encode_object(context, &members.first) {
        Some(first) => match encode_object(context, &members.second) {
            Some(second) => match encode_object_list(context, &members.rest, 0, Vec::new()) {
                Some(rest) => Some(AtLeastTwo {
                    first,
                    second,
                    rest,
                }),
                None => None,
            },
            None => None,
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Axioms
// ---------------------------------------------------------------------------

/// `out` with the axiom; `None` when there is no room.
pub(crate) fn push(mut out: Vec<AnnotatedAxiom>, axiom: Axiom) -> Option<Vec<AnnotatedAxiom>> {
    if out.len() < usize::MAX {
        out.push(AnnotatedAxiom {
            annotations: Vec::new(),
            axiom,
        });
        Some(out)
    } else {
        None
    }
}
/// `out` with the individual no data node.
fn object_assertion(
    individual: &Individual,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match object_individual_of(individual) {
        Some(individual) => push(out, Axiom::ClassAssertion(object_class(), individual)),
        None => None,
    }
}
fn object_assertions(
    individuals: &Vec<Individual>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < individuals.len() {
        match object_assertion(&individuals[index], out) {
            Some(out) => object_assertions(individuals, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with the individuals of the nominals of a class expression no data
/// nodes.
fn nominal_objects(
    class: &ClassExpression,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match class {
        ClassExpression::ObjectIntersectionOf(members)
        | ClassExpression::ObjectUnionOf(members) => nominal_members(members, out),
        ClassExpression::ObjectComplementOf(inner) => nominal_objects(inner, out),
        ClassExpression::ObjectOneOf(individuals) => {
            match object_assertion(&individuals.first, out) {
                Some(out) => object_assertions(&individuals.rest, 0, out),
                None => None,
            }
        }
        ClassExpression::ObjectSomeValuesFrom(_, filler)
        | ClassExpression::ObjectAllValuesFrom(_, filler) => nominal_objects(filler, out),
        ClassExpression::ObjectHasValue(_, individual) => object_assertion(individual, out),
        ClassExpression::ObjectMinCardinality(_, _, filler)
        | ClassExpression::ObjectMaxCardinality(_, _, filler)
        | ClassExpression::ObjectExactCardinality(_, _, filler) => match filler {
            Some(filler) => nominal_objects(filler, out),
            None => Some(out),
        },
        _ => Some(out),
    }
}
fn nominal_list(
    classes: &Vec<ClassExpression>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < classes.len() {
        match nominal_objects(&classes[index], out) {
            Some(out) => nominal_list(classes, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
fn nominal_members(
    members: &AtLeastTwo<ClassExpression>,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match nominal_objects(&members.first, out) {
        Some(out) => match nominal_objects(&members.second, out) {
            Some(out) => nominal_list(&members.rest, 0, out),
            None => None,
        },
        None => None,
    }
}
fn data_roles_from(
    context: &Context,
    data: &Vec<DataProperty>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Option<Vec<ObjectPropertyExpression>> {
    if index < data.len() {
        match data_role(context, &data[index]) {
            Some(role) => {
                out.push(role);
                data_roles_from(context, data, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn data_members(
    context: &Context,
    data: &AtLeastTwo<DataProperty>,
) -> Option<AtLeastTwo<ObjectPropertyExpression>> {
    match data_role(context, &data.first) {
        Some(first) => match data_role(context, &data.second) {
            Some(second) => match data_roles_from(context, &data.rest, 0, Vec::new()) {
                Some(rest) => Some(AtLeastTwo {
                    first,
                    second,
                    rest,
                }),
                None => None,
            },
            None => None,
        },
        None => None,
    }
}
fn object_roles_from(
    context: &Context,
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Option<Vec<ObjectPropertyExpression>> {
    if index < roles.len() {
        match object_role(context, &roles[index]) {
            Some(role) => {
                out.push(role);
                object_roles_from(context, roles, index + 1, out)
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
fn object_members(
    context: &Context,
    roles: &AtLeastTwo<ObjectPropertyExpression>,
) -> Option<AtLeastTwo<ObjectPropertyExpression>> {
    match object_role(context, &roles.first) {
        Some(first) => match object_role(context, &roles.second) {
            Some(second) => match object_roles_from(context, &roles.rest, 0, Vec::new()) {
                Some(rest) => Some(AtLeastTwo {
                    first,
                    second,
                    rest,
                }),
                None => None,
            },
            None => None,
        },
        None => None,
    }
}
fn individual_members(individuals: &AtLeastTwo<Individual>) -> Option<AtLeastTwo<Individual>> {
    match object_individual_of(&individuals.first) {
        Some(first) => match object_individual_of(&individuals.second) {
            Some(second) => match individuals_from(&individuals.rest, 0, Vec::new()) {
                Some(rest) => Some(AtLeastTwo {
                    first,
                    second,
                    rest,
                }),
                None => None,
            },
            None => None,
        },
        None => None,
    }
}
/// `out` with every member of the list no data node.
fn member_objects(
    individuals: &AtLeastTwo<Individual>,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match object_assertion(&individuals.first, out) {
        Some(out) => match object_assertion(&individuals.second, out) {
            Some(out) => object_assertions(&individuals.rest, 0, out),
            None => None,
        },
        None => None,
    }
}
/// `out` with the axiom and the individuals of the nominals of the class
/// expressions no data nodes.
fn with_nominals(
    out: Vec<AnnotatedAxiom>,
    axiom: Axiom,
    members: &AtLeastTwo<ClassExpression>,
) -> Option<Vec<AnnotatedAxiom>> {
    match push(out, axiom) {
        Some(out) => nominal_members(members, out),
        None => None,
    }
}
fn domain_or_range(
    context: &Context,
    role: &ObjectPropertyExpression,
    class: &ClassExpression,
    domain: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match (object_role(context, role), encode_class(context, class)) {
        (Some(copy), Some(encoded)) => match nominal_objects(class, out) {
            Some(out) => {
                if universal(role) {
                    push(out, Axiom::SubClassOf(object_class(), encoded))
                } else if domain {
                    push(out, Axiom::ObjectPropertyDomain(copy, encoded))
                } else {
                    push(out, Axiom::ObjectPropertyRange(copy, encoded))
                }
            }
            None => None,
        },
        _ => None,
    }
}
/// `out` with the axiom on a role of the context, made from its copy.
fn role_axiom(
    context: &Context,
    role: &ObjectPropertyExpression,
    kind: u8,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match object_role(context, role) {
        Some(copy) => {
            let axiom = if kind == 0 {
                Axiom::FunctionalObjectProperty(copy)
            } else if kind == 1 {
                Axiom::InverseFunctionalObjectProperty(copy)
            } else if kind == 2 {
                Axiom::IrreflexiveObjectProperty(copy)
            } else if kind == 3 {
                Axiom::SymmetricObjectProperty(copy)
            } else if kind == 4 {
                Axiom::AsymmetricObjectProperty(copy)
            } else {
                Axiom::TransitiveObjectProperty(copy)
            };
            push(out, axiom)
        }
        None => None,
    }
}
/// `out` with an assertion between two individuals along a role, positive or
/// negative, and both individuals no data nodes.
fn related(
    role: ObjectPropertyExpression,
    source: &Individual,
    target: &Individual,
    negative: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match (object_individual_of(source), object_individual_of(target)) {
        (Some(from), Some(to)) => match object_assertion(source, out) {
            Some(out) => match object_assertion(target, out) {
                Some(out) => {
                    if negative {
                        push(out, Axiom::NegativeObjectPropertyAssertion(role, from, to))
                    } else {
                        push(out, Axiom::ObjectPropertyAssertion(role, from, to))
                    }
                }
                None => None,
            },
            None => None,
        },
        _ => None,
    }
}
/// `out` with a data assertion along the role, positive or negative, its
/// individual no data node.
fn valued(
    role: ObjectPropertyExpression,
    source: &Individual,
    value: Individual,
    negative: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match object_individual_of(source) {
        Some(from) => match object_assertion(source, out) {
            Some(out) => {
                if negative {
                    push(
                        out,
                        Axiom::NegativeObjectPropertyAssertion(role, from, value),
                    )
                } else {
                    push(out, Axiom::ObjectPropertyAssertion(role, from, value))
                }
            }
            None => None,
        },
        None => None,
    }
}
/// A copy of a role or role chain of the context.
fn encode_sub(
    context: &Context,
    sub: &SubObjectPropertyExpression,
) -> Option<SubObjectPropertyExpression> {
    match sub {
        SubObjectPropertyExpression::Single(role) => match object_role(context, role) {
            Some(role) => Some(SubObjectPropertyExpression::Single(role)),
            None => None,
        },
        SubObjectPropertyExpression::Chain(roles) => match object_members(context, roles) {
            Some(roles) => Some(SubObjectPropertyExpression::Chain(roles)),
            None => None,
        },
    }
}
/// `out` with the axioms an axiom becomes.
pub(crate) fn encode_axiom(
    context: &Context,
    item: &Axiom,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match item {
        Axiom::Declaration(_) => Some(out),
        Axiom::SubClassOf(sub, sup) => {
            match (encode_object(context, sub), encode_class(context, sup)) {
                (Some(left), Some(right)) => match push(out, Axiom::SubClassOf(left, right)) {
                    Some(out) => match nominal_objects(sub, out) {
                        Some(out) => nominal_objects(sup, out),
                        None => None,
                    },
                    None => None,
                },
                _ => None,
            }
        }
        Axiom::EquivalentClasses(members) => match encode_object_members(context, members) {
            Some(encoded) => with_nominals(out, Axiom::EquivalentClasses(encoded), members),
            None => None,
        },
        Axiom::DisjointClasses(members) => match encode_object_members(context, members) {
            Some(encoded) => with_nominals(out, Axiom::DisjointClasses(encoded), members),
            None => None,
        },
        Axiom::DisjointUnion(class, members) => {
            if is_thing(class) || reserved(&class.iri.spelling) {
                None
            } else {
                match encode_object_members(context, members) {
                    Some(encoded) => with_nominals(
                        out,
                        Axiom::DisjointUnion(
                            Class {
                                iri: Iri {
                                    spelling: copy_bytes(&class.iri.spelling),
                                },
                            },
                            encoded,
                        ),
                        members,
                    ),
                    None => None,
                }
            }
        }
        Axiom::SubObjectPropertyOf(sub, sup) => {
            if sub_universal(sub) && !universal(sup) {
                None
            } else {
                match (encode_sub(context, sub), object_role(context, sup)) {
                    (Some(sub), Some(sup)) => push(out, Axiom::SubObjectPropertyOf(sub, sup)),
                    _ => None,
                }
            }
        }
        Axiom::EquivalentObjectProperties(roles) => {
            if members_universal(roles) {
                None
            } else {
                match object_members(context, roles) {
                    Some(roles) => push(out, Axiom::EquivalentObjectProperties(roles)),
                    None => None,
                }
            }
        }
        Axiom::DisjointObjectProperties(roles) => match object_members(context, roles) {
            Some(roles) => push(out, Axiom::DisjointObjectProperties(roles)),
            None => None,
        },
        Axiom::InverseObjectProperties(first, second) => {
            if universal(first) || universal(second) {
                None
            } else {
                match (object_role(context, first), object_role(context, second)) {
                    (Some(first), Some(second)) => {
                        push(out, Axiom::InverseObjectProperties(first, second))
                    }
                    _ => None,
                }
            }
        }
        Axiom::ObjectPropertyDomain(role, class) => {
            domain_or_range(context, role, class, true, out)
        }
        Axiom::ObjectPropertyRange(role, class) => {
            domain_or_range(context, role, class, false, out)
        }
        Axiom::FunctionalObjectProperty(role) => {
            if universal(role) {
                None
            } else {
                role_axiom(context, role, 0, out)
            }
        }
        Axiom::InverseFunctionalObjectProperty(role) => {
            if universal(role) {
                None
            } else {
                role_axiom(context, role, 1, out)
            }
        }
        Axiom::ReflexiveObjectProperty(role) => match object_role(context, role) {
            Some(copy) => {
                if universal(role) {
                    push(out, Axiom::ReflexiveObjectProperty(copy))
                } else {
                    push(
                        out,
                        Axiom::SubClassOf(object_class(), ClassExpression::ObjectHasSelf(copy)),
                    )
                }
            }
            None => None,
        },
        Axiom::IrreflexiveObjectProperty(role) => role_axiom(context, role, 2, out),
        Axiom::SymmetricObjectProperty(role) => role_axiom(context, role, 3, out),
        Axiom::AsymmetricObjectProperty(role) => role_axiom(context, role, 4, out),
        Axiom::TransitiveObjectProperty(role) => role_axiom(context, role, 5, out),
        Axiom::SubDataPropertyOf(sub, sup) => {
            if is_top_data(sup) {
                if reserved(&sub.iri.spelling) {
                    None
                } else {
                    Some(out)
                }
            } else {
                match (data_role(context, sub), data_role(context, sup)) {
                    (Some(sub), Some(sup)) => push(
                        out,
                        Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(sub), sup),
                    ),
                    _ => None,
                }
            }
        }
        Axiom::EquivalentDataProperties(data) => match data_members(context, data) {
            Some(roles) => push(out, Axiom::EquivalentObjectProperties(roles)),
            None => None,
        },
        Axiom::DisjointDataProperties(data) => match data_members(context, data) {
            Some(roles) => push(out, Axiom::DisjointObjectProperties(roles)),
            None => None,
        },
        Axiom::DataPropertyDomain(property, class) => {
            match (data_role(context, property), encode_class(context, class)) {
                (Some(role), Some(encoded)) => match nominal_objects(class, out) {
                    Some(out) => push(out, Axiom::ObjectPropertyDomain(role, encoded)),
                    None => None,
                },
                _ => None,
            }
        }
        Axiom::DataPropertyRange(property, range) => {
            match (data_role(context, property), encode_range(context, range)) {
                (Some(role), Some(class)) => push(out, Axiom::ObjectPropertyRange(role, class)),
                _ => None,
            }
        }
        Axiom::FunctionalDataProperty(property) => match data_role(context, property) {
            Some(role) => push(out, Axiom::FunctionalObjectProperty(role)),
            None => None,
        },
        Axiom::DatatypeDefinition(_, _) => None,
        Axiom::HasKey(_, _, _) => None,
        Axiom::SameIndividual(individuals) => match individual_members(individuals) {
            Some(encoded) => match push(out, Axiom::SameIndividual(encoded)) {
                Some(out) => member_objects(individuals, out),
                None => None,
            },
            None => None,
        },
        Axiom::DifferentIndividuals(individuals) => match individual_members(individuals) {
            Some(encoded) => match push(out, Axiom::DifferentIndividuals(encoded)) {
                Some(out) => member_objects(individuals, out),
                None => None,
            },
            None => None,
        },
        Axiom::ClassAssertion(class, individual) => {
            match (
                encode_class(context, class),
                object_individual_of(individual),
            ) {
                (Some(encoded), Some(copy)) => match nominal_objects(class, out) {
                    Some(out) => push(
                        out,
                        Axiom::ClassAssertion(and(encoded, object_class()), copy),
                    ),
                    None => None,
                },
                _ => None,
            }
        }
        Axiom::ObjectPropertyAssertion(role, source, target) => match object_role(context, role) {
            Some(copy) => related(copy, source, target, false, out),
            None => None,
        },
        Axiom::NegativeObjectPropertyAssertion(role, source, target) => {
            match object_role(context, role) {
                Some(copy) => related(copy, source, target, true, out),
                None => None,
            }
        }
        Axiom::DataPropertyAssertion(property, source, literal) => {
            match (
                data_role(context, property),
                literal_individual(context, literal),
            ) {
                (Some(role), Some(value)) => valued(role, source, value, false, out),
                _ => None,
            }
        }
        Axiom::NegativeDataPropertyAssertion(property, source, literal) => {
            match (
                data_role(context, property),
                literal_individual(context, literal),
            ) {
                (Some(role), Some(value)) => valued(role, source, value, true, out),
                _ => None,
            }
        }
        Axiom::AnnotationAssertion(_, _, _)
        | Axiom::SubAnnotationPropertyOf(_, _)
        | Axiom::AnnotationPropertyDomain(_, _)
        | Axiom::AnnotationPropertyRange(_, _) => Some(out),
    }
}
fn encode_items(
    context: &Context,
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < items.len() {
        match encode_axiom(context, &items[index].axiom, out) {
            Some(out) => encode_items(context, items, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}

// ---------------------------------------------------------------------------
// The axioms of the encoding itself
// ---------------------------------------------------------------------------

/// `out` with the domain and range of every object property of
/// `context.roles[index..]` no data nodes.
fn role_axioms(
    context: &Context,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < context.roles.len() {
        let domain = ObjectPropertyExpression::Property(ObjectProperty {
            iri: Iri {
                spelling: copy_bytes(&context.roles[index].iri.spelling),
            },
        });
        let range = ObjectPropertyExpression::Property(ObjectProperty {
            iri: Iri {
                spelling: copy_bytes(&context.roles[index].iri.spelling),
            },
        });
        match push(out, Axiom::ObjectPropertyDomain(domain, object_class())) {
            Some(out) => match push(out, Axiom::ObjectPropertyRange(range, object_class())) {
                Some(out) => role_axioms(context, index + 1, out),
                None => None,
            },
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with every data property of `context.data[index..]` relating
/// elements that are no data nodes to data nodes.
fn data_axioms(
    context: &Context,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < context.data.len() {
        match (
            data_role(context, &context.data[index]),
            data_role(context, &context.data[index]),
        ) {
            (Some(domain), Some(range)) => {
                match push(out, Axiom::ObjectPropertyDomain(domain, object_class())) {
                    Some(out) => match push(out, Axiom::ObjectPropertyRange(range, data_class())) {
                        Some(out) => data_axioms(context, index + 1, out),
                        None => None,
                    },
                    None => None,
                }
            }
            _ => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with an axiom on two kinds in use: the first included in the second,
/// or the two disjoint.
fn kinds_axiom(
    kinds: &Kinds,
    first: Kind,
    second: Kind,
    inclusion: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if used(kinds, first) && used(kinds, second) {
        if inclusion {
            push(
                out,
                Axiom::SubClassOf(kind_class(first), kind_class(second)),
            )
        } else {
            push(
                out,
                Axiom::DisjointClasses(AtLeastTwo {
                    first: kind_class(first),
                    second: kind_class(second),
                    rest: Vec::new(),
                }),
            )
        }
    } else {
        Some(out)
    }
}
/// `out` with the booleans as the individuals of the two truth values, if the
/// booleans are in use.
fn truth_axiom(context: &Context, out: Vec<AnnotatedAxiom>) -> Option<Vec<AnnotatedAxiom>> {
    if context.kinds.boolean {
        match (
            value_index(&context.values, &DataValue::Truth(true), 0),
            value_index(&context.values, &DataValue::Truth(false), 0),
        ) {
            (Some(truth), Some(falsity)) => {
                let mut rest = Vec::new();
                rest.push(value_individual(falsity));
                push(
                    out,
                    Axiom::SubClassOf(
                        kind_class(Kind::Boolean),
                        ClassExpression::ObjectOneOf(NonEmpty {
                            first: value_individual(truth),
                            rest,
                        }),
                    ),
                )
            }
            _ => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with the inclusions of the numeric kinds in use: integers are
/// decimals, decimals rationals and rationals reals.
fn number_axioms(kinds: &Kinds, out: Vec<AnnotatedAxiom>) -> Option<Vec<AnnotatedAxiom>> {
    let out = match kinds_axiom(kinds, Kind::Integer, Kind::Decimal, true, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, Kind::Integer, Kind::Rational, true, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, Kind::Integer, Kind::Real, true, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, Kind::Decimal, Kind::Rational, true, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, Kind::Decimal, Kind::Real, true, out) {
        Some(out) => out,
        None => return None,
    };
    kinds_axiom(kinds, Kind::Rational, Kind::Real, true, out)
}
/// `out` with a numeric kind in use apart from the strings, the plain
/// literals and the booleans.
fn apart_axioms(
    kinds: &Kinds,
    kind: Kind,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    let out = match kinds_axiom(kinds, kind, Kind::String, false, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, kind, Kind::Plain, false, out) {
        Some(out) => out,
        None => return None,
    };
    kinds_axiom(kinds, kind, Kind::Boolean, false, out)
}
/// `out` with the inclusions and disjointness of the kinds in use and the
/// booleans.
fn kind_axioms(context: &Context, out: Vec<AnnotatedAxiom>) -> Option<Vec<AnnotatedAxiom>> {
    let kinds = &context.kinds;
    let out = match number_axioms(kinds, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, Kind::String, Kind::Plain, true, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match apart_axioms(kinds, Kind::Integer, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match apart_axioms(kinds, Kind::Decimal, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match apart_axioms(kinds, Kind::Rational, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match apart_axioms(kinds, Kind::Real, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, Kind::String, Kind::Boolean, false, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kinds_axiom(kinds, Kind::Plain, Kind::Boolean, false, out) {
        Some(out) => out,
        None => return None,
    };
    truth_axiom(context, out)
}
/// Bit `position` of `value`.
fn bit(value: usize, position: usize) -> bool {
    if position == 0 {
        value % 2 == 1
    } else {
        bit(value / 2, position - 1)
    }
}
/// The number of bits that tell `count` values apart: the least `bits` with
/// `count ≤ 2^bits`, where `power` is `2^bits`.
fn bits_for(count: usize, bits: usize, power: usize) -> usize {
    if power < count {
        if power <= usize::MAX / 2 {
            bits_for(count, bits + 1, power * 2)
        } else {
            bits + 1
        }
    } else {
        bits
    }
}
/// `out` with the individual in the class, or in its complement.
fn member(
    class: ClassExpression,
    positive: bool,
    individual: Individual,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if positive {
        push(out, Axiom::ClassAssertion(class, individual))
    } else {
        push(
            out,
            Axiom::ClassAssertion(
                ClassExpression::ObjectComplementOf(Box::new(class)),
                individual,
            ),
        )
    }
}
/// `out` with the literal value at `index` in the class of the kind, or in its
/// complement, if the kind is in use.
fn kind_member(
    context: &Context,
    kind: Kind,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if used(&context.kinds, kind) && index < context.values.len() {
        member(
            kind_class(kind),
            in_kind(&context.values[index], kind),
            value_individual(index),
            out,
        )
    } else {
        Some(out)
    }
}
/// `out` with the literal value at `index` in the bit classes
/// `position..bits` or their complements.
fn bit_members(
    index: usize,
    position: usize,
    bits: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if position < bits {
        match member(
            bit_class(position),
            bit(index, position),
            value_individual(index),
            out,
        ) {
            Some(out) => bit_members(index, position + 1, bits, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with a numeric literal value at `index` in its own closed cut and
/// outside its own open cut, when numbers are ordered.
/// `out` with the literal value at `index` in the class of every cut of
/// `context.cuts[cut..]` that contains its number, and outside the others.
fn cut_memberships(
    context: &Context,
    index: usize,
    cut: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if (index < context.values.len()) & (cut < context.cuts.len()) {
        match member(
            cut_class(cut),
            in_cut(&context.cuts[cut], &context.values[index]),
            value_individual(index),
            out,
        ) {
            Some(out) => cut_memberships(context, index, cut + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
fn cut_members(
    context: &Context,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if context.kinds.ordered & (index < context.values.len()) {
        if numeric(&context.values[index]) {
            cut_memberships(context, index, 0, out)
        } else {
            Some(out)
        }
    } else {
        Some(out)
    }
}
fn number_members(
    context: &Context,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match kind_member(context, Kind::Rational, index, out) {
        Some(out) => match kind_member(context, Kind::Real, index, out) {
            Some(out) => cut_members(context, index, out),
            None => None,
        },
        None => None,
    }
}
/// `out` with the classes of the literal values from `index` on: `D`, each
/// kind class in use or its complement, the classes of the numbers at and
/// above a numeric value, and each bit class or its complement.
fn value_axioms(
    context: &Context,
    index: usize,
    bits: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < context.values.len() {
        let out = match push(
            out,
            Axiom::ClassAssertion(data_class(), value_individual(index)),
        ) {
            Some(out) => out,
            None => return None,
        };
        let out = match kind_member(context, Kind::Integer, index, out) {
            Some(out) => out,
            None => return None,
        };
        let out = match kind_member(context, Kind::Decimal, index, out) {
            Some(out) => out,
            None => return None,
        };
        let out = match kind_member(context, Kind::String, index, out) {
            Some(out) => out,
            None => return None,
        };
        let out = match kind_member(context, Kind::Plain, index, out) {
            Some(out) => out,
            None => return None,
        };
        let out = match kind_member(context, Kind::Boolean, index, out) {
            Some(out) => out,
            None => return None,
        };
        let out = match number_members(context, index, out) {
            Some(out) => out,
            None => return None,
        };
        match bit_members(index, 0, bits, out) {
            Some(out) => value_axioms(context, index + 1, bits, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The natural number `count`.
fn natural_of(count: usize) -> Natural {
    if count == 0 {
        Natural::Zero
    } else {
        Natural::Succ(Box::new(natural_of(count - 1)))
    }
}
/// `out` with the axiom on the integers in the cut at `low` and outside the
/// cut at `high`, neighbours of different numbers in the order of the cuts:
/// none when there are none, and at most their number at any element along
/// `U` when there are fewer than `capacity`; they are counted up to one more
/// than the capacity.
/// Whether a literal value is an integer in the cut `low` and outside the cut
/// `high`.
fn in_run(low: &Cut, high: &Cut, value: &DataValue) -> bool {
    in_kind(value, Kind::Integer) & in_cut(low, value) & !in_cut(high, value)
}
/// `found` with `individual` added.
fn add_named(
    found: Option<NonEmpty<Individual>>,
    individual: Individual,
) -> Option<NonEmpty<Individual>> {
    match found {
        None => Some(NonEmpty {
            first: individual,
            rest: Vec::new(),
        }),
        Some(mut list) => {
            if list.rest.len() < usize::MAX {
                list.rest.push(individual);
            }
            Some(list)
        }
    }
}
/// `found` with the individuals of the literal values of `values[index..]`
/// that are integers between the cuts `low` and `high`.
fn run_literals(
    context: &Context,
    low: &Cut,
    high: &Cut,
    index: usize,
    found: Option<NonEmpty<Individual>>,
) -> Option<NonEmpty<Individual>> {
    if index < context.values.len() {
        if in_run(low, high, &context.values[index]) {
            run_literals(
                context,
                low,
                high,
                index + 1,
                add_named(found, value_individual(index)),
            )
        } else {
            run_literals(context, low, high, index + 1, found)
        }
    } else {
        found
    }
}
/// `count` plus the number of literal values of `values[index..]` that are
/// integers between the cuts `low` and `high`.
fn run_count(context: &Context, low: &Cut, high: &Cut, index: usize, count: usize) -> usize {
    if index < context.values.len() {
        if in_run(low, high, &context.values[index]) & (count < usize::MAX) {
            run_count(context, low, high, index + 1, count + 1)
        } else {
            run_count(context, low, high, index + 1, count)
        }
    } else {
        count
    }
}
/// The integers between `low` and `high` that are no literal values: none
/// when there are none, a class of the literal values when every integer
/// there is one.
fn no_free_integers(low: usize, high: usize, named: Option<NonEmpty<Individual>>) -> Axiom {
    match named {
        None => Axiom::SubClassOf(
            and(kind_class(Kind::Integer), cut_class(low)),
            cut_class(high),
        ),
        Some(list) => Axiom::SubClassOf(
            and3(
                kind_class(Kind::Integer),
                cut_class(low),
                not(cut_class(high)),
            ),
            ClassExpression::ObjectOneOf(list),
        ),
    }
}
/// The integers between `low` and `high` that are no literal values.
fn free_integers(low: usize, high: usize, named: Option<NonEmpty<Individual>>) -> ClassExpression {
    match named {
        None => and3(
            kind_class(Kind::Integer),
            cut_class(low),
            not(cut_class(high)),
        ),
        Some(list) => and(
            and3(
                kind_class(Kind::Integer),
                cut_class(low),
                not(cut_class(high)),
            ),
            not(ClassExpression::ObjectOneOf(list)),
        ),
    }
}
/// `out` with the axiom on the integers between the neighbouring cuts `low`
/// and `high` of different numbers that are no literal values: none of them
/// when there are none, and at most their number at any element along `U`
/// when there are fewer than `capacity`; they are counted up to one more than
/// the capacity.
fn gap_axiom(
    context: &Context,
    low: usize,
    high: usize,
    capacity: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if (low < context.cuts.len()) & (high < context.cuts.len()) & (capacity < usize::MAX / 16) {
        let named = run_count(context, &context.cuts[low], &context.cuts[high], 0, 0);
        if named < usize::MAX / 16 - capacity {
            let size = run_size(
                &context.cuts[low],
                &context.cuts[high],
                capacity + 1 + named,
            );
            if named <= size {
                let free = size - named;
                let found = run_literals(context, &context.cuts[low], &context.cuts[high], 0, None);
                if free == 0 {
                    push(out, no_free_integers(low, high, found))
                } else if free < capacity {
                    push(
                        out,
                        Axiom::SubClassOf(
                            thing(),
                            ClassExpression::ObjectMaxCardinality(
                                natural_of(free),
                                data_super(),
                                Some(Box::new(free_integers(low, high, found))),
                            ),
                        ),
                    )
                } else {
                    Some(out)
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}
fn between_axiom(
    context: &Context,
    low: usize,
    high: usize,
    capacity: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if (low < context.cuts.len()) & (high < context.cuts.len()) {
        if same_value(&context.cuts[low].value, &context.cuts[high].value) {
            match value_index(&context.values, &context.cuts[low].value, 0) {
                Some(index) => push(
                    out,
                    Axiom::SubClassOf(
                        and(cut_class(low), not(cut_class(high))),
                        ClassExpression::ObjectOneOf(NonEmpty {
                            first: value_individual(index),
                            rest: Vec::new(),
                        }),
                    ),
                ),
                None => None,
            }
        } else if context.kinds.integer {
            gap_axiom(context, low, high, capacity, out)
        } else {
            Some(out)
        }
    } else {
        None
    }
}
/// `out` with the axioms of the cuts from `order[position..]` on, in order:
/// each cut after the first inside the one before it, with the axiom between
/// the two.
fn chain_axioms(
    context: &Context,
    order: &Vec<usize>,
    position: usize,
    capacity: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if (0 < position) & (position < order.len()) {
        let low = order[position - 1];
        let high = order[position];
        match push(out, Axiom::SubClassOf(cut_class(high), cut_class(low))) {
            Some(out) => match between_axiom(context, low, high, capacity, out) {
                Some(out) => chain_axioms(context, order, position + 1, capacity, out),
                None => None,
            },
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with every data property of `context.data[index..]` below `U`.
fn super_axioms(
    context: &Context,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < context.data.len() {
        match data_role(context, &context.data[index]) {
            Some(role) => match push(
                out,
                Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(role), data_super()),
            ) {
                Some(out) => super_axioms(context, index + 1, out),
                None => None,
            },
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with the first cut inside the reals, if there is a cut.
fn least_axiom(order: &Vec<usize>, out: Vec<AnnotatedAxiom>) -> Option<Vec<AnnotatedAxiom>> {
    if 0 < order.len() {
        push(
            out,
            Axiom::SubClassOf(cut_class(order[0]), kind_class(Kind::Real)),
        )
    } else {
        Some(out)
    }
}
/// Whether a literal value is no number or a number short enough to compare.
fn value_fits(value: &DataValue) -> bool {
    if numeric(value) {
        fits(value)
    } else {
        true
    }
}
/// Whether every literal value of `values[index..]` is no number or a number
/// short enough to compare.
fn values_fit(context: &Context, index: usize) -> bool {
    if index < context.values.len() {
        if value_fits(&context.values[index]) {
            values_fit(context, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the cuts are of numbers short enough to compare, and every number
/// among the literal values has both its cuts.
fn encodable(context: &Context) -> bool {
    cuts_fit(&context.cuts, 0) & values_fit(context, 0)
}
/// `out` with the axioms of the ordered numbers, when numbers are ordered: the
/// first cut inside the reals and the chain of the cuts, and when the integers
/// are in use, every data property below `U`.
fn region_axioms(
    context: &Context,
    capacity: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if context.kinds.ordered {
        let order = cut_order(&context.cuts);
        let out = match least_axiom(&order, out) {
            Some(out) => out,
            None => return None,
        };
        let out = match chain_axioms(context, &order, 1, capacity, out) {
            Some(out) => out,
            None => return None,
        };
        if context.kinds.integer {
            super_axioms(context, 0, out)
        } else {
            Some(out)
        }
    } else {
        Some(out)
    }
}
/// The encoding of a closure in the context: its axioms' encodings, then the
/// axioms of the object and data properties, of the kinds, of the ordered
/// numbers and of the literal values, and the further individual that is no
/// data node. `capacity` bounds the counts of the data restrictions of the
/// closure and its questions together.
pub fn encode(
    context: &Context,
    capacity: usize,
    items: &Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if !encodable(context) {
        return None;
    }
    let out = match encode_items(context, items, 0, Vec::new()) {
        Some(out) => out,
        None => return None,
    };
    let out = match role_axioms(context, 0, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match data_axioms(context, 0, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match kind_axioms(context, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match region_axioms(context, capacity, out) {
        Some(out) => out,
        None => return None,
    };
    match value_axioms(context, 0, bits_for(context.values.len(), 0, 1), out) {
        Some(out) => push(
            out,
            Axiom::ClassAssertion(object_class(), object_individual()),
        ),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The individuals of a closure
// ---------------------------------------------------------------------------

/// `nodes` with the individuals of `individuals[index..]`.
fn list_individuals(
    nodes: Vec<Individual>,
    individuals: &Vec<Individual>,
    index: usize,
) -> Option<Vec<Individual>> {
    if index < individuals.len() {
        match intern(nodes, &individuals[index]) {
            Some(nodes) => list_individuals(nodes, individuals, index + 1),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// `nodes` with the individuals of the nominals and value restrictions of a
/// class expression.
pub(crate) fn class_individuals(
    nodes: Vec<Individual>,
    class: &ClassExpression,
) -> Option<Vec<Individual>> {
    match class {
        ClassExpression::ObjectIntersectionOf(members)
        | ClassExpression::ObjectUnionOf(members) => members_individuals(nodes, members),
        ClassExpression::ObjectComplementOf(inner) => class_individuals(nodes, inner),
        ClassExpression::ObjectOneOf(individuals) => match intern(nodes, &individuals.first) {
            Some(nodes) => list_individuals(nodes, &individuals.rest, 0),
            None => None,
        },
        ClassExpression::ObjectSomeValuesFrom(_, filler)
        | ClassExpression::ObjectAllValuesFrom(_, filler) => class_individuals(nodes, filler),
        ClassExpression::ObjectHasValue(_, individual) => intern(nodes, individual),
        ClassExpression::ObjectMinCardinality(_, _, filler)
        | ClassExpression::ObjectMaxCardinality(_, _, filler)
        | ClassExpression::ObjectExactCardinality(_, _, filler) => match filler {
            Some(filler) => class_individuals(nodes, filler),
            None => Some(nodes),
        },
        _ => Some(nodes),
    }
}
fn classes_individuals(
    nodes: Vec<Individual>,
    classes: &Vec<ClassExpression>,
    index: usize,
) -> Option<Vec<Individual>> {
    if index < classes.len() {
        match class_individuals(nodes, &classes[index]) {
            Some(nodes) => classes_individuals(nodes, classes, index + 1),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
fn members_individuals(
    nodes: Vec<Individual>,
    members: &AtLeastTwo<ClassExpression>,
) -> Option<Vec<Individual>> {
    match class_individuals(nodes, &members.first) {
        Some(nodes) => match class_individuals(nodes, &members.second) {
            Some(nodes) => classes_individuals(nodes, &members.rest, 0),
            None => None,
        },
        None => None,
    }
}
/// `nodes` with the individuals an axiom mentions.
pub(crate) fn axiom_individuals(nodes: Vec<Individual>, axiom: &Axiom) -> Option<Vec<Individual>> {
    match axiom {
        Axiom::SubClassOf(sub, sup) => match class_individuals(nodes, sub) {
            Some(nodes) => class_individuals(nodes, sup),
            None => None,
        },
        Axiom::EquivalentClasses(members)
        | Axiom::DisjointClasses(members)
        | Axiom::DisjointUnion(_, members) => members_individuals(nodes, members),
        Axiom::ObjectPropertyDomain(_, class)
        | Axiom::ObjectPropertyRange(_, class)
        | Axiom::DataPropertyDomain(_, class) => class_individuals(nodes, class),
        Axiom::SameIndividual(individuals) | Axiom::DifferentIndividuals(individuals) => {
            match intern(nodes, &individuals.first) {
                Some(nodes) => match intern(nodes, &individuals.second) {
                    Some(nodes) => list_individuals(nodes, &individuals.rest, 0),
                    None => None,
                },
                None => None,
            }
        }
        Axiom::ClassAssertion(class, individual) => match intern(nodes, individual) {
            Some(nodes) => class_individuals(nodes, class),
            None => None,
        },
        Axiom::ObjectPropertyAssertion(_, source, target)
        | Axiom::NegativeObjectPropertyAssertion(_, source, target) => {
            match intern(nodes, source) {
                Some(nodes) => intern(nodes, target),
                None => None,
            }
        }
        Axiom::DataPropertyAssertion(_, source, _)
        | Axiom::NegativeDataPropertyAssertion(_, source, _) => intern(nodes, source),
        _ => Some(nodes),
    }
}
/// `nodes` with the individuals that the axioms of `items[index..]` mention.
pub(crate) fn items_individuals(
    nodes: Vec<Individual>,
    items: &Vec<AnnotatedAxiom>,
    index: usize,
) -> Option<Vec<Individual>> {
    if index < items.len() {
        match axiom_individuals(nodes, &items[index].axiom) {
            Some(nodes) => items_individuals(nodes, items, index + 1),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// Whether the named individual is among `nodes` and its name is not the
/// encoding's.
fn named_known(nodes: &Vec<Individual>, individual: &NamedIndividual) -> bool {
    if reserved(&individual.iri.spelling) {
        false
    } else {
        position(
            nodes,
            &Individual::Named(NamedIndividual {
                iri: Iri {
                    spelling: copy_bytes(&individual.iri.spelling),
                },
            }),
            0,
        ) != 0
    }
}
/// Whether the individual is named and among `nodes`.
fn individual_known(nodes: &Vec<Individual>, individual: &Individual) -> bool {
    match individual {
        Individual::Named(_) => position(nodes, individual, 0) != 0,
        Individual::Anonymous(_) => false,
    }
}
fn individuals_known(nodes: &Vec<Individual>, individuals: &Vec<Individual>, index: usize) -> bool {
    if index < individuals.len() {
        individual_known(nodes, &individuals[index])
            && individuals_known(nodes, individuals, index + 1)
    } else {
        true
    }
}
/// Whether every individual of the nominals and value restrictions of a class
/// expression is named and among `nodes`.
fn class_known(nodes: &Vec<Individual>, class: &ClassExpression) -> bool {
    match class {
        ClassExpression::ObjectIntersectionOf(members)
        | ClassExpression::ObjectUnionOf(members) => {
            class_known(nodes, &members.first)
                && class_known(nodes, &members.second)
                && classes_known(nodes, &members.rest, 0)
        }
        ClassExpression::ObjectComplementOf(inner) => class_known(nodes, inner),
        ClassExpression::ObjectOneOf(individuals) => {
            individual_known(nodes, &individuals.first)
                && individuals_known(nodes, &individuals.rest, 0)
        }
        ClassExpression::ObjectSomeValuesFrom(_, filler)
        | ClassExpression::ObjectAllValuesFrom(_, filler) => class_known(nodes, filler),
        ClassExpression::ObjectHasValue(_, individual) => individual_known(nodes, individual),
        ClassExpression::ObjectMinCardinality(_, _, filler)
        | ClassExpression::ObjectMaxCardinality(_, _, filler)
        | ClassExpression::ObjectExactCardinality(_, _, filler) => match filler {
            Some(filler) => class_known(nodes, filler),
            None => true,
        },
        _ => true,
    }
}
fn classes_known(nodes: &Vec<Individual>, classes: &Vec<ClassExpression>, index: usize) -> bool {
    if index < classes.len() {
        class_known(nodes, &classes[index]) && classes_known(nodes, classes, index + 1)
    } else {
        true
    }
}

// ---------------------------------------------------------------------------
// Queries
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The counts of the data restrictions
// ---------------------------------------------------------------------------

/// The cap on the counts of data restrictions: a closure and its questions
/// together must count fewer values.
pub(crate) const LIMIT: usize = usize::MAX / 16;
/// Room for the counts of the data restrictions of the questions to a
/// prepared closure.
const QUESTION_ROOM: usize = 64;
/// `total + amount`, or `LIMIT` when that is not less.
pub(crate) fn add_count(total: usize, amount: usize) -> usize {
    if (total < LIMIT) & (amount < LIMIT) {
        if total + amount < LIMIT {
            total + amount
        } else {
            LIMIT
        }
    } else {
        LIMIT
    }
}
/// `total` plus a natural number, capped at `LIMIT`.
fn natural_count(value: &Natural, total: usize) -> usize {
    match value {
        Natural::Zero => total,
        Natural::Succ(inner) => natural_count(inner, add_count(total, 1)),
    }
}
/// `total` plus the counts of the data restrictions of a class expression,
/// each restriction counting the values it is decided by, capped at `LIMIT`.
pub(crate) fn class_count(class: &ClassExpression, total: usize) -> usize {
    match class {
        ClassExpression::Class(_) => total,
        ClassExpression::ObjectIntersectionOf(members)
        | ClassExpression::ObjectUnionOf(members) => members_count(members, total),
        ClassExpression::ObjectComplementOf(inner) => class_count(inner, total),
        ClassExpression::ObjectOneOf(_) => total,
        ClassExpression::ObjectSomeValuesFrom(_, filler)
        | ClassExpression::ObjectAllValuesFrom(_, filler) => class_count(filler, total),
        ClassExpression::ObjectHasValue(_, _) => total,
        ClassExpression::ObjectHasSelf(_) => total,
        ClassExpression::ObjectMinCardinality(_, _, filler)
        | ClassExpression::ObjectMaxCardinality(_, _, filler)
        | ClassExpression::ObjectExactCardinality(_, _, filler) => match filler {
            Some(filler) => class_count(filler, total),
            None => total,
        },
        ClassExpression::DataSomeValuesFrom(_, _)
        | ClassExpression::DataAllValuesFrom(_, _)
        | ClassExpression::DataHasValue(_, _) => add_count(total, 1),
        ClassExpression::DataMinCardinality(count, _, _) => natural_count(count, total),
        ClassExpression::DataMaxCardinality(count, _, _) => {
            natural_count(count, add_count(total, 1))
        }
        ClassExpression::DataExactCardinality(count, _, _) => {
            natural_count(count, natural_count(count, add_count(total, 1)))
        }
    }
}
fn classes_count(classes: &Vec<ClassExpression>, index: usize, total: usize) -> usize {
    if index < classes.len() {
        classes_count(classes, index + 1, class_count(&classes[index], total))
    } else {
        total
    }
}
fn members_count(members: &AtLeastTwo<ClassExpression>, total: usize) -> usize {
    classes_count(
        &members.rest,
        0,
        class_count(&members.second, class_count(&members.first, total)),
    )
}
/// `total` plus the counts of the data restrictions of an axiom's class
/// expressions.
fn axiom_count(axiom: &Axiom, total: usize) -> usize {
    match axiom {
        Axiom::SubClassOf(sub, sup) => class_count(sup, class_count(sub, total)),
        Axiom::EquivalentClasses(members)
        | Axiom::DisjointClasses(members)
        | Axiom::DisjointUnion(_, members) => members_count(members, total),
        Axiom::ObjectPropertyDomain(_, class)
        | Axiom::ObjectPropertyRange(_, class)
        | Axiom::DataPropertyDomain(_, class)
        | Axiom::ClassAssertion(class, _) => class_count(class, total),
        _ => total,
    }
}
pub(crate) fn items_count(items: &Vec<AnnotatedAxiom>, index: usize, total: usize) -> usize {
    if index < items.len() {
        items_count(items, index + 1, axiom_count(&items[index].axiom, total))
    } else {
        total
    }
}

// ---------------------------------------------------------------------------
// The queries
// ---------------------------------------------------------------------------

/// A closure prepared for the queries: as it is when it has no data
/// properties, literals, datatypes or keys, otherwise its context, the
/// individuals it mentions, its encoding and the room its encoding leaves for
/// the counts of the data restrictions of a question, and for a closure with
/// keys the same with its keys' class expressions included and its encoding
/// with the keys (`key_ontology`).
pub enum Prepared {
    Plain(shi_ontology::Prepared),
    Encoded(Context, Vec<Individual>, shi_ontology::Prepared, usize),
    Keyed(Context, Vec<Individual>, shi_ontology::Prepared, usize),
}
/// Whether the context has no data properties, literal values or datatypes.
fn data_free(context: &Context) -> bool {
    context.data.len() == 0
        && context.values.len() == 0
        && !context.kinds.integer
        && !context.kinds.decimal
        && !context.kinds.string
        && !context.kinds.plain
        && !context.kinds.boolean
        && !context.kinds.real
        && !context.kinds.rational
        && !context.kinds.ordered
}
/// The closure prepared in the context: encoded with its keys when it has
/// keys, as it is when the context has no data, and otherwise encoded; with
/// `room` for the counts of a question's data restrictions.
fn prepare_in(items: &Vec<AnnotatedAxiom>, context: Context, room: usize) -> Option<Prepared> {
    if key_ontology::has_keys(items, 0) {
        key_ontology::prepare(items, context, room)
    } else if data_free(&context) {
        match shi_ontology::prepare(items) {
            Some(prepared) => Some(Prepared::Plain(prepared)),
            None => None,
        }
    } else {
        let capacity = add_count(items_count(items, 0, 0), room);
        if capacity < LIMIT {
            match (
                encode(&context, capacity, items),
                items_individuals(Vec::new(), items, 0),
            ) {
                (Some(encoded), Some(nodes)) => match shi_ontology::prepare(&encoded) {
                    Some(prepared) => Some(Prepared::Encoded(context, nodes, prepared, room)),
                    None => None,
                },
                _ => None,
            }
        } else {
            None
        }
    }
}
/// Prepare a closure for queries about it; a query that uses a literal value,
/// datatype, object or data property outside the closure, or whose data
/// restrictions count more than 64 values, gets no answer.
pub fn prepare(items: &Vec<AnnotatedAxiom>) -> Option<Prepared> {
    prepare_in(items, finished(closure_context(items)), QUESTION_ROOM)
}
/// Whether the prepared closure has a model.
pub fn prepared_consistent(prepared: &Prepared) -> Option<bool> {
    match prepared {
        Prepared::Plain(prepared) => shi_ontology::prepared_consistent(prepared),
        Prepared::Encoded(_, _, prepared, _) => shi_ontology::prepared_consistent(prepared),
        Prepared::Keyed(_, _, prepared, _) => shi_ontology::prepared_consistent(prepared),
    }
}
/// Whether some model of the prepared closure has an instance of the class
/// expression.
pub fn prepared_class_satisfiable(prepared: &Prepared, class: &ClassExpression) -> Option<bool> {
    match prepared {
        Prepared::Plain(prepared) => shi_ontology::prepared_class_satisfiable(prepared, class),
        Prepared::Encoded(context, nodes, prepared, room) => {
            if !class_known(nodes, class) {
                return None;
            }
            if *room < class_count(class, 0) {
                return None;
            }
            match encode_class(context, class) {
                Some(encoded) => shi_ontology::prepared_class_satisfiable(
                    prepared,
                    &and(encoded, object_class()),
                ),
                None => None,
            }
        }
        Prepared::Keyed(context, nodes, prepared, room) => {
            if !class_known(nodes, class) {
                return None;
            }
            if *room < class_count(class, 0) {
                return None;
            }
            match encode_class(context, class) {
                Some(encoded) => shi_ontology::prepared_class_satisfiable(
                    prepared,
                    &and(encoded, object_class()),
                ),
                None => None,
            }
        }
    }
}
/// Whether every instance of `sub` is an instance of `sup` in every model of
/// the prepared closure.
pub fn prepared_subsumed(
    prepared: &Prepared,
    sub: &ClassExpression,
    sup: &ClassExpression,
) -> Option<bool> {
    match prepared {
        Prepared::Plain(prepared) => shi_ontology::prepared_subsumed(prepared, sub, sup),
        Prepared::Encoded(context, nodes, prepared, room) => {
            if !(class_known(nodes, sub) && class_known(nodes, sup)) {
                return None;
            }
            if *room < class_count(sup, class_count(sub, 0)) {
                return None;
            }
            match (encode_class(context, sub), encode_class(context, sup)) {
                (Some(sub), Some(sup)) => {
                    shi_ontology::prepared_subsumed(prepared, &and(sub, object_class()), &sup)
                }
                _ => None,
            }
        }
        Prepared::Keyed(context, nodes, prepared, room) => {
            if !(class_known(nodes, sub) && class_known(nodes, sup)) {
                return None;
            }
            if *room < class_count(sup, class_count(sub, 0)) {
                return None;
            }
            match (encode_class(context, sub), encode_class(context, sup)) {
                (Some(sub), Some(sup)) => {
                    shi_ontology::prepared_subsumed(prepared, &and(sub, object_class()), &sup)
                }
                _ => None,
            }
        }
    }
}
/// Whether the named individual is an instance of the class expression in
/// every model of the prepared closure; for a closure with keys only about an
/// individual the closure names, since keys apply to the named individuals of
/// the vocabulary.
pub fn prepared_instance_of(
    prepared: &Prepared,
    individual: &NamedIndividual,
    class: &ClassExpression,
) -> Option<bool> {
    match prepared {
        Prepared::Plain(prepared) => {
            shi_ontology::prepared_instance_of(prepared, individual, class)
        }
        Prepared::Encoded(context, nodes, prepared, room) => {
            if reserved(&individual.iri.spelling) || !class_known(nodes, class) {
                return None;
            }
            if *room < class_count(class, 0) {
                return None;
            }
            match encode_class(context, class) {
                Some(encoded) => shi_ontology::prepared_instance_of(
                    prepared,
                    individual,
                    &or(encoded, data_class()),
                ),
                None => None,
            }
        }
        Prepared::Keyed(context, nodes, prepared, room) => {
            if !named_known(nodes, individual) || !class_known(nodes, class) {
                return None;
            }
            if *room < class_count(class, 0) {
                return None;
            }
            match encode_class(context, class) {
                Some(encoded) => shi_ontology::prepared_instance_of(
                    prepared,
                    individual,
                    &or(encoded, data_class()),
                ),
                None => None,
            }
        }
    }
}
/// Whether the closure has a model, for every datatype map that is the OWL 2
/// map on the datatypes of `datatypes`.
pub fn consistent(items: &Vec<AnnotatedAxiom>) -> Option<bool> {
    match prepare_in(items, finished(closure_context(items)), 0) {
        Some(prepared) => prepared_consistent(&prepared),
        None => None,
    }
}
/// Whether some model of the closure has an instance of the class expression.
pub fn class_satisfiable(items: &Vec<AnnotatedAxiom>, class: &ClassExpression) -> Option<bool> {
    let context = finished(class_context(closure_context(items), class));
    match prepare_in(items, context, class_count(class, 0)) {
        Some(prepared) => prepared_class_satisfiable(&prepared, class),
        None => None,
    }
}
/// Whether every instance of `sub` is an instance of `sup` in every model of
/// the closure.
pub fn subsumed(
    items: &Vec<AnnotatedAxiom>,
    sub: &ClassExpression,
    sup: &ClassExpression,
) -> Option<bool> {
    let context = finished(class_context(
        class_context(closure_context(items), sub),
        sup,
    ));
    match prepare_in(items, context, class_count(sup, class_count(sub, 0))) {
        Some(prepared) => prepared_subsumed(&prepared, sub, sup),
        None => None,
    }
}
/// Whether the named individual is an instance of the class expression in
/// every model of the closure.
pub fn instance_of(
    items: &Vec<AnnotatedAxiom>,
    individual: &NamedIndividual,
    class: &ClassExpression,
) -> Option<bool> {
    let context = finished(class_context(closure_context(items), class));
    match prepare_in(items, context, class_count(class, 0)) {
        Some(prepared) => prepared_instance_of(&prepared, individual, class),
        None => None,
    }
}
