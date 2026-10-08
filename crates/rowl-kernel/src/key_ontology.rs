//! Keys (`HasKey`) in the ontology queries, by an encoding into the SROIQ
//! axioms that `data_ontology` hands to `shi_ontology`.
//!
//! A key `HasKey(CE (P1 … Pm) (Q1 … Qn))` says that two named instances of `CE`
//! that share a named `Pi`-value for every `i` and a `Qj`-value for every `j` are
//! equal (OWL 2 Direct Semantics, Table 9). Only named individuals take part,
//! and the named elements of a model are the individuals of its vocabulary, so
//! the encoding marks every named individual of the closure with a fresh class
//! `N` (whose elements are no data nodes) and asks every key of named elements
//! only. A data property `Qj` counts by the role of its data encoding, along
//! which any data value is shared, named or not:
//!
//! - a key with one property `P`, when the closure has no transitive property
//!   and no property chain, becomes `N ⊑ ≤1 P⁻.(CE ⊓ N)`: a named value has at
//!   most one named instance of `CE` as its `P`-predecessor; for one data
//!   property `Q`, `D ⊑ ≤1 Q⁻.(CE ⊓ N)` for every data value. The completion
//!   forest decides this with its choose rule and its merges;
//! - every other key becomes, with a fresh role `mark` whose self loops mark the
//!   named elements (`N ⊑ ∃mark.Self`) and for every key property `Pi` a fresh
//!   role `share(Pi)` with `Pi ∘ mark ∘ Pi⁻ ⊑ share(Pi)` (two elements that share
//!   a named `Pi`-value), one assertion at every named individual `x`:
//!   `x : ∀share(P1).(¬N ⊔ ¬CE ⊔ {x} ⊔ ∀share(P2)⁻.¬{x} ⊔ … ⊔
//!   ∀share(Pm)⁻.¬{x} ⊔ ∀share(P1)⁻.(¬{x} ⊔ ¬CE))`: if `x` is in `CE`, every
//!   named instance of `CE` that shares a named value with `x` along every key
//!   property is `x`. The last disjunct says, at an element that shares a value
//!   with `x` along `P1`, that `x` is not in `CE`, so the case split on `CE` at
//!   `x` happens only where an element shares a value with `x`, and not at every
//!   named individual. When a key that is not counted has a data property,
//!   `D ⊑ ∃mark.Self` marks the data values too, and the roles of the data
//!   properties take part like the object properties.
//!
//! Both forms hold in a model of the encoding exactly when the key holds for
//! the named individuals, so the encoding has a model exactly when the closure
//! has one in which every named individual of the closure is named: a model of
//! the encoding gives an OWL model whose named elements are the closure's named
//! individuals, and an OWL model, with `N` its named elements, `mark` their self
//! loops and `share(P)` the pairs that share a named `P`-value, gives a model of
//! the encoding.
//!
//! The encoding's own names start with the byte 0 and the tag `K`: `N` is
//! `[0, K]`, `mark` is `[0, K, R]` and `share(P)` is `[0, K, S]` followed by 0
//! for a named property or 1 for an inverse one and the property's name.
//!
//! `None` means that a key has no property, the universal role or the top or
//! bottom data property, that a key has a data property while numbers are
//! ordered (their bounded runs of integers would need every value named), that
//! a name is too long, or that the data encoding of the rest of the closure
//! gives no answer.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::manual_map,
    clippy::needless_return,
    clippy::too_many_arguments,
    clippy::vec_init_then_push,
    clippy::len_zero,
    clippy::match_like_matches_macro,
    clippy::if_same_then_else
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::concepts::{copy_individual, copy_role};
use crate::data_ontology::{self, Context, Prepared};
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, Class, ClassExpression, DataProperty, Individual, Iri,
    NonEmpty, ObjectProperty, ObjectPropertyExpression, SubObjectPropertyExpression,
};
use crate::probes::Natural;
use crate::shi_ontology;

// ---------------------------------------------------------------------------
// The keys of a closure
// ---------------------------------------------------------------------------

/// Whether the axiom is a key.
fn is_key(axiom: &Axiom) -> bool {
    match axiom {
        Axiom::HasKey(_, _, _) => true,
        _ => false,
    }
}
/// Whether one of `items[index..]` is a key.
pub fn has_keys(items: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < items.len() {
        if is_key(&items[index].axiom) {
            true
        } else {
            has_keys(items, index + 1)
        }
    } else {
        false
    }
}
/// The context with the class expression and the properties of a key.
fn key_context(context: Context, axiom: &Axiom) -> Context {
    match axiom {
        Axiom::HasKey(class, objects, data) => {
            let context = data_ontology::class_context(context, class);
            let context = data_ontology::roles_context(context, objects, 0);
            data_ontology::data_list_context(context, data, 0)
        }
        _ => context,
    }
}
/// The context with the class expressions and properties of the keys of
/// `items[index..]`.
pub fn keys_context(context: Context, items: &Vec<AnnotatedAxiom>, index: usize) -> Context {
    if index < items.len() {
        keys_context(key_context(context, &items[index].axiom), items, index + 1)
    } else {
        context
    }
}
/// `nodes` with the individuals of the nominals and value restrictions of a
/// key's class expression.
fn key_class_individuals(nodes: Vec<Individual>, axiom: &Axiom) -> Option<Vec<Individual>> {
    match axiom {
        Axiom::HasKey(class, _, _) => data_ontology::class_individuals(nodes, class),
        _ => Some(nodes),
    }
}
/// `nodes` with the individuals of the class expressions of the keys of
/// `items[index..]`.
pub fn key_individuals(
    nodes: Vec<Individual>,
    items: &Vec<AnnotatedAxiom>,
    index: usize,
) -> Option<Vec<Individual>> {
    if index < items.len() {
        match key_class_individuals(nodes, &items[index].axiom) {
            Some(nodes) => key_individuals(nodes, items, index + 1),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// Whether the axiom makes a property transitive or includes a property chain
/// in one.
fn complex_axiom(axiom: &Axiom) -> bool {
    match axiom {
        Axiom::TransitiveObjectProperty(_) => true,
        Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Chain(_), _) => true,
        _ => false,
    }
}
/// Whether one of `items[index..]` makes a property transitive or includes a
/// property chain in one, which may make a key property not simple.
pub fn complex_roles(items: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < items.len() {
        if complex_axiom(&items[index].axiom) {
            true
        } else {
            complex_roles(items, index + 1)
        }
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The encoding's own names
// ---------------------------------------------------------------------------

/// The byte 0, the tag `K` and `rest`.
fn key_name(rest: Vec<u8>) -> Vec<u8> {
    data_ontology::tagged_name(b'K', rest)
}
/// The class `N` of the named elements.
fn named_class() -> ClassExpression {
    ClassExpression::Class(Class {
        iri: Iri {
            spelling: key_name(Vec::new()),
        },
    })
}
/// The role `mark` whose self loops mark the named elements.
fn mark_role() -> ObjectPropertyExpression {
    let mut rest = Vec::new();
    rest.push(b'R');
    ObjectPropertyExpression::Property(ObjectProperty {
        iri: Iri {
            spelling: key_name(rest),
        },
    })
}
/// The name `[0, K, S, orientation]` followed by the property's name; `None`
/// when it would be too long.
fn share_name(property: &ObjectProperty, orientation: u8) -> Option<ObjectProperty> {
    if property.iri.spelling.len() < usize::MAX - 4 {
        let mut rest = Vec::new();
        rest.push(b'S');
        rest.push(orientation);
        Some(ObjectProperty {
            iri: Iri {
                spelling: key_name(data_ontology::copy_after(&property.iri.spelling, 0, rest)),
            },
        })
    } else {
        None
    }
}
/// The role `share(role)` of the pairs of elements that share a marked value
/// along the role; `None` when the name would be too long.
fn share_role(role: &ObjectPropertyExpression) -> Option<ObjectProperty> {
    match role {
        ObjectPropertyExpression::Property(property) => share_name(property, 0),
        ObjectPropertyExpression::Inverse(property) => share_name(property, 1),
    }
}
/// The inverse of a role.
fn inverse_of(role: ObjectPropertyExpression) -> ObjectPropertyExpression {
    match role {
        ObjectPropertyExpression::Property(property) => ObjectPropertyExpression::Inverse(property),
        ObjectPropertyExpression::Inverse(property) => ObjectPropertyExpression::Property(property),
    }
}
fn not(class: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(class))
}
/// The nominal of a copy of the individual.
fn nominal(individual: &Individual) -> ClassExpression {
    ClassExpression::ObjectOneOf(NonEmpty {
        first: copy_individual(individual),
        rest: Vec::new(),
    })
}

// ---------------------------------------------------------------------------
// The axioms of the keys
// ---------------------------------------------------------------------------

/// `out` with every named individual of `nodes[index..]` in `N` and every
/// anonymous one no data node.
fn named_assertions(
    nodes: &Vec<Individual>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < nodes.len() {
        match named_assertion(&nodes[index], out) {
            Some(out) => named_assertions(nodes, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with the individual in `N` if it is named and its name is not the
/// encoding's, and no data node if it is anonymous.
fn named_assertion(
    individual: &Individual,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match data_ontology::object_individual_of(individual) {
        Some(copy) => match individual {
            Individual::Named(_) => {
                data_ontology::push(out, Axiom::ClassAssertion(named_class(), copy))
            }
            Individual::Anonymous(_) => data_ontology::push(
                out,
                Axiom::ClassAssertion(data_ontology::object_class(), copy),
            ),
        },
        None => None,
    }
}
/// Whether the role is the universal role, in either orientation, for some
/// role of `roles[index..]`.
fn any_universal(roles: &Vec<ObjectPropertyExpression>, index: usize) -> bool {
    if index < roles.len() {
        if data_ontology::universal(&roles[index]) {
            true
        } else {
            any_universal(roles, index + 1)
        }
    } else {
        false
    }
}
/// Whether a key with `objects` object properties and `data` data properties
/// is counted: it has one property, when the closure allows counting.
fn counted(objects: usize, data: usize, counting: bool) -> bool {
    counting & (((objects == 1) & (data == 0)) | ((objects == 0) & (data == 1)))
}
/// `out` with the roles of the data properties of `data[index..]` in the data
/// encoding; `None` for the bottom data property or one without a role.
fn data_key_roles(
    context: &Context,
    data: &Vec<DataProperty>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Option<Vec<ObjectPropertyExpression>> {
    if index < data.len() {
        if data_ontology::is_bottom_data(&data[index]) {
            None
        } else {
            match data_ontology::data_role(context, &data[index]) {
                Some(role) => {
                    if out.len() < usize::MAX {
                        out.push(role);
                        data_key_roles(context, data, index + 1, out)
                    } else {
                        None
                    }
                }
                None => None,
            }
        }
    } else {
        Some(out)
    }
}
/// `out` with copies of the roles of `roles[index..]`.
fn append_roles(
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Option<Vec<ObjectPropertyExpression>> {
    if index < roles.len() {
        if out.len() < usize::MAX {
            out.push(copy_role(&roles[index]));
            append_roles(roles, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// `out` with `N ⊑ ≤1 role⁻.(class ⊓ N)`.
fn counted_key(
    context: &Context,
    class: &ClassExpression,
    role: &ObjectPropertyExpression,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match (
        data_ontology::object_role(context, role),
        data_ontology::encode_class(context, class),
    ) {
        (Some(copy), Some(encoded)) => data_ontology::push(
            out,
            Axiom::SubClassOf(
                named_class(),
                ClassExpression::ObjectMaxCardinality(
                    Natural::Succ(Box::new(Natural::Zero)),
                    inverse_of(copy),
                    Some(Box::new(data_ontology::and(encoded, named_class()))),
                ),
            ),
        ),
        _ => None,
    }
}
/// `out` with `D ⊑ ≤1 role⁻.(class ⊓ N)` for the role of a data property: a
/// data value has at most one named instance of the class as predecessor.
fn data_counted_key(
    context: &Context,
    class: &ClassExpression,
    role: &ObjectPropertyExpression,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match data_ontology::encode_class(context, class) {
        Some(encoded) => data_ontology::push(
            out,
            Axiom::SubClassOf(
                data_ontology::data_class(),
                ClassExpression::ObjectMaxCardinality(
                    Natural::Succ(Box::new(Natural::Zero)),
                    inverse_of(copy_role(role)),
                    Some(Box::new(data_ontology::and(encoded, named_class()))),
                ),
            ),
        ),
        None => None,
    }
}
/// `out` with `role ∘ mark ∘ role⁻ ⊑ share(role)` for the role of a data
/// property.
fn data_chain(
    role: &ObjectPropertyExpression,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match share_role(role) {
        Some(share) => {
            let mut rest = Vec::new();
            rest.push(inverse_of(copy_role(role)));
            data_ontology::push(
                out,
                Axiom::SubObjectPropertyOf(
                    SubObjectPropertyExpression::Chain(AtLeastTwo {
                        first: copy_role(role),
                        second: mark_role(),
                        rest,
                    }),
                    ObjectPropertyExpression::Property(share),
                ),
            )
        }
        None => None,
    }
}
/// `out` with the chain of every role of a data property of `roles[index..]`.
fn data_chains(
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < roles.len() {
        match data_chain(&roles[index], out) {
            Some(out) => data_chains(roles, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with `role ∘ mark ∘ role⁻ ⊑ share(role)`.
fn chain(
    context: &Context,
    role: &ObjectPropertyExpression,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match (
        data_ontology::object_role(context, role),
        data_ontology::object_role(context, role),
        share_role(role),
    ) {
        (Some(first), Some(last), Some(share)) => {
            let mut rest = Vec::new();
            rest.push(inverse_of(last));
            data_ontology::push(
                out,
                Axiom::SubObjectPropertyOf(
                    SubObjectPropertyExpression::Chain(AtLeastTwo {
                        first,
                        second: mark_role(),
                        rest,
                    }),
                    ObjectPropertyExpression::Property(share),
                ),
            )
        }
        _ => None,
    }
}
/// `out` with the chain of every role of `roles[index..]`.
fn chains(
    context: &Context,
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < roles.len() {
        match chain(context, &roles[index], out) {
            Some(out) => chains(context, roles, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with `∀share(role)⁻.¬{x}` for every role of `roles[index..]`: no
/// element shares a marked value along the role with `x`.
fn apart(
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    individual: &Individual,
    mut out: Vec<ClassExpression>,
) -> Option<Vec<ClassExpression>> {
    if index < roles.len() {
        match share_role(&roles[index]) {
            Some(share) => {
                if out.len() < usize::MAX {
                    out.push(ClassExpression::ObjectAllValuesFrom(
                        ObjectPropertyExpression::Inverse(share),
                        Box::new(not(nominal(individual))),
                    ));
                    apart(roles, index + 1, individual, out)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `rest` followed by `∀share(P1)⁻.(¬{x} ⊔ ¬CE)`: at an element that shares a
/// marked value with `x` along `P1`, this says that `x` is not in `CE`.
fn outside(
    rest: Vec<ClassExpression>,
    share: ObjectProperty,
    class: ClassExpression,
    individual: &Individual,
) -> Option<Vec<ClassExpression>> {
    let mut rest = rest;
    if rest.len() < usize::MAX {
        rest.push(ClassExpression::ObjectAllValuesFrom(
            ObjectPropertyExpression::Inverse(share),
            Box::new(data_ontology::or(not(nominal(individual)), not(class))),
        ));
        Some(rest)
    } else {
        None
    }
}
/// `out` with `x : ∀share(P1).(¬N ⊔ ¬CE ⊔ {x} ⊔ ∀share(P2)⁻.¬{x} ⊔ … ⊔
/// ∀share(P1)⁻.(¬{x} ⊔ ¬CE))` for a named individual `x` whose name is not the
/// encoding's: every named instance of `CE` that shares a marked value with `x`
/// along every key property is `x`, unless `x` is not in `CE`. The case split
/// on `CE` at `x` sits inside `∀share(P1)`, so the completion forest makes it
/// only where an element shares a value with `x`.
fn shared_assertion(
    context: &Context,
    class: &ClassExpression,
    roles: &Vec<ObjectPropertyExpression>,
    individual: &Individual,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    let mut rest = Vec::new();
    rest.push(nominal(individual));
    match (
        data_ontology::encode_class(context, class),
        data_ontology::encode_class(context, class),
        share_role(&roles[0]),
        share_role(&roles[0]),
        apart(roles, 1, individual, rest),
        data_ontology::object_individual_of(individual),
    ) {
        (Some(outer), Some(inner), Some(share), Some(back), Some(rest), Some(copy)) => {
            match outside(rest, back, outer, individual) {
                Some(rest) => data_ontology::push(
                    out,
                    Axiom::ClassAssertion(
                        ClassExpression::ObjectAllValuesFrom(
                            ObjectPropertyExpression::Property(share),
                            Box::new(ClassExpression::ObjectUnionOf(Box::new(AtLeastTwo {
                                first: not(named_class()),
                                second: not(inner),
                                rest,
                            }))),
                        ),
                        copy,
                    ),
                ),
                None => None,
            }
        }
        _ => None,
    }
}
/// `out` with the assertion of a key at every named individual of
/// `nodes[index..]`.
fn shared_assertions(
    context: &Context,
    class: &ClassExpression,
    roles: &Vec<ObjectPropertyExpression>,
    nodes: &Vec<Individual>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < nodes.len() {
        match shared_at(context, class, roles, &nodes[index], out) {
            Some(out) => shared_assertions(context, class, roles, nodes, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// `out` with the assertion of a key at the individual if it is named.
fn shared_at(
    context: &Context,
    class: &ClassExpression,
    roles: &Vec<ObjectPropertyExpression>,
    individual: &Individual,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match individual {
        Individual::Named(_) => shared_assertion(context, class, roles, individual, out),
        Individual::Anonymous(_) => Some(out),
    }
}
/// `out` with the axioms of a key whose properties are `objects`, none of them
/// the universal role, and the data properties of the roles `data`.
fn key_with(
    context: &Context,
    class: &ClassExpression,
    objects: &Vec<ObjectPropertyExpression>,
    data: &Vec<ObjectPropertyExpression>,
    nodes: &Vec<Individual>,
    counting: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if counted(objects.len(), data.len(), counting) {
        if objects.len() == 1 {
            counted_key(context, class, &objects[0], out)
        } else {
            data_counted_key(context, class, &data[0], out)
        }
    } else {
        match append_roles(objects, 0, Vec::new()) {
            Some(roles) => match append_roles(data, 0, roles) {
                Some(roles) => match chains(context, objects, 0, out) {
                    Some(out) => match data_chains(data, 0, out) {
                        Some(out) => shared_assertions(context, class, &roles, nodes, 0, out),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            },
            None => None,
        }
    }
}
/// `out` with the axioms of a key; `None` for a key with no property, the
/// universal role or the top or bottom data property, or with a data property
/// while numbers are ordered, floating-point numbers are in use or facets cut
/// the time lines.
fn key_axioms(
    context: &Context,
    class: &ClassExpression,
    objects: &Vec<ObjectPropertyExpression>,
    data: &Vec<DataProperty>,
    nodes: &Vec<Individual>,
    counting: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if (objects.len() == 0) & (data.len() == 0) {
        None
    } else if any_universal(objects, 0) {
        None
    } else if (data.len() != 0)
        & (context.kinds.ordered
            | context.kinds.double
            | context.kinds.float
            | (context.times.len() != 0))
    {
        None
    } else {
        match data_key_roles(context, data, 0, Vec::new()) {
            Some(roles) => key_with(context, class, objects, &roles, nodes, counting, out),
            None => None,
        }
    }
}
/// `out` with the axioms of the axiom if it is a key.
fn axiom_keys(
    context: &Context,
    axiom: &Axiom,
    nodes: &Vec<Individual>,
    counting: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    match axiom {
        Axiom::HasKey(class, objects, data) => {
            key_axioms(context, class, objects, data, nodes, counting, out)
        }
        _ => Some(out),
    }
}
/// `out` with the axioms of the keys of `items[index..]`.
fn keys_from(
    context: &Context,
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    index: usize,
    counting: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < items.len() {
        match axiom_keys(context, &items[index].axiom, nodes, counting, out) {
            Some(out) => keys_from(context, items, nodes, index + 1, counting, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// Whether a key of `items[index..]` is not counted, which needs the self
/// loops of `mark`.
fn shared_from(items: &Vec<AnnotatedAxiom>, index: usize, counting: bool) -> bool {
    if index < items.len() {
        if shared_key(&items[index].axiom, counting) {
            true
        } else {
            shared_from(items, index + 1, counting)
        }
    } else {
        false
    }
}
/// Whether the axiom is a key that is not counted.
fn shared_key(axiom: &Axiom, counting: bool) -> bool {
    match axiom {
        Axiom::HasKey(_, objects, data) => !counted(objects.len(), data.len(), counting),
        _ => false,
    }
}
/// Whether the axiom is a key with a data property that is not counted.
fn data_shared_key(axiom: &Axiom, counting: bool) -> bool {
    match axiom {
        Axiom::HasKey(_, objects, data) => {
            (data.len() != 0) & !counted(objects.len(), data.len(), counting)
        }
        _ => false,
    }
}
/// Whether a key of `items[index..]` with a data property is not counted,
/// which needs the self loops of `mark` at the data values.
fn data_shared_from(items: &Vec<AnnotatedAxiom>, index: usize, counting: bool) -> bool {
    if index < items.len() {
        if data_shared_key(&items[index].axiom, counting) {
            true
        } else {
            data_shared_from(items, index + 1, counting)
        }
    } else {
        false
    }
}
/// `out` with `N ⊑ ∃mark.Self` when a key is not counted, and `D ⊑ ∃mark.Self`
/// when a key with a data property is not counted.
fn marks(
    items: &Vec<AnnotatedAxiom>,
    counting: bool,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    let out = if shared_from(items, 0, counting) {
        match data_ontology::push(
            out,
            Axiom::SubClassOf(named_class(), ClassExpression::ObjectHasSelf(mark_role())),
        ) {
            Some(out) => out,
            None => return None,
        }
    } else {
        out
    };
    if data_shared_from(items, 0, counting) {
        data_ontology::push(
            out,
            Axiom::SubClassOf(
                data_ontology::data_class(),
                ClassExpression::ObjectHasSelf(mark_role()),
            ),
        )
    } else {
        Some(out)
    }
}

// ---------------------------------------------------------------------------
// The encoding
// ---------------------------------------------------------------------------

/// `out` with the encodings of the axioms of `items[index..]` other than keys.
fn unkeyed(
    context: &Context,
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < items.len() {
        if is_key(&items[index].axiom) {
            unkeyed(context, items, index + 1, out)
        } else {
            match data_ontology::encode_axiom(context, &items[index].axiom, out) {
                Some(out) => unkeyed(context, items, index + 1, out),
                None => None,
            }
        }
    } else {
        Some(out)
    }
}
/// The encoding of a closure with keys in the context for a capacity that
/// bounds the counts of its data restrictions and its questions': the
/// encoding's own axioms (the data encoding of no axioms), the encodings of the
/// axioms other than keys, `N ⊑ ¬D`, every named individual of `nodes` in `N`,
/// and the axioms of the keys, counted where `counting` allows.
pub fn encode(
    context: &Context,
    capacity: usize,
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    counting: bool,
) -> Option<Vec<AnnotatedAxiom>> {
    let empty: Vec<AnnotatedAxiom> = Vec::new();
    let out = match data_ontology::encode(context, capacity, &empty) {
        Some(out) => out,
        None => return None,
    };
    let out = match unkeyed(context, items, 0, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match data_ontology::push(
        out,
        Axiom::SubClassOf(named_class(), data_ontology::object_class()),
    ) {
        Some(out) => out,
        None => return None,
    };
    let out = match named_assertions(nodes, 0, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match marks(items, counting, out) {
        Some(out) => out,
        None => return None,
    };
    keys_from(context, items, nodes, 0, counting, out)
}
/// `total` plus the counts of the data restrictions of the axiom's class
/// expression if it is a key.
fn key_count(axiom: &Axiom, total: usize) -> usize {
    match axiom {
        Axiom::HasKey(class, _, _) => data_ontology::class_count(class, total),
        _ => total,
    }
}
/// `total` plus the counts of the data restrictions of the class expressions of
/// the keys of `items[index..]`.
fn keys_count(items: &Vec<AnnotatedAxiom>, index: usize, total: usize) -> usize {
    if index < items.len() {
        keys_count(items, index + 1, key_count(&items[index].axiom, total))
    } else {
        total
    }
}
/// The encoding of a closure with keys prepared: the individuals the closure
/// names, its keys' class expressions included, and its encoding for a
/// capacity with `room` for a question's data restrictions, prepared for the
/// SROIQ queries.
fn prepare_with(
    items: &Vec<AnnotatedAxiom>,
    context: Context,
    capacity: usize,
    room: usize,
) -> Option<Prepared> {
    let nodes = match data_ontology::items_individuals(Vec::new(), items, 0) {
        Some(nodes) => nodes,
        None => return None,
    };
    let nodes = match key_individuals(nodes, items, 0) {
        Some(nodes) => nodes,
        None => return None,
    };
    match encode(&context, capacity, items, &nodes, !complex_roles(items, 0)) {
        Some(encoded) => match shi_ontology::prepare(&encoded) {
            Some(prepared) => Some(Prepared::Keyed(context, nodes, prepared, room)),
            None => None,
        },
        None => None,
    }
}
/// A closure with keys prepared in the context with `room` for the counts of a
/// question's data restrictions: the context with the keys' class expressions
/// and properties, finished again, the individuals the closure names, its
/// keys' class expressions included, and its encoding prepared for the SROIQ
/// queries; `None` when the counts of the data restrictions of the closure, its
/// keys' class expressions included, and the room reach the cap.
pub fn prepare(items: &Vec<AnnotatedAxiom>, context: Context, room: usize) -> Option<Prepared> {
    let context = data_ontology::finished(keys_context(context, items, 0));
    let capacity = data_ontology::add_count(
        keys_count(items, 0, data_ontology::items_count(items, 0, 0)),
        room,
    );
    if capacity < data_ontology::LIMIT {
        prepare_with(items, context, capacity, room)
    } else {
        None
    }
}
