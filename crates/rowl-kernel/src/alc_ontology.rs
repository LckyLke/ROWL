//! ALC consistency, class satisfiability, subsumption and instance checking for
//! an axiom closure with assertions about individuals.
//!
//! Every supported class axiom becomes a concept in negation normal form that
//! holds at every element exactly when the axiom holds: `C ⊑ D` becomes `¬C ⊔ D`,
//! equivalent classes hold all together or not at all, disjoint classes are
//! pairwise excluded, a disjoint union also equates the class with the union of
//! its members, and a domain or range restricts the property's sources or
//! targets. Declarations, annotation axioms and assertions impose nothing on
//! it. The conjunction of these concepts is the TBox concept of the closure.
//!
//! The role axioms `SubObjectPropertyOf` and `EquivalentObjectProperties` between
//! named object properties and `TransitiveObjectProperty` of a named object
//! property become the role box of the completion (see `role_box`): every
//! inclusion is added together with its compositions with the inclusions
//! already listed, so the role box stays closed under composition.
//!
//! The assertions become the facts and edges of the completion for named
//! individuals (see `abox`). Every individual gets a node, node 0 stands for one
//! more element, a class assertion is a concept at its individual's node, and
//! an object property assertion is an edge along its named property. Without
//! role axioms, a negative object property assertion contradicts the closure
//! exactly when the same edge is asserted, because the completion's models
//! relate nodes only along asserted edges. Queries add their concepts at node 0
//! or at the queried individual's node.
//!
//! The answer is `None` when an axiom has any other form, when a class
//! expression is outside the ALC fragment, when a translated concept uses
//! `owl:topObjectProperty` or `owl:bottomObjectProperty` (whose fixed meaning
//! the tableau does not model) or `owl:Thing` or `owl:Nothing` as an ordinary
//! named class (the translation turns those classes into top and bottom), when
//! an object property assertion or role axiom uses one of the two built-in
//! properties, when negative object property assertions meet role axioms, or
//! when there are more than `usize::MAX - 2` distinct individuals or
//! `usize::MAX` concepts, inclusions or transitive properties to list.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::manual_map,
    clippy::vec_init_then_push,
    clippy::len_zero
)] // Indexed operations, explicit branches and pushes without macros for the pinned extraction subset.
use crate::abox::{abox_satisfiable_with, Edges, Facts};
use crate::assertion_equality::same_individual_value;
use crate::model::{
    AnnotatedAxiom, AnonymousIndividual, AtLeastTwo, Axiom, Class, ClassExpression, Individual,
    NamedIndividual, ObjectProperty, ObjectPropertyExpression, SubObjectPropertyExpression,
};
use crate::nnf::{connect, copy_bytes, copy_iri, nnf, NnfConcept};
use crate::role_box::{RoleBox, RoleInclusion};
use crate::symbols::same_spelling;

fn equal_from(key: &Vec<u8>, pattern: &[u8], index: usize) -> bool {
    if index < key.len() {
        key[index] == pattern[index] && equal_from(key, pattern, index + 1)
    } else {
        true
    }
}
pub(crate) fn same_pattern(key: &Vec<u8>, pattern: &[u8]) -> bool {
    key.len() == pattern.len() && equal_from(key, pattern, 0)
}
/// `owl:Thing` or `owl:Nothing`.
pub(crate) fn builtin_class(class: &Class) -> bool {
    same_pattern(&class.iri.spelling, b"http://www.w3.org/2002/07/owl#Thing")
        || same_pattern(
            &class.iri.spelling,
            b"http://www.w3.org/2002/07/owl#Nothing",
        )
}
/// `owl:topObjectProperty` or `owl:bottomObjectProperty`.
fn builtin_role(role: &ObjectProperty) -> bool {
    same_pattern(
        &role.iri.spelling,
        b"http://www.w3.org/2002/07/owl#topObjectProperty",
    ) || same_pattern(
        &role.iri.spelling,
        b"http://www.w3.org/2002/07/owl#bottomObjectProperty",
    )
}
/// Whether no built-in class occurs as a named class and no built-in object
/// property occurs as a role, so the tableau reads every name as an ordinary one.
fn proper(concept: &NnfConcept) -> bool {
    match concept {
        NnfConcept::Top => true,
        NnfConcept::Bottom => true,
        NnfConcept::Atom(class) => !builtin_class(class),
        NnfConcept::NotAtom(class) => !builtin_class(class),
        NnfConcept::And(left, right) => proper(left) && proper(right),
        NnfConcept::Or(left, right) => proper(left) && proper(right),
        NnfConcept::Exists(role, filler) => !builtin_role(role) && proper(filler),
        NnfConcept::Forall(role, filler) => !builtin_role(role) && proper(filler),
    }
}

/// Conjoin onto `joined`, for every `k ≥ index`, that `member` and `values[k]`
/// share no element.
fn apart_from(
    member: &ClassExpression,
    values: &Vec<ClassExpression>,
    index: usize,
    joined: NnfConcept,
) -> Option<NnfConcept> {
    if index < values.len() {
        let left = match nnf(member, false) {
            Some(left) => left,
            None => return None,
        };
        let right = match nnf(&values[index], false) {
            Some(right) => right,
            None => return None,
        };
        apart_from(
            member,
            values,
            index + 1,
            NnfConcept::And(
                Box::new(joined),
                Box::new(NnfConcept::Or(Box::new(left), Box::new(right))),
            ),
        )
    } else {
        Some(joined)
    }
}
/// Conjoin onto `joined` that the members `values[index..]` are pairwise disjoint.
fn pairwise_from(
    values: &Vec<ClassExpression>,
    index: usize,
    joined: NnfConcept,
) -> Option<NnfConcept> {
    if index < values.len() {
        match apart_from(&values[index], values, index + 1, joined) {
            Some(joined) => pairwise_from(values, index + 1, joined),
            None => None,
        }
    } else {
        Some(joined)
    }
}
/// Every two member occurrences share no element.
fn pairwise(members: &AtLeastTwo<ClassExpression>) -> Option<NnfConcept> {
    let first = match nnf(&members.first, false) {
        Some(first) => first,
        None => return None,
    };
    let second = match nnf(&members.second, false) {
        Some(second) => second,
        None => return None,
    };
    let joined = match apart_from(
        &members.first,
        &members.rest,
        0,
        NnfConcept::Or(Box::new(first), Box::new(second)),
    ) {
        Some(joined) => joined,
        None => return None,
    };
    let joined = match apart_from(&members.second, &members.rest, 0, joined) {
        Some(joined) => joined,
        None => return None,
    };
    pairwise_from(&members.rest, 0, joined)
}
fn is_named(property: &ObjectPropertyExpression) -> bool {
    match property {
        ObjectPropertyExpression::Property(_) => true,
        ObjectPropertyExpression::Inverse(_) => false,
    }
}
/// Whether every expression in `values[index..]` is a named object property.
fn named_from(values: &Vec<ObjectPropertyExpression>, index: usize) -> bool {
    if index < values.len() {
        is_named(&values[index]) && named_from(values, index + 1)
    } else {
        true
    }
}
/// Whether every member is a named object property.
fn named_members(members: &AtLeastTwo<ObjectPropertyExpression>) -> bool {
    is_named(&members.first) && is_named(&members.second) && named_from(&members.rest, 0)
}
/// A concept that holds at every element exactly when the axiom holds, for
/// the supported axioms.
fn axiom_concept(axiom: &Axiom) -> Option<NnfConcept> {
    match axiom {
        Axiom::Declaration(_) => Some(NnfConcept::Top),
        Axiom::SubClassOf(sub, sup) => {
            let outside = match nnf(sub, false) {
                Some(outside) => outside,
                None => return None,
            };
            let inside = match nnf(sup, true) {
                Some(inside) => inside,
                None => return None,
            };
            Some(NnfConcept::Or(Box::new(outside), Box::new(inside)))
        }
        Axiom::EquivalentClasses(members) => {
            let all = match connect(members, true, true) {
                Some(all) => all,
                None => return None,
            };
            let none = match connect(members, false, true) {
                Some(none) => none,
                None => return None,
            };
            Some(NnfConcept::Or(Box::new(all), Box::new(none)))
        }
        Axiom::DisjointClasses(members) => pairwise(members),
        Axiom::DisjointUnion(class, members) => {
            let named = ClassExpression::Class(Class {
                iri: copy_iri(&class.iri),
            });
            let outside = match nnf(&named, false) {
                Some(outside) => outside,
                None => return None,
            };
            let inside = match nnf(&named, true) {
                Some(inside) => inside,
                None => return None,
            };
            let some = match connect(members, true, false) {
                Some(some) => some,
                None => return None,
            };
            let none = match connect(members, false, true) {
                Some(none) => none,
                None => return None,
            };
            let disjoint = match pairwise(members) {
                Some(disjoint) => disjoint,
                None => return None,
            };
            Some(NnfConcept::And(
                Box::new(NnfConcept::And(
                    Box::new(NnfConcept::Or(Box::new(outside), Box::new(some))),
                    Box::new(NnfConcept::Or(Box::new(inside), Box::new(none))),
                )),
                Box::new(disjoint),
            ))
        }
        Axiom::ObjectPropertyDomain(property, class) => match property {
            ObjectPropertyExpression::Property(role) => {
                let inside = match nnf(class, true) {
                    Some(inside) => inside,
                    None => return None,
                };
                let role = ObjectProperty {
                    iri: copy_iri(&role.iri),
                };
                Some(NnfConcept::Or(
                    Box::new(NnfConcept::Forall(role, Box::new(NnfConcept::Bottom))),
                    Box::new(inside),
                ))
            }
            ObjectPropertyExpression::Inverse(_) => None,
        },
        Axiom::ObjectPropertyRange(property, class) => match property {
            ObjectPropertyExpression::Property(role) => {
                let inside = match nnf(class, true) {
                    Some(inside) => inside,
                    None => return None,
                };
                let role = ObjectProperty {
                    iri: copy_iri(&role.iri),
                };
                Some(NnfConcept::Forall(role, Box::new(inside)))
            }
            ObjectPropertyExpression::Inverse(_) => None,
        },
        Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Single(ObjectPropertyExpression::Property(_)),
            ObjectPropertyExpression::Property(_),
        ) => Some(NnfConcept::Top),
        Axiom::EquivalentObjectProperties(members) => {
            if named_members(members) {
                Some(NnfConcept::Top)
            } else {
                None
            }
        }
        Axiom::TransitiveObjectProperty(ObjectPropertyExpression::Property(_)) => {
            Some(NnfConcept::Top)
        }
        Axiom::AnnotationAssertion(_, _, _) => Some(NnfConcept::Top),
        Axiom::SubAnnotationPropertyOf(_, _) => Some(NnfConcept::Top),
        Axiom::AnnotationPropertyDomain(_, _) => Some(NnfConcept::Top),
        Axiom::AnnotationPropertyRange(_, _) => Some(NnfConcept::Top),
        Axiom::ClassAssertion(_, _) => Some(NnfConcept::Top),
        Axiom::ObjectPropertyAssertion(_, _, _) => Some(NnfConcept::Top),
        Axiom::NegativeObjectPropertyAssertion(_, _, _) => Some(NnfConcept::Top),
        _ => None,
    }
}
/// Conjoin onto `joined` the concepts of the axioms `items[index..]`.
fn internalize_from(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    joined: NnfConcept,
) -> Option<NnfConcept> {
    if index < items.len() {
        match axiom_concept(&items[index].axiom) {
            Some(concept) => internalize_from(
                items,
                index + 1,
                NnfConcept::And(Box::new(joined), Box::new(concept)),
            ),
            None => None,
        }
    } else {
        Some(joined)
    }
}
/// The TBox concept of an axiom closure: it holds at every element exactly when
/// every class axiom holds; assertions impose nothing on it. `None` when some
/// axiom is not supported.
pub fn internalize(items: &Vec<AnnotatedAxiom>) -> Option<NnfConcept> {
    internalize_from(items, 0, NnfConcept::Top)
}
fn copy_property(property: &ObjectProperty) -> ObjectProperty {
    ObjectProperty {
        iri: copy_iri(&property.iri),
    }
}
/// `found` with every property listed as included in `sup` in
/// `inclusions[index..]`, in list order; `None` when there is no room.
fn subs_from(
    inclusions: &Vec<RoleInclusion>,
    index: usize,
    sup: &ObjectProperty,
    mut found: Vec<ObjectProperty>,
) -> Option<Vec<ObjectProperty>> {
    if index < inclusions.len() {
        if same_spelling(&inclusions[index].sup.iri.spelling, &sup.iri.spelling) {
            if found.len() < usize::MAX {
                found.push(copy_property(&inclusions[index].sub));
                subs_from(inclusions, index + 1, sup, found)
            } else {
                None
            }
        } else {
            subs_from(inclusions, index + 1, sup, found)
        }
    } else {
        Some(found)
    }
}
/// `found` with every property listed as including `sub` in
/// `inclusions[index..]`, in list order; `None` when there is no room.
fn sups_from(
    inclusions: &Vec<RoleInclusion>,
    index: usize,
    sub: &ObjectProperty,
    mut found: Vec<ObjectProperty>,
) -> Option<Vec<ObjectProperty>> {
    if index < inclusions.len() {
        if same_spelling(&inclusions[index].sub.iri.spelling, &sub.iri.spelling) {
            if found.len() < usize::MAX {
                found.push(copy_property(&inclusions[index].sup));
                sups_from(inclusions, index + 1, sub, found)
            } else {
                None
            }
        } else {
            sups_from(inclusions, index + 1, sub, found)
        }
    } else {
        Some(found)
    }
}
/// `out` with `sub ⊑ above[index..]` for every listed property, in order.
fn row_from(
    sub: &ObjectProperty,
    above: &Vec<ObjectProperty>,
    index: usize,
    mut out: Vec<RoleInclusion>,
) -> Option<Vec<RoleInclusion>> {
    if index < above.len() {
        if out.len() < usize::MAX {
            out.push(RoleInclusion {
                sub: copy_property(sub),
                sup: copy_property(&above[index]),
            });
            row_from(sub, above, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// `out` with `below[index..] ⊑ above` for every pair, in order.
fn pairs_from(
    below: &Vec<ObjectProperty>,
    index: usize,
    above: &Vec<ObjectProperty>,
    out: Vec<RoleInclusion>,
) -> Option<Vec<RoleInclusion>> {
    if index < below.len() {
        match row_from(&below[index], above, 0, out) {
            Some(out) => pairs_from(below, index + 1, above, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The role box with `sub ⊑ sup` and its compositions with the listed
/// inclusions: every property included in `sub` (and `sub` itself) becomes
/// included in every property including `sup` (and `sup` itself). A role box
/// closed under composition stays closed.
fn add_inclusion(roles: RoleBox, sub: &ObjectProperty, sup: &ObjectProperty) -> Option<RoleBox> {
    let mut start = Vec::new();
    start.push(copy_property(sub));
    let below = match subs_from(&roles.inclusions, 0, sub, start) {
        Some(below) => below,
        None => return None,
    };
    let mut end = Vec::new();
    end.push(copy_property(sup));
    let above = match sups_from(&roles.inclusions, 0, sup, end) {
        Some(above) => above,
        None => return None,
    };
    match pairs_from(&below, 0, &above, roles.inclusions) {
        Some(inclusions) => Some(RoleBox {
            inclusions,
            transitive: roles.transitive,
        }),
        None => None,
    }
}
fn add_transitive(mut roles: RoleBox, role: &ObjectProperty) -> Option<RoleBox> {
    if roles.transitive.len() < usize::MAX {
        roles.transitive.push(copy_property(role));
        Some(roles)
    } else {
        None
    }
}
/// The named properties of a member list, in order; `None` for an inverse.
fn member_roles(members: &AtLeastTwo<ObjectPropertyExpression>) -> Option<Vec<ObjectProperty>> {
    let mut roles = Vec::new();
    match &members.first {
        ObjectPropertyExpression::Property(role) => roles.push(copy_property(role)),
        ObjectPropertyExpression::Inverse(_) => return None,
    }
    match &members.second {
        ObjectPropertyExpression::Property(role) => roles.push(copy_property(role)),
        ObjectPropertyExpression::Inverse(_) => return None,
    }
    rest_roles(&members.rest, 0, roles)
}
fn rest_roles(
    values: &Vec<ObjectPropertyExpression>,
    index: usize,
    mut roles: Vec<ObjectProperty>,
) -> Option<Vec<ObjectProperty>> {
    if index < values.len() {
        match &values[index] {
            ObjectPropertyExpression::Property(role) => {
                if roles.len() < usize::MAX {
                    roles.push(copy_property(role));
                    rest_roles(values, index + 1, roles)
                } else {
                    None
                }
            }
            ObjectPropertyExpression::Inverse(_) => None,
        }
    } else {
        Some(roles)
    }
}
/// The role box with `member ⊑ members[index..]` for every listed member.
fn includes_from(
    roles: RoleBox,
    member: &ObjectProperty,
    members: &Vec<ObjectProperty>,
    index: usize,
) -> Option<RoleBox> {
    if index < members.len() {
        match add_inclusion(roles, member, &members[index]) {
            Some(roles) => includes_from(roles, member, members, index + 1),
            None => None,
        }
    } else {
        Some(roles)
    }
}
/// The role box with `members[index..] ⊑ members` for every pair.
fn equivalent_from(roles: RoleBox, members: &Vec<ObjectProperty>, index: usize) -> Option<RoleBox> {
    if index < members.len() {
        match includes_from(roles, &members[index], members, 0) {
            Some(roles) => equivalent_from(roles, members, index + 1),
            None => None,
        }
    } else {
        Some(roles)
    }
}
/// The role box with every member of an equivalence included in every member;
/// `None` for an inverse member or when there is no room.
fn add_equivalent(
    roles: RoleBox,
    members: &AtLeastTwo<ObjectPropertyExpression>,
) -> Option<RoleBox> {
    match member_roles(members) {
        Some(members) => equivalent_from(roles, &members, 0),
        None => None,
    }
}
/// The role box with the role axioms of `items[index..]`; `None` when an
/// equivalence has an inverse member or there is no room.
fn role_box_from(items: &Vec<AnnotatedAxiom>, index: usize, roles: RoleBox) -> Option<RoleBox> {
    if index < items.len() {
        let roles = match &items[index].axiom {
            Axiom::SubObjectPropertyOf(
                SubObjectPropertyExpression::Single(ObjectPropertyExpression::Property(sub)),
                ObjectPropertyExpression::Property(sup),
            ) => add_inclusion(roles, sub, sup),
            Axiom::EquivalentObjectProperties(members) => add_equivalent(roles, members),
            Axiom::TransitiveObjectProperty(ObjectPropertyExpression::Property(role)) => {
                add_transitive(roles, role)
            }
            _ => Some(roles),
        };
        match roles {
            Some(roles) => role_box_from(items, index + 1, roles),
            None => None,
        }
    } else {
        Some(roles)
    }
}
/// The role box of a closure, closed under composition.
fn role_box(items: &Vec<AnnotatedAxiom>) -> Option<RoleBox> {
    role_box_from(
        items,
        0,
        RoleBox {
            inclusions: Vec::new(),
            transitive: Vec::new(),
        },
    )
}
/// Whether `items[index..]` has a negative object property assertion.
pub(crate) fn has_negative(items: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::NegativeObjectPropertyAssertion(_, _, _) => true,
            _ => has_negative(items, index + 1),
        }
    } else {
        false
    }
}
/// A concept that must hold at a node.
pub struct Placed {
    pub node: usize,
    pub concept: NnfConcept,
}
fn copy_individual(individual: &Individual) -> Individual {
    match individual {
        Individual::Named(named) => Individual::Named(NamedIndividual {
            iri: copy_iri(&named.iri),
        }),
        Individual::Anonymous(anonymous) => Individual::Anonymous(AnonymousIndividual {
            scope: copy_bytes(&anonymous.scope),
            label: copy_bytes(&anonymous.label),
        }),
    }
}
/// The node of `individual`: its position in `nodes` from `index`, plus one, or
/// 0 when it is absent.
pub(crate) fn position(nodes: &Vec<Individual>, individual: &Individual, index: usize) -> usize {
    if index < nodes.len() {
        if same_individual_value(&nodes[index], individual) {
            index + 1
        } else {
            position(nodes, individual, index + 1)
        }
    } else {
        0
    }
}
/// `nodes` with `individual` at the end when it is new; `None` when there is no
/// room for another node.
pub(crate) fn intern(
    mut nodes: Vec<Individual>,
    individual: &Individual,
) -> Option<Vec<Individual>> {
    if position(&nodes, individual, 0) != 0 {
        Some(nodes)
    } else if nodes.len() < usize::MAX - 1 {
        nodes.push(copy_individual(individual));
        Some(nodes)
    } else {
        None
    }
}
fn intern_pair(
    nodes: Vec<Individual>,
    source: &Individual,
    target: &Individual,
) -> Option<Vec<Individual>> {
    match intern(nodes, source) {
        Some(nodes) => intern(nodes, target),
        None => None,
    }
}
/// `nodes` with every new individual of the assertions in `items[index..]`, in
/// order of first occurrence.
pub(crate) fn individuals_from(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    nodes: Vec<Individual>,
) -> Option<Vec<Individual>> {
    if index < items.len() {
        let nodes = match &items[index].axiom {
            Axiom::ClassAssertion(_, member) => intern(nodes, member),
            Axiom::ObjectPropertyAssertion(_, source, target) => intern_pair(nodes, source, target),
            Axiom::NegativeObjectPropertyAssertion(_, source, target) => {
                intern_pair(nodes, source, target)
            }
            _ => Some(nodes),
        };
        match nodes {
            Some(nodes) => individuals_from(items, index + 1, nodes),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// `placed` with the class assertions of `items[index..]` at their individuals'
/// nodes; `None` when a class expression is outside the fragment or there is no
/// room for another placed concept.
fn assertions_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    index: usize,
    mut placed: Vec<Placed>,
) -> Option<Vec<Placed>> {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::ClassAssertion(class, member) => match nnf(class, true) {
                Some(concept) => {
                    if placed.len() < usize::MAX {
                        placed.push(Placed {
                            node: position(nodes, member, 0),
                            concept,
                        });
                        assertions_from(items, nodes, index + 1, placed)
                    } else {
                        None
                    }
                }
                None => None,
            },
            _ => assertions_from(items, nodes, index + 1, placed),
        }
    } else {
        Some(placed)
    }
}
/// Whether every concept in `placed[index..]` is proper.
fn placed_proper(placed: &Vec<Placed>, index: usize) -> bool {
    if index < placed.len() {
        proper(&placed[index].concept) && placed_proper(placed, index + 1)
    } else {
        true
    }
}
pub(crate) fn named_property(property: &ObjectPropertyExpression) -> &ObjectProperty {
    match property {
        ObjectPropertyExpression::Property(role) => role,
        ObjectPropertyExpression::Inverse(role) => role,
    }
}
/// Whether no expression in `values[index..]` names a built-in object property.
fn rest_proper(values: &Vec<ObjectPropertyExpression>, index: usize) -> bool {
    if index < values.len() {
        let here = role_proper(&values[index]);
        here && rest_proper(values, index + 1)
    } else {
        true
    }
}
pub(crate) fn role_proper(property: &ObjectPropertyExpression) -> bool {
    !builtin_role(named_property(property))
}
/// Whether no member names a built-in object property.
fn members_proper(members: &AtLeastTwo<ObjectPropertyExpression>) -> bool {
    let first = role_proper(&members.first);
    let second = role_proper(&members.second);
    first && second && rest_proper(&members.rest, 0)
}
/// Whether neither property of an inclusion is a built-in object property.
fn pair_proper(sub: &ObjectPropertyExpression, sup: &ObjectPropertyExpression) -> bool {
    let below = role_proper(sub);
    let above = role_proper(sup);
    below && above
}
/// Whether no object property assertion or role axiom in `items[index..]` uses
/// a built-in object property.
fn roles_proper(items: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < items.len() {
        let here = match &items[index].axiom {
            Axiom::ObjectPropertyAssertion(property, _, _) => {
                !builtin_role(named_property(property))
            }
            Axiom::NegativeObjectPropertyAssertion(property, _, _) => {
                !builtin_role(named_property(property))
            }
            Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(sub), sup) => {
                pair_proper(sub, sup)
            }
            Axiom::EquivalentObjectProperties(members) => members_proper(members),
            Axiom::TransitiveObjectProperty(property) => role_proper(property),
            _ => true,
        };
        here && roles_proper(items, index + 1)
    } else {
        true
    }
}
/// `edges` with an edge for every object property assertion in `items[index..]`,
/// oriented along its named property.
fn edges_from<'a>(
    items: &'a Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    index: usize,
    edges: Edges<'a>,
) -> Edges<'a> {
    if index < items.len() {
        let edges = match &items[index].axiom {
            Axiom::ObjectPropertyAssertion(
                ObjectPropertyExpression::Property(role),
                source,
                target,
            ) => Edges::Entry {
                role,
                source: position(nodes, source, 0),
                target: position(nodes, target, 0),
                next: Box::new(edges),
            },
            Axiom::ObjectPropertyAssertion(
                ObjectPropertyExpression::Inverse(role),
                source,
                target,
            ) => Edges::Entry {
                role,
                source: position(nodes, target, 0),
                target: position(nodes, source, 0),
                next: Box::new(edges),
            },
            _ => edges,
        };
        edges_from(items, nodes, index + 1, edges)
    } else {
        edges
    }
}
/// Whether the edge is among `edges`; the edges are handed back.
fn has_edge<'a>(
    edges: Edges<'a>,
    role: &ObjectProperty,
    source: usize,
    target: usize,
) -> (bool, Edges<'a>) {
    match edges {
        Edges::Empty => (false, Edges::Empty),
        Edges::Entry {
            role: other,
            source: from,
            target: to,
            next,
        } => {
            let here = from == source
                && to == target
                && same_spelling(&other.iri.spelling, &role.iri.spelling);
            let (later, rest) = has_edge(*next, role, source, target);
            (
                here || later,
                Edges::Entry {
                    role: other,
                    source: from,
                    target: to,
                    next: Box::new(rest),
                },
            )
        }
    }
}
/// Whether a negative object property assertion in `items[index..]` denies an
/// edge in `edges`; the edges are handed back.
fn denied_from<'a>(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    index: usize,
    edges: Edges<'a>,
) -> (bool, Edges<'a>) {
    if index < items.len() {
        let (here, edges) = match &items[index].axiom {
            Axiom::NegativeObjectPropertyAssertion(
                ObjectPropertyExpression::Property(role),
                source,
                target,
            ) => has_edge(
                edges,
                role,
                position(nodes, source, 0),
                position(nodes, target, 0),
            ),
            Axiom::NegativeObjectPropertyAssertion(
                ObjectPropertyExpression::Inverse(role),
                source,
                target,
            ) => has_edge(
                edges,
                role,
                position(nodes, target, 0),
                position(nodes, source, 0),
            ),
            _ => (false, edges),
        };
        let (later, edges) = denied_from(items, nodes, index + 1, edges);
        (here || later, edges)
    } else {
        (false, edges)
    }
}
/// `facts` with a fact for every concept in `placed[index..]`.
fn facts_from<'a>(placed: &'a Vec<Placed>, index: usize, facts: Facts<'a>) -> Facts<'a> {
    if index < placed.len() {
        facts_from(
            placed,
            index + 1,
            Facts::Entry {
                node: placed[index].node,
                concept: &placed[index].concept,
                next: Box::new(facts),
            },
        )
    } else {
        facts
    }
}
/// Whether the closure has a model with elements for its individuals and one
/// more element, in which the `extra` concepts hold at their nodes: node 0 is
/// the further element and node `i + 1` the individual `nodes[i]`.
fn closure_satisfiable(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    extra: Vec<Placed>,
) -> Option<bool> {
    let axioms = match internalize(items) {
        Some(axioms) => axioms,
        None => return None,
    };
    let placed = match assertions_from(items, nodes, 0, extra) {
        Some(placed) => placed,
        None => return None,
    };
    let roles = match role_box(items) {
        Some(roles) => roles,
        None => return None,
    };
    if !(proper(&axioms) && placed_proper(&placed, 0) && roles_proper(items, 0)) {
        return None;
    }
    if has_negative(items, 0) && !(roles.inclusions.len() == 0 && roles.transitive.len() == 0) {
        return None;
    }
    let edges = edges_from(items, nodes, 0, Edges::Empty);
    let (denied, edges) = denied_from(items, nodes, 0, edges);
    if denied {
        return Some(false);
    }
    Some(abox_satisfiable_with(
        nodes.len() + 1,
        facts_from(&placed, 0, Facts::Empty),
        edges,
        &axioms,
        &roles,
    ))
}
/// Whether the closure has a model at all.
pub fn consistent(items: &Vec<AnnotatedAxiom>) -> Option<bool> {
    let nodes = match individuals_from(items, 0, Vec::new()) {
        Some(nodes) => nodes,
        None => return None,
    };
    closure_satisfiable(items, &nodes, Vec::new())
}
/// Whether some model of the closure has an instance of the class expression.
pub fn class_satisfiable(items: &Vec<AnnotatedAxiom>, class: &ClassExpression) -> Option<bool> {
    let concept = match nnf(class, true) {
        Some(concept) => concept,
        None => return None,
    };
    let nodes = match individuals_from(items, 0, Vec::new()) {
        Some(nodes) => nodes,
        None => return None,
    };
    let mut extra = Vec::new();
    extra.push(Placed { node: 0, concept });
    closure_satisfiable(items, &nodes, extra)
}
/// Whether every instance of `sub` is an instance of `sup` in every model of the closure.
pub fn subsumed(
    items: &Vec<AnnotatedAxiom>,
    sub: &ClassExpression,
    sup: &ClassExpression,
) -> Option<bool> {
    let inside = match nnf(sub, true) {
        Some(inside) => inside,
        None => return None,
    };
    let outside = match nnf(sup, false) {
        Some(outside) => outside,
        None => return None,
    };
    let nodes = match individuals_from(items, 0, Vec::new()) {
        Some(nodes) => nodes,
        None => return None,
    };
    let mut extra = Vec::new();
    extra.push(Placed {
        node: 0,
        concept: inside,
    });
    extra.push(Placed {
        node: 0,
        concept: outside,
    });
    match closure_satisfiable(items, &nodes, extra) {
        Some(satisfiable) => Some(!satisfiable),
        None => None,
    }
}
/// Whether the named individual is an instance of the class expression in every
/// model of the closure.
pub fn instance_of(
    items: &Vec<AnnotatedAxiom>,
    individual: &NamedIndividual,
    class: &ClassExpression,
) -> Option<bool> {
    let outside = match nnf(class, false) {
        Some(outside) => outside,
        None => return None,
    };
    let nodes = match individuals_from(items, 0, Vec::new()) {
        Some(nodes) => nodes,
        None => return None,
    };
    let named = Individual::Named(NamedIndividual {
        iri: copy_iri(&individual.iri),
    });
    let mut extra = Vec::new();
    extra.push(Placed {
        node: position(&nodes, &named, 0),
        concept: outside,
    });
    match closure_satisfiable(items, &nodes, extra) {
        Some(satisfiable) => Some(!satisfiable),
        None => None,
    }
}
