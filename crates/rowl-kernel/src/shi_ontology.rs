//! SHI consistency, class satisfiability, subsumption and instance checking for
//! an axiom closure with assertions, decided by the completion graph tableau.
//!
//! Class expressions are translated into ALCI concepts (see `concepts`). Every
//! class axiom becomes inclusions `C ⊑ D`: a subclass axiom is one, equivalent
//! classes include the first member in every other member and back, disjoint
//! classes include every member in the complement of every later member, and a
//! disjoint union includes the class in the union of its members and every
//! member in the class, which the members also partition. An inclusion whose
//! left side is absorbable becomes a definition `A ⊑ C`, which the tableau
//! unfolds only at nodes that list `A`: a named class absorbs directly,
//! `∃r.E ⊑ D` becomes `E ⊑ ∀r⁻.D`, and `E ⊓ F ⊓ … ⊑ D` becomes
//! `E ⊑ ¬F ⊔ … ⊔ D`. Every other inclusion conjoins `¬C ⊔ D` onto the TBox
//! concept, which holds everywhere. A domain conjoins `∀r⁻.C` and a range
//! `∀r.C`, so neither branches.
//!
//! The role axioms `SubObjectPropertyOf` without chains,
//! `EquivalentObjectProperties`, `InverseObjectProperties`,
//! `SymmetricObjectProperty` and `TransitiveObjectProperty`, on named or inverse
//! object properties, become a role hierarchy. Every inclusion is added with
//! its inverse, each together with its compositions with the inclusions already
//! listed, and every transitive property with its inverse, so the hierarchy
//! stays closed as the tableau requires.
//!
//! Every individual of an assertion gets a node after node 0, which stands for
//! one more element. Class assertions and the query's concepts are facts at
//! nodes, and object property assertions are links. Without role axioms, a
//! negative object property assertion contradicts the closure exactly when a
//! link relates the same individuals along the same property, in either
//! orientation, because the tableau's models relate named individuals only
//! along links.
//!
//! `prepare` reads a closure once: its individuals, class parts, role hierarchy,
//! facts and links, and the check of its negative assertions. The `prepared_`
//! queries then only translate their class expressions and run the tableau, so
//! many questions about one closure share that work; the plain queries prepare
//! and ask once.
//!
//! The answer is `None` when an axiom has any other form, when a class
//! expression is outside ALCI, when a concept, definition, role axiom or
//! assertion uses `owl:topObjectProperty` or `owl:bottomObjectProperty` (whose
//! fixed meaning the tableau does not model), when negative object property
//! assertions meet role axioms, or when a list would exceed the `usize` range.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::manual_map,
    clippy::vec_init_then_push,
    clippy::len_zero,
    clippy::needless_return,
    clippy::if_same_then_else
)] // Indexed operations, explicit branches and pushes without macros for the pinned extraction subset.
use crate::alc_ontology::{builtin_class, has_negative, individuals_from, position, role_proper};
use crate::completion::{satisfiable, Definition, Fact, Link};
use crate::concepts::{copy_role, inverse, same_role, translate, Concept};
use crate::hierarchy::{below, is_transitive, Inclusion, RoleHierarchy};
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, Class, ClassExpression, Individual, NamedIndividual,
    ObjectPropertyExpression, SubObjectPropertyExpression,
};
use crate::nnf::copy_iri;

/// What the class axioms require: the TBox concept, which holds at every
/// element, and the definitions `A ⊑ C`, which hold wherever `A` does.
pub struct Parts {
    pub axioms: Concept,
    pub definitions: Vec<Definition>,
}

/// Whether no built-in class occurs as a named class and no built-in object
/// property as a role, so the tableau reads every name as an ordinary one.
fn proper(concept: &Concept) -> bool {
    match concept {
        Concept::Top => true,
        Concept::Bottom => true,
        Concept::Atom(class) => !builtin_class(class),
        Concept::NotAtom(class) => !builtin_class(class),
        Concept::And(left, right) => proper(left) && proper(right),
        Concept::Or(left, right) => proper(left) && proper(right),
        Concept::Exists(role, filler) => role_proper(role) && proper(filler),
        Concept::Forall(role, filler) => role_proper(role) && proper(filler),
    }
}
/// Whether every definition in `definitions[index..]` defines an ordinary class
/// by a proper concept.
fn definitions_proper(definitions: &Vec<Definition>, index: usize) -> bool {
    if index < definitions.len() {
        let here = !builtin_class(&definitions[index].class) && proper(&definitions[index].concept);
        here && definitions_proper(definitions, index + 1)
    } else {
        true
    }
}
/// Whether every fact in `facts[index..]` has a proper concept.
fn facts_proper(facts: &Vec<Fact>, index: usize) -> bool {
    if index < facts.len() {
        proper(&facts[index].concept) && facts_proper(facts, index + 1)
    } else {
        true
    }
}

/// Whether an inclusion `sub ⊑ D` can become a definition: `sub` is a named
/// class other than the built-in ones, an existential restriction whose filler
/// is absorbable, or an intersection whose first member is.
fn absorbable(sub: &ClassExpression) -> bool {
    match sub {
        ClassExpression::Class(class) => !builtin_class(class),
        ClassExpression::ObjectSomeValuesFrom(_, filler) => absorbable(filler),
        ClassExpression::ObjectIntersectionOf(members) => absorbable(&members.first),
        _ => false,
    }
}
/// `joined ⊔ ¬values[index] ⊔ …`: `joined` holds or some class from `index` on
/// does not.
fn fail_from(values: &Vec<ClassExpression>, index: usize, joined: Concept) -> Option<Concept> {
    if index < values.len() {
        match translate(&values[index], false) {
            Some(outside) => fail_from(
                values,
                index + 1,
                Concept::Or(Box::new(joined), Box::new(outside)),
            ),
            None => None,
        }
    } else {
        Some(joined)
    }
}
/// The definition equivalent to `sub ⊑ sup` for an absorbable `sub`: `A ⊑ sup`
/// for a named class, the definition of `filler ⊑ ∀r⁻.sup` for `∃r.filler`,
/// and the definition of `first ⊑ ¬second ⊔ … ⊔ sup` for an intersection.
fn absorb(sub: &ClassExpression, sup: Concept) -> Option<Definition> {
    match sub {
        ClassExpression::Class(class) => Some(Definition {
            class: Class {
                iri: copy_iri(&class.iri),
            },
            concept: sup,
        }),
        ClassExpression::ObjectSomeValuesFrom(role, filler) => {
            absorb(filler, Concept::Forall(inverse(role), Box::new(sup)))
        }
        ClassExpression::ObjectIntersectionOf(members) => {
            let second = match translate(&members.second, false) {
                Some(second) => second,
                None => return None,
            };
            let others = match fail_from(&members.rest, 0, second) {
                Some(others) => others,
                None => return None,
            };
            absorb(&members.first, Concept::Or(Box::new(others), Box::new(sup)))
        }
        _ => None,
    }
}
/// The parts with `sub ⊑ sup`: a definition when `sub` is absorbable, else
/// `¬sub ⊔ sup` conjoined onto the TBox concept.
fn include(sub: &ClassExpression, sup: Concept, mut parts: Parts) -> Option<Parts> {
    if absorbable(sub) {
        match absorb(sub, sup) {
            Some(definition) => {
                if parts.definitions.len() < usize::MAX {
                    parts.definitions.push(definition);
                    Some(parts)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        match translate(sub, false) {
            Some(outside) => Some(Parts {
                axioms: Concept::And(
                    Box::new(parts.axioms),
                    Box::new(Concept::Or(Box::new(outside), Box::new(sup))),
                ),
                definitions: parts.definitions,
            }),
            None => None,
        }
    }
}
/// The parts with `left ⊑ right` and `right ⊑ left`.
fn include_both(left: &ClassExpression, right: &ClassExpression, parts: Parts) -> Option<Parts> {
    let forward = match translate(right, true) {
        Some(forward) => forward,
        None => return None,
    };
    let parts = match include(left, forward, parts) {
        Some(parts) => parts,
        None => return None,
    };
    let backward = match translate(left, true) {
        Some(backward) => backward,
        None => return None,
    };
    include(right, backward, parts)
}
/// The parts with `first` equivalent to every class in `values[index..]`.
fn equal_from(
    first: &ClassExpression,
    values: &Vec<ClassExpression>,
    index: usize,
    parts: Parts,
) -> Option<Parts> {
    if index < values.len() {
        match include_both(first, &values[index], parts) {
            Some(parts) => equal_from(first, values, index + 1, parts),
            None => None,
        }
    } else {
        Some(parts)
    }
}
/// The parts with every member equivalent to the first.
fn equivalent(members: &AtLeastTwo<ClassExpression>, parts: Parts) -> Option<Parts> {
    match include_both(&members.first, &members.second, parts) {
        Some(parts) => equal_from(&members.first, &members.rest, 0, parts),
        None => None,
    }
}
/// The parts with `member` disjoint from every class in `values[index..]`.
fn apart_from(
    member: &ClassExpression,
    values: &Vec<ClassExpression>,
    index: usize,
    parts: Parts,
) -> Option<Parts> {
    if index < values.len() {
        let outside = match translate(&values[index], false) {
            Some(outside) => outside,
            None => return None,
        };
        match include(member, outside, parts) {
            Some(parts) => apart_from(member, values, index + 1, parts),
            None => None,
        }
    } else {
        Some(parts)
    }
}
/// The parts with the classes `values[index..]` pairwise disjoint.
fn pairwise_from(values: &Vec<ClassExpression>, index: usize, parts: Parts) -> Option<Parts> {
    if index < values.len() {
        match apart_from(&values[index], values, index + 1, parts) {
            Some(parts) => pairwise_from(values, index + 1, parts),
            None => None,
        }
    } else {
        Some(parts)
    }
}
/// The parts with the members pairwise disjoint.
fn disjoint(members: &AtLeastTwo<ClassExpression>, parts: Parts) -> Option<Parts> {
    let second = match translate(&members.second, false) {
        Some(second) => second,
        None => return None,
    };
    let parts = match include(&members.first, second, parts) {
        Some(parts) => parts,
        None => return None,
    };
    let parts = match apart_from(&members.first, &members.rest, 0, parts) {
        Some(parts) => parts,
        None => return None,
    };
    let parts = match apart_from(&members.second, &members.rest, 0, parts) {
        Some(parts) => parts,
        None => return None,
    };
    pairwise_from(&members.rest, 0, parts)
}
/// `joined ⊔ values[index] ⊔ …`: `joined` holds or some class from `index` on
/// does.
fn some_from(values: &Vec<ClassExpression>, index: usize, joined: Concept) -> Option<Concept> {
    if index < values.len() {
        match translate(&values[index], true) {
            Some(inside) => some_from(
                values,
                index + 1,
                Concept::Or(Box::new(joined), Box::new(inside)),
            ),
            None => None,
        }
    } else {
        Some(joined)
    }
}
/// The parts with every class in `values[index..]` included in `whole`.
fn within_from(
    values: &Vec<ClassExpression>,
    index: usize,
    whole: &ClassExpression,
    parts: Parts,
) -> Option<Parts> {
    if index < values.len() {
        let inside = match translate(whole, true) {
            Some(inside) => inside,
            None => return None,
        };
        match include(&values[index], inside, parts) {
            Some(parts) => within_from(values, index + 1, whole, parts),
            None => None,
        }
    } else {
        Some(parts)
    }
}
/// The parts with the class equal to the union of the members, which are
/// pairwise disjoint.
fn disjoint_union(
    class: &Class,
    members: &AtLeastTwo<ClassExpression>,
    parts: Parts,
) -> Option<Parts> {
    let whole = ClassExpression::Class(Class {
        iri: copy_iri(&class.iri),
    });
    let first = match translate(&members.first, true) {
        Some(first) => first,
        None => return None,
    };
    let second = match translate(&members.second, true) {
        Some(second) => second,
        None => return None,
    };
    let union = match some_from(
        &members.rest,
        0,
        Concept::Or(Box::new(first), Box::new(second)),
    ) {
        Some(union) => union,
        None => return None,
    };
    let parts = match include(&whole, union, parts) {
        Some(parts) => parts,
        None => return None,
    };
    let inside = match translate(&whole, true) {
        Some(inside) => inside,
        None => return None,
    };
    let parts = match include(&members.first, inside, parts) {
        Some(parts) => parts,
        None => return None,
    };
    let inside = match translate(&whole, true) {
        Some(inside) => inside,
        None => return None,
    };
    let parts = match include(&members.second, inside, parts) {
        Some(parts) => parts,
        None => return None,
    };
    let parts = match within_from(&members.rest, 0, &whole, parts) {
        Some(parts) => parts,
        None => return None,
    };
    disjoint(members, parts)
}
/// The parts with `concept` conjoined onto the TBox concept.
fn conjoin(parts: Parts, concept: Concept) -> Parts {
    Parts {
        axioms: Concept::And(Box::new(parts.axioms), Box::new(concept)),
        definitions: parts.definitions,
    }
}
/// The parts with what the axiom requires of every element; assertions,
/// declarations, annotation axioms and role axioms leave them unchanged.
/// `None` when the axiom is not supported.
fn axiom_parts(axiom: &Axiom, parts: Parts) -> Option<Parts> {
    match axiom {
        Axiom::Declaration(_) => Some(parts),
        Axiom::SubClassOf(sub, sup) => match translate(sup, true) {
            Some(inside) => include(sub, inside, parts),
            None => None,
        },
        Axiom::EquivalentClasses(members) => equivalent(members, parts),
        Axiom::DisjointClasses(members) => disjoint(members, parts),
        Axiom::DisjointUnion(class, members) => disjoint_union(class, members, parts),
        Axiom::ObjectPropertyDomain(property, class) => match translate(class, true) {
            Some(inside) => Some(conjoin(
                parts,
                Concept::Forall(inverse(property), Box::new(inside)),
            )),
            None => None,
        },
        Axiom::ObjectPropertyRange(property, class) => match translate(class, true) {
            Some(inside) => Some(conjoin(
                parts,
                Concept::Forall(copy_role(property), Box::new(inside)),
            )),
            None => None,
        },
        Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(_), _) => Some(parts),
        Axiom::EquivalentObjectProperties(_) => Some(parts),
        Axiom::InverseObjectProperties(_, _) => Some(parts),
        Axiom::SymmetricObjectProperty(_) => Some(parts),
        Axiom::TransitiveObjectProperty(_) => Some(parts),
        Axiom::AnnotationAssertion(_, _, _) => Some(parts),
        Axiom::SubAnnotationPropertyOf(_, _) => Some(parts),
        Axiom::AnnotationPropertyDomain(_, _) => Some(parts),
        Axiom::AnnotationPropertyRange(_, _) => Some(parts),
        Axiom::ClassAssertion(_, _) => Some(parts),
        Axiom::ObjectPropertyAssertion(_, _, _) => Some(parts),
        Axiom::NegativeObjectPropertyAssertion(_, _, _) => Some(parts),
        _ => None,
    }
}
/// The parts with what the axioms `items[index..]` require.
fn parts_from(items: &Vec<AnnotatedAxiom>, index: usize, parts: Parts) -> Option<Parts> {
    if index < items.len() {
        match axiom_parts(&items[index].axiom, parts) {
            Some(parts) => parts_from(items, index + 1, parts),
            None => None,
        }
    } else {
        Some(parts)
    }
}
/// What the class axioms of a closure require; `None` when some axiom is not
/// supported.
pub fn class_parts(items: &Vec<AnnotatedAxiom>) -> Option<Parts> {
    parts_from(
        items,
        0,
        Parts {
            axioms: Concept::Top,
            definitions: Vec::new(),
        },
    )
}

/// `found` with every role listed as included in `sup` in
/// `inclusions[index..]`, in list order; `None` when there is no room.
fn subs_from(
    inclusions: &Vec<Inclusion>,
    index: usize,
    sup: &ObjectPropertyExpression,
    mut found: Vec<ObjectPropertyExpression>,
) -> Option<Vec<ObjectPropertyExpression>> {
    if index < inclusions.len() {
        if same_role(&inclusions[index].sup, sup) {
            if found.len() < usize::MAX {
                found.push(copy_role(&inclusions[index].sub));
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
/// `found` with every role listed as including `sub` in `inclusions[index..]`,
/// in list order; `None` when there is no room.
fn sups_from(
    inclusions: &Vec<Inclusion>,
    index: usize,
    sub: &ObjectPropertyExpression,
    mut found: Vec<ObjectPropertyExpression>,
) -> Option<Vec<ObjectPropertyExpression>> {
    if index < inclusions.len() {
        if same_role(&inclusions[index].sub, sub) {
            if found.len() < usize::MAX {
                found.push(copy_role(&inclusions[index].sup));
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
/// The hierarchy with `sub ⊑ above[index..]`, skipping every inclusion it
/// already has.
fn row_from(
    sub: &ObjectPropertyExpression,
    above: &Vec<ObjectPropertyExpression>,
    index: usize,
    mut roles: RoleHierarchy,
) -> Option<RoleHierarchy> {
    if index < above.len() {
        if below(&roles, sub, &above[index]) {
            row_from(sub, above, index + 1, roles)
        } else if roles.inclusions.len() < usize::MAX {
            roles.inclusions.push(Inclusion {
                sub: copy_role(sub),
                sup: copy_role(&above[index]),
            });
            row_from(sub, above, index + 1, roles)
        } else {
            None
        }
    } else {
        Some(roles)
    }
}
/// The hierarchy with `lower[index..] ⊑ above` for every pair.
fn pairs_from(
    lower: &Vec<ObjectPropertyExpression>,
    index: usize,
    above: &Vec<ObjectPropertyExpression>,
    roles: RoleHierarchy,
) -> Option<RoleHierarchy> {
    if index < lower.len() {
        match row_from(&lower[index], above, 0, roles) {
            Some(roles) => pairs_from(lower, index + 1, above, roles),
            None => None,
        }
    } else {
        Some(roles)
    }
}
/// The hierarchy with `sub ⊑ sup` and its compositions with the listed
/// inclusions: every role included in `sub` (and `sub` itself) becomes
/// included in every role including `sup` (and `sup` itself).
fn add_one(
    roles: RoleHierarchy,
    sub: &ObjectPropertyExpression,
    sup: &ObjectPropertyExpression,
) -> Option<RoleHierarchy> {
    let mut start = Vec::new();
    start.push(copy_role(sub));
    let lower = match subs_from(&roles.inclusions, 0, sub, start) {
        Some(lower) => lower,
        None => return None,
    };
    let mut end = Vec::new();
    end.push(copy_role(sup));
    let upper = match sups_from(&roles.inclusions, 0, sup, end) {
        Some(upper) => upper,
        None => return None,
    };
    pairs_from(&lower, 0, &upper, roles)
}
/// The hierarchy with `sub ⊑ sup` and `inv(sub) ⊑ inv(sup)`, each with its
/// compositions; a closed hierarchy stays closed.
fn add_inclusion(
    roles: RoleHierarchy,
    sub: &ObjectPropertyExpression,
    sup: &ObjectPropertyExpression,
) -> Option<RoleHierarchy> {
    let roles = match add_one(roles, sub, sup) {
        Some(roles) => roles,
        None => return None,
    };
    let flipped_sub = inverse(sub);
    let flipped_sup = inverse(sup);
    add_one(roles, &flipped_sub, &flipped_sup)
}
/// The hierarchy with `left ⊑ right` and `right ⊑ left`.
fn add_equal(
    roles: RoleHierarchy,
    left: &ObjectPropertyExpression,
    right: &ObjectPropertyExpression,
) -> Option<RoleHierarchy> {
    match add_inclusion(roles, left, right) {
        Some(roles) => add_inclusion(roles, right, left),
        None => None,
    }
}
/// The hierarchy with `first` equal to every role in `values[index..]`.
fn same_from(
    first: &ObjectPropertyExpression,
    values: &Vec<ObjectPropertyExpression>,
    index: usize,
    roles: RoleHierarchy,
) -> Option<RoleHierarchy> {
    if index < values.len() {
        match add_equal(roles, first, &values[index]) {
            Some(roles) => same_from(first, values, index + 1, roles),
            None => None,
        }
    } else {
        Some(roles)
    }
}
/// The hierarchy with every member equal to the first.
fn add_equivalent(
    roles: RoleHierarchy,
    members: &AtLeastTwo<ObjectPropertyExpression>,
) -> Option<RoleHierarchy> {
    match add_equal(roles, &members.first, &members.second) {
        Some(roles) => same_from(&members.first, &members.rest, 0, roles),
        None => None,
    }
}
/// The hierarchy with the role and its inverse transitive, unless listed.
fn add_transitive(
    mut roles: RoleHierarchy,
    role: &ObjectPropertyExpression,
) -> Option<RoleHierarchy> {
    if is_transitive(&roles, role) {
        Some(roles)
    } else if roles.transitive.len() < usize::MAX - 1 {
        roles.transitive.push(copy_role(role));
        roles.transitive.push(inverse(role));
        Some(roles)
    } else {
        None
    }
}
/// The hierarchy with the role axioms of `items[index..]`; `None` when there is
/// no room.
fn hierarchy_from(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    roles: RoleHierarchy,
) -> Option<RoleHierarchy> {
    if index < items.len() {
        let roles = match &items[index].axiom {
            Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(sub), sup) => {
                add_inclusion(roles, sub, sup)
            }
            Axiom::EquivalentObjectProperties(members) => add_equivalent(roles, members),
            Axiom::InverseObjectProperties(first, second) => {
                let flipped = inverse(second);
                add_equal(roles, first, &flipped)
            }
            Axiom::SymmetricObjectProperty(role) => {
                let flipped = inverse(role);
                add_inclusion(roles, role, &flipped)
            }
            Axiom::TransitiveObjectProperty(role) => add_transitive(roles, role),
            _ => Some(roles),
        };
        match roles {
            Some(roles) => hierarchy_from(items, index + 1, roles),
            None => None,
        }
    } else {
        Some(roles)
    }
}
/// The role hierarchy of a closure, closed under composition and inverses.
pub fn role_hierarchy(items: &Vec<AnnotatedAxiom>) -> Option<RoleHierarchy> {
    hierarchy_from(
        items,
        0,
        RoleHierarchy {
            inclusions: Vec::new(),
            transitive: Vec::new(),
        },
    )
}
/// Whether neither role of an inclusion is a built-in object property.
fn pair_proper(sub: &ObjectPropertyExpression, sup: &ObjectPropertyExpression) -> bool {
    let lower = role_proper(sub);
    let upper = role_proper(sup);
    lower && upper
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
/// Whether no member names a built-in object property.
fn members_proper(members: &AtLeastTwo<ObjectPropertyExpression>) -> bool {
    let first = role_proper(&members.first);
    let second = role_proper(&members.second);
    first && second && rest_proper(&members.rest, 0)
}
/// Whether no object property assertion or role axiom in `items[index..]` uses
/// a built-in object property.
fn roles_proper(items: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < items.len() {
        let here = match &items[index].axiom {
            Axiom::ObjectPropertyAssertion(property, _, _) => role_proper(property),
            Axiom::NegativeObjectPropertyAssertion(property, _, _) => role_proper(property),
            Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(sub), sup) => {
                pair_proper(sub, sup)
            }
            Axiom::EquivalentObjectProperties(members) => members_proper(members),
            Axiom::InverseObjectProperties(first, second) => pair_proper(first, second),
            Axiom::SymmetricObjectProperty(property) => role_proper(property),
            Axiom::TransitiveObjectProperty(property) => role_proper(property),
            _ => true,
        };
        here && roles_proper(items, index + 1)
    } else {
        true
    }
}

/// `facts` with the class assertions of `items[index..]` at their individuals'
/// nodes; `None` when a class expression is outside ALCI or there is no room.
fn assertions_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    index: usize,
    mut facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::ClassAssertion(class, member) => match translate(class, true) {
                Some(concept) => {
                    if facts.len() < usize::MAX {
                        facts.push(Fact {
                            node: position(nodes, member, 0),
                            concept,
                        });
                        assertions_from(items, nodes, index + 1, facts)
                    } else {
                        None
                    }
                }
                None => None,
            },
            _ => assertions_from(items, nodes, index + 1, facts),
        }
    } else {
        Some(facts)
    }
}
/// `links` with a link for every object property assertion of `items[index..]`;
/// `None` when there is no room.
fn links_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    index: usize,
    mut links: Vec<Link>,
) -> Option<Vec<Link>> {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::ObjectPropertyAssertion(role, source, target) => {
                if links.len() < usize::MAX {
                    links.push(Link {
                        role: copy_role(role),
                        from: position(nodes, source, 0),
                        to: position(nodes, target, 0),
                    });
                    links_from(items, nodes, index + 1, links)
                } else {
                    None
                }
            }
            _ => links_from(items, nodes, index + 1, links),
        }
    } else {
        Some(links)
    }
}
/// Whether the link goes from `source` to `target` along `role`.
fn link_is(link: &Link, role: &ObjectPropertyExpression, source: usize, target: usize) -> bool {
    if link.from == source {
        if link.to == target {
            same_role(&link.role, role)
        } else {
            false
        }
    } else {
        false
    }
}
/// Whether a link in `links[index..]` relates `source` to `target` along
/// `role`: it goes from `source` to `target` along `role`, or back along
/// `flipped`, the inverse of `role`.
fn linked_from(
    links: &Vec<Link>,
    index: usize,
    role: &ObjectPropertyExpression,
    flipped: &ObjectPropertyExpression,
    source: usize,
    target: usize,
) -> bool {
    if index < links.len() {
        if link_is(&links[index], role, source, target) {
            true
        } else if link_is(&links[index], flipped, target, source) {
            true
        } else {
            linked_from(links, index + 1, role, flipped, source, target)
        }
    } else {
        false
    }
}
/// Whether a negative object property assertion in `items[index..]` denies a
/// link.
fn denied_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    links: &Vec<Link>,
    index: usize,
) -> bool {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::NegativeObjectPropertyAssertion(role, source, target) => {
                let flipped = inverse(role);
                let here = linked_from(
                    links,
                    0,
                    role,
                    &flipped,
                    position(nodes, source, 0),
                    position(nodes, target, 0),
                );
                here || denied_from(items, nodes, links, index + 1)
            }
            _ => denied_from(items, nodes, links, index + 1),
        }
    } else {
        false
    }
}
/// An axiom closure read once for many queries: its individuals, what its class
/// axioms require, the facts of its class assertions, its role hierarchy, the
/// links of its object property assertions, and whether a negative object
/// property assertion denies one of them.
pub struct Prepared {
    pub nodes: Vec<Individual>,
    pub parts: Parts,
    pub facts: Vec<Fact>,
    pub roles: RoleHierarchy,
    pub links: Vec<Link>,
    pub denied: bool,
}
/// Read an axiom closure for queries; `None` when it is outside the supported
/// fragment or a list would exceed the `usize` range.
pub fn prepare(items: &Vec<AnnotatedAxiom>) -> Option<Prepared> {
    let nodes = match individuals_from(items, 0, Vec::new()) {
        Some(nodes) => nodes,
        None => return None,
    };
    let parts = match class_parts(items) {
        Some(parts) => parts,
        None => return None,
    };
    let facts = match assertions_from(items, &nodes, 0, Vec::new()) {
        Some(facts) => facts,
        None => return None,
    };
    let roles = match role_hierarchy(items) {
        Some(roles) => roles,
        None => return None,
    };
    if !(proper(&parts.axioms)
        && definitions_proper(&parts.definitions, 0)
        && facts_proper(&facts, 0)
        && roles_proper(items, 0))
    {
        return None;
    }
    if has_negative(items, 0) && !(roles.inclusions.len() == 0 && roles.transitive.len() == 0) {
        return None;
    }
    let links = match links_from(items, &nodes, 0, Vec::new()) {
        Some(links) => links,
        None => return None,
    };
    let denied = denied_from(items, &nodes, &links, 0);
    Some(Prepared {
        nodes,
        parts,
        facts,
        roles,
        links,
        denied,
    })
}
/// Whether the prepared closure has a model with elements for its individuals
/// and one more element, in which the `extra` facts hold at their nodes: node 0
/// is the further element and node `i + 1` the individual `nodes[i]`.
fn prepared_satisfiable(prepared: &Prepared, extra: &Vec<Fact>) -> Option<bool> {
    if !facts_proper(extra, 0) {
        return None;
    }
    if prepared.denied {
        return Some(false);
    }
    satisfiable(
        prepared.nodes.len() + 1,
        extra,
        &prepared.facts,
        &prepared.links,
        &prepared.parts.axioms,
        &prepared.parts.definitions,
        &prepared.roles,
    )
}
/// Whether the prepared closure has a model at all.
pub fn prepared_consistent(prepared: &Prepared) -> Option<bool> {
    prepared_satisfiable(prepared, &Vec::new())
}
/// Whether some model of the prepared closure has an instance of the class
/// expression.
pub fn prepared_class_satisfiable(prepared: &Prepared, class: &ClassExpression) -> Option<bool> {
    let concept = match translate(class, true) {
        Some(concept) => concept,
        None => return None,
    };
    let mut extra = Vec::new();
    extra.push(Fact { node: 0, concept });
    prepared_satisfiable(prepared, &extra)
}
/// Whether every instance of `sub` is an instance of `sup` in every model of
/// the prepared closure.
pub fn prepared_subsumed(
    prepared: &Prepared,
    sub: &ClassExpression,
    sup: &ClassExpression,
) -> Option<bool> {
    let inside = match translate(sub, true) {
        Some(inside) => inside,
        None => return None,
    };
    let outside = match translate(sup, false) {
        Some(outside) => outside,
        None => return None,
    };
    let mut extra = Vec::new();
    extra.push(Fact {
        node: 0,
        concept: inside,
    });
    extra.push(Fact {
        node: 0,
        concept: outside,
    });
    match prepared_satisfiable(prepared, &extra) {
        Some(satisfiable) => Some(!satisfiable),
        None => None,
    }
}
/// Whether the named individual is an instance of the class expression in
/// every model of the prepared closure.
pub fn prepared_instance_of(
    prepared: &Prepared,
    individual: &NamedIndividual,
    class: &ClassExpression,
) -> Option<bool> {
    let outside = match translate(class, false) {
        Some(outside) => outside,
        None => return None,
    };
    let named = Individual::Named(NamedIndividual {
        iri: copy_iri(&individual.iri),
    });
    let mut extra = Vec::new();
    extra.push(Fact {
        node: position(&prepared.nodes, &named, 0),
        concept: outside,
    });
    match prepared_satisfiable(prepared, &extra) {
        Some(satisfiable) => Some(!satisfiable),
        None => None,
    }
}
/// Whether the closure has a model at all.
pub fn consistent(items: &Vec<AnnotatedAxiom>) -> Option<bool> {
    match prepare(items) {
        Some(prepared) => prepared_consistent(&prepared),
        None => None,
    }
}
/// Whether some model of the closure has an instance of the class expression.
pub fn class_satisfiable(items: &Vec<AnnotatedAxiom>, class: &ClassExpression) -> Option<bool> {
    match prepare(items) {
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
    match prepare(items) {
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
    match prepare(items) {
        Some(prepared) => prepared_instance_of(&prepared, individual, class),
        None => None,
    }
}
