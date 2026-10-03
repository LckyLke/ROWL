//! Consistency, class satisfiability, subsumption and instance checking for an
//! axiom closure with assertions: SHI decided by the completion graph tableau,
//! and SHOIQ, with number restrictions on simple roles and nominals of named
//! individuals, by the completion forest.
//!
//! Class expressions are translated into ALCIQO concepts (see `concepts`). Every
//! class axiom becomes inclusions `C ⊑ D`: a subclass axiom is one, equivalent
//! classes include the first member in every other member and back, disjoint
//! classes include every member in the complement of every later member, and a
//! disjoint union includes the class in the union of its members and every
//! member in the class, which the members also partition. An inclusion whose
//! left side is absorbable becomes a definition `A ⊑ C`, which the tableau
//! unfolds only at nodes that list `A`: a named class absorbs directly,
//! `∃r.E ⊑ D` becomes `E ⊑ ∀r⁻.D`, and `E ⊓ F ⊓ … ⊑ D` becomes
//! `E ⊑ ¬F ⊔ … ⊔ D`. Every other inclusion conjoins `¬C ⊔ D` onto the TBox
//! concept, which holds everywhere. A domain conjoins `∀r⁻.C`, a range
//! `∀r.C`, a functional property `≤1 r.⊤` and an inverse functional property
//! `≤1 r⁻.⊤`.
//!
//! The role axioms `SubObjectPropertyOf` without chains,
//! `EquivalentObjectProperties`, `InverseObjectProperties`,
//! `SymmetricObjectProperty` and `TransitiveObjectProperty`, on named or inverse
//! object properties, become a role hierarchy. Every inclusion is added with
//! its inverse, each together with its compositions with the inclusions already
//! listed, and every transitive property with its inverse, so the hierarchy
//! stays closed as the tableaux require.
//!
//! Every individual of an assertion, equality or inequality, and every
//! individual of a nominal of the closure, gets a node after node 0, which
//! stands for one more element, and the members of a `SameIndividual` axiom
//! share the node of their representative. Class assertions and the query's
//! concepts are facts at those nodes, and object property assertions are links.
//! A question whose concepts have no number restriction and no nominal goes to
//! the completion graph tableau, unless the closure has negative assertions next
//! to role axioms. There, without role axioms, a negative object property
//! assertion contradicts the closure exactly when a link relates the same nodes
//! along the same property, in either orientation, because the tableau's models
//! relate named individuals only along links, and a `DifferentIndividuals`
//! axiom contradicts the closure exactly when two of its members share a node,
//! because the tableau's models keep different nodes apart. Every other
//! question goes to the completion forest, which merges individuals when a
//! maximum restriction or a nominal requires it, with three more kinds of
//! facts: the nominal `{a}` of every individual at its node, the members of
//! every inequality outside each other's nominals, and `∀r.¬{b}` at the source
//! `a` of every negative assertion `¬r(a, b)`.
//!
//! `prepare` reads a closure once: its individuals, class parts, role hierarchy,
//! facts and links, and the check of its negative assertions. The `prepared_`
//! queries then only translate their class expressions and run a tableau, so
//! many questions about one closure share that work; the plain queries prepare
//! and ask once.
//!
//! The answer is `None` when an axiom has any other form, when a class
//! expression is outside ALCIQO, when a concept, definition, role axiom or
//! assertion uses `owl:topObjectProperty` or `owl:bottomObjectProperty` (whose
//! fixed meaning the tableaux do not model), when a nominal is of an anonymous
//! individual or, in a question, of an individual the closure does not have,
//! when the completion forest meets a nominal below an anonymous element of a
//! tree, when a number restriction counts along a role that is not simple, or
//! when a list would exceed the `usize` range.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::manual_map,
    clippy::vec_init_then_push,
    clippy::len_zero,
    clippy::needless_return,
    clippy::if_same_then_else
)] // Indexed operations, explicit branches and pushes without macros for the pinned extraction subset.
use crate::alc_ontology::{
    builtin_class, has_negative, individuals_from, intern, position, role_proper,
};
use crate::completion::{satisfiable, Definition, Fact, Link};
use crate::concepts::{copy_individual, copy_role, inverse, same_role, translate, Concept};
use crate::forest;
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

/// Whether the individual is a named one, which a reinterpretation of the
/// anonymous individuals leaves in place.
fn named_individual(individual: &Individual) -> bool {
    match individual {
        Individual::Named(_) => true,
        Individual::Anonymous(_) => false,
    }
}
/// Whether no built-in class occurs as a named class, no built-in object
/// property as a role and no anonymous individual in a nominal, so the tableaux
/// read every name as an ordinary one.
fn proper(concept: &Concept) -> bool {
    match concept {
        Concept::Top => true,
        Concept::Bottom => true,
        Concept::Atom(class) => !builtin_class(class),
        Concept::NotAtom(class) => !builtin_class(class),
        Concept::One(individual) => named_individual(individual),
        Concept::NotOne(individual) => named_individual(individual),
        Concept::And(left, right) => proper(left) && proper(right),
        Concept::Or(left, right) => proper(left) && proper(right),
        Concept::Exists(role, filler) => role_proper(role) && proper(filler),
        Concept::Forall(role, filler) => role_proper(role) && proper(filler),
        Concept::AtLeast(_, role, filler) => role_proper(role) && proper(filler),
        Concept::AtMost(_, role, filler) => role_proper(role) && proper(filler),
    }
}
/// Whether a number restriction occurs, which only the completion forest
/// counts.
fn counts(concept: &Concept) -> bool {
    match concept {
        Concept::And(left, right) => counts(left) || counts(right),
        Concept::Or(left, right) => counts(left) || counts(right),
        Concept::Exists(_, filler) => counts(filler),
        Concept::Forall(_, filler) => counts(filler),
        Concept::AtLeast(_, _, _) => true,
        Concept::AtMost(_, _, _) => true,
        _ => false,
    }
}
/// Whether a definition in `definitions[index..]` counts.
fn definitions_count(definitions: &Vec<Definition>, index: usize) -> bool {
    if index < definitions.len() {
        counts(&definitions[index].concept) || definitions_count(definitions, index + 1)
    } else {
        false
    }
}
/// Whether a fact in `facts[index..]` counts.
fn facts_count(facts: &Vec<Fact>, index: usize) -> bool {
    if index < facts.len() {
        counts(&facts[index].concept) || facts_count(facts, index + 1)
    } else {
        false
    }
}
/// Whether the TBox concept, a definition or a fact counts.
fn closure_counts(parts: &Parts, facts: &Vec<Fact>) -> bool {
    counts(&parts.axioms) || definitions_count(&parts.definitions, 0) || facts_count(facts, 0)
}
/// Whether a nominal occurs, which only the completion forest decides.
fn nominal(concept: &Concept) -> bool {
    match concept {
        Concept::One(_) => true,
        Concept::NotOne(_) => true,
        Concept::And(left, right) => nominal(left) || nominal(right),
        Concept::Or(left, right) => nominal(left) || nominal(right),
        Concept::Exists(_, filler) => nominal(filler),
        Concept::Forall(_, filler) => nominal(filler),
        Concept::AtLeast(_, _, filler) => nominal(filler),
        Concept::AtMost(_, _, filler) => nominal(filler),
        _ => false,
    }
}
/// Whether a definition in `definitions[index..]` has a nominal.
fn definitions_nominal(definitions: &Vec<Definition>, index: usize) -> bool {
    if index < definitions.len() {
        nominal(&definitions[index].concept) || definitions_nominal(definitions, index + 1)
    } else {
        false
    }
}
/// Whether a fact in `facts[index..]` has a nominal.
fn facts_nominal(facts: &Vec<Fact>, index: usize) -> bool {
    if index < facts.len() {
        nominal(&facts[index].concept) || facts_nominal(facts, index + 1)
    } else {
        false
    }
}
/// Whether the TBox concept, a definition or a fact has a nominal.
fn closure_nominal(parts: &Parts, facts: &Vec<Fact>) -> bool {
    nominal(&parts.axioms) || definitions_nominal(&parts.definitions, 0) || facts_nominal(facts, 0)
}
/// Whether the individual of every nominal of `concept` has a node.
fn known(nodes: &Vec<Individual>, concept: &Concept) -> bool {
    match concept {
        Concept::One(individual) => position(nodes, individual, 0) != 0,
        Concept::NotOne(individual) => position(nodes, individual, 0) != 0,
        Concept::And(left, right) => known(nodes, left) && known(nodes, right),
        Concept::Or(left, right) => known(nodes, left) && known(nodes, right),
        Concept::Exists(_, filler) => known(nodes, filler),
        Concept::Forall(_, filler) => known(nodes, filler),
        Concept::AtLeast(_, _, filler) => known(nodes, filler),
        Concept::AtMost(_, _, filler) => known(nodes, filler),
        _ => true,
    }
}
/// Whether the individual of every nominal of a fact in `facts[index..]` has a
/// node.
fn facts_known(nodes: &Vec<Individual>, facts: &Vec<Fact>, index: usize) -> bool {
    if index < facts.len() {
        known(nodes, &facts[index].concept) && facts_known(nodes, facts, index + 1)
    } else {
        true
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
        Axiom::FunctionalObjectProperty(property) => Some(conjoin(
            parts,
            Concept::AtMost(1, copy_role(property), Box::new(Concept::Top)),
        )),
        Axiom::InverseFunctionalObjectProperty(property) => Some(conjoin(
            parts,
            Concept::AtMost(1, inverse(property), Box::new(Concept::Top)),
        )),
        Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(_), _) => Some(parts),
        Axiom::EquivalentObjectProperties(_) => Some(parts),
        Axiom::InverseObjectProperties(_, _) => Some(parts),
        Axiom::SymmetricObjectProperty(_) => Some(parts),
        Axiom::TransitiveObjectProperty(_) => Some(parts),
        Axiom::AnnotationAssertion(_, _, _) => Some(parts),
        Axiom::SubAnnotationPropertyOf(_, _) => Some(parts),
        Axiom::AnnotationPropertyDomain(_, _) => Some(parts),
        Axiom::AnnotationPropertyRange(_, _) => Some(parts),
        Axiom::SameIndividual(_) => Some(parts),
        Axiom::DifferentIndividuals(_) => Some(parts),
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

/// `nodes` with every new member of `rest[index..]`; `None` when there is no
/// room.
fn intern_rest(
    nodes: Vec<Individual>,
    rest: &Vec<Individual>,
    index: usize,
) -> Option<Vec<Individual>> {
    if index < rest.len() {
        match intern(nodes, &rest[index]) {
            Some(nodes) => intern_rest(nodes, rest, index + 1),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// `nodes` with every new member of an equality or inequality.
fn intern_members(
    nodes: Vec<Individual>,
    members: &AtLeastTwo<Individual>,
) -> Option<Vec<Individual>> {
    let nodes = match intern(nodes, &members.first) {
        Some(nodes) => nodes,
        None => return None,
    };
    let nodes = match intern(nodes, &members.second) {
        Some(nodes) => nodes,
        None => return None,
    };
    intern_rest(nodes, &members.rest, 0)
}
/// `nodes` with every new member of the equalities and inequalities of
/// `items[index..]`, in order of first occurrence.
fn members_from(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    nodes: Vec<Individual>,
) -> Option<Vec<Individual>> {
    if index < items.len() {
        let nodes = match &items[index].axiom {
            Axiom::SameIndividual(members) => intern_members(nodes, members),
            Axiom::DifferentIndividuals(members) => intern_members(nodes, members),
            _ => Some(nodes),
        };
        match nodes {
            Some(nodes) => members_from(items, index + 1, nodes),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// `out` with every node from `index` below `count` as its own representative.
fn identity_from(count: usize, index: usize, mut out: Vec<usize>) -> Vec<usize> {
    if index < count {
        out.push(index);
        identity_from(count, index + 1, out)
    } else {
        out
    }
}
/// `same` with every representative `from` in `same[index..]` replaced by
/// `into`.
fn relabel(mut same: Vec<usize>, from: usize, into: usize, index: usize) -> Vec<usize> {
    if index < same.len() {
        if same[index] == from {
            same[index] = into;
        }
        relabel(same, from, into, index + 1)
    } else {
        same
    }
}
/// `same` with the classes of the nodes `left` and `right` joined under the
/// representative of `left`.
fn unite(same: Vec<usize>, left: usize, right: usize) -> Vec<usize> {
    if left < same.len() && right < same.len() {
        let into = same[left];
        let from = same[right];
        if into == from {
            same
        } else {
            relabel(same, from, into, 0)
        }
    } else {
        same
    }
}
/// `same` with every member of `rest[index..]` joined to the node `first`.
fn unite_rest(
    same: Vec<usize>,
    nodes: &Vec<Individual>,
    first: usize,
    rest: &Vec<Individual>,
    index: usize,
) -> Vec<usize> {
    if index < rest.len() {
        let other = position(nodes, &rest[index], 0);
        let same = unite(same, first, other);
        unite_rest(same, nodes, first, rest, index + 1)
    } else {
        same
    }
}
/// `same` with the members of every equality of `items[index..]` joined.
fn equalities_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    index: usize,
    same: Vec<usize>,
) -> Vec<usize> {
    if index < items.len() {
        let same = match &items[index].axiom {
            Axiom::SameIndividual(members) => {
                let first = position(nodes, &members.first, 0);
                let second = position(nodes, &members.second, 0);
                let same = unite(same, first, second);
                unite_rest(same, nodes, first, &members.rest, 0)
            }
            _ => same,
        };
        equalities_from(items, nodes, index + 1, same)
    } else {
        same
    }
}
/// The representative of `node`, or the node itself outside `same`.
fn representative(same: &Vec<usize>, node: usize) -> usize {
    if node < same.len() {
        same[node]
    } else {
        node
    }
}
/// The node of an individual: the representative of its position.
fn node_of(nodes: &Vec<Individual>, same: &Vec<usize>, individual: &Individual) -> usize {
    representative(same, position(nodes, individual, 0))
}
/// Whether a member of `rest[index..]` has the node `node`.
fn meets(
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    node: usize,
    rest: &Vec<Individual>,
    index: usize,
) -> bool {
    if index < rest.len() {
        if node_of(nodes, same, &rest[index]) == node {
            true
        } else {
            meets(nodes, same, node, rest, index + 1)
        }
    } else {
        false
    }
}
/// Whether two members of `rest[index..]` share a node.
fn repeats(
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    rest: &Vec<Individual>,
    index: usize,
) -> bool {
    if index < rest.len() {
        let node = node_of(nodes, same, &rest[index]);
        if meets(nodes, same, node, rest, index + 1) {
            true
        } else {
            repeats(nodes, same, rest, index + 1)
        }
    } else {
        false
    }
}
/// Whether two members of an inequality share a node.
fn shares(nodes: &Vec<Individual>, same: &Vec<usize>, members: &AtLeastTwo<Individual>) -> bool {
    let first = node_of(nodes, same, &members.first);
    let second = node_of(nodes, same, &members.second);
    if first == second {
        true
    } else if meets(nodes, same, first, &members.rest, 0) {
        true
    } else if meets(nodes, same, second, &members.rest, 0) {
        true
    } else {
        repeats(nodes, same, &members.rest, 0)
    }
}
/// Whether two members of an inequality of `items[index..]` share a node.
fn clash_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    index: usize,
) -> bool {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::DifferentIndividuals(members) => {
                if shares(nodes, same, members) {
                    true
                } else {
                    clash_from(items, nodes, same, index + 1)
                }
            }
            _ => clash_from(items, nodes, same, index + 1),
        }
    } else {
        false
    }
}
/// `nodes` with every new individual of a nominal of `concept`; `None` when
/// there is no room.
fn nominal_individuals(nodes: Vec<Individual>, concept: &Concept) -> Option<Vec<Individual>> {
    match concept {
        Concept::One(individual) => intern(nodes, individual),
        Concept::NotOne(individual) => intern(nodes, individual),
        Concept::And(left, right) => match nominal_individuals(nodes, left) {
            Some(nodes) => nominal_individuals(nodes, right),
            None => None,
        },
        Concept::Or(left, right) => match nominal_individuals(nodes, left) {
            Some(nodes) => nominal_individuals(nodes, right),
            None => None,
        },
        Concept::Exists(_, filler) => nominal_individuals(nodes, filler),
        Concept::Forall(_, filler) => nominal_individuals(nodes, filler),
        Concept::AtLeast(_, _, filler) => nominal_individuals(nodes, filler),
        Concept::AtMost(_, _, filler) => nominal_individuals(nodes, filler),
        _ => Some(nodes),
    }
}
/// `nodes` with every new individual of a nominal of a definition in
/// `definitions[index..]`.
fn definition_individuals(
    nodes: Vec<Individual>,
    definitions: &Vec<Definition>,
    index: usize,
) -> Option<Vec<Individual>> {
    if index < definitions.len() {
        match nominal_individuals(nodes, &definitions[index].concept) {
            Some(nodes) => definition_individuals(nodes, definitions, index + 1),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// `nodes` with every new individual of a nominal of the concept of a class
/// expression; `None` when it is outside ALCIQO.
fn class_individuals(nodes: Vec<Individual>, class: &ClassExpression) -> Option<Vec<Individual>> {
    match translate(class, true) {
        Some(concept) => nominal_individuals(nodes, &concept),
        None => None,
    }
}
/// `nodes` with every new individual of a nominal of a class assertion in
/// `items[index..]`; `None` when a class expression is outside ALCIQO.
fn assertion_individuals(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    nodes: Vec<Individual>,
) -> Option<Vec<Individual>> {
    if index < items.len() {
        let nodes = match &items[index].axiom {
            Axiom::ClassAssertion(class, _) => class_individuals(nodes, class),
            _ => Some(nodes),
        };
        match nodes {
            Some(nodes) => assertion_individuals(items, index + 1, nodes),
            None => None,
        }
    } else {
        Some(nodes)
    }
}
/// `facts` with one more fact; `None` when there is no room.
fn add_fact(mut facts: Vec<Fact>, node: usize, concept: Concept) -> Option<Vec<Fact>> {
    if facts.len() < usize::MAX {
        facts.push(Fact { node, concept });
        Some(facts)
    } else {
        None
    }
}
/// `facts` with the nominal of every individual of `nodes[index..]` at its
/// node.
fn named_from(
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    index: usize,
    facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < nodes.len() {
        let node = node_of(nodes, same, &nodes[index]);
        match add_fact(facts, node, Concept::One(copy_individual(&nodes[index]))) {
            Some(facts) => named_from(nodes, same, index + 1, facts),
            None => None,
        }
    } else {
        Some(facts)
    }
}
/// `facts` with `member` outside the nominal of every individual of
/// `rest[index..]`.
fn apart_rest(
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    member: &Individual,
    rest: &Vec<Individual>,
    index: usize,
    facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < rest.len() {
        let node = node_of(nodes, same, member);
        match add_fact(facts, node, Concept::NotOne(copy_individual(&rest[index]))) {
            Some(facts) => apart_rest(nodes, same, member, rest, index + 1, facts),
            None => None,
        }
    } else {
        Some(facts)
    }
}
/// `facts` with every individual of `rest[index..]` outside the nominals of the
/// later ones.
fn apart_within(
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    rest: &Vec<Individual>,
    index: usize,
    facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < rest.len() {
        match apart_rest(nodes, same, &rest[index], rest, index + 1, facts) {
            Some(facts) => apart_within(nodes, same, rest, index + 1, facts),
            None => None,
        }
    } else {
        Some(facts)
    }
}
/// `facts` with every member of an inequality outside the nominals of the later
/// ones.
fn apart_members(
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    members: &AtLeastTwo<Individual>,
    facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    let node = node_of(nodes, same, &members.first);
    let facts = match add_fact(
        facts,
        node,
        Concept::NotOne(copy_individual(&members.second)),
    ) {
        Some(facts) => facts,
        None => return None,
    };
    let facts = match apart_rest(nodes, same, &members.first, &members.rest, 0, facts) {
        Some(facts) => facts,
        None => return None,
    };
    let facts = match apart_rest(nodes, same, &members.second, &members.rest, 0, facts) {
        Some(facts) => facts,
        None => return None,
    };
    apart_within(nodes, same, &members.rest, 0, facts)
}
/// `facts` with the members of every inequality of `items[index..]` apart.
fn unequal_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    index: usize,
    facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < items.len() {
        let facts = match &items[index].axiom {
            Axiom::DifferentIndividuals(members) => apart_members(nodes, same, members, facts),
            _ => Some(facts),
        };
        match facts {
            Some(facts) => unequal_from(items, nodes, same, index + 1, facts),
            None => None,
        }
    } else {
        Some(facts)
    }
}
/// `facts` with the source of every negative object property assertion of
/// `items[index..]` related along its property only outside the target's
/// nominal.
fn refused_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    index: usize,
    facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < items.len() {
        let facts = match &items[index].axiom {
            Axiom::NegativeObjectPropertyAssertion(role, source, target) => {
                let node = node_of(nodes, same, source);
                let concept = Concept::Forall(
                    copy_role(role),
                    Box::new(Concept::NotOne(copy_individual(target))),
                );
                add_fact(facts, node, concept)
            }
            _ => Some(facts),
        };
        match facts {
            Some(facts) => refused_from(items, nodes, same, index + 1, facts),
            None => None,
        }
    } else {
        Some(facts)
    }
}

/// `facts` with the class assertions of `items[index..]` at their individuals'
/// nodes; `None` when a class expression is outside ALCIQ or there is no room.
fn assertions_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    index: usize,
    mut facts: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::ClassAssertion(class, member) => match translate(class, true) {
                Some(concept) => {
                    if facts.len() < usize::MAX {
                        facts.push(Fact {
                            node: node_of(nodes, same, member),
                            concept,
                        });
                        assertions_from(items, nodes, same, index + 1, facts)
                    } else {
                        None
                    }
                }
                None => None,
            },
            _ => assertions_from(items, nodes, same, index + 1, facts),
        }
    } else {
        Some(facts)
    }
}
/// `links` with a link for every object property assertion of `items[index..]`
/// between its individuals' nodes; `None` when there is no room.
fn links_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
    index: usize,
    mut links: Vec<Link>,
) -> Option<Vec<Link>> {
    if index < items.len() {
        match &items[index].axiom {
            Axiom::ObjectPropertyAssertion(role, source, target) => {
                if links.len() < usize::MAX {
                    links.push(Link {
                        role: copy_role(role),
                        from: node_of(nodes, same, source),
                        to: node_of(nodes, same, target),
                    });
                    links_from(items, nodes, same, index + 1, links)
                } else {
                    None
                }
            }
            _ => links_from(items, nodes, same, index + 1, links),
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
/// link between its individuals' nodes.
fn denied_from(
    items: &Vec<AnnotatedAxiom>,
    nodes: &Vec<Individual>,
    same: &Vec<usize>,
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
                    node_of(nodes, same, source),
                    node_of(nodes, same, target),
                );
                here || denied_from(items, nodes, same, links, index + 1)
            }
            _ => denied_from(items, nodes, same, links, index + 1),
        }
    } else {
        false
    }
}
/// Whether negative object property assertions meet role axioms, which only
/// the completion forest decides.
fn tangled(items: &Vec<AnnotatedAxiom>, roles: &RoleHierarchy) -> bool {
    has_negative(items, 0) && !(roles.inclusions.len() == 0 && roles.transitive.len() == 0)
}
/// An axiom closure read once for many queries: its individuals, the
/// representative node of every node, what its class axioms require, the facts
/// of its class assertions, the facts the completion forest also gets (the
/// nominal of every individual at its node, the members of every inequality
/// outside each other's nominals, and the source of every negative object
/// property assertion related along its property only outside the target's
/// nominal), its role hierarchy, the links of its object property assertions,
/// whether a negative object property assertion denies one of them, whether
/// every question goes to the completion forest, and whether two members of an
/// inequality share a node.
pub struct Prepared {
    pub nodes: Vec<Individual>,
    pub same: Vec<usize>,
    pub parts: Parts,
    pub facts: Vec<Fact>,
    pub bound: Vec<Fact>,
    pub roles: RoleHierarchy,
    pub links: Vec<Link>,
    pub denied: bool,
    pub forest: bool,
    pub clash: bool,
}
/// Read an axiom closure for queries; `None` when it is outside the supported
/// fragment or a list would exceed the `usize` range.
pub fn prepare(items: &Vec<AnnotatedAxiom>) -> Option<Prepared> {
    let nodes = match individuals_from(items, 0, Vec::new()) {
        Some(nodes) => nodes,
        None => return None,
    };
    let nodes = match members_from(items, 0, nodes) {
        Some(nodes) => nodes,
        None => return None,
    };
    let parts = match class_parts(items) {
        Some(parts) => parts,
        None => return None,
    };
    let nodes = match nominal_individuals(nodes, &parts.axioms) {
        Some(nodes) => nodes,
        None => return None,
    };
    let nodes = match definition_individuals(nodes, &parts.definitions, 0) {
        Some(nodes) => nodes,
        None => return None,
    };
    let nodes = match assertion_individuals(items, 0, nodes) {
        Some(nodes) => nodes,
        None => return None,
    };
    let start = identity_from(nodes.len() + 1, 0, Vec::new());
    let same = equalities_from(items, &nodes, 0, start);
    let facts = match assertions_from(items, &nodes, &same, 0, Vec::new()) {
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
    let links = match links_from(items, &nodes, &same, 0, Vec::new()) {
        Some(links) => links,
        None => return None,
    };
    let bound = match assertions_from(items, &nodes, &same, 0, Vec::new()) {
        Some(bound) => bound,
        None => return None,
    };
    let bound = match named_from(&nodes, &same, 0, bound) {
        Some(bound) => bound,
        None => return None,
    };
    let bound = match unequal_from(items, &nodes, &same, 0, bound) {
        Some(bound) => bound,
        None => return None,
    };
    let bound = match refused_from(items, &nodes, &same, 0, bound) {
        Some(bound) => bound,
        None => return None,
    };
    let denied = denied_from(items, &nodes, &same, &links, 0);
    let forest =
        closure_counts(&parts, &facts) || closure_nominal(&parts, &facts) || tangled(items, &roles);
    let clash = clash_from(items, &nodes, &same, 0);
    Some(Prepared {
        nodes,
        same,
        parts,
        facts,
        bound,
        roles,
        links,
        denied,
        forest,
        clash,
    })
}
/// Whether the question goes to the completion forest: the prepared closure
/// does, or the extra facts count or have a nominal.
fn question_forest(prepared: &Prepared, extra: &Vec<Fact>) -> bool {
    prepared.forest || facts_count(extra, 0) || facts_nominal(extra, 0)
}
/// Whether the prepared closure has a model with elements for its individuals
/// and one more element, in which the `extra` facts hold at their nodes: node 0
/// is the further element and node `i + 1` the individual `nodes[i]`, which
/// sits at the node of its representative. An inequality two of whose members
/// share a node rules out every model. A question that counts or has a
/// nominal, or about a closure with negative assertions next to role axioms,
/// goes to the completion forest with the facts it also gets; every other
/// question to the completion graph tableau.
fn prepared_satisfiable(prepared: &Prepared, extra: &Vec<Fact>) -> Option<bool> {
    if !facts_proper(extra, 0) {
        return None;
    }
    if !facts_known(&prepared.nodes, extra, 0) {
        return None;
    }
    if prepared.clash {
        return Some(false);
    }
    if question_forest(prepared, extra) {
        return forest::satisfiable(
            prepared.nodes.len() + 1,
            extra,
            &prepared.bound,
            &prepared.links,
            &prepared.parts.axioms,
            &prepared.parts.definitions,
            &prepared.roles,
        );
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
        node: node_of(&prepared.nodes, &prepared.same, &named),
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
