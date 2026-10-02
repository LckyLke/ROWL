//! ALC class satisfiability and subsumption with respect to an axiom closure.
//!
//! Every supported axiom becomes a concept in negation normal form that holds
//! at every element exactly when the axiom holds: `C ⊑ D` becomes `¬C ⊔ D`,
//! equivalent classes hold all together or not at all, disjoint classes are
//! pairwise excluded, a disjoint union also equates the class with the union of
//! its members, and a domain or range restricts the property's sources or
//! targets. Declarations and annotation axioms impose nothing. The conjunction
//! of these concepts is the TBox concept of the closure, which the tableau with
//! blocking decides against.
//!
//! The answer is `None` when an axiom has any other form, when a class
//! expression is outside the ALC fragment, or when a translated concept uses
//! `owl:topObjectProperty` or `owl:bottomObjectProperty` (whose fixed meaning
//! the tableau does not model) or `owl:Thing` or `owl:Nothing` as an ordinary
//! named class (the translation turns those classes into top and bottom).
#![allow(clippy::ptr_arg, clippy::question_mark)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, Class, ClassExpression, ObjectProperty,
    ObjectPropertyExpression,
};
use crate::nnf::{connect, copy_iri, nnf, NnfConcept};
use crate::tbox::satisfiable_in;

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
/// `owl:Thing` or `owl:Nothing`.
fn builtin_class(class: &Class) -> bool {
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
        Axiom::AnnotationAssertion(_, _, _) => Some(NnfConcept::Top),
        Axiom::SubAnnotationPropertyOf(_, _) => Some(NnfConcept::Top),
        Axiom::AnnotationPropertyDomain(_, _) => Some(NnfConcept::Top),
        Axiom::AnnotationPropertyRange(_, _) => Some(NnfConcept::Top),
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
/// every axiom holds. `None` when some axiom is not supported.
pub fn internalize(items: &Vec<AnnotatedAxiom>) -> Option<NnfConcept> {
    internalize_from(items, 0, NnfConcept::Top)
}
/// Whether the closure has a model at all.
pub fn consistent(items: &Vec<AnnotatedAxiom>) -> Option<bool> {
    let axioms = match internalize(items) {
        Some(axioms) => axioms,
        None => return None,
    };
    if proper(&axioms) {
        Some(satisfiable_in(&NnfConcept::Top, &axioms))
    } else {
        None
    }
}
/// Whether some model of the closure has an instance of the class expression.
pub fn class_satisfiable(items: &Vec<AnnotatedAxiom>, class: &ClassExpression) -> Option<bool> {
    let axioms = match internalize(items) {
        Some(axioms) => axioms,
        None => return None,
    };
    let concept = match nnf(class, true) {
        Some(concept) => concept,
        None => return None,
    };
    if proper(&axioms) && proper(&concept) {
        Some(satisfiable_in(&concept, &axioms))
    } else {
        None
    }
}
/// Whether every instance of `sub` is an instance of `sup` in every model of the closure.
pub fn subsumed(
    items: &Vec<AnnotatedAxiom>,
    sub: &ClassExpression,
    sup: &ClassExpression,
) -> Option<bool> {
    let axioms = match internalize(items) {
        Some(axioms) => axioms,
        None => return None,
    };
    let inside = match nnf(sub, true) {
        Some(inside) => inside,
        None => return None,
    };
    let outside = match nnf(sup, false) {
        Some(outside) => outside,
        None => return None,
    };
    let concept = NnfConcept::And(Box::new(inside), Box::new(outside));
    if proper(&axioms) && proper(&concept) {
        Some(!satisfiable_in(&concept, &axioms))
    } else {
        None
    }
}
