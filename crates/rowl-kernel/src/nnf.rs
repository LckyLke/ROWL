//! Negation normal form for the class expressions the tableau decides.
//!
//! The supported fragment is ALC: named classes, intersections, unions,
//! complements, and existential and universal restrictions on named object
//! properties. `owl:Thing` and `owl:Nothing` become the top and bottom concepts.
//! Every other expression returns `None`; later reasoner stages extend the
//! fragment. Negation is pushed inward, so it only occurs on named classes.
#![allow(clippy::ptr_arg, clippy::question_mark)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::class_equality::{is_nothing, is_thing};
use crate::model::{
    AtLeastTwo, Class, ClassExpression, Iri, ObjectProperty, ObjectPropertyExpression,
};

/// A concept in negation normal form; the type admits no other negation.
pub enum NnfConcept {
    Top,
    Bottom,
    Atom(Class),
    NotAtom(Class),
    And(Box<NnfConcept>, Box<NnfConcept>),
    Or(Box<NnfConcept>, Box<NnfConcept>),
    Exists(ObjectProperty, Box<NnfConcept>),
    Forall(ObjectProperty, Box<NnfConcept>),
}

fn copy_from(source: &Vec<u8>, index: usize, mut target: Vec<u8>) -> Vec<u8> {
    if index < source.len() {
        target.push(source[index]);
        copy_from(source, index + 1, target)
    } else {
        target
    }
}
fn copy_iri(iri: &Iri) -> Iri {
    Iri {
        spelling: copy_from(&iri.spelling, 0, Vec::new()),
    }
}
/// A named class, a built-in top/bottom class, or its complement.
fn named(expression: &ClassExpression, class: &Class, positive: bool) -> NnfConcept {
    if is_thing(expression) {
        if positive {
            NnfConcept::Top
        } else {
            NnfConcept::Bottom
        }
    } else if is_nothing(expression) {
        if positive {
            NnfConcept::Bottom
        } else {
            NnfConcept::Top
        }
    } else {
        let copied = Class {
            iri: copy_iri(&class.iri),
        };
        if positive {
            NnfConcept::Atom(copied)
        } else {
            NnfConcept::NotAtom(copied)
        }
    }
}
fn join(conjunctive: bool, left: NnfConcept, right: NnfConcept) -> NnfConcept {
    if conjunctive {
        NnfConcept::And(Box::new(left), Box::new(right))
    } else {
        NnfConcept::Or(Box::new(left), Box::new(right))
    }
}
/// Join the translations of `values[index..]` onto `joined`, left-nested.
fn fold_from(
    values: &Vec<ClassExpression>,
    index: usize,
    positive: bool,
    conjunctive: bool,
    joined: NnfConcept,
) -> Option<NnfConcept> {
    if index < values.len() {
        let next = match nnf(&values[index], positive) {
            Some(next) => next,
            None => return None,
        };
        fold_from(
            values,
            index + 1,
            positive,
            conjunctive,
            join(conjunctive, joined, next),
        )
    } else {
        Some(joined)
    }
}
/// Translate every member and join them all with one connective.
fn connect(
    members: &AtLeastTwo<ClassExpression>,
    positive: bool,
    conjunctive: bool,
) -> Option<NnfConcept> {
    let first = match nnf(&members.first, positive) {
        Some(first) => first,
        None => return None,
    };
    let second = match nnf(&members.second, positive) {
        Some(second) => second,
        None => return None,
    };
    fold_from(
        &members.rest,
        0,
        positive,
        conjunctive,
        join(conjunctive, first, second),
    )
}
/// An existential or universal restriction on a named object property.
fn restriction(
    property: &ObjectPropertyExpression,
    filler: &ClassExpression,
    positive: bool,
    existential: bool,
) -> Option<NnfConcept> {
    let role = match property {
        ObjectPropertyExpression::Property(p) => ObjectProperty {
            iri: copy_iri(&p.iri),
        },
        ObjectPropertyExpression::Inverse(_) => return None,
    };
    let inner = match nnf(filler, positive) {
        Some(inner) => inner,
        None => return None,
    };
    if existential {
        Some(NnfConcept::Exists(role, Box::new(inner)))
    } else {
        Some(NnfConcept::Forall(role, Box::new(inner)))
    }
}
/// Translate a class expression (`positive`) or its complement (`!positive`)
/// into negation normal form. De Morgan's laws turn negated intersections into
/// unions and back, and negated existential restrictions into universal ones
/// and back. Returns `None` outside the supported ALC fragment.
pub fn nnf(expression: &ClassExpression, positive: bool) -> Option<NnfConcept> {
    match expression {
        ClassExpression::Class(class) => Some(named(expression, class, positive)),
        ClassExpression::ObjectIntersectionOf(members) => connect(members, positive, positive),
        ClassExpression::ObjectUnionOf(members) => connect(members, positive, !positive),
        ClassExpression::ObjectComplementOf(inner) => nnf(inner, !positive),
        ClassExpression::ObjectSomeValuesFrom(property, filler) => {
            restriction(property, filler, positive, positive)
        }
        ClassExpression::ObjectAllValuesFrom(property, filler) => {
            restriction(property, filler, positive, !positive)
        }
        _ => None,
    }
}
