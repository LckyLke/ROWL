//! Concepts in negation normal form with inverse roles, and their translation
//! from OWL class expressions.
//!
//! The supported fragment is ALCI: named classes, intersections, unions,
//! complements, and existential and universal restrictions on object property
//! expressions, named or inverse. `owl:Thing` and `owl:Nothing` become the top
//! and bottom concepts. Every other expression returns `None`. Negation is
//! pushed inward, so it only occurs on named classes. The completion graph
//! tableau decides these concepts; `nnf` keeps the inverse-free concepts of the
//! earlier tableaux.
#![allow(clippy::ptr_arg, clippy::question_mark)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::class_equality::{is_nothing, is_thing};
use crate::model::{AtLeastTwo, Class, ClassExpression, ObjectProperty, ObjectPropertyExpression};
use crate::nnf::copy_iri;
use crate::symbols::same_spelling;

/// A concept in negation normal form whose roles are object property
/// expressions; the type admits no other negation.
pub enum Concept {
    Top,
    Bottom,
    Atom(Class),
    NotAtom(Class),
    And(Box<Concept>, Box<Concept>),
    Or(Box<Concept>, Box<Concept>),
    Exists(ObjectPropertyExpression, Box<Concept>),
    Forall(ObjectPropertyExpression, Box<Concept>),
}

/// A copy of an object property expression.
pub(crate) fn copy_role(role: &ObjectPropertyExpression) -> ObjectPropertyExpression {
    match role {
        ObjectPropertyExpression::Property(property) => {
            ObjectPropertyExpression::Property(ObjectProperty {
                iri: copy_iri(&property.iri),
            })
        }
        ObjectPropertyExpression::Inverse(property) => {
            ObjectPropertyExpression::Inverse(ObjectProperty {
                iri: copy_iri(&property.iri),
            })
        }
    }
}
/// The inverse of an object property expression.
pub fn inverse(role: &ObjectPropertyExpression) -> ObjectPropertyExpression {
    match role {
        ObjectPropertyExpression::Property(property) => {
            ObjectPropertyExpression::Inverse(ObjectProperty {
                iri: copy_iri(&property.iri),
            })
        }
        ObjectPropertyExpression::Inverse(property) => {
            ObjectPropertyExpression::Property(ObjectProperty {
                iri: copy_iri(&property.iri),
            })
        }
    }
}
/// The same expression: the same orientation and the same exact spelling.
pub fn same_role(left: &ObjectPropertyExpression, right: &ObjectPropertyExpression) -> bool {
    match (left, right) {
        (ObjectPropertyExpression::Property(a), ObjectPropertyExpression::Property(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (ObjectPropertyExpression::Inverse(a), ObjectPropertyExpression::Inverse(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        _ => false,
    }
}
/// A named class, a built-in top/bottom class, or its complement.
fn named(expression: &ClassExpression, class: &Class, positive: bool) -> Concept {
    if is_thing(expression) {
        if positive {
            Concept::Top
        } else {
            Concept::Bottom
        }
    } else if is_nothing(expression) {
        if positive {
            Concept::Bottom
        } else {
            Concept::Top
        }
    } else {
        let copied = Class {
            iri: copy_iri(&class.iri),
        };
        if positive {
            Concept::Atom(copied)
        } else {
            Concept::NotAtom(copied)
        }
    }
}
fn join(conjunctive: bool, left: Concept, right: Concept) -> Concept {
    if conjunctive {
        Concept::And(Box::new(left), Box::new(right))
    } else {
        Concept::Or(Box::new(left), Box::new(right))
    }
}
/// Join the translations of `values[index..]` onto `joined`, left-nested.
fn fold_from(
    values: &Vec<ClassExpression>,
    index: usize,
    positive: bool,
    conjunctive: bool,
    joined: Concept,
) -> Option<Concept> {
    if index < values.len() {
        let next = match translate(&values[index], positive) {
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
) -> Option<Concept> {
    let first = match translate(&members.first, positive) {
        Some(first) => first,
        None => return None,
    };
    let second = match translate(&members.second, positive) {
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
/// An existential or universal restriction on an object property expression.
fn restriction(
    property: &ObjectPropertyExpression,
    filler: &ClassExpression,
    positive: bool,
    existential: bool,
) -> Option<Concept> {
    let inner = match translate(filler, positive) {
        Some(inner) => inner,
        None => return None,
    };
    if existential {
        Some(Concept::Exists(copy_role(property), Box::new(inner)))
    } else {
        Some(Concept::Forall(copy_role(property), Box::new(inner)))
    }
}
/// Translate a class expression (`positive`) or its complement (`!positive`)
/// into negation normal form. De Morgan's laws turn negated intersections into
/// unions and back, and negated existential restrictions into universal ones
/// and back. Returns `None` outside the supported ALCI fragment.
pub fn translate(expression: &ClassExpression, positive: bool) -> Option<Concept> {
    match expression {
        ClassExpression::Class(class) => Some(named(expression, class, positive)),
        ClassExpression::ObjectIntersectionOf(members) => connect(members, positive, positive),
        ClassExpression::ObjectUnionOf(members) => connect(members, positive, !positive),
        ClassExpression::ObjectComplementOf(inner) => translate(inner, !positive),
        ClassExpression::ObjectSomeValuesFrom(property, filler) => {
            restriction(property, filler, positive, positive)
        }
        ClassExpression::ObjectAllValuesFrom(property, filler) => {
            restriction(property, filler, positive, !positive)
        }
        _ => None,
    }
}
