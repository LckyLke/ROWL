//! Concepts in negation normal form with inverse roles, and their translation
//! from OWL class expressions.
//!
//! The supported fragment is ALCIQ: named classes, intersections, unions,
//! complements, existential and universal restrictions, and minimum, maximum and
//! exact cardinality restrictions on object property expressions, named or
//! inverse, with cardinalities below `usize::MAX`. `owl:Thing` and `owl:Nothing`
//! become the top and bottom concepts. Every other expression returns `None`.
//! Negation is pushed inward, so it only occurs on named classes: the complement
//! of `≥n r.C` is `≤(n-1) r.C` (`⊥` for `n = 0`) and the complement of `≤n r.C`
//! is `≥(n+1) r.C`. The completion graph tableau decides the concepts without
//! cardinality restrictions; `nnf` keeps the inverse-free concepts of the
//! earlier tableaux.
#![allow(clippy::ptr_arg, clippy::question_mark, clippy::manual_map)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::class_equality::{is_nothing, is_thing};
use crate::model::{AtLeastTwo, Class, ClassExpression, ObjectProperty, ObjectPropertyExpression};
use crate::nnf::copy_iri;
use crate::probes::Natural;
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
    /// At least `n` neighbours along the role satisfy the filler.
    AtLeast(usize, ObjectPropertyExpression, Box<Concept>),
    /// At most `n` neighbours along the role satisfy the filler.
    AtMost(usize, ObjectPropertyExpression, Box<Concept>),
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
/// A copy of a concept.
pub(crate) fn copy_concept(concept: &Concept) -> Concept {
    match concept {
        Concept::Top => Concept::Top,
        Concept::Bottom => Concept::Bottom,
        Concept::Atom(class) => Concept::Atom(Class {
            iri: copy_iri(&class.iri),
        }),
        Concept::NotAtom(class) => Concept::NotAtom(Class {
            iri: copy_iri(&class.iri),
        }),
        Concept::And(left, right) => {
            Concept::And(Box::new(copy_concept(left)), Box::new(copy_concept(right)))
        }
        Concept::Or(left, right) => {
            Concept::Or(Box::new(copy_concept(left)), Box::new(copy_concept(right)))
        }
        Concept::Exists(role, filler) => {
            Concept::Exists(copy_role(role), Box::new(copy_concept(filler)))
        }
        Concept::Forall(role, filler) => {
            Concept::Forall(copy_role(role), Box::new(copy_concept(filler)))
        }
        Concept::AtLeast(n, role, filler) => {
            Concept::AtLeast(*n, copy_role(role), Box::new(copy_concept(filler)))
        }
        Concept::AtMost(n, role, filler) => {
            Concept::AtMost(*n, copy_role(role), Box::new(copy_concept(filler)))
        }
    }
}
/// The complements of both concepts, joined by intersection (`conjunctive`) or
/// union.
fn negate_pair(left: &Concept, right: &Concept, conjunctive: bool) -> Option<Concept> {
    let first = match negate(left) {
        Some(first) => first,
        None => return None,
    };
    let second = match negate(right) {
        Some(second) => second,
        None => return None,
    };
    Some(join(conjunctive, first, second))
}
/// The complement of a concept, in negation normal form; `None` when a
/// cardinality would exceed `usize::MAX`.
pub fn negate(concept: &Concept) -> Option<Concept> {
    match concept {
        Concept::Top => Some(Concept::Bottom),
        Concept::Bottom => Some(Concept::Top),
        Concept::Atom(class) => Some(Concept::NotAtom(Class {
            iri: copy_iri(&class.iri),
        })),
        Concept::NotAtom(class) => Some(Concept::Atom(Class {
            iri: copy_iri(&class.iri),
        })),
        Concept::And(left, right) => negate_pair(left, right, false),
        Concept::Or(left, right) => negate_pair(left, right, true),
        Concept::Exists(role, filler) => match negate(filler) {
            Some(inner) => Some(Concept::Forall(copy_role(role), Box::new(inner))),
            None => None,
        },
        Concept::Forall(role, filler) => match negate(filler) {
            Some(inner) => Some(Concept::Exists(copy_role(role), Box::new(inner))),
            None => None,
        },
        Concept::AtLeast(n, role, filler) => {
            if *n == 0 {
                Some(Concept::Bottom)
            } else {
                Some(Concept::AtMost(
                    *n - 1,
                    copy_role(role),
                    Box::new(copy_concept(filler)),
                ))
            }
        }
        Concept::AtMost(n, role, filler) => {
            if *n < usize::MAX {
                Some(Concept::AtLeast(
                    *n + 1,
                    copy_role(role),
                    Box::new(copy_concept(filler)),
                ))
            } else {
                None
            }
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
/// The value of a cardinality, when it is below `usize::MAX` so that one more
/// still fits.
fn bound(n: &Natural) -> Option<usize> {
    match n {
        Natural::Zero => Some(0),
        Natural::Succ(previous) => match bound(previous) {
            Some(value) => {
                if value < usize::MAX - 1 {
                    Some(value + 1)
                } else {
                    None
                }
            }
            None => None,
        },
    }
}
/// The filler of a cardinality restriction; `owl:Thing` when it has none.
fn cardinality_filler(filler: &Option<Box<ClassExpression>>) -> Option<Concept> {
    match filler {
        Some(inner) => translate(inner, true),
        None => Some(Concept::Top),
    }
}
/// A minimum (`minimum`) or maximum cardinality restriction (`!positive`: its
/// complement); `None` outside the fragment.
fn cardinality(
    n: &Natural,
    property: &ObjectPropertyExpression,
    filler: &Option<Box<ClassExpression>>,
    positive: bool,
    minimum: bool,
) -> Option<Concept> {
    let n = match bound(n) {
        Some(n) => n,
        None => return None,
    };
    let inner = match cardinality_filler(filler) {
        Some(inner) => inner,
        None => return None,
    };
    if minimum {
        if positive {
            Some(Concept::AtLeast(n, copy_role(property), Box::new(inner)))
        } else if n == 0 {
            Some(Concept::Bottom)
        } else {
            Some(Concept::AtMost(n - 1, copy_role(property), Box::new(inner)))
        }
    } else if positive {
        Some(Concept::AtMost(n, copy_role(property), Box::new(inner)))
    } else if n < usize::MAX {
        Some(Concept::AtLeast(
            n + 1,
            copy_role(property),
            Box::new(inner),
        ))
    } else {
        None
    }
}
/// An exact cardinality restriction: `≥n ⊓ ≤n`, or `≤(n-1) ⊔ ≥(n+1)` for its
/// complement.
fn exactly(
    n: &Natural,
    property: &ObjectPropertyExpression,
    filler: &Option<Box<ClassExpression>>,
    positive: bool,
) -> Option<Concept> {
    let low = match cardinality(n, property, filler, positive, true) {
        Some(low) => low,
        None => return None,
    };
    let high = match cardinality(n, property, filler, positive, false) {
        Some(high) => high,
        None => return None,
    };
    Some(join(positive, low, high))
}
/// Translate a class expression (`positive`) or its complement (`!positive`)
/// into negation normal form. De Morgan's laws turn negated intersections into
/// unions and back, negated existential restrictions into universal ones and
/// back, and negated cardinality restrictions into the opposite bound. Returns
/// `None` outside the supported ALCIQ fragment.
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
        ClassExpression::ObjectMinCardinality(n, property, filler) => {
            cardinality(n, property, filler, positive, true)
        }
        ClassExpression::ObjectMaxCardinality(n, property, filler) => {
            cardinality(n, property, filler, positive, false)
        }
        ClassExpression::ObjectExactCardinality(n, property, filler) => {
            exactly(n, property, filler, positive)
        }
        _ => None,
    }
}
