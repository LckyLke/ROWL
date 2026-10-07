//! Entailment of named facts.
//!
//! A closure entails an assertion when every model of the closure satisfies
//! it. For a property assertion about named individuals, its negative, and an
//! equality or inequality of two named individuals, the negation of the fact
//! is again an assertion: the negative of a property assertion and the other
//! way round, and the inequality of two individuals and the other way round.
//! The closure entails the fact exactly when the closure with the negation
//! has no model (`Rowl.Facts.entails_iff_inconsistent`), so the verified
//! consistency procedures decide it: part by part when the closure falls
//! apart along its assertions (`components::consistent_by_parts`), and by the
//! whole closure otherwise. An assertion about an anonymous individual says
//! that some individual exists; its negation is no assertion, and it gets no
//! answer here.
//!
//! `None` means that the fact is of another kind or about an anonymous
//! individual, that the closure has an axiom that cannot be copied, or that
//! the consistency procedures do not answer.
#![allow(
    clippy::ptr_arg,
    clippy::needless_return,
    clippy::match_like_matches_macro,
    clippy::manual_map,
    clippy::collapsible_else_if,
    clippy::collapsible_match,
    clippy::len_zero,
    clippy::question_mark,
    clippy::collapsible_if
)] // Indexed operations and explicit branches for the pinned extraction subset.
use crate::components::{consistent_by_parts, copy_axiom, meaningless};
use crate::data_ontology::consistent;
use crate::model::{AnnotatedAxiom, Axiom, Individual};

/// Whether the individual is named.
fn named(individual: &Individual) -> bool {
    match individual {
        Individual::Named(_) => true,
        Individual::Anonymous(_) => false,
    }
}
/// The negation of a fact about named individuals, from the fact itself.
fn flip(fact: Axiom) -> Option<Axiom> {
    match fact {
        Axiom::ObjectPropertyAssertion(role, source, target) => {
            if named(&source) {
                if named(&target) {
                    Some(Axiom::NegativeObjectPropertyAssertion(role, source, target))
                } else {
                    None
                }
            } else {
                None
            }
        }
        Axiom::NegativeObjectPropertyAssertion(role, source, target) => {
            if named(&source) {
                if named(&target) {
                    Some(Axiom::ObjectPropertyAssertion(role, source, target))
                } else {
                    None
                }
            } else {
                None
            }
        }
        Axiom::DataPropertyAssertion(property, source, literal) => {
            if named(&source) {
                Some(Axiom::NegativeDataPropertyAssertion(
                    property, source, literal,
                ))
            } else {
                None
            }
        }
        Axiom::NegativeDataPropertyAssertion(property, source, literal) => {
            if named(&source) {
                Some(Axiom::DataPropertyAssertion(property, source, literal))
            } else {
                None
            }
        }
        Axiom::SameIndividual(individuals) => {
            if individuals.rest.len() == 0 {
                if named(&individuals.first) {
                    if named(&individuals.second) {
                        Some(Axiom::DifferentIndividuals(individuals))
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
        Axiom::DifferentIndividuals(individuals) => {
            if individuals.rest.len() == 0 {
                if named(&individuals.first) {
                    if named(&individuals.second) {
                        Some(Axiom::SameIndividual(individuals))
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
        _ => None,
    }
}
/// The assertion that an interpretation satisfies exactly when it does not
/// satisfy the fact, for a property assertion or its negative about named
/// individuals and an equality or inequality of two named individuals; `None`
/// for any other axiom.
pub fn negation(fact: &Axiom) -> Option<Axiom> {
    match copy_axiom(fact) {
        Some(copied) => flip(copied),
        None => None,
    }
}
/// `out` with copies, without annotations, of the axioms of `items[index..]`
/// that mean something; `None` when one cannot be copied or there is no room.
fn meaningful(
    items: &Vec<AnnotatedAxiom>,
    index: usize,
    mut out: Vec<AnnotatedAxiom>,
) -> Option<Vec<AnnotatedAxiom>> {
    if index < items.len() {
        if meaningless(&items[index].axiom) {
            meaningful(items, index + 1, out)
        } else {
            match copy_axiom(&items[index].axiom) {
                Some(copied) => {
                    if out.len() < usize::MAX {
                        out.push(AnnotatedAxiom {
                            annotations: Vec::new(),
                            axiom: copied,
                        });
                        meaningful(items, index + 1, out)
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
/// Whether the closure has a model, part by part when it falls apart along
/// its assertions and as a whole otherwise.
fn consistent_closure(items: &Vec<AnnotatedAxiom>) -> Option<bool> {
    match consistent_by_parts(items) {
        Some(answer) => Some(answer),
        None => consistent(items),
    }
}
/// Whether every model of the closure satisfies the fact: a property
/// assertion or its negative about named individuals, or an equality or
/// inequality of two named individuals. It is decided by the consistency of
/// the closure with the fact's negation; a closure without a model entails
/// every fact.
pub fn entails_fact(items: &Vec<AnnotatedAxiom>, fact: &Axiom) -> Option<bool> {
    match negation(fact) {
        Some(negated) => match meaningful(items, 0, Vec::new()) {
            Some(mut closure) => {
                if closure.len() < usize::MAX {
                    closure.push(AnnotatedAxiom {
                        annotations: Vec::new(),
                        axiom: negated,
                    });
                    match consistent_closure(&closure) {
                        Some(answer) => Some(!answer),
                        None => None,
                    }
                } else {
                    None
                }
            }
            None => None,
        },
        None => None,
    }
}
