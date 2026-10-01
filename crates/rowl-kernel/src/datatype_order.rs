//! OWL 2 §11.2 datatype-definition dependency order on a supplied raw closure.
//! Exact datatype identity; every datatype occurrence in a defining range counts.
//! Availability, lexical/facet validity and custom datatype positions are separate.
#![allow(clippy::ptr_arg)] // Indexed extraction subset.

use crate::collection::{range_entities, EntityUses};
use crate::model::{AnnotatedAxiom, Axiom, Iri};
use crate::symbols::same_spelling;
use crate::typing::EntityKind;

pub enum Dependencies<'a> {
    Empty,
    Edge {
        smaller: &'a Iri,
        larger: &'a Iri,
        next: Box<Dependencies<'a>>,
    },
}

pub enum DependencyCheck<'a> {
    Acyclic,
    Cycle { smaller: &'a Iri, larger: &'a Iri },
}

fn dependency_uses<'a>(
    uses: EntityUses<'a>,
    defined: &'a Iri,
    tail: Dependencies<'a>,
) -> Dependencies<'a> {
    match uses {
        EntityUses::Empty => tail,
        EntityUses::Entry {
            iri,
            kind: EntityKind::Datatype,
            next,
        } => Dependencies::Edge {
            smaller: iri,
            larger: defined,
            next: Box::new(dependency_uses(*next, defined, tail)),
        },
        EntityUses::Entry { next, .. } => dependency_uses(*next, defined, tail),
    }
}

fn axiom_dependencies<'a>(item: &'a AnnotatedAxiom, tail: Dependencies<'a>) -> Dependencies<'a> {
    match &item.axiom {
        Axiom::DatatypeDefinition(defined, range) => {
            dependency_uses(range_entities(range), &defined.iri, tail)
        }
        _ => tail,
    }
}

fn visit_axioms<'a>(axioms: &'a Vec<AnnotatedAxiom>, index: usize) -> Dependencies<'a> {
    if index < axioms.len() {
        let tail = visit_axioms(axioms, index + 1);
        axiom_dependencies(&axioms[index], tail)
    } else {
        Dependencies::Empty
    }
}

/// Ordered exact dependency occurrences from all datatype definitions.
/// Enclosing annotations do not belong to a definition's data range.
pub fn collect_dependencies(axioms: &Vec<AnnotatedAxiom>) -> Dependencies<'_> {
    visit_axioms(axioms, 0)
}

/// Directed reflexive reachability, retaining the input graph exactly.
/// Removing one edge at each recursive call guarantees termination, including
/// on cyclic or repeated inputs. A path can avoid that edge or cross it once.
/// This proof-first implementation permits exponential running time.
pub fn reachable<'a>(edges: Dependencies<'a>, left: &Iri, right: &Iri) -> (bool, Dependencies<'a>) {
    if same_spelling(&left.spelling, &right.spelling) {
        (true, edges)
    } else {
        match edges {
            Dependencies::Empty => (false, Dependencies::Empty),
            Dependencies::Edge {
                smaller: a,
                larger: b,
                next,
            } => {
                let (direct, next) = reachable(*next, left, right);
                if direct {
                    (
                        true,
                        Dependencies::Edge {
                            smaller: a,
                            larger: b,
                            next: Box::new(next),
                        },
                    )
                } else {
                    let (to_a, next) = reachable(next, left, a);
                    let (from_b, next) = reachable(next, b, right);
                    (
                        to_a && from_b,
                        Dependencies::Edge {
                            smaller: a,
                            larger: b,
                            next: Box::new(next),
                        },
                    )
                }
            }
        }
    }
}

/// A rejected original edge has a reverse path, including reflexive self edges.
/// Directed diamonds and repeated same-direction edges are permitted.
pub fn check_dependencies(edges: Dependencies<'_>) -> DependencyCheck<'_> {
    match edges {
        Dependencies::Empty => DependencyCheck::Acyclic,
        Dependencies::Edge {
            smaller,
            larger,
            next,
        } => {
            let (reverse, next) = reachable(*next, larger, smaller);
            if reverse {
                DependencyCheck::Cycle { smaller, larger }
            } else {
                check_dependencies(next)
            }
        }
    }
}

/// Decide the full dependency-order restriction from the actual raw axiom vector.
/// This alone does not check other datatype or OWL 2 DL restrictions.
pub fn check_acyclic(axioms: &Vec<AnnotatedAxiom>) -> DependencyCheck<'_> {
    check_dependencies(collect_dependencies(axioms))
}
