//! Named-boundary restriction of the anonymous assertion graph.
//!
//! Each connected component must contain an anonymous vertex incident to at most
//! one structurally distinct positive assertion with a named endpoint. Other
//! anonymous occurrences are isolated, have no such assertions, and qualify.
//! This is the literal normative OWL 2 §11.2 condition. It is separate from
//! forest checking, edge multiplicity, positional restrictions and scope assembly.
#![allow(clippy::ptr_arg)] // Pinned extraction covers these indexed Vec operations.

use crate::anonymous_graph::{collect_edges, connected, same_individual, AnonymousEdges};
use crate::assertion_equality::same_object_assertion;
use crate::model::{AnnotatedAxiom, AnonymousIndividual, Axiom, Individual};

pub enum BoundaryCheck<'a> {
    Allowed,
    /// An original anonymous endpoint whose entire component has no valid root.
    NoRoot(&'a AnonymousIndividual),
}

/// First anonymous endpoint of a positive object assertion, if present.
pub fn first_candidate(item: &AnnotatedAxiom) -> Option<&AnonymousIndividual> {
    match &item.axiom {
        Axiom::ObjectPropertyAssertion(_, Individual::Anonymous(a), _) => Some(a),
        Axiom::ObjectPropertyAssertion(_, Individual::Named(_), Individual::Anonymous(b)) => {
            Some(b)
        }
        _ => None,
    }
}

/// The other endpoint only when both are anonymous.
pub fn second_candidate(item: &AnnotatedAxiom) -> Option<&AnonymousIndividual> {
    match &item.axiom {
        Axiom::ObjectPropertyAssertion(_, Individual::Anonymous(_), Individual::Anonymous(b)) => {
            Some(b)
        }
        _ => None,
    }
}

/// Incident positive object assertion with exactly one named endpoint.
pub fn touches_named(item: &AnnotatedAxiom, vertex: &AnonymousIndividual) -> bool {
    match &item.axiom {
        Axiom::ObjectPropertyAssertion(_, Individual::Anonymous(a), Individual::Named(_))
        | Axiom::ObjectPropertyAssertion(_, Individual::Named(_), Individual::Anonymous(a)) => {
            same_individual(a, vertex)
        }
        _ => false,
    }
}

fn row_from(
    axioms: &Vec<AnnotatedAxiom>,
    vertex: &AnonymousIndividual,
    first: &AnnotatedAxiom,
    index: usize,
) -> bool {
    if index < axioms.len() {
        let second = &axioms[index];
        if touches_named(second, vertex) && !same_object_assertion(first, second) {
            false
        } else {
            row_from(axioms, vertex, first, index + 1)
        }
    } else {
        true
    }
}

fn limit_from(axioms: &Vec<AnnotatedAxiom>, vertex: &AnonymousIndividual, index: usize) -> bool {
    if index < axioms.len() {
        let first = &axioms[index];
        if touches_named(first, vertex) && !row_from(axioms, vertex, first, 0) {
            false
        } else {
            limit_from(axioms, vertex, index + 1)
        }
    } else {
        true
    }
}

/// Raw duplicate occurrences count once under annotated structural equivalence.
pub fn at_most_one(axioms: &Vec<AnnotatedAxiom>, vertex: &AnonymousIndividual) -> bool {
    limit_from(axioms, vertex, 0)
}

fn qualifies<'a>(
    axioms: &Vec<AnnotatedAxiom>,
    edges: AnonymousEdges<'a>,
    root: &AnonymousIndividual,
    candidate: Option<&AnonymousIndividual>,
) -> (bool, AnonymousEdges<'a>) {
    match candidate {
        None => (false, edges),
        Some(vertex) => {
            let (reachable, edges) = connected(edges, root, vertex);
            (reachable && at_most_one(axioms, vertex), edges)
        }
    }
}

fn find_from<'a>(
    axioms: &Vec<AnnotatedAxiom>,
    edges: AnonymousEdges<'a>,
    root: &AnonymousIndividual,
    index: usize,
) -> (bool, AnonymousEdges<'a>) {
    if index < axioms.len() {
        let item = &axioms[index];
        let (first, edges) = qualifies(axioms, edges, root, first_candidate(item));
        if first {
            (true, edges)
        } else {
            let (second, edges) = qualifies(axioms, edges, root, second_candidate(item));
            if second {
                (true, edges)
            } else {
                find_from(axioms, edges, root, index + 1)
            }
        }
    } else {
        (false, edges)
    }
}

fn check_from<'a>(
    axioms: &'a Vec<AnnotatedAxiom>,
    edges: AnonymousEdges<'a>,
    index: usize,
) -> BoundaryCheck<'a> {
    if index < axioms.len() {
        let item = &axioms[index];
        let edges = match first_candidate(item) {
            None => edges,
            Some(root) => {
                let (found, edges) = find_from(axioms, edges, root, 0);
                if !found {
                    return BoundaryCheck::NoRoot(root);
                }
                edges
            }
        };
        let edges = match second_candidate(item) {
            None => edges,
            Some(root) => {
                let (found, edges) = find_from(axioms, edges, root, 0);
                if !found {
                    return BoundaryCheck::NoRoot(root);
                }
                edges
            }
        };
        check_from(axioms, edges, index + 1)
    } else {
        BoundaryCheck::Allowed
    }
}

/// Decide the named-boundary condition on a supplied standardized-apart closure.
/// Candidates come from the actual raw axioms; no caller vertex list is trusted.
/// This deliberately favors simple proved loops over performance.
pub fn check_boundary(axioms: &Vec<AnnotatedAxiom>) -> BoundaryCheck<'_> {
    check_from(axioms, collect_edges(axioms), 0)
}
