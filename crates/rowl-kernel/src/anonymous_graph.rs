//! Undirected anonymous assertion graph from a supplied raw axiom closure.
//!
//! Repeated endpoint pairs denote one graph edge, even if their properties or
//! annotations differ. The separate OWL edge-multiplicity condition must still
//! be checked. Every other anonymous occurrence is an isolated vertex and
//! cannot introduce a cycle. Scope/label comparison does not assume distinct
//! logical denotations. Imported scopes must already be standardized apart.
#![allow(clippy::ptr_arg)] // The pinned extraction models Vec/index primitives.

use crate::model::{AnnotatedAxiom, AnonymousIndividual, Axiom, Individual};
use crate::symbols::same_spelling;

pub enum AnonymousEdges<'a> {
    Empty,
    Edge {
        left: &'a AnonymousIndividual,
        right: &'a AnonymousIndividual,
        next: Box<AnonymousEdges<'a>>,
    },
}

pub enum ForestCheck<'a> {
    Forest,
    SelfLoop(&'a AnonymousIndividual),
    Cycle {
        left: &'a AnonymousIndividual,
        right: &'a AnonymousIndividual,
    },
}

/// Exact structural identity in an already standardized-apart closure.
pub fn same_individual(left: &AnonymousIndividual, right: &AnonymousIndividual) -> bool {
    same_spelling(&left.scope, &right.scope) && same_spelling(&left.label, &right.label)
}

fn collect_from<'a>(axioms: &'a Vec<AnnotatedAxiom>, index: usize) -> AnonymousEdges<'a> {
    if index < axioms.len() {
        let next = collect_from(axioms, index + 1);
        match &axioms[index].axiom {
            Axiom::ObjectPropertyAssertion(
                _,
                Individual::Anonymous(left),
                Individual::Anonymous(right),
            ) => AnonymousEdges::Edge {
                left,
                right,
                next: Box::new(next),
            },
            _ => next,
        }
    } else {
        AnonymousEdges::Empty
    }
}

/// Preserve the ordered anonymous-to-anonymous positive assertions. Annotation
/// assertions and negative assertions do not generate graph edges.
pub fn collect_edges(axioms: &Vec<AnnotatedAxiom>) -> AnonymousEdges<'_> {
    collect_from(axioms, 0)
}

fn contains_edge<'a>(
    edges: AnonymousEdges<'a>,
    left: &AnonymousIndividual,
    right: &AnonymousIndividual,
) -> (bool, AnonymousEdges<'a>) {
    match edges {
        AnonymousEdges::Empty => (false, AnonymousEdges::Empty),
        AnonymousEdges::Edge {
            left: a,
            right: b,
            next,
        } => {
            if (same_individual(a, left) && same_individual(b, right))
                || (same_individual(a, right) && same_individual(b, left))
            {
                (
                    true,
                    AnonymousEdges::Edge {
                        left: a,
                        right: b,
                        next,
                    },
                )
            } else {
                let (found, next) = contains_edge(*next, left, right);
                (
                    found,
                    AnonymousEdges::Edge {
                        left: a,
                        right: b,
                        next: Box::new(next),
                    },
                )
            }
        }
    }
}

/// Exact finite undirected connectivity. The recursion removes one edge at
/// every call. A walk can either avoid that edge or cross it once in either
/// direction; repeated crossings can be removed. This correctness-first
/// implementation deliberately accepts exponential running time.
pub fn connected<'a>(
    edges: AnonymousEdges<'a>,
    left: &AnonymousIndividual,
    right: &AnonymousIndividual,
) -> (bool, AnonymousEdges<'a>) {
    if same_individual(left, right) {
        (true, edges)
    } else {
        match edges {
            AnonymousEdges::Empty => (false, AnonymousEdges::Empty),
            AnonymousEdges::Edge {
                left: a,
                right: b,
                next,
            } => {
                let (direct, next) = connected(*next, left, right);
                if direct {
                    (
                        true,
                        AnonymousEdges::Edge {
                            left: a,
                            right: b,
                            next: Box::new(next),
                        },
                    )
                } else {
                    let (to_a, next) = connected(next, left, a);
                    let (from_b, next) = connected(next, b, right);
                    if to_a && from_b {
                        (
                            true,
                            AnonymousEdges::Edge {
                                left: a,
                                right: b,
                                next: Box::new(next),
                            },
                        )
                    } else {
                        let (to_b, next) = connected(next, left, b);
                        let (from_a, next) = connected(next, a, right);
                        (
                            to_b && from_a,
                            AnonymousEdges::Edge {
                                left: a,
                                right: b,
                                next: Box::new(next),
                            },
                        )
                    }
                }
            }
        }
    }
}

/// Decide loop freedom and absence of undirected cycles. A duplicate undirected
/// edge is ignored here; assertions with that pair still need the distinct
/// edge-multiplicity check. A cycle outcome identifies an input edge whose
/// removal leaves another path between its distinct endpoints.
pub fn check_edges(edges: AnonymousEdges<'_>) -> ForestCheck<'_> {
    match edges {
        AnonymousEdges::Empty => ForestCheck::Forest,
        AnonymousEdges::Edge { left, right, next } => {
            if same_individual(left, right) {
                ForestCheck::SelfLoop(left)
            } else {
                let (duplicate, next) = contains_edge(*next, left, right);
                if duplicate {
                    check_edges(next)
                } else {
                    let (reachable, next) = connected(next, left, right);
                    if reachable {
                        ForestCheck::Cycle { left, right }
                    } else {
                        check_edges(next)
                    }
                }
            }
        }
    }
}

/// The forest condition for all positive anonymous assertions in the supplied
/// closure. This alone does not establish all OWL 2 DL global restrictions.
pub fn check_forest(axioms: &Vec<AnnotatedAxiom>) -> ForestCheck<'_> {
    check_edges(collect_edges(axioms))
}
