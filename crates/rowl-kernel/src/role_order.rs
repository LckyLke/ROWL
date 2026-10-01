//! Property-hierarchy regularity on a supplied complete raw OWL axiom closure.
//! Forced chain constraints, finite transitive/inverse-source closure and
//! ordinary hierarchy compatibility compose into the full regularity decision.
//! Other DL restrictions and canonical imports remain separate stages.
#![allow(clippy::ptr_arg)] // Vec/index subset used by the checked extraction.
use crate::roles::{same_role, Edges, Role, Roles};

pub enum OrderClosure<'a> {
    Complete(Edges<'a>),
    MissingPair { sub: Role<'a>, sup: Role<'a> },
}
enum TakenPair<'a> {
    Missing,
    Found(Edges<'a>),
}

fn append<'a>(left: Edges<'a>, right: Edges<'a>) -> Edges<'a> {
    match left {
        Edges::Empty => right,
        Edges::Entry { sub, sup, next } => Edges::Entry {
            sub,
            sup,
            next: Box::new(append(*next, right)),
        },
    }
}
fn split_roles(values: Roles<'_>) -> (Roles<'_>, Roles<'_>) {
    match values {
        Roles::Empty => (Roles::Empty, Roles::Empty),
        Roles::Entry { role, next } => {
            let (left, right) = split_roles(*next);
            (
                Roles::Entry {
                    role: Role {
                        iri: role.iri,
                        inverse: role.inverse,
                    },
                    next: Box::new(left),
                },
                Roles::Entry {
                    role,
                    next: Box::new(right),
                },
            )
        }
    }
}
fn pairs_with<'a>(source: &Role<'a>, targets: Roles<'a>) -> (Edges<'a>, Roles<'a>) {
    match targets {
        Roles::Empty => (Edges::Empty, Roles::Empty),
        Roles::Entry { role, next } => {
            let (pairs, restored) = pairs_with(source, *next);
            (
                Edges::Entry {
                    sub: Role {
                        iri: source.iri,
                        inverse: source.inverse,
                    },
                    sup: Role {
                        iri: role.iri,
                        inverse: role.inverse,
                    },
                    next: Box::new(pairs),
                },
                Roles::Entry {
                    role,
                    next: Box::new(restored),
                },
            )
        }
    }
}
fn all_pairs<'a>(sources: Roles<'a>, targets: Roles<'a>) -> Edges<'a> {
    match sources {
        Roles::Empty => Edges::Empty,
        Roles::Entry { role, next } => {
            let (head, targets) = pairs_with(&role, targets);
            append(head, all_pairs(*next, targets))
        }
    }
}
fn contains<'a>(values: Edges<'a>, sub: &Role<'_>, sup: &Role<'_>) -> (bool, Edges<'a>) {
    match values {
        Edges::Empty => (false, Edges::Empty),
        Edges::Entry {
            sub: a,
            sup: b,
            next,
        } => {
            if same_role(&a, sub) && same_role(&b, sup) {
                (
                    true,
                    Edges::Entry {
                        sub: a,
                        sup: b,
                        next,
                    },
                )
            } else {
                let (found, restored) = contains(*next, sub, sup);
                (
                    found,
                    Edges::Entry {
                        sub: a,
                        sup: b,
                        next: Box::new(restored),
                    },
                )
            }
        }
    }
}
fn take<'a>(values: Edges<'a>, sub: &Role<'_>, sup: &Role<'_>) -> TakenPair<'a> {
    match values {
        Edges::Empty => TakenPair::Missing,
        Edges::Entry {
            sub: a,
            sup: b,
            next,
        } => {
            if same_role(&a, sub) && same_role(&b, sup) {
                TakenPair::Found(*next)
            } else {
                match take(*next, sub, sup) {
                    TakenPair::Missing => TakenPair::Missing,
                    TakenPair::Found(remaining) => TakenPair::Found(Edges::Entry {
                        sub: a,
                        sup: b,
                        next: Box::new(remaining),
                    }),
                }
            }
        }
    }
}
fn predecessors<'a>(sub: &Role<'a>, sup: &Role<'a>, values: Edges<'a>) -> (Edges<'a>, Edges<'a>) {
    match values {
        Edges::Empty => (Edges::Empty, Edges::Empty),
        Edges::Entry {
            sub: a,
            sup: b,
            next,
        } => {
            let (tail, restored) = predecessors(sub, sup, *next);
            if same_role(&b, sub) {
                (
                    Edges::Entry {
                        sub: Role {
                            iri: a.iri,
                            inverse: a.inverse,
                        },
                        sup: Role {
                            iri: sup.iri,
                            inverse: sup.inverse,
                        },
                        next: Box::new(tail),
                    },
                    Edges::Entry {
                        sub: a,
                        sup: b,
                        next: Box::new(restored),
                    },
                )
            } else {
                (
                    tail,
                    Edges::Entry {
                        sub: a,
                        sup: b,
                        next: Box::new(restored),
                    },
                )
            }
        }
    }
}
fn successors<'a>(sub: &Role<'a>, sup: &Role<'a>, values: Edges<'a>) -> (Edges<'a>, Edges<'a>) {
    match values {
        Edges::Empty => (Edges::Empty, Edges::Empty),
        Edges::Entry {
            sub: a,
            sup: b,
            next,
        } => {
            let (tail, restored) = successors(sub, sup, *next);
            if same_role(&a, sup) {
                (
                    Edges::Entry {
                        sub: Role {
                            iri: sub.iri,
                            inverse: sub.inverse,
                        },
                        sup: Role {
                            iri: b.iri,
                            inverse: b.inverse,
                        },
                        next: Box::new(tail),
                    },
                    Edges::Entry {
                        sub: a,
                        sup: b,
                        next: Box::new(restored),
                    },
                )
            } else {
                (
                    tail,
                    Edges::Entry {
                        sub: a,
                        sup: b,
                        next: Box::new(restored),
                    },
                )
            }
        }
    }
}
fn inverse_source<'a>(sub: &Role<'a>, sup: &Role<'a>) -> Edges<'a> {
    if !sup.inverse {
        Edges::Entry {
            sub: Role {
                iri: sub.iri,
                inverse: !sub.inverse,
            },
            sup: Role {
                iri: sup.iri,
                inverse: sup.inverse,
            },
            next: Box::new(Edges::Empty),
        }
    } else {
        Edges::Empty
    }
}
fn discover<'a>(pending: Edges<'a>, available: Edges<'a>, resolved: Edges<'a>) -> OrderClosure<'a> {
    match pending {
        Edges::Empty => OrderClosure::Complete(resolved),
        Edges::Entry { sub, sup, next } => {
            let (seen, resolved) = contains(resolved, &sub, &sup);
            if seen {
                discover(*next, available, resolved)
            } else {
                match take(available, &sub, &sup) {
                    TakenPair::Missing => OrderClosure::MissingPair { sub, sup },
                    TakenPair::Found(remaining) => {
                        let (before, resolved) = predecessors(&sub, &sup, resolved);
                        let (after, resolved) = successors(&sub, &sup, resolved);
                        let pending = append(
                            inverse_source(&sub, &sup),
                            append(before, append(after, *next)),
                        );
                        let resolved = Edges::Entry {
                            sub,
                            sup,
                            next: Box::new(resolved),
                        };
                        discover(pending, remaining, resolved)
                    }
                }
            }
        }
    }
}

/// Least relation containing seeds, closed under transitivity and inversion of
/// the source whenever the target is a direct property. Duplicate nodes/seeds
/// and cycles are supported. A missing required pair is reported explicitly.
pub fn close_order<'a>(nodes: Roles<'a>, seeds: Edges<'a>) -> OrderClosure<'a> {
    let (sources, targets) = split_roles(nodes);
    discover(seeds, all_pairs(sources, targets), Edges::Empty)
}

fn to_super<'a>(values: Roles<'a>, sup: &Role<'a>) -> Edges<'a> {
    match values {
        Roles::Empty => Edges::Empty,
        Roles::Entry { role, next } => Edges::Entry {
            sub: role,
            sup: Role {
                iri: sup.iri,
                inverse: sup.inverse,
            },
            next: Box::new(to_super(*next, sup)),
        },
    }
}
fn trim_last<'a>(values: Roles<'a>, sup: &Role<'a>) -> Edges<'a> {
    match values {
        Roles::Empty => Edges::Empty,
        Roles::Entry { role, next } => match *next {
            Roles::Empty => {
                if same_role(&role, sup) {
                    Edges::Empty
                } else {
                    Edges::Entry {
                        sub: role,
                        sup: Role {
                            iri: sup.iri,
                            inverse: sup.inverse,
                        },
                        next: Box::new(Edges::Empty),
                    }
                }
            }
            tail => Edges::Entry {
                sub: role,
                sup: Role {
                    iri: sup.iri,
                    inverse: sup.inverse,
                },
                next: Box::new(trim_last(tail, sup)),
            },
        },
    }
}
fn roles_empty(values: &Roles<'_>) -> bool {
    matches!(values, Roles::Empty)
}
fn non_top_seeds<'a>(values: Roles<'a>, sup: &Role<'a>) -> Edges<'a> {
    match values {
        Roles::Empty => Edges::Empty,
        Roles::Entry { role, next } => {
            if same_role(&role, sup) {
                match *next {
                    Roles::Empty => Edges::Empty,
                    Roles::Entry {
                        role: second,
                        next: rest,
                    } => {
                        if roles_empty(&rest) && same_role(&second, sup) {
                            Edges::Empty
                        } else {
                            to_super(
                                Roles::Entry {
                                    role: second,
                                    next: rest,
                                },
                                sup,
                            )
                        }
                    }
                }
            } else {
                trim_last(Roles::Entry { role, next }, sup)
            }
        }
    }
}
fn chain_seeds<'a>(
    chain: &'a crate::model::AtLeastTwo<crate::model::ObjectPropertyExpression>,
    sup: &'a crate::model::ObjectPropertyExpression,
) -> Edges<'a> {
    let sup = crate::roles::expression_role(sup);
    if crate::roles::is_top_role(&sup) {
        Edges::Empty
    } else {
        non_top_seeds(crate::roles::property_roles(chain), &sup)
    }
}
fn all_chain_seeds(chains: crate::roles::Chains<'_>) -> Edges<'_> {
    match chains {
        crate::roles::Chains::Empty => Edges::Empty,
        crate::roles::Chains::Entry { chain, sup, next } => {
            append(chain_seeds(chain, sup), all_chain_seeds(*next))
        }
    }
}

/// Construct and close the order constraints forced by the actual raw chains.
/// Strictness and compatibility with the ordinary hierarchy still need checking.
pub fn least_chain_order(axioms: &Vec<crate::model::AnnotatedAxiom>) -> OrderClosure<'_> {
    let facts = crate::roles::collect_facts(axioms);
    close_order(facts.nodes, all_chain_seeds(facts.chains))
}

pub enum RegularityCheck<'a> {
    Regular(Edges<'a>),
    HierarchyConflict {
        sub: Role<'a>,
        sup: Role<'a>,
    },
    /// Excluded by raw syntax completeness in the verified entry point.
    MissingPair {
        sub: Role<'a>,
        sup: Role<'a>,
    },
    /// Excluded for a reached raw-AST role in the verified entry point.
    MissingHierarchyNode(Role<'a>),
}
fn check_pairs<'a>(
    axioms: &'a Vec<crate::model::AnnotatedAxiom>,
    order: Edges<'a>,
) -> RegularityCheck<'a> {
    match order {
        Edges::Empty => RegularityCheck::Regular(Edges::Empty),
        Edges::Entry { sub, sup, next } => {
            let facts = crate::roles::collect_facts(axioms);
            let root = Roles::Entry {
                role: Role {
                    iri: sup.iri,
                    inverse: sup.inverse,
                },
                next: Box::new(Roles::Empty),
            };
            match crate::roles::non_simple_closure(facts.nodes, root, facts.edges) {
                crate::roles::RoleClosure::MissingNode(role) => {
                    RegularityCheck::MissingHierarchyNode(role)
                }
                crate::roles::RoleClosure::Complete(reached) => {
                    let (conflict, _) = crate::roles::contains_role(reached, &sub);
                    if conflict {
                        RegularityCheck::HierarchyConflict { sub, sup }
                    } else {
                        match check_pairs(axioms, *next) {
                            RegularityCheck::Regular(tail) => {
                                RegularityCheck::Regular(Edges::Entry {
                                    sub,
                                    sup,
                                    next: Box::new(tail),
                                })
                            }
                            other => other,
                        }
                    }
                }
            }
        }
    }
}

/// Decide the full OWL 2 structural property-hierarchy regularity condition for
/// the complete supplied raw axiom closure. Preserve a concrete valid ordering
/// or identify a forced order pair contradicted by hierarchy reachability.
/// This does not check the other OWL DL restrictions or assemble imports.
pub fn check_regularity(axioms: &Vec<crate::model::AnnotatedAxiom>) -> RegularityCheck<'_> {
    match least_chain_order(axioms) {
        OrderClosure::Complete(order) => check_pairs(axioms, order),
        OrderClosure::MissingPair { sub, sup } => RegularityCheck::MissingPair { sub, sup },
    }
}
