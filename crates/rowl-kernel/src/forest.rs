//! A completion forest tableau for SHOIQ with named individuals.
//!
//! The forest has one root per named individual and trees of anonymous nodes
//! below them. Labels are lists of literal entries of the concept table, as in
//! the completion graph, and the edge from a parent to a tree node carries a
//! list of roles. Rules are searched in a fixed order:
//!
//! 1. every active node satisfies the requirements of the individuals merged
//!    into it, the TBox concept and the unfoldings of its classes, and a tree
//!    node or a new named node the filler it was created for (its seed);
//! 2. along every edge, in both directions, universal restrictions pass their
//!    filler on, and through transitive roles the restriction itself; a self
//!    restriction `∃s.Self` of a node is a loop, an edge from the node to
//!    itself along `s`;
//! 3. a node with `¬∃r.Self` that is its own neighbour along `r` is a clash;
//! 4. a node whose label has the nominal `{a}` is merged into the named node of
//!    `a`, the node of the first requirement with `{a}`, unless they are known
//!    to differ, which is a clash; a nominal or the complement of one whose
//!    individual has no named node gives no answer;
//! 5. for every `≤n r.C` of a node, every neighbour along `r` decides `C`
//!    (the choose rule);
//! 6. when `≤n r.C` of a named node counts a tree node that is not its child,
//!    which the model may repeat, new named nodes take the place of such
//!    nodes: the rule guesses how many neighbours along `r` satisfy `C`, from
//!    1 up to `n`, trying each guess in turn, and creates that many new named
//!    nodes with the seed `C`, an added edge from the node and the guess as a
//!    bound on those neighbours; once the bound exists, the tree node is
//!    merged with one of the first `bound` counted named neighbours;
//! 7. when more than `n` of those neighbours satisfy `C`, two of the first
//!    `n + 1` that are not known to differ are merged, trying each such pair in
//!    turn; when all of them differ, it is a clash; a pair of a tree node with
//!    a loop and its own child or parent gives no answer;
//! 8. every `∃r.C` and `≥n r.C` of an unblocked node that has fewer
//!    neighbours along `r` satisfying `C` than it requires, and was not
//!    expanded yet, creates new tree nodes with the filler as their seed,
//!    pairwise different.
//!
//! When no rule applies, every such restriction of an unblocked node is checked
//! to have enough neighbours; the differences between the nodes a restriction
//! created keep them from being merged, so the check passes, and otherwise
//! there is no answer.
//!
//! A merge moves a tree node into a sibling, into its grandparent or into a
//! named node, or a named node into another one. The target receives the label,
//! the edge from the parent and the added edges of the merged node, and its
//! differences, and the merged node is pruned with its subtree. Merging a tree
//! node into a named node adds edges from its parent, which may be a tree node,
//! to the named node. A tree node is blocked when its label, its parent's label
//! and the roles in between repeat a tree node with a tree parent on its path to
//! its root (pairwise blocking), which counting with inverse roles needs; the
//! added edges of blocked nodes are left out. Number restrictions and
//! complements of self restrictions must be on simple roles, which no
//! transitive role is included in. New named nodes come after every node that
//! created them, and each restriction of a named node gets them at most once,
//! so the run terminates.
//!
//! Backjumping works as in the completion graph: nodes, edges and differences
//! record the branch points they depend on, and a choice that a failure did not
//! depend on is not retried. `None` means that a structure would exceed the
//! `usize` range, that a number restriction or the complement of a self
//! restriction is on a role that is not simple, that the individual of a
//! nominal has no named node, that a restriction with a bound from new named
//! nodes has fewer counted named neighbours than the bound, or that a merge
//! would move a tree node into its parent.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::collapsible_match,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::needless_return,
    clippy::single_match,
    clippy::manual_map,
    clippy::manual_filter,
    clippy::boxed_local,
    clippy::match_like_matches_macro,
    clippy::needless_bool,
    clippy::if_same_then_else,
    clippy::too_many_arguments,
    clippy::vec_init_then_push
)] // Indexed operations, explicit branches and pushes without macros for the pinned extraction subset.
use crate::assertion_equality::same_individual_value;
use crate::completion::{
    clashes, contains, copy_label, copy_links, copy_pending, holds, intern_definitions,
    intern_facts, join, join_from, missing_along, missing_unfolding, same_label, without_from,
    Definition, Fact, Link, Outcome, Pending, Problem,
};
use crate::concept_table::{close, intern, Entry};
use crate::concepts::{copy_role, inverse, same_role, Concept};
use crate::hierarchy::{below, RoleHierarchy};
use crate::model::{Individual, ObjectPropertyExpression};

/// A node of the forest.
pub struct Node {
    /// The literal entries of the label.
    pub label: Vec<usize>,
    /// For a tree node: its parent, the roles of the edge from the parent, and
    /// the filler it was created for.
    pub parent: usize,
    pub roles: Vec<ObjectPropertyExpression>,
    pub seed: usize,
    pub tree: bool,
    /// Whether the node is part of the forest; merged and pruned nodes are not.
    pub active: bool,
    /// The existential and minimum restrictions of the label already expanded.
    pub done: Vec<usize>,
    /// The branch points the node depends on.
    pub deps: Vec<usize>,
}
/// An edge between named nodes that a merge added.
pub struct Edge {
    pub role: ObjectPropertyExpression,
    pub from: usize,
    pub to: usize,
    pub deps: Vec<usize>,
}
/// Two nodes that stand for different elements.
pub struct Distinct {
    pub left: usize,
    pub right: usize,
    pub deps: Vec<usize>,
}
/// A bound on the neighbours of a named node along the role of its maximum
/// restriction `restriction` that satisfy the filler: the number of new named
/// nodes the rule for that restriction guessed and created.
pub struct Cap {
    pub node: usize,
    pub restriction: usize,
    pub bound: usize,
    pub deps: Vec<usize>,
}
/// Two nodes that may be merged.
pub struct Pair {
    pub first: usize,
    pub second: usize,
}
/// The state of a run: the nodes, the added edges, the differences, for every
/// named individual the named node it was merged into (its own node while that
/// is active), and the bounds that new named nodes were created for.
pub struct Forest {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub distinct: Vec<Distinct>,
    pub same: Vec<usize>,
    pub caps: Vec<Cap>,
}
/// The next rule to apply.
pub enum Step {
    Add {
        node: usize,
        concept: usize,
    },
    Choose {
        node: usize,
        left: usize,
        right: usize,
    },
    Merge {
        node: usize,
        restriction: usize,
    },
    Name {
        node: usize,
        restriction: usize,
    },
    Capped {
        node: usize,
        restriction: usize,
    },
    Nominal {
        node: usize,
        root: usize,
    },
    Loop {
        node: usize,
    },
    Create {
        node: usize,
        generator: usize,
    },
    Stuck,
    Done,
}

/// Whether a role of `list[index..]` (`forward`), or the inverse of one, is
/// included in `role`.
fn along_from(
    roles: &RoleHierarchy,
    list: &Vec<ObjectPropertyExpression>,
    role: &ObjectPropertyExpression,
    forward: bool,
    index: usize,
) -> bool {
    if index < list.len() {
        let here = if forward {
            below(roles, &list[index], role)
        } else {
            let back = inverse(&list[index]);
            below(roles, &back, role)
        };
        if here {
            true
        } else {
            along_from(roles, list, role, forward, index + 1)
        }
    } else {
        false
    }
}
/// `out` with `node` unless it lists it; `None` when there is no room.
fn with_node(mut out: Vec<usize>, node: usize) -> Option<Vec<usize>> {
    if contains(&out, node, 0) {
        Some(out)
    } else if out.len() < usize::MAX {
        out.push(node);
        Some(out)
    } else {
        None
    }
}
/// The named node that the individual `named` was merged into.
fn representative(graph: &Forest, named: usize) -> usize {
    if named < graph.same.len() {
        graph.same[named]
    } else {
        named
    }
}
/// `out` with the active tree nodes of `nodes[index..]` below `node` along a
/// role included in `role`.
fn children_along(
    graph: &Forest,
    roles: &RoleHierarchy,
    node: usize,
    role: &ObjectPropertyExpression,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < graph.nodes.len() {
        let mut here = false;
        if graph.nodes[index].tree {
            if graph.nodes[index].active {
                if graph.nodes[index].parent == node {
                    here = along_from(roles, &graph.nodes[index].roles, role, true, 0);
                }
            }
        }
        let out = if here {
            match with_node(out, index) {
                Some(out) => out,
                None => return None,
            }
        } else {
            out
        };
        children_along(graph, roles, node, role, index + 1, out)
    } else {
        Some(out)
    }
}
/// `out` with the parent of the tree node `node`, when it is reached along a
/// role included in `role`.
fn parent_along(
    graph: &Forest,
    roles: &RoleHierarchy,
    node: usize,
    role: &ObjectPropertyExpression,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if node < graph.nodes.len() {
        if graph.nodes[node].tree {
            if along_from(roles, &graph.nodes[node].roles, role, false, 0) {
                return with_node(out, graph.nodes[node].parent);
            }
        }
    }
    Some(out)
}
/// `out` with the other end of an edge from `from` to `to` along `edge`, for
/// each end that is `node`, when the edge leads from it along a role included
/// in `role`.
fn ends(
    roles: &RoleHierarchy,
    out: Vec<usize>,
    from: usize,
    to: usize,
    edge: &ObjectPropertyExpression,
    node: usize,
    role: &ObjectPropertyExpression,
) -> Option<Vec<usize>> {
    let out = if from == node {
        if below(roles, edge, role) {
            match with_node(out, to) {
                Some(out) => out,
                None => return None,
            }
        } else {
            out
        }
    } else {
        out
    };
    if to == node {
        let back = inverse(edge);
        if below(roles, &back, role) {
            return with_node(out, from);
        }
    }
    Some(out)
}
/// `out` with the named nodes that `links[index..]`, read through the merges,
/// relate to `node` along a role included in `role`.
fn links_along(
    graph: &Forest,
    roles: &RoleHierarchy,
    links: &Vec<Link>,
    node: usize,
    role: &ObjectPropertyExpression,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < links.len() {
        let from = representative(graph, links[index].from);
        let to = representative(graph, links[index].to);
        match ends(roles, out, from, to, &links[index].role, node, role) {
            Some(out) => links_along(graph, roles, links, node, role, index + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// Whether a node is active and not blocked: the model has it, and so its
/// added edges.
fn live(graph: &Forest, node: usize) -> bool {
    if node < graph.nodes.len() {
        if graph.nodes[node].active {
            !blocked(graph, node)
        } else {
            false
        }
    } else {
        false
    }
}
/// `out` with the nodes that the edges of `edges[index..]` from live nodes,
/// read through the merges, relate to `node` along a role included in `role`.
fn edges_along(
    graph: &Forest,
    roles: &RoleHierarchy,
    node: usize,
    role: &ObjectPropertyExpression,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < graph.edges.len() {
        let from = representative(graph, graph.edges[index].from);
        let to = representative(graph, graph.edges[index].to);
        let out = if live(graph, from) {
            match ends(roles, out, from, to, &graph.edges[index].role, node, role) {
                Some(out) => out,
                None => return None,
            }
        } else {
            out
        };
        edges_along(graph, roles, node, role, index + 1, out)
    } else {
        Some(out)
    }
}
/// Whether the entry `item` is a self restriction `∃s.Self` whose loop leads
/// along a role included in `role`, in either direction.
fn looping(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    item: usize,
    role: &ObjectPropertyExpression,
) -> bool {
    if item < entries.len() {
        match &entries[item] {
            Entry::HasSelf(own) => {
                if below(roles, own, role) {
                    true
                } else {
                    below(roles, &inverse(own), role)
                }
            }
            _ => false,
        }
    } else {
        false
    }
}
/// Whether a self restriction of `label[index..]` has a loop along a role
/// included in `role`.
fn self_along(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    label: &Vec<usize>,
    role: &ObjectPropertyExpression,
    index: usize,
) -> bool {
    if index < label.len() {
        if looping(entries, roles, label[index], role) {
            true
        } else {
            self_along(entries, roles, label, role, index + 1)
        }
    } else {
        false
    }
}
/// `out` with `node` itself, when a self restriction of its label has a loop
/// along a role included in `role`.
fn loops_along(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    role: &ObjectPropertyExpression,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if node < graph.nodes.len() {
        if self_along(&problem.entries, roles, &graph.nodes[node].label, role, 0) {
            return with_node(out, node);
        }
    }
    Some(out)
}
/// The neighbours of `node` along a role included in `role`, each once: its
/// children, its parent, the named nodes linked to it, the nodes an added edge
/// from a live node relates to it, and itself when its label has a self
/// restriction along the role.
fn neighbours(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    role: &ObjectPropertyExpression,
) -> Option<Vec<usize>> {
    let out = match children_along(graph, roles, node, role, 0, Vec::new()) {
        Some(out) => out,
        None => return None,
    };
    let out = match parent_along(graph, roles, node, role, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match links_along(graph, roles, &problem.links, node, role, 0, out) {
        Some(out) => out,
        None => return None,
    };
    let out = match edges_along(graph, roles, node, role, 0, out) {
        Some(out) => out,
        None => return None,
    };
    loops_along(problem, roles, graph, node, role, out)
}
/// The label of a node; empty for an index out of range.
fn label_of(graph: &Forest, node: usize) -> Vec<usize> {
    if node < graph.nodes.len() {
        copy_label(&graph.nodes[node].label, 0, Vec::new())
    } else {
        Vec::new()
    }
}
/// `out` with the nodes of `list[index..]` whose labels satisfy `concept`;
/// `None` when there is no room.
fn satisfying(
    entries: &Vec<Entry>,
    graph: &Forest,
    list: &Vec<usize>,
    concept: usize,
    index: usize,
    mut out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < list.len() {
        let label = label_of(graph, list[index]);
        if holds(entries, &label, concept) {
            if out.len() < usize::MAX {
                out.push(list[index]);
            } else {
                return None;
            }
        }
        satisfying(entries, graph, list, concept, index + 1, out)
    } else {
        Some(out)
    }
}
/// The first requirement of `requirements[index..]` of an individual merged
/// into `node` that the label does not satisfy.
fn missing_requirement(
    problem: &Problem,
    graph: &Forest,
    label: &Vec<usize>,
    node: usize,
    index: usize,
) -> Option<usize> {
    if index < problem.requirements.len() {
        let requirement = &problem.requirements[index];
        let missing = if representative(graph, requirement.node) == node {
            !holds(&problem.entries, label, requirement.concept)
        } else {
            false
        };
        if missing {
            Some(requirement.concept)
        } else {
            missing_requirement(problem, graph, label, node, index + 1)
        }
    } else {
        None
    }
}
/// Whether `node` has a seed: a tree node, or a named node beyond the
/// individuals' nodes.
fn seeded(graph: &Forest, node: usize) -> bool {
    if node < graph.nodes.len() {
        if graph.nodes[node].tree {
            true
        } else if node < graph.same.len() {
            false
        } else {
            true
        }
    } else {
        false
    }
}
/// What the label of the active node `node` misses: a requirement, the TBox
/// concept, an unfolding, or the seed of a tree node or of a new named node.
fn missing_at(problem: &Problem, graph: &Forest, node: usize) -> Option<usize> {
    if node < graph.nodes.len() {
        let label = &graph.nodes[node].label;
        match missing_requirement(problem, graph, label, node, 0) {
            Some(concept) => Some(concept),
            None => {
                if !holds(&problem.entries, label, problem.axioms) {
                    Some(problem.axioms)
                } else {
                    match missing_unfolding(problem, label, 0) {
                        Some(concept) => Some(concept),
                        None => {
                            if seeded(graph, node) {
                                if !holds(&problem.entries, label, graph.nodes[node].seed) {
                                    return Some(graph.nodes[node].seed);
                                }
                            }
                            None
                        }
                    }
                }
            }
        }
    } else {
        None
    }
}
/// The first active node of `nodes[index..]` that misses something, and what.
fn missing_node(problem: &Problem, graph: &Forest, index: usize) -> Option<(usize, usize)> {
    if index < graph.nodes.len() {
        let found = if graph.nodes[index].active {
            missing_at(problem, graph, index)
        } else {
            None
        };
        match found {
            Some(concept) => Some((index, concept)),
            None => missing_node(problem, graph, index + 1),
        }
    } else {
        None
    }
}
/// What an edge from `from` to `to` along `role` requires in either direction
/// that is missing, with the node that misses it.
fn missing_edge(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    graph: &Forest,
    from: usize,
    to: usize,
    role: &ObjectPropertyExpression,
) -> Option<(usize, usize)> {
    if from < graph.nodes.len() && to < graph.nodes.len() {
        match missing_along(
            entries,
            roles,
            &graph.nodes[from].label,
            role,
            &graph.nodes[to].label,
            0,
        ) {
            Some(concept) => Some((to, concept)),
            None => {
                let back = inverse(role);
                match missing_along(
                    entries,
                    roles,
                    &graph.nodes[to].label,
                    &back,
                    &graph.nodes[from].label,
                    0,
                ) {
                    Some(concept) => Some((from, concept)),
                    None => None,
                }
            }
        }
    } else {
        None
    }
}
/// What the edge from the parent of `node` along a role of `roles[index..]`
/// misses.
fn missing_roles(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    index: usize,
) -> Option<(usize, usize)> {
    if node < graph.nodes.len() {
        if index < graph.nodes[node].roles.len() {
            match missing_edge(
                entries,
                roles,
                graph,
                graph.nodes[node].parent,
                node,
                &graph.nodes[node].roles[index],
            ) {
                Some(found) => Some(found),
                None => missing_roles(entries, roles, graph, node, index + 1),
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// The first edge to an active tree node of `nodes[index..]` that misses
/// something.
fn missing_tree(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    index: usize,
) -> Option<(usize, usize)> {
    if index < graph.nodes.len() {
        let found = if graph.nodes[index].tree {
            if graph.nodes[index].active {
                missing_roles(&problem.entries, roles, graph, index, 0)
            } else {
                None
            }
        } else {
            None
        };
        match found {
            Some(found) => Some(found),
            None => missing_tree(problem, roles, graph, index + 1),
        }
    } else {
        None
    }
}
/// The first link of `links[index..]`, read through the merges, that misses
/// something.
fn missing_link(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    index: usize,
) -> Option<(usize, usize)> {
    if index < problem.links.len() {
        let link = &problem.links[index];
        match missing_edge(
            &problem.entries,
            roles,
            graph,
            representative(graph, link.from),
            representative(graph, link.to),
            &link.role,
        ) {
            Some(found) => Some(found),
            None => missing_link(problem, roles, graph, index + 1),
        }
    } else {
        None
    }
}
/// The first edge of `edges[index..]` from a live node, read through the
/// merges, that misses something.
fn missing_added(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    index: usize,
) -> Option<(usize, usize)> {
    if index < graph.edges.len() {
        let from = representative(graph, graph.edges[index].from);
        let found = if live(graph, from) {
            missing_edge(
                &problem.entries,
                roles,
                graph,
                from,
                representative(graph, graph.edges[index].to),
                &graph.edges[index].role,
            )
        } else {
            None
        };
        match found {
            Some(found) => Some(found),
            None => missing_added(problem, roles, graph, index + 1),
        }
    } else {
        None
    }
}
/// What a self restriction of `label[index..]` of `node` requires along its
/// loop that `node` misses.
fn missing_loop(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    index: usize,
) -> Option<(usize, usize)> {
    if node < graph.nodes.len() {
        if index < graph.nodes[node].label.len() {
            let item = graph.nodes[node].label[index];
            let found = if item < entries.len() {
                match &entries[item] {
                    Entry::HasSelf(own) => missing_edge(entries, roles, graph, node, node, own),
                    _ => None,
                }
            } else {
                None
            };
            match found {
                Some(found) => Some(found),
                None => missing_loop(entries, roles, graph, node, index + 1),
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// The first loop of an active node of `nodes[index..]` that misses something.
fn missing_loops(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    index: usize,
) -> Option<(usize, usize)> {
    if index < graph.nodes.len() {
        let found = if graph.nodes[index].active {
            missing_loop(&problem.entries, roles, graph, index, 0)
        } else {
            None
        };
        match found {
            Some(found) => Some(found),
            None => missing_loops(problem, roles, graph, index + 1),
        }
    } else {
        None
    }
}
/// Whether `label[index..]` of `node` has the complement `¬∃r.Self` of a self
/// restriction while `node` is its own neighbour along `r`; `None` when there
/// is no room.
fn looped_from(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    index: usize,
) -> Option<bool> {
    if node < graph.nodes.len() {
        if index < graph.nodes[node].label.len() {
            let item = graph.nodes[node].label[index];
            let here = if item < problem.entries.len() {
                match &problem.entries[item] {
                    Entry::NotSelf(role) => match neighbours(problem, roles, graph, node, role) {
                        Some(list) => contains(&list, node, 0),
                        None => return None,
                    },
                    _ => false,
                }
            } else {
                false
            };
            if here {
                Some(true)
            } else {
                looped_from(problem, roles, graph, node, index + 1)
            }
        } else {
            Some(false)
        }
    } else {
        Some(false)
    }
}
/// The first active node of `nodes[index..]` with `¬∃r.Self` that is its own
/// neighbour along `r`; `None` when there is no room.
fn looped_node(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    index: usize,
) -> Option<Option<usize>> {
    if index < graph.nodes.len() {
        let here = if graph.nodes[index].active {
            match looped_from(problem, roles, graph, index, 0) {
                Some(here) => here,
                None => return None,
            }
        } else {
            false
        };
        if here {
            Some(Some(index))
        } else {
            looped_node(problem, roles, graph, index + 1)
        }
    } else {
        Some(None)
    }
}
/// The first neighbour of `list[index..]` that decides neither `left` nor
/// `right`.
fn undecided(
    entries: &Vec<Entry>,
    graph: &Forest,
    list: &Vec<usize>,
    left: usize,
    right: usize,
    index: usize,
) -> Option<usize> {
    if index < list.len() {
        let label = label_of(graph, list[index]);
        if holds(entries, &label, left) {
            undecided(entries, graph, list, left, right, index + 1)
        } else if holds(entries, &label, right) {
            undecided(entries, graph, list, left, right, index + 1)
        } else {
            Some(list[index])
        }
    } else {
        None
    }
}
/// Whether a tree node of `list[index..]` that is not a child of `node`
/// satisfies `concept`: a neighbour along an added edge, which the model may
/// repeat.
fn repeated_satisfying(
    entries: &Vec<Entry>,
    graph: &Forest,
    list: &Vec<usize>,
    node: usize,
    concept: usize,
    index: usize,
) -> bool {
    if index < list.len() {
        let other = list[index];
        let mut here = false;
        if other < graph.nodes.len() {
            if graph.nodes[other].tree {
                if graph.nodes[other].parent != node {
                    here = holds(entries, &graph.nodes[other].label, concept);
                }
            }
        }
        if here {
            true
        } else {
            repeated_satisfying(entries, graph, list, node, concept, index + 1)
        }
    } else {
        false
    }
}
/// The index of the first cap of `caps[index..]` on the restriction
/// `restriction` of `node`.
fn cap_at(caps: &Vec<Cap>, node: usize, restriction: usize, index: usize) -> Option<usize> {
    if index < caps.len() {
        if caps[index].node == node {
            if caps[index].restriction == restriction {
                return Some(index);
            }
        }
        cap_at(caps, node, restriction, index + 1)
    } else {
        None
    }
}
/// `out` with the named nodes of `list[index..]`; `None` when there is no room.
fn named_of(
    graph: &Forest,
    list: &Vec<usize>,
    index: usize,
    mut out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < list.len() {
        let mut named = false;
        if list[index] < graph.nodes.len() {
            named = !graph.nodes[list[index]].tree;
        }
        if named {
            if out.len() < usize::MAX {
                out.push(list[index]);
            } else {
                return None;
            }
        }
        named_of(graph, list, index + 1, out)
    } else {
        Some(out)
    }
}
/// The first tree node of `list[index..]` that is not a child of `node`.
fn first_repeated(graph: &Forest, list: &Vec<usize>, node: usize, index: usize) -> Option<usize> {
    if index < list.len() {
        let other = list[index];
        let mut here = false;
        if other < graph.nodes.len() {
            if graph.nodes[other].tree {
                here = graph.nodes[other].parent != node;
            }
        }
        if here {
            Some(other)
        } else {
            first_repeated(graph, list, node, index + 1)
        }
    } else {
        None
    }
}
/// For the maximum restrictions of `label[index..]` of `node`: the first
/// neighbour along the role that decides neither the filler nor its complement
/// (`choose`), or the first restriction with more neighbours that satisfy the
/// filler than it allows (`!choose`). A restriction of a named node that counts
/// a tree node along an added edge asks for new named nodes, and once they exist
/// for a merge into one of them; no answer when it has fewer counted named
/// neighbours than their bound.
fn counting_from(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    choose: bool,
    index: usize,
) -> Option<Option<Step>> {
    if node < graph.nodes.len() {
        if index < graph.nodes[node].label.len() {
            let item = graph.nodes[node].label[index];
            let mut found = None;
            if item < problem.entries.len() {
                match &problem.entries[item] {
                    Entry::AtMost(n, role, filler, complement) => {
                        let list = match neighbours(problem, roles, graph, node, role) {
                            Some(list) => list,
                            None => return None,
                        };
                        if choose {
                            match undecided(&problem.entries, graph, &list, *filler, *complement, 0)
                            {
                                Some(other) => {
                                    found = Some(Step::Choose {
                                        node: other,
                                        left: *filler,
                                        right: *complement,
                                    })
                                }
                                None => {}
                            }
                        } else {
                            let many = match satisfying(
                                &problem.entries,
                                graph,
                                &list,
                                *filler,
                                0,
                                Vec::new(),
                            ) {
                                Some(many) => many,
                                None => return None,
                            };
                            let mut repeated = false;
                            if !graph.nodes[node].tree {
                                repeated = repeated_satisfying(
                                    &problem.entries,
                                    graph,
                                    &list,
                                    node,
                                    *filler,
                                    0,
                                );
                            }
                            if repeated {
                                match cap_at(&graph.caps, node, item, 0) {
                                    Some(cap) => {
                                        let named = match named_of(graph, &many, 0, Vec::new()) {
                                            Some(named) => named,
                                            None => return None,
                                        };
                                        if graph.caps[cap].bound <= named.len() {
                                            found = Some(Step::Capped {
                                                node,
                                                restriction: item,
                                            });
                                        } else {
                                            return None;
                                        }
                                    }
                                    None => {
                                        found = Some(Step::Name {
                                            node,
                                            restriction: item,
                                        });
                                    }
                                }
                            } else if *n < many.len() {
                                found = Some(Step::Merge {
                                    node,
                                    restriction: item,
                                });
                            }
                        }
                    }
                    _ => {}
                }
            }
            match found {
                Some(step) => Some(Some(step)),
                None => counting_from(problem, roles, graph, node, choose, index + 1),
            }
        } else {
            Some(None)
        }
    } else {
        Some(None)
    }
}
/// The first counting step (`choose` or merge) at an active node of
/// `nodes[index..]`.
fn counting(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    choose: bool,
    index: usize,
) -> Option<Option<Step>> {
    if index < graph.nodes.len() {
        let found = if graph.nodes[index].active {
            match counting_from(problem, roles, graph, index, choose, 0) {
                Some(found) => found,
                None => return None,
            }
        } else {
            None
        };
        match found {
            Some(step) => Some(Some(step)),
            None => counting(problem, roles, graph, choose, index + 1),
        }
    } else {
        Some(None)
    }
}
/// Whether the role lists have the same roles.
fn role_listed(
    list: &Vec<ObjectPropertyExpression>,
    role: &ObjectPropertyExpression,
    index: usize,
) -> bool {
    if index < list.len() {
        if same_role(&list[index], role) {
            true
        } else {
            role_listed(list, role, index + 1)
        }
    } else {
        false
    }
}
/// Whether every role of `small[index..]` is in `large`.
fn roles_within(
    small: &Vec<ObjectPropertyExpression>,
    large: &Vec<ObjectPropertyExpression>,
    index: usize,
) -> bool {
    if index < small.len() {
        if role_listed(large, &small[index], 0) {
            roles_within(small, large, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the tree nodes `node` and `other` have the same label, parents with
/// the same label, and the same roles from their parents, where the parent of
/// `other` is a tree node too.
fn same_pair(graph: &Forest, node: usize, other: usize) -> bool {
    if node < graph.nodes.len() && other < graph.nodes.len() {
        let first = graph.nodes[node].parent;
        let second = graph.nodes[other].parent;
        if first < graph.nodes.len() && second < graph.nodes.len() && graph.nodes[second].tree {
            if same_label(&graph.nodes[node].label, &graph.nodes[other].label) {
                if same_label(&graph.nodes[first].label, &graph.nodes[second].label) {
                    if roles_within(&graph.nodes[node].roles, &graph.nodes[other].roles, 0) {
                        return roles_within(
                            &graph.nodes[other].roles,
                            &graph.nodes[node].roles,
                            0,
                        );
                    }
                }
            }
        }
    }
    false
}
/// Whether the pair of `node` repeats the pair of `ancestor` or of a tree node
/// above it.
fn repeats_above(graph: &Forest, node: usize, ancestor: usize) -> bool {
    if ancestor < graph.nodes.len() {
        if graph.nodes[ancestor].tree {
            if same_pair(graph, node, ancestor) {
                true
            } else if graph.nodes[ancestor].parent < ancestor {
                repeats_above(graph, node, graph.nodes[ancestor].parent)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}
/// Whether a tree node on the path from `node` up to its root repeats the pair
/// of a tree node above it.
fn blocked(graph: &Forest, node: usize) -> bool {
    if node < graph.nodes.len() {
        if graph.nodes[node].tree {
            let parent = graph.nodes[node].parent;
            if parent < node {
                if repeats_above(graph, node, parent) {
                    true
                } else {
                    blocked(graph, parent)
                }
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}
/// Whether the entry creates neighbours: an existential or minimum restriction.
fn generating(entry: &Entry) -> bool {
    match entry {
        Entry::Exists(_, _) => true,
        Entry::AtLeast(_, _, _) => true,
        _ => false,
    }
}
/// Whether `node` has as many neighbours along the role of the restriction
/// `generator` that satisfy its filler as the restriction requires; `None` when
/// there is no room or the entry creates no neighbours.
fn enough(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    generator: usize,
) -> Option<bool> {
    let (role, count, filler) = match generator_of(&problem.entries, generator) {
        Some(found) => found,
        None => return None,
    };
    let list = match neighbours(problem, roles, graph, node, &role) {
        Some(list) => list,
        None => return None,
    };
    match satisfying(&problem.entries, graph, &list, filler, 0, Vec::new()) {
        Some(many) => Some(count <= many.len()),
        None => None,
    }
}
/// Whether the entry `item` creates neighbours and, when `expand`, was not
/// expanded at `node`.
fn candidate(problem: &Problem, graph: &Forest, node: usize, item: usize, expand: bool) -> bool {
    if item < problem.entries.len() && node < graph.nodes.len() {
        if generating(&problem.entries[item]) {
            if expand {
                !contains(&graph.nodes[node].done, item, 0)
            } else {
                true
            }
        } else {
            false
        }
    } else {
        false
    }
}
/// The first restriction of `label[index..]` of `node` that creates neighbours,
/// lacks some, and (when `expand`) was not expanded; `None` when there is no
/// room.
fn lacking(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    node: usize,
    expand: bool,
    index: usize,
) -> Option<Option<usize>> {
    if node < graph.nodes.len() {
        if index < graph.nodes[node].label.len() {
            let item = graph.nodes[node].label[index];
            if candidate(problem, graph, node, item, expand) {
                match enough(problem, roles, graph, node, item) {
                    Some(true) => {}
                    Some(false) => return Some(Some(item)),
                    None => return None,
                }
            }
            lacking(problem, roles, graph, node, expand, index + 1)
        } else {
            Some(None)
        }
    } else {
        Some(None)
    }
}
/// The first active, unblocked node of `nodes[index..]` with a restriction that
/// lacks neighbours (and, when `expand`, was not expanded), and that
/// restriction; `None` when there is no room.
fn missing_successor(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: &Forest,
    expand: bool,
    index: usize,
) -> Option<Option<(usize, usize)>> {
    if index < graph.nodes.len() {
        let mut found = None;
        if graph.nodes[index].active {
            if !blocked(graph, index) {
                match lacking(problem, roles, graph, index, expand, 0) {
                    Some(item) => found = item,
                    None => return None,
                }
            }
        }
        match found {
            Some(item) => Some(Some((index, item))),
            None => missing_successor(problem, roles, graph, expand, index + 1),
        }
    } else {
        Some(None)
    }
}
/// Whether the entry `concept` is the nominal of `individual`.
fn names(problem: &Problem, concept: usize, individual: &Individual) -> bool {
    if concept < problem.entries.len() {
        match &problem.entries[concept] {
            Entry::One(other) => same_individual_value(other, individual),
            _ => false,
        }
    } else {
        false
    }
}
/// The named node of `individual`: the node of the first requirement of
/// `requirements[index..]` with its nominal, read through the merges; `None`
/// when there is none.
fn nominal_root(
    problem: &Problem,
    graph: &Forest,
    individual: &Individual,
    index: usize,
) -> Option<usize> {
    if index < problem.requirements.len() {
        if names(problem, problem.requirements[index].concept, individual) {
            Some(representative(graph, problem.requirements[index].node))
        } else {
            nominal_root(problem, graph, individual, index + 1)
        }
    } else {
        None
    }
}
/// The named node of a nominal of `label[index..]` of `node`, when it is not
/// `node` itself; `None` when the individual of a nominal, or of the complement
/// of one, has no named node.
fn nominal_at(
    problem: &Problem,
    graph: &Forest,
    node: usize,
    index: usize,
) -> Option<Option<usize>> {
    if node < graph.nodes.len() {
        if index < graph.nodes[node].label.len() {
            let item = graph.nodes[node].label[index];
            if item < problem.entries.len() {
                match &problem.entries[item] {
                    Entry::One(individual) => match nominal_root(problem, graph, individual, 0) {
                        Some(root) => {
                            if root != node {
                                return Some(Some(root));
                            }
                        }
                        None => return None,
                    },
                    Entry::NotOne(individual) => {
                        match nominal_root(problem, graph, individual, 0) {
                            Some(_) => {}
                            None => return None,
                        }
                    }
                    _ => {}
                }
            }
            nominal_at(problem, graph, node, index + 1)
        } else {
            Some(None)
        }
    } else {
        Some(None)
    }
}
/// The first active node of `nodes[index..]` with a nominal of another named
/// node, and that node; `None` when a nominal has no named node.
fn nominal_node(problem: &Problem, graph: &Forest, index: usize) -> Option<Option<(usize, usize)>> {
    if index < graph.nodes.len() {
        let found = if graph.nodes[index].active {
            match nominal_at(problem, graph, index, 0) {
                Some(found) => found,
                None => return None,
            }
        } else {
            None
        };
        match found {
            Some(root) => Some(Some((index, root))),
            None => nominal_node(problem, graph, index + 1),
        }
    } else {
        Some(None)
    }
}
/// The next rule: a missing concept of a node or an edge, else a nominal to
/// merge, else a neighbour to decide, else a merge, else a restriction to
/// expand; when none applies, the check that every restriction has enough
/// neighbours (`Stuck` when one has not); `None` when there is no room or a
/// nominal has no named node.
fn next_step(problem: &Problem, roles: &RoleHierarchy, graph: &Forest) -> Option<Step> {
    match missing_node(problem, graph, 0) {
        Some((node, concept)) => return Some(Step::Add { node, concept }),
        None => {}
    }
    match missing_tree(problem, roles, graph, 0) {
        Some((node, concept)) => return Some(Step::Add { node, concept }),
        None => {}
    }
    match missing_link(problem, roles, graph, 0) {
        Some((node, concept)) => return Some(Step::Add { node, concept }),
        None => {}
    }
    match missing_added(problem, roles, graph, 0) {
        Some((node, concept)) => return Some(Step::Add { node, concept }),
        None => {}
    }
    match missing_loops(problem, roles, graph, 0) {
        Some((node, concept)) => return Some(Step::Add { node, concept }),
        None => {}
    }
    match looped_node(problem, roles, graph, 0) {
        Some(Some(node)) => return Some(Step::Loop { node }),
        Some(None) => {}
        None => return None,
    }
    match nominal_node(problem, graph, 0) {
        Some(Some((node, root))) => return Some(Step::Nominal { node, root }),
        Some(None) => {}
        None => return None,
    }
    match counting(problem, roles, graph, true, 0) {
        Some(Some(step)) => return Some(step),
        Some(None) => {}
        None => return None,
    }
    match counting(problem, roles, graph, false, 0) {
        Some(Some(step)) => return Some(step),
        Some(None) => {}
        None => return None,
    }
    match missing_successor(problem, roles, graph, true, 0) {
        Some(Some((node, generator))) => Some(Step::Create { node, generator }),
        Some(None) => match missing_successor(problem, roles, graph, false, 0) {
            Some(Some(_)) => Some(Step::Stuck),
            Some(None) => Some(Step::Done),
            None => None,
        },
        None => None,
    }
}
fn copy_roles(
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Vec<ObjectPropertyExpression> {
    if index < roles.len() {
        if out.len() < usize::MAX {
            out.push(copy_role(&roles[index]));
        }
        copy_roles(roles, index + 1, out)
    } else {
        out
    }
}
fn copy_nodes(nodes: &Vec<Node>, index: usize, mut out: Vec<Node>) -> Vec<Node> {
    if index < nodes.len() {
        if out.len() < usize::MAX {
            out.push(Node {
                label: copy_label(&nodes[index].label, 0, Vec::new()),
                parent: nodes[index].parent,
                roles: copy_roles(&nodes[index].roles, 0, Vec::new()),
                seed: nodes[index].seed,
                tree: nodes[index].tree,
                active: nodes[index].active,
                done: copy_label(&nodes[index].done, 0, Vec::new()),
                deps: copy_label(&nodes[index].deps, 0, Vec::new()),
            });
        }
        copy_nodes(nodes, index + 1, out)
    } else {
        out
    }
}
fn copy_edges(edges: &Vec<Edge>, index: usize, mut out: Vec<Edge>) -> Vec<Edge> {
    if index < edges.len() {
        if out.len() < usize::MAX {
            out.push(Edge {
                role: copy_role(&edges[index].role),
                from: edges[index].from,
                to: edges[index].to,
                deps: copy_label(&edges[index].deps, 0, Vec::new()),
            });
        }
        copy_edges(edges, index + 1, out)
    } else {
        out
    }
}
fn copy_distinct(distinct: &Vec<Distinct>, index: usize, mut out: Vec<Distinct>) -> Vec<Distinct> {
    if index < distinct.len() {
        if out.len() < usize::MAX {
            out.push(Distinct {
                left: distinct[index].left,
                right: distinct[index].right,
                deps: copy_label(&distinct[index].deps, 0, Vec::new()),
            });
        }
        copy_distinct(distinct, index + 1, out)
    } else {
        out
    }
}
fn copy_caps(caps: &Vec<Cap>, index: usize, mut out: Vec<Cap>) -> Vec<Cap> {
    if index < caps.len() {
        if out.len() < usize::MAX {
            out.push(Cap {
                node: caps[index].node,
                restriction: caps[index].restriction,
                bound: caps[index].bound,
                deps: copy_label(&caps[index].deps, 0, Vec::new()),
            });
        }
        copy_caps(caps, index + 1, out)
    } else {
        out
    }
}
fn copy_forest(graph: &Forest) -> Forest {
    Forest {
        nodes: copy_nodes(&graph.nodes, 0, Vec::new()),
        edges: copy_edges(&graph.edges, 0, Vec::new()),
        distinct: copy_distinct(&graph.distinct, 0, Vec::new()),
        same: copy_label(&graph.same, 0, Vec::new()),
        caps: copy_caps(&graph.caps, 0, Vec::new()),
    }
}
/// The forest with `item` added to the label of `node`, which then also depends
/// on `deps`; `None` when there is no room.
fn insert(mut graph: Forest, node: usize, item: usize, deps: &Vec<usize>) -> Option<Forest> {
    if node < graph.nodes.len() {
        if graph.nodes[node].label.len() < usize::MAX {
            match join(&graph.nodes[node].deps, deps) {
                Some(joined) => {
                    graph.nodes[node].label.push(item);
                    graph.nodes[node].deps = joined;
                    Some(graph)
                }
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// Try the left disjunct under the new branch point `depth`. If it fails with a
/// clash that does not depend on that point, the right disjunct fails the same
/// way and the clash is reported; otherwise the right disjunct is tried on a
/// copy, depending on the points the left failure depended on.
fn branch(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    left: usize,
    right: usize,
    next: Box<Pending>,
    deps: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    if depth < usize::MAX {
        let other = copy_forest(&graph);
        let other_next = copy_pending(&next);
        let mut point = Vec::new();
        point.push(depth);
        let left_deps = match join(&deps, &point) {
            Some(left_deps) => left_deps,
            None => return None,
        };
        match add(
            problem,
            roles,
            graph,
            node,
            Pending::Item {
                concept: left,
                next,
            },
            left_deps,
            depth + 1,
        ) {
            Some(Outcome::Accepted) => Some(Outcome::Accepted),
            Some(Outcome::Rejected(clash)) => {
                if contains(&clash, depth, 0) {
                    let rest = without_from(&clash, depth, 0, Vec::new());
                    match join(&deps, &rest) {
                        Some(right_deps) => add(
                            problem,
                            roles,
                            other,
                            node,
                            Pending::Item {
                                concept: right,
                                next: Box::new(other_next),
                            },
                            right_deps,
                            depth,
                        ),
                        None => None,
                    }
                } else {
                    Some(Outcome::Rejected(clash))
                }
            }
            None => None,
        }
    } else {
        None
    }
}
/// Add a literal, which depends on `deps`, to the label of `node` unless it is
/// there; a complementary literal is a clash that depends on the node's points
/// and `deps`.
fn add_literal(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    concept: usize,
    next: Box<Pending>,
    deps: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    if node < graph.nodes.len() {
        if contains(&graph.nodes[node].label, concept, 0) {
            add(problem, roles, graph, node, *next, deps, depth)
        } else if clashes(&problem.entries, &graph.nodes[node].label, concept, 0) {
            match join(&graph.nodes[node].deps, &deps) {
                Some(clash) => Some(Outcome::Rejected(clash)),
                None => None,
            }
        } else {
            match insert(graph, node, concept, &deps) {
                Some(graph) => add(problem, roles, graph, node, *next, deps, depth),
                None => None,
            }
        }
    } else {
        None
    }
}
/// Add the pending entries, which depend on `deps`, to the label of `node`,
/// then continue the run; `depth` is the next free branch point.
fn add(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    pending: Pending,
    deps: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    match pending {
        Pending::Empty => run(problem, roles, graph, depth),
        Pending::Item { concept, next } => {
            if concept < problem.entries.len() {
                match &problem.entries[concept] {
                    Entry::Top => add(problem, roles, graph, node, *next, deps, depth),
                    Entry::Bottom => Some(Outcome::Rejected(deps)),
                    Entry::And(left, right) => add(
                        problem,
                        roles,
                        graph,
                        node,
                        Pending::Item {
                            concept: *left,
                            next: Box::new(Pending::Item {
                                concept: *right,
                                next,
                            }),
                        },
                        deps,
                        depth,
                    ),
                    Entry::Or(left, right) => branch(
                        problem, roles, graph, node, *left, *right, next, deps, depth,
                    ),
                    _ => add_literal(problem, roles, graph, node, concept, next, deps, depth),
                }
            } else {
                None
            }
        }
    }
}
/// The role, the number of neighbours and the filler of a restriction that
/// creates neighbours.
fn generator_of(
    entries: &Vec<Entry>,
    generator: usize,
) -> Option<(ObjectPropertyExpression, usize, usize)> {
    if generator < entries.len() {
        match &entries[generator] {
            Entry::Exists(role, filler) => Some((copy_role(role), 1, *filler)),
            Entry::AtLeast(n, role, filler) => Some((copy_role(role), *n, *filler)),
            _ => None,
        }
    } else {
        None
    }
}
/// The forest with `count` more tree nodes below `node` along `role`, each with
/// the seed `filler`, depending on `deps`.
fn children(
    mut graph: Forest,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
    deps: &Vec<usize>,
    count: usize,
) -> Option<Forest> {
    if count > 0 {
        if graph.nodes.len() < usize::MAX {
            let mut list = Vec::new();
            list.push(copy_role(role));
            graph.nodes.push(Node {
                label: Vec::new(),
                parent: node,
                roles: list,
                seed: filler,
                tree: true,
                active: true,
                done: Vec::new(),
                deps: copy_label(deps, 0, Vec::new()),
            });
            children(graph, node, role, filler, deps, count - 1)
        } else {
            None
        }
    } else {
        Some(graph)
    }
}
/// The forest where `node` differs from every node of `nodes[other..]`.
fn differ_from(mut graph: Forest, node: usize, other: usize, deps: &Vec<usize>) -> Option<Forest> {
    if other < graph.nodes.len() {
        if graph.distinct.len() < usize::MAX {
            graph.distinct.push(Distinct {
                left: node,
                right: other,
                deps: copy_label(deps, 0, Vec::new()),
            });
            differ_from(graph, node, other + 1, deps)
        } else {
            None
        }
    } else {
        Some(graph)
    }
}
/// The forest where the nodes of `nodes[node..]` pairwise differ.
fn pairwise(graph: Forest, node: usize, deps: &Vec<usize>) -> Option<Forest> {
    if node < graph.nodes.len() {
        match differ_from(graph, node, node + 1, deps) {
            Some(graph) => pairwise(graph, node + 1, deps),
            None => None,
        }
    } else {
        Some(graph)
    }
}
/// The forest after expanding the restriction `generator` of `node`: new tree
/// nodes along its role with its filler as their seed, pairwise different,
/// depending on the points of `node`, and the restriction marked as expanded.
fn expanded(entries: &Vec<Entry>, graph: Forest, node: usize, generator: usize) -> Option<Forest> {
    let (role, count, filler) = match generator_of(entries, generator) {
        Some(found) => found,
        None => return None,
    };
    if node < graph.nodes.len() {
        let deps = copy_label(&graph.nodes[node].deps, 0, Vec::new());
        let first = graph.nodes.len();
        let graph = match children(graph, node, &role, filler, &deps, count) {
            Some(graph) => graph,
            None => return None,
        };
        let mut graph = match pairwise(graph, first, &deps) {
            Some(graph) => graph,
            None => return None,
        };
        if graph.nodes[node].done.len() < usize::MAX {
            graph.nodes[node].done.push(generator);
            Some(graph)
        } else {
            None
        }
    } else {
        None
    }
}
/// Expand a restriction of `node`, then continue the run.
fn create(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    generator: usize,
    depth: usize,
) -> Option<Outcome> {
    match expanded(&problem.entries, graph, node, generator) {
        Some(graph) => run(problem, roles, graph, depth),
        None => None,
    }
}
/// `out` with the points of the end of every link and edge of `node`, read
/// through the merges, and of those edges.
fn linked_deps(
    graph: &Forest,
    links: &Vec<Link>,
    node: usize,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < links.len() {
        let from = representative(graph, links[index].from);
        let to = representative(graph, links[index].to);
        let out = if from == node {
            match end_deps(graph, to, out) {
                Some(out) => out,
                None => return None,
            }
        } else {
            out
        };
        let out = if to == node {
            match end_deps(graph, from, out) {
                Some(out) => out,
                None => return None,
            }
        } else {
            out
        };
        linked_deps(graph, links, node, index + 1, out)
    } else {
        Some(out)
    }
}
/// `out` with the points of every edge of `edges[index..]` at `node`, read
/// through the merges, and of its other end.
fn edge_deps(graph: &Forest, node: usize, index: usize, out: Vec<usize>) -> Option<Vec<usize>> {
    if index < graph.edges.len() {
        let from = representative(graph, graph.edges[index].from);
        let to = representative(graph, graph.edges[index].to);
        let at = if from == node {
            true
        } else if to == node {
            true
        } else {
            false
        };
        let out = if at {
            let out = match join_from(&graph.edges[index].deps, 0, out) {
                Some(out) => out,
                None => return None,
            };
            let out = match end_deps(graph, from, out) {
                Some(out) => out,
                None => return None,
            };
            match end_deps(graph, to, out) {
                Some(out) => out,
                None => return None,
            }
        } else {
            out
        };
        edge_deps(graph, node, index + 1, out)
    } else {
        Some(out)
    }
}
/// `out` with the points of node `end`, if there is such a node.
fn end_deps(graph: &Forest, end: usize, out: Vec<usize>) -> Option<Vec<usize>> {
    if end < graph.nodes.len() {
        join_from(&graph.nodes[end].deps, 0, out)
    } else {
        Some(out)
    }
}
/// `out` with the points of every active tree node of `nodes[index..]` below
/// `node`.
fn children_deps(graph: &Forest, node: usize, index: usize, out: Vec<usize>) -> Option<Vec<usize>> {
    if index < graph.nodes.len() {
        let child = if graph.nodes[index].tree {
            if graph.nodes[index].active {
                graph.nodes[index].parent == node
            } else {
                false
            }
        } else {
            false
        };
        if child {
            match join_from(&graph.nodes[index].deps, 0, out) {
                Some(out) => children_deps(graph, node, index + 1, out),
                None => None,
            }
        } else {
            children_deps(graph, node, index + 1, out)
        }
    } else {
        Some(out)
    }
}
/// The points the labels of `node` and of its neighbours depend on, and the
/// edges between them: everything a rule at `node` can rest on.
fn rule_deps(problem: &Problem, graph: &Forest, node: usize) -> Option<Vec<usize>> {
    if node < graph.nodes.len() {
        let own = copy_label(&graph.nodes[node].deps, 0, Vec::new());
        let with_parent = if graph.nodes[node].tree {
            end_deps(graph, graph.nodes[node].parent, own)
        } else {
            Some(own)
        };
        let out = match with_parent {
            Some(out) => out,
            None => return None,
        };
        let out = match children_deps(graph, node, 0, out) {
            Some(out) => out,
            None => return None,
        };
        let out = match linked_deps(graph, &problem.links, node, 0, out) {
            Some(out) => out,
            None => return None,
        };
        edge_deps(graph, node, 0, out)
    } else {
        None
    }
}
/// Whether `distinct[index..]` says that the two nodes differ.
fn differ(graph: &Forest, left: usize, right: usize, index: usize) -> bool {
    if index < graph.distinct.len() {
        let fact = &graph.distinct[index];
        let here = if fact.left == left {
            fact.right == right
        } else if fact.left == right {
            fact.right == left
        } else {
            false
        };
        if here {
            true
        } else {
            differ(graph, left, right, index + 1)
        }
    } else {
        false
    }
}
/// `out` with the points of every difference of `distinct[index..]` between
/// two nodes of `chosen`.
fn differences_deps(
    graph: &Forest,
    chosen: &Vec<usize>,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < graph.distinct.len() {
        let fact = &graph.distinct[index];
        let inside = if contains(chosen, fact.left, 0) {
            contains(chosen, fact.right, 0)
        } else {
            false
        };
        if inside {
            match join_from(&fact.deps, 0, out) {
                Some(out) => differences_deps(graph, chosen, index + 1, out),
                None => None,
            }
        } else {
            differences_deps(graph, chosen, index + 1, out)
        }
    } else {
        Some(out)
    }
}
/// `out` with every pair of `chosen[first]` and a node of `chosen[second..]`
/// that are not known to differ.
fn pairs_with(
    graph: &Forest,
    chosen: &Vec<usize>,
    first: usize,
    second: usize,
    mut out: Vec<Pair>,
) -> Option<Vec<Pair>> {
    if first < chosen.len() {
        if second < chosen.len() {
            if differ(graph, chosen[first], chosen[second], 0) {
                pairs_with(graph, chosen, first, second + 1, out)
            } else if out.len() < usize::MAX {
                out.push(Pair {
                    first: chosen[first],
                    second: chosen[second],
                });
                pairs_with(graph, chosen, first, second + 1, out)
            } else {
                None
            }
        } else {
            Some(out)
        }
    } else {
        Some(out)
    }
}
/// `out` with every pair of nodes of `chosen[first..]` that are not known to
/// differ.
fn pairs_from(
    graph: &Forest,
    chosen: &Vec<usize>,
    first: usize,
    out: Vec<Pair>,
) -> Option<Vec<Pair>> {
    if first < chosen.len() {
        match pairs_with(graph, chosen, first, first + 1, out) {
            Some(out) => pairs_from(graph, chosen, first + 1, out),
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The first `count` nodes of `list[index..]`, after `out`.
fn first_nodes(list: &Vec<usize>, count: usize, index: usize, mut out: Vec<usize>) -> Vec<usize> {
    if index < list.len() {
        if out.len() < count {
            out.push(list[index]);
            first_nodes(list, count, index + 1, out)
        } else {
            out
        }
    } else {
        out
    }
}
/// `out` with the roles of `list[index..]`, inverted when `invert`; `None`
/// when there is no room.
fn add_roles(
    list: &Vec<ObjectPropertyExpression>,
    invert: bool,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Option<Vec<ObjectPropertyExpression>> {
    if index < list.len() {
        if out.len() < usize::MAX {
            let role = if invert {
                inverse(&list[index])
            } else {
                copy_role(&list[index])
            };
            out.push(role);
            add_roles(list, invert, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The forest where the tree node `node` also has the inverses of the roles of
/// `from` and depends on `deps`: a child of `node` merged into the parent of
/// `node`.
fn upward(mut graph: Forest, node: usize, from: usize, deps: &Vec<usize>) -> Option<Forest> {
    if node < graph.nodes.len() && from < graph.nodes.len() {
        let start = copy_roles(&graph.nodes[node].roles, 0, Vec::new());
        let added = match add_roles(&graph.nodes[from].roles, true, 0, start) {
            Some(added) => added,
            None => return None,
        };
        let joined = match join(&graph.nodes[node].deps, deps) {
            Some(joined) => joined,
            None => return None,
        };
        graph.nodes[node].roles = added;
        graph.nodes[node].deps = joined;
        Some(graph)
    } else {
        None
    }
}
/// The forest where the tree node `into` also has the roles of its sibling
/// `from`.
fn sideways(mut graph: Forest, from: usize, into: usize) -> Option<Forest> {
    if from < graph.nodes.len() && into < graph.nodes.len() {
        let start = copy_roles(&graph.nodes[into].roles, 0, Vec::new());
        let added = match add_roles(&graph.nodes[from].roles, false, 0, start) {
            Some(added) => added,
            None => return None,
        };
        graph.nodes[into].roles = added;
        Some(graph)
    } else {
        None
    }
}
/// `out` with an edge from `node` to `into` along every role of
/// `list[index..]`, depending on `deps`; `None` when there is no room.
fn add_edges(
    list: &Vec<ObjectPropertyExpression>,
    node: usize,
    into: usize,
    deps: &Vec<usize>,
    index: usize,
    mut out: Vec<Edge>,
) -> Option<Vec<Edge>> {
    if index < list.len() {
        if out.len() < usize::MAX {
            out.push(Edge {
                role: copy_role(&list[index]),
                from: node,
                to: into,
                deps: copy_label(deps, 0, Vec::new()),
            });
            add_edges(list, node, into, deps, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The forest with an edge from the named node `node` to the named node `into`
/// along every role of the tree node `from`, depending on `deps`.
fn linked(
    mut graph: Forest,
    node: usize,
    from: usize,
    into: usize,
    deps: &Vec<usize>,
) -> Option<Forest> {
    if from < graph.nodes.len() {
        let start = copy_edges(&graph.edges, 0, Vec::new());
        let added = match add_edges(&graph.nodes[from].roles, node, into, deps, 0, start) {
            Some(added) => added,
            None => return None,
        };
        graph.edges = added;
        Some(graph)
    } else {
        None
    }
}
/// `out` with the representatives of `same[index..]`, `into` in place of
/// `from`.
fn renamed(
    same: &Vec<usize>,
    from: usize,
    into: usize,
    index: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if index < same.len() {
        if out.len() < usize::MAX {
            if same[index] == from {
                out.push(into);
            } else {
                out.push(same[index]);
            }
        }
        renamed(same, from, into, index + 1, out)
    } else {
        out
    }
}
/// `out` with a difference between `into` and every node that a difference of
/// `distinct[index..]` says `from` differs from, also depending on `deps`;
/// `None` when there is no room.
fn inherit(
    distinct: &Vec<Distinct>,
    from: usize,
    into: usize,
    deps: &Vec<usize>,
    index: usize,
    mut out: Vec<Distinct>,
) -> Option<Vec<Distinct>> {
    if index < distinct.len() {
        let left = distinct[index].left;
        let right = distinct[index].right;
        let other = if left == from {
            Some(right)
        } else if right == from {
            Some(left)
        } else {
            None
        };
        match other {
            Some(other) => {
                let joined = match join(&distinct[index].deps, deps) {
                    Some(joined) => joined,
                    None => return None,
                };
                if out.len() < usize::MAX {
                    out.push(Distinct {
                        left: into,
                        right: other,
                        deps: joined,
                    });
                    inherit(distinct, from, into, deps, index + 1, out)
                } else {
                    None
                }
            }
            None => inherit(distinct, from, into, deps, index + 1, out),
        }
    } else {
        Some(out)
    }
}
/// `out` with copies of the nodes of `nodes[index..]`, where a tree node whose
/// parent among the copies is not active is not active either.
fn pruned(nodes: &Vec<Node>, index: usize, mut out: Vec<Node>) -> Vec<Node> {
    if index < nodes.len() {
        if out.len() < usize::MAX {
            let mut active = nodes[index].active;
            if nodes[index].tree {
                let parent = nodes[index].parent;
                if parent < out.len() {
                    if !out[parent].active {
                        active = false;
                    }
                }
            }
            out.push(Node {
                label: copy_label(&nodes[index].label, 0, Vec::new()),
                parent: nodes[index].parent,
                roles: copy_roles(&nodes[index].roles, 0, Vec::new()),
                seed: nodes[index].seed,
                tree: nodes[index].tree,
                active,
                done: copy_label(&nodes[index].done, 0, Vec::new()),
                deps: copy_label(&nodes[index].deps, 0, Vec::new()),
            });
        }
        pruned(nodes, index + 1, out)
    } else {
        out
    }
}
/// The label of `node` as pending entries, from `label[index..]` on.
fn pending_from(label: &Vec<usize>, index: usize) -> Pending {
    if index < label.len() {
        Pending::Item {
            concept: label[index],
            next: Box::new(pending_from(label, index + 1)),
        }
    } else {
        Pending::Empty
    }
}
/// `out` with an edge from `into` for every edge of `edges[index..]` from the
/// tree node `from`, also depending on `deps`; `None` when there is no room.
fn carried_from(
    edges: &Vec<Edge>,
    from: usize,
    into: usize,
    deps: &Vec<usize>,
    index: usize,
    mut out: Vec<Edge>,
) -> Option<Vec<Edge>> {
    if index < edges.len() {
        if edges[index].from == from {
            let joined = match join(&edges[index].deps, deps) {
                Some(joined) => joined,
                None => return None,
            };
            if out.len() < usize::MAX {
                out.push(Edge {
                    role: copy_role(&edges[index].role),
                    from: into,
                    to: edges[index].to,
                    deps: joined,
                });
            } else {
                return None;
            }
        }
        carried_from(edges, from, into, deps, index + 1, out)
    } else {
        Some(out)
    }
}
/// The forest where `into` also has the added edges of the tree node `from`.
fn carried(mut graph: Forest, from: usize, into: usize, deps: &Vec<usize>) -> Option<Forest> {
    let start = copy_edges(&graph.edges, 0, Vec::new());
    match carried_from(&graph.edges, from, into, deps, 0, start) {
        Some(edges) => {
            graph.edges = edges;
            Some(graph)
        }
        None => None,
    }
}
/// Whether an end of the edge is `node`.
fn at_node(edge: &Edge, node: usize) -> bool {
    if edge.from == node {
        true
    } else {
        edge.to == node
    }
}
/// The edge with an end at the named node `from` moved to `into`, then also
/// depending on `deps`; any other edge as it is. `None` when there is no room.
fn relink(edge: &Edge, from: usize, into: usize, deps: &Vec<usize>) -> Option<Edge> {
    let source = if edge.from == from { into } else { edge.from };
    let target = if edge.to == from { into } else { edge.to };
    let depends = if at_node(edge, from) {
        match join(&edge.deps, deps) {
            Some(depends) => depends,
            None => return None,
        }
    } else {
        copy_label(&edge.deps, 0, Vec::new())
    };
    Some(Edge {
        role: copy_role(&edge.role),
        from: source,
        to: target,
        deps: depends,
    })
}
/// `out` with the edges of `edges[index..]`, each relinked from the named node
/// `from` to `into`; `None` when there is no room.
fn relinked(
    edges: &Vec<Edge>,
    from: usize,
    into: usize,
    deps: &Vec<usize>,
    index: usize,
    mut out: Vec<Edge>,
) -> Option<Vec<Edge>> {
    if index < edges.len() {
        let edge = match relink(&edges[index], from, into, deps) {
            Some(edge) => edge,
            None => return None,
        };
        if out.len() < usize::MAX {
            out.push(edge);
            relinked(edges, from, into, deps, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The forest where `from` hands its edges over to `into`: a merged tree node's
/// edge from its parent goes onto the parent of its parent (`upward`), onto a
/// sibling (`sideways`) or onto a named node (`linked`), and its added edges go
/// to `into`; a merged named node passes its individuals and its added edges
/// on.
fn moved(graph: Forest, from: usize, into: usize, joined: &Vec<usize>) -> Option<Forest> {
    if from < graph.nodes.len() && into < graph.nodes.len() {
        if graph.nodes[from].tree {
            let node = graph.nodes[from].parent;
            if node < graph.nodes.len() {
                let graph = if graph.nodes[node].tree && graph.nodes[node].parent == into {
                    upward(graph, node, from, joined)
                } else if graph.nodes[into].tree {
                    sideways(graph, from, into)
                } else {
                    linked(graph, node, from, into, joined)
                };
                match graph {
                    Some(graph) => carried(graph, from, into, joined),
                    None => None,
                }
            } else {
                None
            }
        } else {
            let same = renamed(&graph.same, from, into, 0, Vec::new());
            let edges = match relinked(&graph.edges, from, into, joined, 0, Vec::new()) {
                Some(edges) => edges,
                None => return None,
            };
            let mut graph = graph;
            graph.same = same;
            graph.edges = edges;
            Some(graph)
        }
    } else {
        None
    }
}
/// The forest after merging `from` into `into`, which then depends on
/// `joined`: `into` gets the edges and the differences of `from`, and `from` is
/// pruned with its subtree.
fn merged(graph: Forest, from: usize, into: usize, joined: &Vec<usize>) -> Option<Forest> {
    let mut graph = match moved(graph, from, into, joined) {
        Some(graph) => graph,
        None => return None,
    };
    if from < graph.nodes.len() && into < graph.nodes.len() {
        let start = copy_distinct(&graph.distinct, 0, Vec::new());
        let distinct = match inherit(&graph.distinct, from, into, joined, 0, start) {
            Some(distinct) => distinct,
            None => return None,
        };
        graph.distinct = distinct;
        graph.nodes[from].active = false;
        let nodes = pruned(&graph.nodes, 0, Vec::new());
        graph.nodes = nodes;
        match join(&graph.nodes[into].deps, joined) {
            Some(depends) => {
                graph.nodes[into].deps = depends;
                Some(graph)
            }
            None => None,
        }
    } else {
        None
    }
}
/// Merge `from` into `into`, which depends on `deps`, then add the label of
/// `from` to `into`.
fn merge(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    from: usize,
    into: usize,
    deps: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    if from < graph.nodes.len() {
        let label = copy_label(&graph.nodes[from].label, 0, Vec::new());
        let joined = match join(&deps, &graph.nodes[from].deps) {
            Some(joined) => joined,
            None => return None,
        };
        match merged(graph, from, into, &joined) {
            Some(graph) => add(
                problem,
                roles,
                graph,
                into,
                pending_from(&label, 0),
                joined,
                depth,
            ),
            None => None,
        }
    } else {
        None
    }
}
/// Whether a pair of neighbours of the tree node `node` has `node` itself and
/// another tree node, its child or its parent: no merge moves a tree node into
/// its parent yet.
fn looped_pair(graph: &Forest, node: usize, pair: &Pair) -> bool {
    if node < graph.nodes.len() && pair.first < graph.nodes.len() && pair.second < graph.nodes.len()
    {
        if graph.nodes[node].tree && graph.nodes[pair.first].tree && graph.nodes[pair.second].tree {
            if pair.first == node {
                true
            } else {
                pair.second == node
            }
        } else {
            false
        }
    } else {
        false
    }
}
/// The merge of a pair of neighbours of `node`: a tree node into a named node,
/// a child into the parent of `node`, a later sibling into an earlier one, a
/// named node into another one.
fn orient(graph: &Forest, node: usize, pair: &Pair) -> (usize, usize) {
    let first = pair.first;
    let second = pair.second;
    if first < graph.nodes.len() && second < graph.nodes.len() && node < graph.nodes.len() {
        if graph.nodes[first].tree {
            if !graph.nodes[second].tree {
                return (first, second);
            }
            if graph.nodes[node].tree {
                if graph.nodes[node].parent == first {
                    return (second, first);
                }
            }
            return (first, second);
        } else if graph.nodes[second].tree {
            return (second, first);
        }
    }
    (second, first)
}
/// Try the merges of `pairs[index..]` in turn: all but the last under the
/// branch point `depth`, skipping the rest when a failure does not depend on
/// it, and the last depending on the points the earlier failures depended on
/// (`skipped`). Without pairs, the restriction is violated: a clash.
fn choices(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    pairs: &Vec<Pair>,
    index: usize,
    deps: Vec<usize>,
    skipped: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    if index < pairs.len() {
        if looped_pair(&graph, node, &pairs[index]) {
            return None;
        }
        let (from, into) = orient(&graph, node, &pairs[index]);
        if index + 1 < pairs.len() {
            if depth < usize::MAX {
                let other = copy_forest(&graph);
                let mut point = Vec::new();
                point.push(depth);
                let here = match join(&deps, &point) {
                    Some(here) => here,
                    None => return None,
                };
                match merge(problem, roles, graph, from, into, here, depth + 1) {
                    Some(Outcome::Accepted) => Some(Outcome::Accepted),
                    Some(Outcome::Rejected(clash)) => {
                        if contains(&clash, depth, 0) {
                            let rest = without_from(&clash, depth, 0, Vec::new());
                            match join(&skipped, &rest) {
                                Some(skipped) => choices(
                                    problem,
                                    roles,
                                    other,
                                    node,
                                    pairs,
                                    index + 1,
                                    deps,
                                    skipped,
                                    depth,
                                ),
                                None => None,
                            }
                        } else {
                            Some(Outcome::Rejected(clash))
                        }
                    }
                    None => None,
                }
            } else {
                None
            }
        } else {
            match join(&deps, &skipped) {
                Some(last) => merge(problem, roles, graph, from, into, last, depth),
                None => None,
            }
        }
    } else {
        match join(&deps, &skipped) {
            Some(clash) => Some(Outcome::Rejected(clash)),
            None => None,
        }
    }
}
/// Apply the maximum restriction `restriction` of `node`, which has more
/// neighbours satisfying its filler than it allows: merge two of the first
/// `n + 1` of them, or report a clash when they all differ.
fn merge_rule(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    restriction: usize,
    depth: usize,
) -> Option<Outcome> {
    if restriction < problem.entries.len() {
        match &problem.entries[restriction] {
            Entry::AtMost(n, role, filler, _) => {
                if *n < usize::MAX {
                    let list = match neighbours(problem, roles, &graph, node, role) {
                        Some(list) => list,
                        None => return None,
                    };
                    let many =
                        match satisfying(&problem.entries, &graph, &list, *filler, 0, Vec::new()) {
                            Some(many) => many,
                            None => return None,
                        };
                    let chosen = first_nodes(&many, *n + 1, 0, Vec::new());
                    let deps = match rule_deps(problem, &graph, node) {
                        Some(deps) => deps,
                        None => return None,
                    };
                    let deps = match differences_deps(&graph, &chosen, 0, deps) {
                        Some(deps) => deps,
                        None => return None,
                    };
                    let pairs = match pairs_from(&graph, &chosen, 0, Vec::new()) {
                        Some(pairs) => pairs,
                        None => return None,
                    };
                    choices(
                        problem,
                        roles,
                        graph,
                        node,
                        &pairs,
                        0,
                        deps,
                        Vec::new(),
                        depth,
                    )
                } else {
                    None
                }
            }
            _ => None,
        }
    } else {
        None
    }
}
/// The rule for a maximum restriction of a named node, with a bound from new
/// named nodes, that counts a tree node along an added edge: in every model of
/// the bound, two of its first `bound` counted named neighbours and that tree
/// node coincide, so merge such a pair, or report a clash when they all differ.
fn capped_rule(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    restriction: usize,
    depth: usize,
) -> Option<Outcome> {
    if restriction < problem.entries.len() {
        match &problem.entries[restriction] {
            Entry::AtMost(_, role, filler, _) => {
                let cap = match cap_at(&graph.caps, node, restriction, 0) {
                    Some(cap) => cap,
                    None => return None,
                };
                let list = match neighbours(problem, roles, &graph, node, role) {
                    Some(list) => list,
                    None => return None,
                };
                let many = match satisfying(&problem.entries, &graph, &list, *filler, 0, Vec::new())
                {
                    Some(many) => many,
                    None => return None,
                };
                let named = match named_of(&graph, &many, 0, Vec::new()) {
                    Some(named) => named,
                    None => return None,
                };
                let mut chosen = first_nodes(&named, graph.caps[cap].bound, 0, Vec::new());
                if chosen.len() < graph.caps[cap].bound {
                    return None;
                }
                let other = match first_repeated(&graph, &many, node, 0) {
                    Some(other) => other,
                    None => return None,
                };
                if chosen.len() < usize::MAX {
                    chosen.push(other);
                } else {
                    return None;
                }
                let deps = match rule_deps(problem, &graph, node) {
                    Some(deps) => deps,
                    None => return None,
                };
                let deps = match join(&deps, &graph.caps[cap].deps) {
                    Some(deps) => deps,
                    None => return None,
                };
                let deps = match differences_deps(&graph, &chosen, 0, deps) {
                    Some(deps) => deps,
                    None => return None,
                };
                let pairs = match pairs_from(&graph, &chosen, 0, Vec::new()) {
                    Some(pairs) => pairs,
                    None => return None,
                };
                choices(
                    problem,
                    roles,
                    graph,
                    node,
                    &pairs,
                    0,
                    deps,
                    Vec::new(),
                    depth,
                )
            }
            _ => None,
        }
    } else {
        None
    }
}
/// The forest with `count` more named nodes, each with the seed `filler` and an
/// added edge from `node` along `role`, depending on `deps`.
fn fresh_named(
    mut graph: Forest,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
    deps: &Vec<usize>,
    count: usize,
) -> Option<Forest> {
    if count > 0 {
        if graph.nodes.len() < usize::MAX {
            if graph.edges.len() < usize::MAX {
                let index = graph.nodes.len();
                graph.nodes.push(Node {
                    label: Vec::new(),
                    parent: node,
                    roles: Vec::new(),
                    seed: filler,
                    tree: false,
                    active: true,
                    done: Vec::new(),
                    deps: copy_label(deps, 0, Vec::new()),
                });
                graph.edges.push(Edge {
                    role: copy_role(role),
                    from: node,
                    to: index,
                    deps: copy_label(deps, 0, Vec::new()),
                });
                fresh_named(graph, node, role, filler, deps, count - 1)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        Some(graph)
    }
}
/// The forest with `count` new named nodes for the restriction `restriction`
/// of `node`, along `role` with the seed `filler`, pairwise different, and the
/// bound `count` on the neighbours of `node` that the restriction counts, all
/// depending on `deps`.
fn named(
    graph: Forest,
    node: usize,
    restriction: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
    count: usize,
    deps: &Vec<usize>,
) -> Option<Forest> {
    let first = graph.nodes.len();
    let graph = match fresh_named(graph, node, role, filler, deps, count) {
        Some(graph) => graph,
        None => return None,
    };
    let mut graph = match pairwise(graph, first, deps) {
        Some(graph) => graph,
        None => return None,
    };
    if graph.caps.len() < usize::MAX {
        graph.caps.push(Cap {
            node,
            restriction,
            bound: count,
            deps: copy_label(deps, 0, Vec::new()),
        });
        Some(graph)
    } else {
        None
    }
}
/// Try the guesses `many..=n` for the number of neighbours of `node` that the
/// restriction `restriction` counts, each creating that many new named nodes:
/// all but the last under the branch point `depth`, skipping the rest when a
/// failure does not depend on it, and the last depending on the points the
/// earlier failures depended on (`skipped`). Without a guess left, it is a
/// clash.
fn guesses(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    restriction: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
    n: usize,
    many: usize,
    deps: Vec<usize>,
    skipped: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    if many <= n {
        if many < n {
            if depth < usize::MAX {
                let other = copy_forest(&graph);
                let mut point = Vec::new();
                point.push(depth);
                let here = match join(&deps, &point) {
                    Some(here) => here,
                    None => return None,
                };
                let made = match named(graph, node, restriction, role, filler, many, &here) {
                    Some(made) => made,
                    None => return None,
                };
                match run(problem, roles, made, depth + 1) {
                    Some(Outcome::Accepted) => Some(Outcome::Accepted),
                    Some(Outcome::Rejected(clash)) => {
                        if contains(&clash, depth, 0) {
                            let rest = without_from(&clash, depth, 0, Vec::new());
                            match join(&skipped, &rest) {
                                Some(skipped) => guesses(
                                    problem,
                                    roles,
                                    other,
                                    node,
                                    restriction,
                                    role,
                                    filler,
                                    n,
                                    many + 1,
                                    deps,
                                    skipped,
                                    depth,
                                ),
                                None => None,
                            }
                        } else {
                            Some(Outcome::Rejected(clash))
                        }
                    }
                    None => None,
                }
            } else {
                None
            }
        } else {
            let last = match join(&deps, &skipped) {
                Some(last) => last,
                None => return None,
            };
            match named(graph, node, restriction, role, filler, many, &last) {
                Some(made) => run(problem, roles, made, depth),
                None => None,
            }
        }
    } else {
        match join(&deps, &skipped) {
            Some(clash) => Some(Outcome::Rejected(clash)),
            None => None,
        }
    }
}
/// The rule for a maximum restriction `≤n r.C` of a named node that counts a
/// tree node along an added edge, which the model may repeat: every model of the
/// restriction has between 1 and `n` neighbours along `r` satisfying `C`, so
/// guess their number and create that many new named nodes for them.
fn name_rule(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    restriction: usize,
    depth: usize,
) -> Option<Outcome> {
    if restriction < problem.entries.len() {
        match &problem.entries[restriction] {
            Entry::AtMost(n, role, filler, _) => {
                let deps = match rule_deps(problem, &graph, node) {
                    Some(deps) => deps,
                    None => return None,
                };
                guesses(
                    problem,
                    roles,
                    graph,
                    node,
                    restriction,
                    role,
                    *filler,
                    *n,
                    1,
                    deps,
                    Vec::new(),
                    depth,
                )
            }
            _ => None,
        }
    } else {
        None
    }
}
/// Merge `node`, whose label has a nominal on the named node `root`, into
/// `root`; a difference between them is a clash.
fn nominal(
    problem: &Problem,
    roles: &RoleHierarchy,
    graph: Forest,
    node: usize,
    root: usize,
    depth: usize,
) -> Option<Outcome> {
    if node < graph.nodes.len() && root < graph.nodes.len() {
        let deps = match join(&graph.nodes[node].deps, &graph.nodes[root].deps) {
            Some(deps) => deps,
            None => return None,
        };
        if differ(&graph, node, root, 0) {
            let mut pair = Vec::new();
            pair.push(node);
            pair.push(root);
            return match differences_deps(&graph, &pair, 0, deps) {
                Some(clash) => Some(Outcome::Rejected(clash)),
                None => None,
            };
        }
        merge(problem, roles, graph, node, root, deps, depth)
    } else {
        None
    }
}
/// Apply rules until a clash, a complete forest, or no room; `depth` is the
/// next free branch point.
fn run(problem: &Problem, roles: &RoleHierarchy, graph: Forest, depth: usize) -> Option<Outcome> {
    match next_step(problem, roles, &graph) {
        Some(Step::Add { node, concept }) => match rule_deps(problem, &graph, node) {
            Some(deps) => add(
                problem,
                roles,
                graph,
                node,
                Pending::Item {
                    concept,
                    next: Box::new(Pending::Empty),
                },
                deps,
                depth,
            ),
            None => None,
        },
        Some(Step::Choose { node, left, right }) => match rule_deps(problem, &graph, node) {
            Some(deps) => branch(
                problem,
                roles,
                graph,
                node,
                left,
                right,
                Box::new(Pending::Empty),
                deps,
                depth,
            ),
            None => None,
        },
        Some(Step::Merge { node, restriction }) => {
            merge_rule(problem, roles, graph, node, restriction, depth)
        }
        Some(Step::Name { node, restriction }) => {
            name_rule(problem, roles, graph, node, restriction, depth)
        }
        Some(Step::Capped { node, restriction }) => {
            capped_rule(problem, roles, graph, node, restriction, depth)
        }
        Some(Step::Nominal { node, root }) => nominal(problem, roles, graph, node, root, depth),
        Some(Step::Loop { node }) => match rule_deps(problem, &graph, node) {
            Some(deps) => Some(Outcome::Rejected(deps)),
            None => None,
        },
        Some(Step::Create { node, generator }) => {
            create(problem, roles, graph, node, generator, depth)
        }
        Some(Step::Stuck) => None,
        Some(Step::Done) => Some(Outcome::Accepted),
        None => None,
    }
}
/// Whether no transitive role of `roles.transitive[index..]` is included in
/// `role`.
fn simple_from(roles: &RoleHierarchy, role: &ObjectPropertyExpression, index: usize) -> bool {
    if index < roles.transitive.len() {
        if below(roles, &roles.transitive[index], role) {
            false
        } else {
            simple_from(roles, role, index + 1)
        }
    } else {
        true
    }
}
/// Whether every number restriction and every complement of a self restriction
/// of `entries[index..]` is on a simple role.
fn counting_simple(entries: &Vec<Entry>, roles: &RoleHierarchy, index: usize) -> bool {
    if index < entries.len() {
        let simple = match &entries[index] {
            Entry::AtLeast(_, role, _) => simple_from(roles, role, 0),
            Entry::AtMost(_, role, _, _) => simple_from(roles, role, 0),
            Entry::NotSelf(role) => simple_from(roles, role, 0),
            _ => true,
        };
        if simple {
            counting_simple(entries, roles, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// The roots for `count` named individuals, each merged only into itself.
fn roots(count: usize, mut graph: Forest) -> Option<Forest> {
    if graph.nodes.len() < count {
        if graph.nodes.len() < usize::MAX {
            let index = graph.nodes.len();
            graph.nodes.push(Node {
                label: Vec::new(),
                parent: 0,
                roles: Vec::new(),
                seed: 0,
                tree: false,
                active: true,
                done: Vec::new(),
                deps: Vec::new(),
            });
            graph.same.push(index);
            roots(count, graph)
        } else {
            None
        }
    } else {
        Some(graph)
    }
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// and every definition, and the object properties satisfy `roles`, has an
/// element for each of the `count` named nodes such that every fact of `query`
/// and of `facts` holds at its node and every link relates its nodes along its
/// role. `roles` must be closed: its inclusions include their compositions and
/// inverses, and its transitive roles their inverses. `None` means that a
/// structure would exceed the `usize` range, that a number restriction or the
/// complement of a self restriction is on a role that is not simple, or that
/// the rules cannot go on (see above).
pub fn satisfiable(
    count: usize,
    query: &Vec<Fact>,
    facts: &Vec<Fact>,
    links: &Vec<Link>,
    axioms: &Concept,
    definitions: &Vec<Definition>,
    roles: &RoleHierarchy,
) -> Option<bool> {
    let (entries, axioms) = match intern(Vec::new(), axioms) {
        Some(pair) => pair,
        None => return None,
    };
    let (entries, requirements) = match intern_facts(entries, query, 0, Vec::new()) {
        Some(pair) => pair,
        None => return None,
    };
    let (entries, requirements) = match intern_facts(entries, facts, 0, requirements) {
        Some(pair) => pair,
        None => return None,
    };
    let (entries, unfoldings) = match intern_definitions(entries, definitions, 0, Vec::new()) {
        Some(pair) => pair,
        None => return None,
    };
    let entries = match close(entries, roles) {
        Some(entries) => entries,
        None => return None,
    };
    if !counting_simple(&entries, roles, 0) {
        return None;
    }
    let graph = match roots(
        count,
        Forest {
            nodes: Vec::new(),
            edges: Vec::new(),
            distinct: Vec::new(),
            same: Vec::new(),
            caps: Vec::new(),
        },
    ) {
        Some(graph) => graph,
        None => return None,
    };
    let problem = Problem {
        entries,
        links: copy_links(links, 0, Vec::new()),
        requirements,
        unfoldings,
        axioms,
    };
    match run(&problem, roles, graph, 0) {
        Some(Outcome::Accepted) => Some(true),
        Some(Outcome::Rejected(_)) => Some(false),
        None => None,
    }
}
