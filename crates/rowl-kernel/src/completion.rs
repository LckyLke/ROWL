//! A completion graph tableau for SHI with named individuals.
//!
//! The graph has one node per named individual and trees of anonymous nodes
//! below them. A label is a list of indices of literal entries of the concept
//! table (named classes, their complements, and existential and universal
//! restrictions); conjunctions are split, disjunctions branch on a copy of the
//! graph, and a literal whose complement is already there is a clash the moment
//! it is inserted. Rules are searched in a fixed order, deterministic ones first:
//!
//! 1. every node satisfies its requirements (the facts at named nodes), the TBox
//!    concept, and every unfolding `A ⊑ C` whose class `A` it has (lazy
//!    unfolding, instead of `¬A ⊔ C` everywhere);
//! 2. along every edge, in both directions, every universal restriction `∀q.d`
//!    with the edge's role included in `q` requires `d`, and `∀t.d` for every
//!    transitive role `t` in between;
//! 3. every existential restriction of an unblocked node needs a neighbour along
//!    an included role that satisfies its filler; otherwise a new tree node is
//!    created.
//!
//! A tree node is blocked when two tree nodes on its path to its named root have
//! the same label (equality blocking, which inverse roles need), so unblocked
//! paths are bounded by the number of label sets.
//!
//! Backjumping: every node records the branch points its label depends on, the
//! points of the disjunctions chosen on the way to it. A rule adds to a node with
//! the points of the node and its neighbours, and a clash reports the points of
//! its node. When the left disjunct of a branch fails without depending on the
//! branch point, the right disjunct would fail the same way and is skipped;
//! otherwise it is tried with the points the failure depended on. `None` means
//! that a structure would exceed the `usize` range, or that a cardinality
//! restriction would be added to a label: this tableau does not count.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::collapsible_match,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::needless_return,
    clippy::single_match,
    clippy::boxed_local,
    clippy::manual_map,
    clippy::manual_filter,
    clippy::if_same_then_else,
    clippy::too_many_arguments,
    clippy::vec_init_then_push
)] // Indexed operations, explicit branches and pushes without macros for the pinned extraction subset.
use crate::concept_table::{close, intern, universal_from, universal_is, Entry};
use crate::concepts::{copy_role, inverse, Concept};
use crate::hierarchy::{below, RoleHierarchy};
use crate::model::{Class, ObjectPropertyExpression};
use crate::nnf::copy_iri;
use crate::symbols::same_spelling;

/// A node: the indices of the literal entries in its label and, for a tree
/// node, its parent and the existential entry that created it.
pub struct Node {
    pub label: Vec<usize>,
    pub parent: usize,
    pub via: usize,
    pub tree: bool,
    /// The branch points the label depends on.
    pub deps: Vec<usize>,
}
/// An edge between named nodes along a role.
pub struct Link {
    pub role: ObjectPropertyExpression,
    pub from: usize,
    pub to: usize,
}
/// A concept that must hold at a named node.
pub struct Fact {
    pub node: usize,
    pub concept: Concept,
}
/// Every element of the named class satisfies the concept.
pub struct Definition {
    pub class: Class,
    pub concept: Concept,
}
/// A table entry that must hold at a named node.
pub struct Requirement {
    pub node: usize,
    pub concept: usize,
}
/// A table entry that must hold wherever the named class holds.
pub struct Unfolding {
    pub class: Class,
    pub concept: usize,
}
/// The fixed part of a run: the concept table, the edges between named nodes,
/// the requirements, the unfoldings and the TBox concept.
pub struct Problem {
    pub entries: Vec<Entry>,
    pub links: Vec<Link>,
    pub requirements: Vec<Requirement>,
    pub unfoldings: Vec<Unfolding>,
    pub axioms: usize,
}
/// Table entries still to be added to one label.
pub enum Pending {
    Empty,
    Item { concept: usize, next: Box<Pending> },
}
/// The next rule to apply.
pub enum Step {
    Add { node: usize, concept: usize },
    Create { node: usize, existential: usize },
    Done,
}
/// The outcome of a search: a complete graph without clashes, or a clash that
/// depends only on the listed branch points.
pub enum Outcome {
    Accepted,
    Rejected(Vec<usize>),
}

/// Whether `label[index..]` has the item.
pub(crate) fn contains(label: &Vec<usize>, item: usize, index: usize) -> bool {
    if index < label.len() {
        if label[index] == item {
            true
        } else {
            contains(label, item, index + 1)
        }
    } else {
        false
    }
}
/// Whether the label satisfies the entry: conjunctions and disjunctions are read
/// propositionally, and every other entry must be listed.
pub(crate) fn holds(entries: &Vec<Entry>, label: &Vec<usize>, concept: usize) -> bool {
    if concept < entries.len() {
        match &entries[concept] {
            Entry::Top => true,
            Entry::Bottom => false,
            Entry::And(left, right) => {
                if *left < concept && *right < concept {
                    if holds(entries, label, *left) {
                        holds(entries, label, *right)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            Entry::Or(left, right) => {
                if *left < concept && *right < concept {
                    if holds(entries, label, *left) {
                        true
                    } else {
                        holds(entries, label, *right)
                    }
                } else {
                    false
                }
            }
            _ => contains(label, concept, 0),
        }
    } else {
        false
    }
}
/// Whether the entries are a named class and its complement.
fn complementary(left: &Entry, right: &Entry) -> bool {
    match (left, right) {
        (Entry::Atom(a), Entry::NotAtom(b)) => same_spelling(&a.iri.spelling, &b.iri.spelling),
        (Entry::NotAtom(a), Entry::Atom(b)) => same_spelling(&a.iri.spelling, &b.iri.spelling),
        _ => false,
    }
}
/// Whether some item of `label[index..]` is complementary to `item`.
pub(crate) fn clashes(entries: &Vec<Entry>, label: &Vec<usize>, item: usize, index: usize) -> bool {
    if index < label.len() {
        let other = label[index];
        let here = if item < entries.len() && other < entries.len() {
            complementary(&entries[item], &entries[other])
        } else {
            false
        };
        if here {
            true
        } else {
            clashes(entries, label, item, index + 1)
        }
    } else {
        false
    }
}
/// Whether the entry is the named class.
fn is_atom(entry: &Entry, class: &Class) -> bool {
    match entry {
        Entry::Atom(other) => same_spelling(&other.iri.spelling, &class.iri.spelling),
        _ => false,
    }
}
/// Whether `label[index..]` has the named class.
fn has_atom(entries: &Vec<Entry>, label: &Vec<usize>, class: &Class, index: usize) -> bool {
    if index < label.len() {
        let item = label[index];
        let here = if item < entries.len() {
            is_atom(&entries[item], class)
        } else {
            false
        };
        if here {
            true
        } else {
            has_atom(entries, label, class, index + 1)
        }
    } else {
        false
    }
}
/// The first requirement of `requirements[index..]` at `node` that the label
/// does not satisfy.
fn missing_requirement(
    problem: &Problem,
    label: &Vec<usize>,
    node: usize,
    index: usize,
) -> Option<usize> {
    if index < problem.requirements.len() {
        let requirement = &problem.requirements[index];
        let missing = if requirement.node == node {
            !holds(&problem.entries, label, requirement.concept)
        } else {
            false
        };
        if missing {
            Some(requirement.concept)
        } else {
            missing_requirement(problem, label, node, index + 1)
        }
    } else {
        None
    }
}
/// Whether the label has the unfolding's class but does not satisfy its concept.
pub(crate) fn unfolding_missing(
    problem: &Problem,
    label: &Vec<usize>,
    unfolding: &Unfolding,
) -> bool {
    if has_atom(&problem.entries, label, &unfolding.class, 0) {
        !holds(&problem.entries, label, unfolding.concept)
    } else {
        false
    }
}
/// The first unfolding of `unfoldings[index..]` whose class the label has but
/// whose concept it does not satisfy.
pub(crate) fn missing_unfolding(
    problem: &Problem,
    label: &Vec<usize>,
    index: usize,
) -> Option<usize> {
    if index < problem.unfoldings.len() {
        if unfolding_missing(problem, label, &problem.unfoldings[index]) {
            Some(problem.unfoldings[index].concept)
        } else {
            missing_unfolding(problem, label, index + 1)
        }
    } else {
        None
    }
}
/// What the label of `node` misses: a requirement, the TBox concept, or an
/// unfolding.
fn missing_at(problem: &Problem, label: &Vec<usize>, node: usize) -> Option<usize> {
    match missing_requirement(problem, label, node, 0) {
        Some(concept) => Some(concept),
        None => {
            if holds(&problem.entries, label, problem.axioms) {
                missing_unfolding(problem, label, 0)
            } else {
                Some(problem.axioms)
            }
        }
    }
}
/// The first node of `nodes[index..]` that misses something, and what.
fn missing_node(problem: &Problem, nodes: &Vec<Node>, index: usize) -> Option<(usize, usize)> {
    if index < nodes.len() {
        match missing_at(problem, &nodes[index].label, index) {
            Some(concept) => Some((index, concept)),
            None => missing_node(problem, nodes, index + 1),
        }
    } else {
        None
    }
}
/// Whether `label[index..]` has an entry `∀role.filler`.
pub(crate) fn has_universal(
    entries: &Vec<Entry>,
    label: &Vec<usize>,
    role: &ObjectPropertyExpression,
    filler: usize,
    index: usize,
) -> bool {
    if index < label.len() {
        let item = label[index];
        let here = if item < entries.len() {
            universal_is(&entries[item], role, filler)
        } else {
            false
        };
        if here {
            true
        } else {
            has_universal(entries, label, role, filler, index + 1)
        }
    } else {
        false
    }
}
/// The first restriction `∀t.filler`, for a transitive role `t` of
/// `roles.transitive[index..]` between `role` and `sup`, that `target` lacks.
pub(crate) fn missing_transitive(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    role: &ObjectPropertyExpression,
    sup: &ObjectPropertyExpression,
    filler: usize,
    target: &Vec<usize>,
    index: usize,
) -> Option<usize> {
    if index < roles.transitive.len() {
        let transitive = &roles.transitive[index];
        if below(roles, role, transitive) {
            if below(roles, transitive, sup) {
                if !has_universal(entries, target, transitive, filler, 0) {
                    let restriction = universal_from(entries, transitive, filler, 0);
                    if restriction < entries.len() {
                        return Some(restriction);
                    }
                }
            }
        }
        missing_transitive(entries, roles, role, sup, filler, target, index + 1)
    } else {
        None
    }
}
/// What the universal restriction `item` requires along `role` that `target`
/// does not satisfy.
pub(crate) fn missing_for(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    item: usize,
    role: &ObjectPropertyExpression,
    target: &Vec<usize>,
) -> Option<usize> {
    if item < entries.len() {
        match &entries[item] {
            Entry::Forall(sup, filler) => {
                if below(roles, role, sup) {
                    if holds(entries, target, *filler) {
                        missing_transitive(entries, roles, role, sup, *filler, target, 0)
                    } else {
                        Some(*filler)
                    }
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
/// What the items of `label[index..]` require along `role` that `target` does
/// not satisfy.
pub(crate) fn missing_along(
    entries: &Vec<Entry>,
    roles: &RoleHierarchy,
    label: &Vec<usize>,
    role: &ObjectPropertyExpression,
    target: &Vec<usize>,
    index: usize,
) -> Option<usize> {
    if index < label.len() {
        match missing_for(entries, roles, label[index], role, target) {
            Some(concept) => Some(concept),
            None => missing_along(entries, roles, label, role, target, index + 1),
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
    nodes: &Vec<Node>,
    from: usize,
    to: usize,
    role: &ObjectPropertyExpression,
) -> Option<(usize, usize)> {
    if from < nodes.len() && to < nodes.len() {
        match missing_along(
            entries,
            roles,
            &nodes[from].label,
            role,
            &nodes[to].label,
            0,
        ) {
            Some(concept) => Some((to, concept)),
            None => {
                let back = inverse(role);
                match missing_along(
                    entries,
                    roles,
                    &nodes[to].label,
                    &back,
                    &nodes[from].label,
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
/// The first edge between named nodes of `links[index..]` that misses something.
fn missing_link(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    index: usize,
) -> Option<(usize, usize)> {
    if index < problem.links.len() {
        let link = &problem.links[index];
        match missing_edge(
            &problem.entries,
            roles,
            nodes,
            link.from,
            link.to,
            &link.role,
        ) {
            Some(found) => Some(found),
            None => missing_link(problem, roles, nodes, index + 1),
        }
    } else {
        None
    }
}
/// The role of the existential entry that created a tree node.
fn created_role(entries: &Vec<Entry>, via: usize) -> Option<ObjectPropertyExpression> {
    if via < entries.len() {
        match &entries[via] {
            Entry::Exists(role, _) => Some(copy_role(role)),
            _ => None,
        }
    } else {
        None
    }
}
/// The first tree edge, to a node of `nodes[index..]`, that misses something.
fn missing_tree(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    index: usize,
) -> Option<(usize, usize)> {
    if index < nodes.len() {
        let found = if nodes[index].tree {
            match created_role(&problem.entries, nodes[index].via) {
                Some(role) => missing_edge(
                    &problem.entries,
                    roles,
                    nodes,
                    nodes[index].parent,
                    index,
                    &role,
                ),
                None => None,
            }
        } else {
            None
        };
        match found {
            Some(found) => Some(found),
            None => missing_tree(problem, roles, nodes, index + 1),
        }
    } else {
        None
    }
}
/// Whether a child of `node` among `nodes[index..]`, created along a role
/// included in `role`, satisfies the filler.
fn child_witness(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
    index: usize,
) -> bool {
    if index < nodes.len() {
        let mut here = false;
        if nodes[index].tree {
            if nodes[index].parent == node {
                match created_role(&problem.entries, nodes[index].via) {
                    Some(created) => {
                        if below(roles, &created, role) {
                            here = holds(&problem.entries, &nodes[index].label, filler);
                        }
                    }
                    None => {}
                }
            }
        }
        if here {
            true
        } else {
            child_witness(problem, roles, nodes, node, role, filler, index + 1)
        }
    } else {
        false
    }
}
/// Whether the parent of the tree node `node`, reached along the inverse of the
/// role that created it, is reached along a role included in `role` and
/// satisfies the filler.
fn parent_witness(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
) -> bool {
    if node < nodes.len() {
        if nodes[node].tree {
            let parent = nodes[node].parent;
            if parent < nodes.len() {
                match created_role(&problem.entries, nodes[node].via) {
                    Some(created) => {
                        let back = inverse(&created);
                        if below(roles, &back, role) {
                            return holds(&problem.entries, &nodes[parent].label, filler);
                        }
                    }
                    None => {}
                }
            }
        }
    }
    false
}
/// Whether the link leads from `node` along a role included in `role` to a
/// node that satisfies the filler.
fn forward_witness(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    link: &Link,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
) -> bool {
    if link.from == node {
        if link.to < nodes.len() {
            if below(roles, &link.role, role) {
                return holds(&problem.entries, &nodes[link.to].label, filler);
            }
        }
    }
    false
}
/// Whether the link leads to `node`, so that its source is reached along the
/// inverse role, which is included in `role`, and satisfies the filler.
fn backward_witness(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    link: &Link,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
) -> bool {
    if link.to == node {
        if link.from < nodes.len() {
            let back = inverse(&link.role);
            if below(roles, &back, role) {
                return holds(&problem.entries, &nodes[link.from].label, filler);
            }
        }
    }
    false
}
/// Whether a named node linked to `node` by an edge of `links[index..]` along a
/// role included in `role` satisfies the filler.
fn link_witness(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
    index: usize,
) -> bool {
    if index < problem.links.len() {
        if forward_witness(
            problem,
            roles,
            nodes,
            &problem.links[index],
            node,
            role,
            filler,
        ) {
            true
        } else if backward_witness(
            problem,
            roles,
            nodes,
            &problem.links[index],
            node,
            role,
            filler,
        ) {
            true
        } else {
            link_witness(problem, roles, nodes, node, role, filler, index + 1)
        }
    } else {
        false
    }
}
/// Whether some neighbour of `node` along a role included in `role` satisfies
/// the filler.
fn has_witness(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    node: usize,
    role: &ObjectPropertyExpression,
    filler: usize,
) -> bool {
    if child_witness(problem, roles, nodes, node, role, filler, 0) {
        true
    } else if parent_witness(problem, roles, nodes, node, role, filler) {
        true
    } else {
        link_witness(problem, roles, nodes, node, role, filler, 0)
    }
}
/// The first existential restriction of `label[index..]` of `node` without a
/// witness.
fn missing_witness(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    node: usize,
    index: usize,
) -> Option<usize> {
    if node < nodes.len() {
        if index < nodes[node].label.len() {
            let item = nodes[node].label[index];
            let mut missing = false;
            if item < problem.entries.len() {
                match &problem.entries[item] {
                    Entry::Exists(role, filler) => {
                        missing = !has_witness(problem, roles, nodes, node, role, *filler);
                    }
                    _ => {}
                }
            }
            if missing {
                Some(item)
            } else {
                missing_witness(problem, roles, nodes, node, index + 1)
            }
        } else {
            None
        }
    } else {
        None
    }
}
/// Whether every item of `small[index..]` is in `large`.
pub(crate) fn subset(small: &Vec<usize>, large: &Vec<usize>, index: usize) -> bool {
    if index < small.len() {
        if contains(large, small[index], 0) {
            subset(small, large, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the two labels have the same items.
pub(crate) fn same_label(left: &Vec<usize>, right: &Vec<usize>) -> bool {
    if subset(left, right, 0) {
        subset(right, left, 0)
    } else {
        false
    }
}
/// Whether the label of `node` is the label of `ancestor` or of a tree node
/// above it.
fn repeats_above(nodes: &Vec<Node>, node: usize, ancestor: usize) -> bool {
    if ancestor < nodes.len() && node < nodes.len() {
        if nodes[ancestor].tree {
            if same_label(&nodes[node].label, &nodes[ancestor].label) {
                true
            } else if nodes[ancestor].parent < ancestor {
                repeats_above(nodes, node, nodes[ancestor].parent)
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
/// Whether a tree node on the path from `node` up to its named root has the
/// label of a tree node above it.
fn blocked(nodes: &Vec<Node>, node: usize) -> bool {
    if node < nodes.len() {
        if nodes[node].tree {
            let parent = nodes[node].parent;
            if parent < node {
                if repeats_above(nodes, node, parent) {
                    true
                } else {
                    blocked(nodes, parent)
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
/// The first unblocked node of `nodes[index..]` with an existential restriction
/// without a witness, and that restriction.
fn missing_successor(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: &Vec<Node>,
    index: usize,
) -> Option<(usize, usize)> {
    if index < nodes.len() {
        let found = match missing_witness(problem, roles, nodes, index, 0) {
            Some(item) => {
                if blocked(nodes, index) {
                    None
                } else {
                    Some(item)
                }
            }
            None => None,
        };
        match found {
            Some(item) => Some((index, item)),
            None => missing_successor(problem, roles, nodes, index + 1),
        }
    } else {
        None
    }
}
/// The next rule: a missing concept of a node or an edge, else a missing
/// successor, else none.
fn next_step(problem: &Problem, roles: &RoleHierarchy, nodes: &Vec<Node>) -> Step {
    match missing_node(problem, nodes, 0) {
        Some((node, concept)) => return Step::Add { node, concept },
        None => {}
    }
    match missing_link(problem, roles, nodes, 0) {
        Some((node, concept)) => return Step::Add { node, concept },
        None => {}
    }
    match missing_tree(problem, roles, nodes, 0) {
        Some((node, concept)) => return Step::Add { node, concept },
        None => {}
    }
    match missing_successor(problem, roles, nodes, 0) {
        Some((node, existential)) => Step::Create { node, existential },
        None => Step::Done,
    }
}
/// The nodes with `item` added to the label of `node`, which then also depends
/// on `deps`; `None` when there is no room.
fn insert(mut nodes: Vec<Node>, node: usize, item: usize, deps: &Vec<usize>) -> Option<Vec<Node>> {
    if node < nodes.len() {
        if nodes[node].label.len() < usize::MAX {
            match join(&nodes[node].deps, deps) {
                Some(joined) => {
                    nodes[node].label.push(item);
                    nodes[node].deps = joined;
                    Some(nodes)
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
pub(crate) fn copy_label(label: &Vec<usize>, index: usize, mut out: Vec<usize>) -> Vec<usize> {
    if index < label.len() {
        if out.len() < usize::MAX {
            out.push(label[index]);
        }
        copy_label(label, index + 1, out)
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
                via: nodes[index].via,
                tree: nodes[index].tree,
                deps: copy_label(&nodes[index].deps, 0, Vec::new()),
            });
        }
        copy_nodes(nodes, index + 1, out)
    } else {
        out
    }
}
pub(crate) fn copy_pending(pending: &Pending) -> Pending {
    match pending {
        Pending::Empty => Pending::Empty,
        Pending::Item { concept, next } => Pending::Item {
            concept: *concept,
            next: Box::new(copy_pending(next)),
        },
    }
}
/// `out` with every point of `set[index..]` it does not list; `None` when there
/// is no room.
pub(crate) fn join_from(set: &Vec<usize>, index: usize, mut out: Vec<usize>) -> Option<Vec<usize>> {
    if index < set.len() {
        if contains(&out, set[index], 0) {
            join_from(set, index + 1, out)
        } else if out.len() < usize::MAX {
            out.push(set[index]);
            join_from(set, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The points of both sets.
pub(crate) fn join(left: &Vec<usize>, right: &Vec<usize>) -> Option<Vec<usize>> {
    join_from(right, 0, copy_label(left, 0, Vec::new()))
}
/// `out` with every point of `set[index..]` other than `point`.
pub(crate) fn without_from(
    set: &Vec<usize>,
    point: usize,
    index: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if index < set.len() {
        if set[index] != point {
            if out.len() < usize::MAX {
                out.push(set[index]);
            }
        }
        without_from(set, point, index + 1, out)
    } else {
        out
    }
}
/// Try the left disjunct on the graph, under the new branch point `depth`. If it
/// fails with a clash that does not depend on that point, the right disjunct
/// fails the same way and the clash is reported; otherwise the right disjunct is
/// tried on a copy, depending on the points the left failure depended on.
fn branch(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: Vec<Node>,
    node: usize,
    left: usize,
    right: usize,
    next: Box<Pending>,
    deps: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    if depth < usize::MAX {
        let other_nodes = copy_nodes(&nodes, 0, Vec::new());
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
            nodes,
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
                            other_nodes,
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
    nodes: Vec<Node>,
    node: usize,
    concept: usize,
    next: Box<Pending>,
    deps: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    if node < nodes.len() {
        if contains(&nodes[node].label, concept, 0) {
            add(problem, roles, nodes, node, *next, deps, depth)
        } else if clashes(&problem.entries, &nodes[node].label, concept, 0) {
            match join(&nodes[node].deps, &deps) {
                Some(clash) => Some(Outcome::Rejected(clash)),
                None => None,
            }
        } else {
            match insert(nodes, node, concept, &deps) {
                Some(nodes) => add(problem, roles, nodes, node, *next, deps, depth),
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
    nodes: Vec<Node>,
    node: usize,
    pending: Pending,
    deps: Vec<usize>,
    depth: usize,
) -> Option<Outcome> {
    match pending {
        Pending::Empty => run(problem, roles, nodes, depth),
        Pending::Item { concept, next } => {
            if concept < problem.entries.len() {
                match &problem.entries[concept] {
                    Entry::Top => add(problem, roles, nodes, node, *next, deps, depth),
                    Entry::Bottom => Some(Outcome::Rejected(deps)),
                    Entry::And(left, right) => add(
                        problem,
                        roles,
                        nodes,
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
                        problem, roles, nodes, node, *left, *right, next, deps, depth,
                    ),
                    Entry::AtLeast(_, _, _) => None,
                    Entry::AtMost(_, _, _, _) => None,
                    Entry::One(_) => None,
                    Entry::NotOne(_) => None,
                    _ => add_literal(problem, roles, nodes, node, concept, next, deps, depth),
                }
            } else {
                None
            }
        }
    }
}
/// The filler of an existential entry.
fn filler_of(entries: &Vec<Entry>, existential: usize) -> Option<usize> {
    if existential < entries.len() {
        match &entries[existential] {
            Entry::Exists(_, filler) => Some(*filler),
            _ => None,
        }
    } else {
        None
    }
}
/// Create a tree node below `node` for the existential entry, with its filler
/// and the TBox concept; the new node depends on the points of `node`.
fn create(
    problem: &Problem,
    roles: &RoleHierarchy,
    mut nodes: Vec<Node>,
    node: usize,
    existential: usize,
    depth: usize,
) -> Option<Outcome> {
    let filler = match filler_of(&problem.entries, existential) {
        Some(filler) => filler,
        None => return None,
    };
    if node < nodes.len() {
        if nodes.len() < usize::MAX {
            let child = nodes.len();
            let deps = copy_label(&nodes[node].deps, 0, Vec::new());
            nodes.push(Node {
                label: Vec::new(),
                parent: node,
                via: existential,
                tree: true,
                deps: copy_label(&deps, 0, Vec::new()),
            });
            add(
                problem,
                roles,
                nodes,
                child,
                Pending::Item {
                    concept: filler,
                    next: Box::new(Pending::Item {
                        concept: problem.axioms,
                        next: Box::new(Pending::Empty),
                    }),
                },
                deps,
                depth,
            )
        } else {
            None
        }
    } else {
        None
    }
}
/// `out` with the points of every tree node of `nodes[index..]` below `node`.
fn children_deps(
    nodes: &Vec<Node>,
    node: usize,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < nodes.len() {
        let child = if nodes[index].tree {
            nodes[index].parent == node
        } else {
            false
        };
        if child {
            match join_from(&nodes[index].deps, 0, out) {
                Some(out) => children_deps(nodes, node, index + 1, out),
                None => None,
            }
        } else {
            children_deps(nodes, node, index + 1, out)
        }
    } else {
        Some(out)
    }
}
/// `out` with the points of node `end`, if there is such a node.
fn end_deps(nodes: &Vec<Node>, end: usize, out: Vec<usize>) -> Option<Vec<usize>> {
    if end < nodes.len() {
        join_from(&nodes[end].deps, 0, out)
    } else {
        Some(out)
    }
}
/// `out` with the points of the other end of every link of `links[index..]`
/// at `node`.
fn linked_deps(
    links: &Vec<Link>,
    nodes: &Vec<Node>,
    node: usize,
    index: usize,
    out: Vec<usize>,
) -> Option<Vec<usize>> {
    if index < links.len() {
        let to = links[index].to;
        let from = links[index].from;
        let forward = if from == node {
            end_deps(nodes, to, out)
        } else {
            Some(out)
        };
        match forward {
            Some(out) => {
                let backward = if to == node {
                    end_deps(nodes, from, out)
                } else {
                    Some(out)
                };
                match backward {
                    Some(out) => linked_deps(links, nodes, node, index + 1, out),
                    None => None,
                }
            }
            None => None,
        }
    } else {
        Some(out)
    }
}
/// The points the labels of `node` and of its neighbours depend on: everything a
/// rule adding to `node` can rest on.
fn rule_deps(problem: &Problem, nodes: &Vec<Node>, node: usize) -> Option<Vec<usize>> {
    if node < nodes.len() {
        let own = copy_label(&nodes[node].deps, 0, Vec::new());
        let with_parent = if nodes[node].tree {
            end_deps(nodes, nodes[node].parent, own)
        } else {
            Some(own)
        };
        match with_parent {
            Some(out) => match children_deps(nodes, node, 0, out) {
                Some(out) => linked_deps(&problem.links, nodes, node, 0, out),
                None => None,
            },
            None => None,
        }
    } else {
        None
    }
}
/// Apply rules until a clash, a complete graph, or no room; `depth` is the next
/// free branch point.
fn run(
    problem: &Problem,
    roles: &RoleHierarchy,
    nodes: Vec<Node>,
    depth: usize,
) -> Option<Outcome> {
    match next_step(problem, roles, &nodes) {
        Step::Add { node, concept } => match rule_deps(problem, &nodes, node) {
            Some(deps) => add(
                problem,
                roles,
                nodes,
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
        Step::Create { node, existential } => {
            create(problem, roles, nodes, node, existential, depth)
        }
        Step::Done => Some(Outcome::Accepted),
    }
}
pub(crate) fn intern_facts(
    entries: Vec<Entry>,
    facts: &Vec<Fact>,
    index: usize,
    mut out: Vec<Requirement>,
) -> Option<(Vec<Entry>, Vec<Requirement>)> {
    if index < facts.len() {
        let (entries, concept) = match intern(entries, &facts[index].concept) {
            Some(pair) => pair,
            None => return None,
        };
        if out.len() < usize::MAX {
            out.push(Requirement {
                node: facts[index].node,
                concept,
            });
            intern_facts(entries, facts, index + 1, out)
        } else {
            None
        }
    } else {
        Some((entries, out))
    }
}
pub(crate) fn intern_definitions(
    entries: Vec<Entry>,
    definitions: &Vec<Definition>,
    index: usize,
    mut out: Vec<Unfolding>,
) -> Option<(Vec<Entry>, Vec<Unfolding>)> {
    if index < definitions.len() {
        let (entries, concept) = match intern(entries, &definitions[index].concept) {
            Some(pair) => pair,
            None => return None,
        };
        if out.len() < usize::MAX {
            out.push(Unfolding {
                class: Class {
                    iri: copy_iri(&definitions[index].class.iri),
                },
                concept,
            });
            intern_definitions(entries, definitions, index + 1, out)
        } else {
            None
        }
    } else {
        Some((entries, out))
    }
}
fn named_nodes(count: usize, mut nodes: Vec<Node>) -> Option<Vec<Node>> {
    if nodes.len() < count {
        if nodes.len() < usize::MAX {
            nodes.push(Node {
                label: Vec::new(),
                parent: 0,
                via: 0,
                tree: false,
                deps: Vec::new(),
            });
            named_nodes(count, nodes)
        } else {
            None
        }
    } else {
        Some(nodes)
    }
}
/// A copy of `links[index..]` after `out`.
pub(crate) fn copy_links(links: &Vec<Link>, index: usize, mut out: Vec<Link>) -> Vec<Link> {
    if index < links.len() {
        if out.len() < usize::MAX {
            out.push(Link {
                role: copy_role(&links[index].role),
                from: links[index].from,
                to: links[index].to,
            });
        }
        copy_links(links, index + 1, out)
    } else {
        out
    }
}
/// Decide whether some interpretation in which every element satisfies `axioms`
/// and every definition, and the object properties satisfy `roles`, has an
/// element for each of the `count` named nodes such that every fact of `query`
/// and of `facts` holds at its node and every link relates its nodes along its
/// role. `roles` must be closed: its inclusions include their compositions and
/// inverses, and its transitive roles their inverses. `None` means that a
/// structure would exceed the `usize` range.
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
    let nodes = match named_nodes(count, Vec::new()) {
        Some(nodes) => nodes,
        None => return None,
    };
    let problem = Problem {
        entries,
        links: copy_links(links, 0, Vec::new()),
        requirements,
        unfoldings,
        axioms,
    };
    match run(&problem, roles, nodes, 0) {
        Some(Outcome::Accepted) => Some(true),
        Some(Outcome::Rejected(_)) => Some(false),
        None => None,
    }
}
