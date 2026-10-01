//! Exact OWL 2 §11 role-preprocessing facts from a supplied full axiom closure.
//!
//! Oriented roles preserve original byte IRIs; chains retain their original
//! ordered syntax. These facts feed the global simplicity/regularity checks.
//! Collecting them alone does not establish DL validity.
#![allow(clippy::ptr_arg)] // Checked Vec/index subset, with owned linked outputs.

use crate::collection::{axiom_entities, EntityUses};
use crate::model::{
    AnnotatedAxiom, AtLeastTwo, Axiom, ClassExpression, Iri, ObjectPropertyExpression,
    SubObjectPropertyExpression,
};
use crate::typing::EntityKind;

pub struct Role<'a> {
    pub iri: &'a Iri,
    pub inverse: bool,
}
pub enum Roles<'a> {
    Empty,
    Entry {
        role: Role<'a>,
        next: Box<Roles<'a>>,
    },
}
pub enum Edges<'a> {
    Empty,
    Entry {
        sub: Role<'a>,
        sup: Role<'a>,
        next: Box<Edges<'a>>,
    },
}
pub enum Chains<'a> {
    Empty,
    Entry {
        chain: &'a AtLeastTwo<ObjectPropertyExpression>,
        sup: &'a ObjectPropertyExpression,
        next: Box<Chains<'a>>,
    },
}
pub struct RoleFacts<'a> {
    pub nodes: Roles<'a>,
    pub edges: Edges<'a>,
    pub composite: Roles<'a>,
    pub simple_required: Roles<'a>,
    pub chains: Chains<'a>,
}

/// Both orientations share the exact original IRI object.
pub fn expression_role(expression: &ObjectPropertyExpression) -> Role<'_> {
    match expression {
        ObjectPropertyExpression::Property(p) => Role {
            iri: &p.iri,
            inverse: false,
        },
        ObjectPropertyExpression::Inverse(p) => Role {
            iri: &p.iri,
            inverse: true,
        },
    }
}
fn copy_role<'a>(role: &Role<'a>) -> Role<'a> {
    Role {
        iri: role.iri,
        inverse: role.inverse,
    }
}
pub fn inverse_role(role: Role<'_>) -> Role<'_> {
    Role {
        iri: role.iri,
        inverse: !role.inverse,
    }
}
fn roles_append<'a>(left: Roles<'a>, right: Roles<'a>) -> Roles<'a> {
    match left {
        Roles::Empty => right,
        Roles::Entry { role, next } => Roles::Entry {
            role,
            next: Box::new(roles_append(*next, right)),
        },
    }
}
fn edges_append<'a>(left: Edges<'a>, right: Edges<'a>) -> Edges<'a> {
    match left {
        Edges::Empty => right,
        Edges::Entry { sub, sup, next } => Edges::Entry {
            sub,
            sup,
            next: Box::new(edges_append(*next, right)),
        },
    }
}
fn chains_append<'a>(left: Chains<'a>, right: Chains<'a>) -> Chains<'a> {
    match left {
        Chains::Empty => right,
        Chains::Entry { chain, sup, next } => Chains::Entry {
            chain,
            sup,
            next: Box::new(chains_append(*next, right)),
        },
    }
}
fn pair_roles(role: Role<'_>) -> Roles<'_> {
    let other = inverse_role(copy_role(&role));
    Roles::Entry {
        role,
        next: Box::new(Roles::Entry {
            role: other,
            next: Box::new(Roles::Empty),
        }),
    }
}
fn edge_pair<'a>(sub: Role<'a>, sup: Role<'a>) -> Edges<'a> {
    let inverse_sub = inverse_role(copy_role(&sub));
    let inverse_sup = inverse_role(copy_role(&sup));
    Edges::Entry {
        sub,
        sup,
        next: Box::new(Edges::Entry {
            sub: inverse_sub,
            sup: inverse_sup,
            next: Box::new(Edges::Empty),
        }),
    }
}
fn both_edges<'a>(left: Role<'a>, right: Role<'a>) -> Edges<'a> {
    let backward = edge_pair(copy_role(&right), copy_role(&left));
    edges_append(edge_pair(left, right), backward)
}
fn same_pattern_from(key: &Vec<u8>, pattern: &[u8], index: usize) -> bool {
    if index < key.len() {
        key[index] == pattern[index] && same_pattern_from(key, pattern, index + 1)
    } else {
        true
    }
}
fn same_pattern(key: &Vec<u8>, pattern: &[u8]) -> bool {
    key.len() == pattern.len() && same_pattern_from(key, pattern, 0)
}
fn builtin_composite(iri: &Iri) -> bool {
    same_pattern(
        &iri.spelling,
        b"http://www.w3.org/2002/07/owl#topObjectProperty",
    ) || same_pattern(
        &iri.spelling,
        b"http://www.w3.org/2002/07/owl#bottomObjectProperty",
    )
}
fn nodes_from(uses: EntityUses<'_>) -> Roles<'_> {
    match uses {
        EntityUses::Empty => Roles::Empty,
        EntityUses::Entry { iri, kind, next } => {
            let tail = nodes_from(*next);
            match kind {
                EntityKind::ObjectProperty => roles_append(
                    pair_roles(Role {
                        iri,
                        inverse: false,
                    }),
                    tail,
                ),
                _ => tail,
            }
        }
    }
}
fn composites_from(uses: EntityUses<'_>) -> Roles<'_> {
    match uses {
        EntityUses::Empty => Roles::Empty,
        EntityUses::Entry { iri, kind, next } => {
            let tail = composites_from(*next);
            match kind {
                EntityKind::ObjectProperty => {
                    if builtin_composite(iri) {
                        Roles::Entry {
                            role: Role {
                                iri,
                                inverse: false,
                            },
                            next: Box::new(tail),
                        }
                    } else {
                        tail
                    }
                }
                _ => tail,
            }
        }
    }
}
fn property_roles_from(values: &Vec<ObjectPropertyExpression>, index: usize) -> Roles<'_> {
    if index < values.len() {
        Roles::Entry {
            role: expression_role(&values[index]),
            next: Box::new(property_roles_from(values, index + 1)),
        }
    } else {
        Roles::Empty
    }
}
pub(crate) fn property_roles(values: &AtLeastTwo<ObjectPropertyExpression>) -> Roles<'_> {
    Roles::Entry {
        role: expression_role(&values.first),
        next: Box::new(Roles::Entry {
            role: expression_role(&values.second),
            next: Box::new(property_roles_from(&values.rest, 0)),
        }),
    }
}
fn equivalent_rest<'a>(
    first: &'a ObjectPropertyExpression,
    rest: &'a Vec<ObjectPropertyExpression>,
    index: usize,
) -> Edges<'a> {
    if index < rest.len() {
        edges_append(
            both_edges(expression_role(first), expression_role(&rest[index])),
            equivalent_rest(first, rest, index + 1),
        )
    } else {
        Edges::Empty
    }
}
fn equivalent_pairs_from(values: &Vec<ObjectPropertyExpression>, index: usize) -> Edges<'_> {
    if index < values.len() {
        edges_append(
            equivalent_rest(&values[index], values, index + 1),
            equivalent_pairs_from(values, index + 1),
        )
    } else {
        Edges::Empty
    }
}
fn equivalent_edges(values: &AtLeastTwo<ObjectPropertyExpression>) -> Edges<'_> {
    edges_append(
        both_edges(
            expression_role(&values.first),
            expression_role(&values.second),
        ),
        edges_append(
            equivalent_rest(&values.first, &values.rest, 0),
            edges_append(
                equivalent_rest(&values.second, &values.rest, 0),
                equivalent_pairs_from(&values.rest, 0),
            ),
        ),
    )
}
fn classes_from(values: &Vec<ClassExpression>, index: usize) -> Roles<'_> {
    if index < values.len() {
        roles_append(
            class_requirements(&values[index]),
            classes_from(values, index + 1),
        )
    } else {
        Roles::Empty
    }
}
fn optional_class(value: &Option<Box<ClassExpression>>) -> Roles<'_> {
    match value {
        None => Roles::Empty,
        Some(value) => class_requirements(value),
    }
}
/// All cardinality and self restrictions, including qualified fillers and
/// arbitrary nested class expressions. Some/all/value restrictions require no
/// simple role merely by using their property.
pub fn class_requirements(expression: &ClassExpression) -> Roles<'_> {
    match expression {
        ClassExpression::ObjectIntersectionOf(values) | ClassExpression::ObjectUnionOf(values) => {
            roles_append(
                class_requirements(&values.first),
                roles_append(
                    class_requirements(&values.second),
                    classes_from(&values.rest, 0),
                ),
            )
        }
        ClassExpression::ObjectComplementOf(inner)
        | ClassExpression::ObjectSomeValuesFrom(_, inner)
        | ClassExpression::ObjectAllValuesFrom(_, inner) => class_requirements(inner),
        ClassExpression::ObjectHasSelf(property) => Roles::Entry {
            role: expression_role(property),
            next: Box::new(Roles::Empty),
        },
        ClassExpression::ObjectMinCardinality(_, property, filler)
        | ClassExpression::ObjectMaxCardinality(_, property, filler)
        | ClassExpression::ObjectExactCardinality(_, property, filler) => Roles::Entry {
            role: expression_role(property),
            next: Box::new(optional_class(filler)),
        },
        _ => Roles::Empty,
    }
}
fn axiom_requirements(axiom: &Axiom) -> Roles<'_> {
    match axiom {
        Axiom::SubClassOf(a, b) => roles_append(class_requirements(a), class_requirements(b)),
        Axiom::EquivalentClasses(values)
        | Axiom::DisjointClasses(values)
        | Axiom::DisjointUnion(_, values) => roles_append(
            class_requirements(&values.first),
            roles_append(
                class_requirements(&values.second),
                classes_from(&values.rest, 0),
            ),
        ),
        Axiom::ObjectPropertyDomain(_, class)
        | Axiom::ObjectPropertyRange(_, class)
        | Axiom::DataPropertyDomain(_, class)
        | Axiom::HasKey(class, _, _)
        | Axiom::ClassAssertion(class, _) => class_requirements(class),
        Axiom::FunctionalObjectProperty(property)
        | Axiom::InverseFunctionalObjectProperty(property)
        | Axiom::IrreflexiveObjectProperty(property)
        | Axiom::AsymmetricObjectProperty(property) => Roles::Entry {
            role: expression_role(property),
            next: Box::new(Roles::Empty),
        },
        Axiom::DisjointObjectProperties(values) => property_roles(values),
        _ => Roles::Empty,
    }
}
/// Preprocess one actual annotated axiom. Chain operands remain ordered and
/// are not ordinary hierarchy edges. Equivalence contributes every distinct
/// occurrence pair, in both directions and both inverse orientations.
pub fn axiom_facts(item: &AnnotatedAxiom) -> RoleFacts<'_> {
    let nodes = nodes_from(axiom_entities(item));
    let builtin = composites_from(axiom_entities(item));
    let simple_required = axiom_requirements(&item.axiom);
    match &item.axiom {
        Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Single(sub), sup) => RoleFacts {
            nodes,
            edges: edge_pair(expression_role(sub), expression_role(sup)),
            composite: builtin,
            simple_required,
            chains: Chains::Empty,
        },
        Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Chain(chain), sup) => RoleFacts {
            nodes,
            edges: Edges::Empty,
            composite: roles_append(builtin, pair_roles(expression_role(sup))),
            simple_required,
            chains: Chains::Entry {
                chain,
                sup,
                next: Box::new(Chains::Empty),
            },
        },
        Axiom::EquivalentObjectProperties(values) => RoleFacts {
            nodes,
            edges: equivalent_edges(values),
            composite: builtin,
            simple_required,
            chains: Chains::Empty,
        },
        Axiom::InverseObjectProperties(a, b) => RoleFacts {
            nodes,
            edges: both_edges(expression_role(a), inverse_role(expression_role(b))),
            composite: builtin,
            simple_required,
            chains: Chains::Empty,
        },
        Axiom::SymmetricObjectProperty(property) => RoleFacts {
            nodes,
            edges: edge_pair(
                expression_role(property),
                inverse_role(expression_role(property)),
            ),
            composite: builtin,
            simple_required,
            chains: Chains::Empty,
        },
        Axiom::TransitiveObjectProperty(property) => RoleFacts {
            nodes,
            edges: Edges::Empty,
            composite: roles_append(builtin, pair_roles(expression_role(property))),
            simple_required,
            chains: Chains::Empty,
        },
        _ => RoleFacts {
            nodes,
            edges: Edges::Empty,
            composite: builtin,
            simple_required,
            chains: Chains::Empty,
        },
    }
}
fn append_facts<'a>(left: RoleFacts<'a>, right: RoleFacts<'a>) -> RoleFacts<'a> {
    RoleFacts {
        nodes: roles_append(left.nodes, right.nodes),
        edges: edges_append(left.edges, right.edges),
        composite: roles_append(left.composite, right.composite),
        simple_required: roles_append(left.simple_required, right.simple_required),
        chains: chains_append(left.chains, right.chains),
    }
}
fn facts_from(items: &Vec<AnnotatedAxiom>, index: usize) -> RoleFacts<'_> {
    if index < items.len() {
        append_facts(axiom_facts(&items[index]), facts_from(items, index + 1))
    } else {
        RoleFacts {
            nodes: Roles::Empty,
            edges: Edges::Empty,
            composite: Roles::Empty,
            simple_required: Roles::Empty,
            chains: Chains::Empty,
        }
    }
}
/// Preserve every supplied axiom occurrence. Import closure construction and
/// structural duplicate canonicalization are separate earlier stages.
pub fn collect_facts(items: &Vec<AnnotatedAxiom>) -> RoleFacts<'_> {
    facts_from(items, 0)
}

/// Finite multi-root reachability result. Missing nodes diagnose malformed
/// externally assembled facts; a complete raw-AST collector supplies all nodes.
pub enum RoleClosure<'a> {
    Complete(Roles<'a>),
    MissingNode(Role<'a>),
}

enum TakenRole<'a> {
    Missing,
    Found { remaining: Roles<'a> },
}

/// Exact byte identity and orientation, including independently allocated IRIs.
pub fn same_role(left: &Role<'_>, right: &Role<'_>) -> bool {
    left.inverse == right.inverse
        && crate::symbols::same_spelling(&left.iri.spelling, &right.iri.spelling)
}

pub(crate) fn contains_role<'a>(values: Roles<'a>, sought: &Role<'_>) -> (bool, Roles<'a>) {
    match values {
        Roles::Empty => (false, Roles::Empty),
        Roles::Entry { role, next } => {
            if same_role(&role, sought) {
                (true, Roles::Entry { role, next })
            } else {
                let (found, tail) = contains_role(*next, sought);
                (
                    found,
                    Roles::Entry {
                        role,
                        next: Box::new(tail),
                    },
                )
            }
        }
    }
}

fn take_role<'a>(values: Roles<'a>, sought: &Role<'_>) -> TakenRole<'a> {
    match values {
        Roles::Empty => TakenRole::Missing,
        Roles::Entry { role, next } => {
            if same_role(&role, sought) {
                TakenRole::Found { remaining: *next }
            } else {
                match take_role(*next, sought) {
                    TakenRole::Missing => TakenRole::Missing,
                    TakenRole::Found { remaining } => TakenRole::Found {
                        remaining: Roles::Entry {
                            role,
                            next: Box::new(remaining),
                        },
                    },
                }
            }
        }
    }
}

fn successors<'a>(edges: Edges<'a>, source: &Role<'_>) -> (Roles<'a>, Edges<'a>) {
    match edges {
        Edges::Empty => (Roles::Empty, Edges::Empty),
        Edges::Entry { sub, sup, next } => {
            let (tail, restored) = successors(*next, source);
            if same_role(&sub, source) {
                (
                    Roles::Entry {
                        role: Role {
                            iri: sup.iri,
                            inverse: sup.inverse,
                        },
                        next: Box::new(tail),
                    },
                    Edges::Entry {
                        sub,
                        sup,
                        next: Box::new(restored),
                    },
                )
            } else {
                (
                    tail,
                    Edges::Entry {
                        sub,
                        sup,
                        next: Box::new(restored),
                    },
                )
            }
        }
    }
}

fn discover_roles<'a>(
    pending: Roles<'a>,
    available: Roles<'a>,
    resolved: Roles<'a>,
    edges: Edges<'a>,
) -> RoleClosure<'a> {
    match pending {
        Roles::Empty => RoleClosure::Complete(resolved),
        Roles::Entry { role, next } => {
            let (seen, resolved) = contains_role(resolved, &role);
            if seen {
                discover_roles(*next, available, resolved, edges)
            } else {
                match take_role(available, &role) {
                    TakenRole::Missing => RoleClosure::MissingNode(role),
                    TakenRole::Found { remaining } => {
                        let (neighbors, edges) = successors(edges, &role);
                        let pending = roles_append(neighbors, *next);
                        let resolved = Roles::Entry {
                            role,
                            next: Box::new(resolved),
                        };
                        discover_roles(pending, remaining, resolved, edges)
                    }
                }
            }
        }
    }
}

/// Follow the structural hierarchy upward from every composite root. Cycles and
/// repeated node/root/edge occurrences are handled without a fuel cutoff. Edges
/// are exactly the supplied edges; no chain operand becomes a hierarchy edge.
pub fn non_simple_closure<'a>(
    nodes: Roles<'a>,
    roots: Roles<'a>,
    edges: Edges<'a>,
) -> RoleClosure<'a> {
    discover_roles(roots, nodes, Roles::Empty, edges)
}

/// Derive the complete graph from actual raw syntax before computing composite
/// reachability. The input must be the complete canonically assembled closure;
/// import assembly and the other DL restrictions remain separate stages.
pub fn classify_non_simple(axioms: &Vec<AnnotatedAxiom>) -> RoleClosure<'_> {
    let facts = collect_facts(axioms);
    non_simple_closure(facts.nodes, facts.composite, facts.edges)
}

/// Result of only the OWL simple-role restriction. Allowed does not certify
/// regularity, declaration typing, imports or the remaining DL restrictions.
pub enum SimplicityCheck<'a> {
    Allowed,
    ForbiddenRole(Role<'a>),
    /// The raw collector's completeness proof excludes this outcome.
    MissingNode(Role<'a>),
}

fn check_required<'a>(required: Roles<'a>, non_simple: Roles<'a>) -> SimplicityCheck<'a> {
    match required {
        Roles::Empty => SimplicityCheck::Allowed,
        Roles::Entry { role, next } => {
            let (found, non_simple) = contains_role(non_simple, &role);
            if found {
                SimplicityCheck::ForbiddenRole(role)
            } else {
                check_required(*next, non_simple)
            }
        }
    }
}

/// Check every restricted role use in the complete supplied raw axiom closure.
/// Return the exact original role at the first forbidden occurrence, in closure
/// and nested-syntax traversal order. Cyclic hierarchies need no fuel cutoff.
pub fn check_simplicity(axioms: &Vec<AnnotatedAxiom>) -> SimplicityCheck<'_> {
    let facts = collect_facts(axioms);
    match non_simple_closure(facts.nodes, facts.composite, facts.edges) {
        RoleClosure::Complete(non_simple) => check_required(facts.simple_required, non_simple),
        RoleClosure::MissingNode(role) => SimplicityCheck::MissingNode(role),
    }
}

pub(crate) fn is_top_role(role: &Role<'_>) -> bool {
    !role.inverse
        && same_pattern(
            &role.iri.spelling,
            b"http://www.w3.org/2002/07/owl#topObjectProperty",
        )
}
