//! Role hierarchies with inverse roles: inclusions between object property
//! expressions and transitive object property expressions.
//!
//! The completion graph tableau needs closed hierarchies: the inclusions
//! include their compositions and, with every inclusion `r ⊑ s`, the inclusion
//! `inv(r) ⊑ inv(s)`, and with every transitive role its inverse. `below` tests
//! inclusion; every role is included in itself.
#![allow(clippy::ptr_arg)] // Indexed operations for the pinned extraction subset.
use crate::concepts::same_role;
use crate::model::ObjectPropertyExpression;

/// Every pair that `sub` relates is related by `sup` too.
pub struct Inclusion {
    pub sub: ObjectPropertyExpression,
    pub sup: ObjectPropertyExpression,
}
/// Inclusions between object property expressions and the transitive object
/// property expressions.
pub struct RoleHierarchy {
    pub inclusions: Vec<Inclusion>,
    pub transitive: Vec<ObjectPropertyExpression>,
}

/// Whether `inclusions[index..]` lists `sub ⊑ sup`.
fn listed_from(
    inclusions: &Vec<Inclusion>,
    index: usize,
    sub: &ObjectPropertyExpression,
    sup: &ObjectPropertyExpression,
) -> bool {
    if index < inclusions.len() {
        let inclusion = &inclusions[index];
        if same_role(&inclusion.sub, sub) && same_role(&inclusion.sup, sup) {
            true
        } else {
            listed_from(inclusions, index + 1, sub, sup)
        }
    } else {
        false
    }
}
/// Whether `sub` is `sup` or listed as included in it; roles are compared by
/// orientation and exact spelling.
pub fn below(
    roles: &RoleHierarchy,
    sub: &ObjectPropertyExpression,
    sup: &ObjectPropertyExpression,
) -> bool {
    same_role(sub, sup) || listed_from(&roles.inclusions, 0, sub, sup)
}
/// Whether `transitive[index..]` lists the role.
fn transitive_from(
    transitive: &Vec<ObjectPropertyExpression>,
    index: usize,
    role: &ObjectPropertyExpression,
) -> bool {
    if index < transitive.len() {
        if same_role(&transitive[index], role) {
            true
        } else {
            transitive_from(transitive, index + 1, role)
        }
    } else {
        false
    }
}
/// Whether the role is listed as transitive.
pub fn is_transitive(roles: &RoleHierarchy, role: &ObjectPropertyExpression) -> bool {
    transitive_from(&roles.transitive, 0, role)
}
