//! Role axioms for the tableaux: inclusions between named object properties
//! and transitive named object properties.
//!
//! The inclusions must be closed under composition: whenever `a ⊑ b` and
//! `b ⊑ c` are listed, `a ⊑ c` is listed too. The tableaux test inclusion with
//! `below`, which also counts every property as included in itself.
#![allow(clippy::ptr_arg)] // Indexed operations for the pinned extraction subset.
use crate::model::ObjectProperty;
use crate::symbols::same_spelling;

/// Every pair that `sub` relates is related by `sup` too.
pub struct RoleInclusion {
    pub sub: ObjectProperty,
    pub sup: ObjectProperty,
}
/// Inclusions between named object properties, closed under composition, and
/// the transitive named object properties.
pub struct RoleBox {
    pub inclusions: Vec<RoleInclusion>,
    pub transitive: Vec<ObjectProperty>,
}

/// Whether `inclusions[index..]` lists `sub ⊑ sup`.
fn included_from(
    inclusions: &Vec<RoleInclusion>,
    index: usize,
    sub: &ObjectProperty,
    sup: &ObjectProperty,
) -> bool {
    if index < inclusions.len() {
        let inclusion = &inclusions[index];
        if same_spelling(&inclusion.sub.iri.spelling, &sub.iri.spelling)
            && same_spelling(&inclusion.sup.iri.spelling, &sup.iri.spelling)
        {
            true
        } else {
            included_from(inclusions, index + 1, sub, sup)
        }
    } else {
        false
    }
}
/// Whether `sub` is `sup` or listed as included in it; properties are compared
/// by exact spelling.
pub fn below(roles: &RoleBox, sub: &ObjectProperty, sup: &ObjectProperty) -> bool {
    same_spelling(&sub.iri.spelling, &sup.iri.spelling)
        || included_from(&roles.inclusions, 0, sub, sup)
}
