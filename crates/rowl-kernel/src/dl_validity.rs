//! OWL 2 DL syntactic validity of a supplied complete axiom closure.
//!
//! `check_ontology` composes the verified checkers in one fixed order and
//! returns `Valid` or the first violation, with the evidence the component
//! checker reports. The order follows the condition lists of the 2012
//! Structural Specification, Section 3:
//!
//! 1. nonempty keys (§9.5) and the structural arities of the raw model;
//! 2. the reserved vocabulary in the ontology and version IRIs (§3.1) and in
//!    every entity position (§5.1–5.6);
//! 3. the typing constraints (§5.8.1), with the built-in declarations of
//!    Table 5: conflicting declarations first, then missing declarations;
//! 4. the global restrictions of §11.2, in the order of that section:
//!    `owl:topDataProperty`, datatypes (with the positions of defined
//!    datatypes, §9.4), simple roles, the property hierarchy and anonymous
//!    individuals.
//!
//! The supplied axioms are taken as the complete axiom closure: imports are
//! not resolved, and anonymous individuals must already be standardized
//! apart. Two OWL 2 DL conditions need the normative datatype map and are not
//! checked here: lexical forms in the lexical space of their datatype (§5.7)
//! and facet values in the facet space of their datatype (§7.5).
//!
//! The declaration typing stage compares exact IRI spellings directly, so it
//! has no symbol-count limit; it decides the same independent predicate as
//! `indexing::check_ontology_typing`. It finds declarations through an index
//! of their positions in buckets chosen by a hash of the IRI's bytes, and
//! still compares the spellings in a bucket exactly. Declaration consistency
//! (§5.8.2) is not an OWL 2 DL condition; `check_declarations` decides it
//! separately.
//!
//! Two shortcuts skip checks that cannot fail, each justified by a theorem:
//! without a property chain the empty order satisfies the restriction on the
//! property hierarchy, and without an object property assertion that has an
//! anonymous endpoint only the positional restriction on anonymous individuals
//! can fail.
#![allow(clippy::ptr_arg)] // Stay in the Vec/index subset of the pinned extraction.

use crate::anonymous::check_positions;
use crate::anonymous_restrictions::{check_anonymous, AnonymousCheck};
use crate::arity::check_arities;
use crate::builtins::builtin_kind;
use crate::collection::{axiom_closure_entities, EntityUses};
use crate::datatype_restrictions::{check_structural_datatypes, StructuralDatatypeCheck};
use crate::keys::check_keys;
use crate::model::{
    AnnotatedAxiom, Annotation, AnonymousIndividual, Axiom, Entity, Individual, Iri, RawOntology,
    SubObjectPropertyExpression,
};
use crate::role_order::{check_regularity, RegularityCheck};
use crate::roles::{check_simplicity, Role, SimplicityCheck};
use crate::topdata::check_axioms as check_top_data;
use crate::typing::{entity_kind, EntityKind};
use crate::vocabulary::{check_reserved_vocabulary, VocabularyResult};

/// The verdict of `check_ontology`: `Valid`, or the first violated restriction
/// in the documented order with the evidence of its component checker.
pub enum DlCheck<'a> {
    Valid,
    /// §9.5: a HasKey axiom without object or data property.
    EmptyKey(&'a AnnotatedAxiom),
    /// Structural arities: fewer than two distinct members where two are
    /// required, or a repeated member of a disjointness or difference axiom.
    Arity(&'a AnnotatedAxiom),
    /// §3.1: a reserved ontology IRI.
    ReservedOntologyIri(&'a Iri),
    /// §3.1: a reserved version IRI.
    ReservedVersionIri(&'a Iri),
    /// §5.1–5.6: a reserved IRI used in a role other than its built-in one.
    ReservedEntity {
        iri: &'a Iri,
        kind: EntityKind,
    },
    /// §5.8.1: the declaration of `iri` as `kind` conflicts with its built-in
    /// role or with a later declaration as `other`.
    ConflictingDeclarations {
        iri: &'a Iri,
        kind: EntityKind,
        other: EntityKind,
    },
    /// §5.8.1: `iri` is used as `kind` without a declaration of that kind.
    MissingDeclaration {
        iri: &'a Iri,
        kind: EntityKind,
    },
    /// §11.2: `owl:topDataProperty` outside a SubDataPropertyOf superproperty.
    TopDataProperty(&'a AnnotatedAxiom),
    /// §11.2: a datatype that is neither built in nor defined.
    MissingDatatypeDefinition(&'a Iri),
    /// §11.2: a definition of `rdfs:Literal` or a datatype of the datatype map.
    PredefinedDatatypeRedefined(&'a AnnotatedAxiom),
    /// §11.2: two structurally different definitions of one datatype.
    MultipleDatatypeDefinitions {
        first: &'a AnnotatedAxiom,
        second: &'a AnnotatedAxiom,
    },
    /// §11.2: cyclic datatype definitions; `larger` is defined using `smaller`,
    /// which depends on `larger`.
    DatatypeCycle {
        smaller: &'a Iri,
        larger: &'a Iri,
    },
    /// §9.4: a defined datatype in a literal or restriction of an ontology
    /// annotation.
    DefinedDatatypeInOntologyAnnotation(&'a Annotation),
    /// §9.4: a defined datatype in a literal or datatype restriction.
    DefinedDatatypePosition(&'a AnnotatedAxiom),
    /// §11.2: a non-simple object property where a simple one is required.
    NonSimpleRole(Role<'a>),
    /// §11.2: the chains force `sub < sup`, but `sup` is a subproperty of `sub`.
    IrregularHierarchy {
        sub: Role<'a>,
        sup: Role<'a>,
    },
    /// §11.2: an anonymous individual in a forbidden axiom or class expression.
    AnonymousPosition(&'a AnnotatedAxiom),
    /// §11.2: an assertion connects an anonymous individual with itself.
    AnonymousSelfLoop(&'a AnonymousIndividual),
    /// §11.2: the anonymous individuals are connected in a cycle.
    AnonymousCycle {
        left: &'a AnonymousIndividual,
        right: &'a AnonymousIndividual,
    },
    /// §11.2: two different assertions connect the same anonymous pair.
    AnonymousMultipleAssertions {
        first: &'a AnnotatedAxiom,
        second: &'a AnnotatedAxiom,
    },
    /// §11.2: no individual of this anonymous tree has at most one assertion
    /// with a named individual.
    AnonymousNoBoundaryRoot(&'a AnonymousIndividual),
}

/// The verdict of the typing constraints of §5.8.1.
pub enum TypingCheck<'a> {
    Valid,
    /// The first declaration, in closure order, that conflicts with the
    /// built-in role of its IRI or with a later declaration of the same IRI.
    ConflictingDeclarations {
        iri: &'a Iri,
        kind: EntityKind,
        other: EntityKind,
    },
    /// The first use of an entity that needs, and lacks, a declaration.
    MissingDeclaration {
        iri: &'a Iri,
        kind: EntityKind,
    },
}

/// The verdict of declaration consistency (§5.8.2), which is not required.
pub enum DeclarationCheck<'a> {
    Consistent,
    /// The first use of `iri` as `kind` without a declaration of that kind.
    Undeclared {
        iri: &'a Iri,
        kind: EntityKind,
    },
}

fn same_kind(left: &EntityKind, right: &EntityKind) -> bool {
    matches!(
        (left, right),
        (EntityKind::Class, EntityKind::Class)
            | (EntityKind::Datatype, EntityKind::Datatype)
            | (EntityKind::ObjectProperty, EntityKind::ObjectProperty)
            | (EntityKind::DataProperty, EntityKind::DataProperty)
            | (
                EntityKind::AnnotationProperty,
                EntityKind::AnnotationProperty
            )
            | (EntityKind::NamedIndividual, EntityKind::NamedIndividual)
    )
}

/// The kinds §5.8.1 forbids for one IRI: a class and a datatype, and two
/// different kinds of property.
fn forbidden(left: &EntityKind, right: &EntityKind) -> bool {
    matches!(
        (left, right),
        (EntityKind::Class, EntityKind::Datatype)
            | (EntityKind::Datatype, EntityKind::Class)
            | (EntityKind::ObjectProperty, EntityKind::DataProperty)
            | (EntityKind::ObjectProperty, EntityKind::AnnotationProperty)
            | (EntityKind::DataProperty, EntityKind::ObjectProperty)
            | (EntityKind::DataProperty, EntityKind::AnnotationProperty)
            | (EntityKind::AnnotationProperty, EntityKind::ObjectProperty)
            | (EntityKind::AnnotationProperty, EntityKind::DataProperty)
    )
}

fn same_before(left: &Vec<u8>, right: &Vec<u8>, end: usize) -> bool {
    if 0 < end {
        left[end - 1] == right[end - 1] && same_before(left, right, end - 1)
    } else {
        true
    }
}

/// Exact byte equality. The bytes are compared from the last one, where the
/// IRIs of one namespace usually differ.
pub fn same_bytes(left: &Vec<u8>, right: &Vec<u8>) -> bool {
    left.len() == right.len() && same_before(left, right, left.len())
}

/// The IRI of a declared entity.
fn entity_iri(entity: &Entity) -> &Iri {
    match entity {
        Entity::Class(c) => &c.iri,
        Entity::Datatype(d) => &d.iri,
        Entity::ObjectProperty(p) => &p.iri,
        Entity::DataProperty(p) => &p.iri,
        Entity::AnnotationProperty(p) => &p.iri,
        Entity::NamedIndividual(i) => &i.iri,
    }
}

/// Whether `entity` declares the spelling of `iri` as `kind`.
fn entity_declares(entity: &Entity, iri: &Iri, kind: &EntityKind) -> bool {
    same_kind(&entity_kind(entity), kind) && same_bytes(&entity_iri(entity).spelling, &iri.spelling)
}

/// Whether `item` is a declaration of the spelling of `iri` as `kind`.
fn item_declares(item: &AnnotatedAxiom, iri: &Iri, kind: &EntityKind) -> bool {
    match &item.axiom {
        Axiom::Declaration(entity) => entity_declares(entity, iri, kind),
        _ => false,
    }
}

/// The number of buckets of the declaration index.
const BUCKETS: usize = 4096;

/// `(hash mod BUCKETS) * 31 + byte`, reduced modulo `BUCKETS`, without overflow.
fn mix(hash: usize, byte: u8) -> usize {
    ((hash % BUCKETS) * 31 + byte as usize) % BUCKETS
}

fn hash_from(bytes: &Vec<u8>, index: usize, hash: usize) -> usize {
    if index < bytes.len() {
        hash_from(bytes, index + 1, mix(hash, bytes[index]))
    } else {
        hash
    }
}

/// The bucket of an IRI in the declaration index. It depends only on the
/// IRI's bytes, so equal spellings share a bucket.
fn bucket_of(iri: &Iri) -> usize {
    hash_from(&iri.spelling, 0, 0)
}

fn empty_buckets(mut out: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    if out.len() < BUCKETS {
        out.push(Vec::new());
        empty_buckets(out)
    } else {
        out
    }
}

/// Whether bucket `bucket` exists and has room for one more position.
fn has_room(buckets: &Vec<Vec<usize>>, bucket: usize) -> bool {
    bucket < buckets.len() && buckets[bucket].len() < usize::MAX
}

/// Add `position` to the bucket `bucket` when both fit.
fn record(mut buckets: Vec<Vec<usize>>, bucket: usize, position: usize) -> Vec<Vec<usize>> {
    if has_room(&buckets, bucket) {
        buckets[bucket].push(position);
    }
    buckets
}

fn index_item(item: &AnnotatedAxiom, position: usize, buckets: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
    match &item.axiom {
        Axiom::Declaration(entity) => record(buckets, bucket_of(entity_iri(entity)), position),
        _ => buckets,
    }
}

fn index_from(
    axioms: &Vec<AnnotatedAxiom>,
    position: usize,
    buckets: Vec<Vec<usize>>,
) -> Vec<Vec<usize>> {
    if position < axioms.len() {
        index_from(
            axioms,
            position + 1,
            index_item(&axioms[position], position, buckets),
        )
    } else {
        buckets
    }
}

/// The declaration index: for every bucket, the positions of the declaration
/// axioms whose IRI falls into it, in increasing order.
fn declaration_index(axioms: &Vec<AnnotatedAxiom>) -> Vec<Vec<usize>> {
    index_from(axioms, 0, empty_buckets(Vec::new()))
}

/// Whether the axiom at `position` declares the spelling of `iri` as `kind`.
fn position_declares(
    axioms: &Vec<AnnotatedAxiom>,
    position: usize,
    iri: &Iri,
    kind: &EntityKind,
) -> bool {
    if position < axioms.len() {
        item_declares(&axioms[position], iri, kind)
    } else {
        false
    }
}

fn declared_at(
    axioms: &Vec<AnnotatedAxiom>,
    positions: &Vec<usize>,
    iri: &Iri,
    kind: &EntityKind,
    at: usize,
) -> bool {
    if at < positions.len() {
        position_declares(axioms, positions[at], iri, kind)
            || declared_at(axioms, positions, iri, kind, at + 1)
    } else {
        false
    }
}

fn declared_in_bucket(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    bucket: usize,
    iri: &Iri,
    kind: &EntityKind,
) -> bool {
    if bucket < index.len() {
        declared_at(axioms, &index[bucket], iri, kind, 0)
    } else {
        false
    }
}

/// Whether a declaration axiom declares the spelling of `iri` as `kind`; only
/// the declarations in the bucket of `iri` can.
fn declared_indexed(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    iri: &Iri,
    kind: &EntityKind,
) -> bool {
    declared_in_bucket(axioms, index, bucket_of(iri), iri, kind)
}

/// Whether `kind` is the built-in role of `iri` (Table 5).
fn builtin_role(iri: &Iri, kind: &EntityKind) -> bool {
    match builtin_kind(&iri.spelling) {
        Some(role) => same_kind(&role, kind),
        None => false,
    }
}

/// `role`, if it is forbidden together with `kind`.
fn conflicting_role(kind: &EntityKind, role: EntityKind) -> Option<EntityKind> {
    if forbidden(kind, &role) {
        Some(role)
    } else {
        None
    }
}

/// The built-in role of `iri`, if it is forbidden together with `kind`.
fn builtin_conflict(iri: &Iri, kind: &EntityKind) -> Option<EntityKind> {
    match builtin_kind(&iri.spelling) {
        Some(role) => conflicting_role(kind, role),
        None => None,
    }
}

/// The kind `item` declares the spelling of `iri` with, if it is forbidden
/// together with `kind`.
fn item_conflict(item: &AnnotatedAxiom, iri: &Iri, kind: &EntityKind) -> Option<EntityKind> {
    match &item.axiom {
        Axiom::Declaration(entity) => {
            if same_bytes(&entity_iri(entity).spelling, &iri.spelling) {
                conflicting_role(kind, entity_kind(entity))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The kind the axiom at `position` declares the spelling of `iri` with, if
/// the position comes after `after` and the kind is forbidden with `kind`.
fn position_conflict(
    axioms: &Vec<AnnotatedAxiom>,
    position: usize,
    iri: &Iri,
    kind: &EntityKind,
    after: usize,
) -> Option<EntityKind> {
    if after < position {
        if position < axioms.len() {
            item_conflict(&axioms[position], iri, kind)
        } else {
            None
        }
    } else {
        None
    }
}

fn conflict_at(
    axioms: &Vec<AnnotatedAxiom>,
    positions: &Vec<usize>,
    iri: &Iri,
    kind: &EntityKind,
    after: usize,
    at: usize,
) -> Option<EntityKind> {
    if at < positions.len() {
        match position_conflict(axioms, positions[at], iri, kind, after) {
            Some(other) => Some(other),
            None => conflict_at(axioms, positions, iri, kind, after, at + 1),
        }
    } else {
        None
    }
}

fn conflict_in_bucket(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    bucket: usize,
    iri: &Iri,
    kind: &EntityKind,
    after: usize,
) -> Option<EntityKind> {
    if bucket < index.len() {
        conflict_at(axioms, &index[bucket], iri, kind, after, 0)
    } else {
        None
    }
}

/// The kind of a declaration after position `after` that declares the
/// spelling of `iri` with a kind forbidden together with `kind`.
fn later_conflict(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    iri: &Iri,
    kind: &EntityKind,
    after: usize,
) -> Option<EntityKind> {
    conflict_in_bucket(axioms, index, bucket_of(iri), iri, kind, after)
}

/// The conflict of the declaration of `entity` at `position` with its
/// built-in role, or else with a later declaration.
fn entity_conflict(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    entity: &Entity,
    position: usize,
) -> Option<EntityKind> {
    match builtin_conflict(entity_iri(entity), &entity_kind(entity)) {
        Some(role) => Some(role),
        None => later_conflict(
            axioms,
            index,
            entity_iri(entity),
            &entity_kind(entity),
            position,
        ),
    }
}

/// The conflict of `item` at `position`, if it is a declaration that
/// conflicts with its built-in role or with a later declaration.
fn item_conflicts<'a>(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    item: &'a AnnotatedAxiom,
    position: usize,
) -> TypingCheck<'a> {
    match &item.axiom {
        Axiom::Declaration(entity) => match entity_conflict(axioms, index, entity, position) {
            Some(other) => TypingCheck::ConflictingDeclarations {
                iri: entity_iri(entity),
                kind: entity_kind(entity),
                other,
            },
            None => TypingCheck::Valid,
        },
        _ => TypingCheck::Valid,
    }
}

/// The first declaration in `axioms[position..]` that conflicts with its
/// built-in role or with a later declaration. A conflict with an earlier
/// declaration is found at that earlier one, since the relation is symmetric.
fn conflict_from<'a>(
    axioms: &'a Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    position: usize,
) -> TypingCheck<'a> {
    if position < axioms.len() {
        match item_conflicts(axioms, index, &axioms[position], position) {
            TypingCheck::Valid => conflict_from(axioms, index, position + 1),
            conflict => conflict,
        }
    } else {
        TypingCheck::Valid
    }
}

/// Whether a use as `kind` needs no declaration: a named individual, unless
/// `strict`.
fn exempt(kind: &EntityKind, strict: bool) -> bool {
    !strict && matches!(kind, EntityKind::NamedIndividual)
}

/// Whether a use of `iri` as `kind` is declared: exempt, a built-in role, or
/// declared explicitly in `axioms`.
fn use_declared(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    iri: &Iri,
    kind: &EntityKind,
    strict: bool,
) -> bool {
    exempt(kind, strict) || builtin_role(iri, kind) || declared_indexed(axioms, index, iri, kind)
}

/// The first use whose spelling is not declared with its kind, explicitly in
/// `axioms` or as a built-in. Named individuals need a declaration only when
/// `strict`.
fn undeclared_from<'a>(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    uses: EntityUses<'a>,
    strict: bool,
) -> Option<(&'a Iri, EntityKind)> {
    match uses {
        EntityUses::Empty => None,
        EntityUses::Entry { iri, kind, next } => {
            if use_declared(axioms, index, iri, &kind, strict) {
                undeclared_from(axioms, index, *next, strict)
            } else {
                Some((iri, kind))
            }
        }
    }
}

fn typing_with<'a>(
    axioms: &'a Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    uses: EntityUses<'a>,
) -> TypingCheck<'a> {
    match conflict_from(axioms, index, 0) {
        TypingCheck::Valid => match undeclared_from(axioms, index, uses, false) {
            Some((iri, kind)) => TypingCheck::MissingDeclaration { iri, kind },
            None => TypingCheck::Valid,
        },
        conflict => conflict,
    }
}

/// The typing constraints of §5.8.1 on the supplied axioms and their
/// annotations, with the built-in declarations of Table 5: no IRI is declared
/// with two forbidden kinds, and every class, datatype and property is
/// declared. Ontology annotations are not axioms and need no declarations.
/// Declarations are found through a hashed index of their positions.
pub fn check_typing(ontology: &RawOntology) -> TypingCheck<'_> {
    typing_with(
        &ontology.axioms,
        &declaration_index(&ontology.axioms),
        axiom_closure_entities(ontology).uses,
    )
}

fn declarations_with<'a>(
    axioms: &Vec<AnnotatedAxiom>,
    index: &Vec<Vec<usize>>,
    uses: EntityUses<'a>,
) -> DeclarationCheck<'a> {
    match undeclared_from(axioms, index, uses, true) {
        Some((iri, kind)) => DeclarationCheck::Undeclared { iri, kind },
        None => DeclarationCheck::Consistent,
    }
}

/// Declaration consistency (§5.8.2): every entity in the supplied axioms,
/// named individuals included, is declared with its kind, explicitly or as a
/// built-in. OWL 2 DL does not require it.
pub fn check_declarations(ontology: &RawOntology) -> DeclarationCheck<'_> {
    declarations_with(
        &ontology.axioms,
        &declaration_index(&ontology.axioms),
        axiom_closure_entities(ontology).uses,
    )
}

/// Whether `item` is a SubObjectPropertyOf axiom with a property chain.
fn is_chain(item: &AnnotatedAxiom) -> bool {
    matches!(
        &item.axiom,
        Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Chain(_), _)
    )
}

fn chain_from(axioms: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < axioms.len() {
        is_chain(&axioms[index]) || chain_from(axioms, index + 1)
    } else {
        false
    }
}

/// Whether some axiom has a property chain. Without one, the empty order
/// satisfies the restriction on the property hierarchy.
pub fn has_chain(axioms: &Vec<AnnotatedAxiom>) -> bool {
    chain_from(axioms, 0)
}

/// Whether `item` is an object property assertion with an anonymous endpoint.
fn anonymous_assertion(item: &AnnotatedAxiom) -> bool {
    matches!(
        &item.axiom,
        Axiom::ObjectPropertyAssertion(_, Individual::Anonymous(_), _)
            | Axiom::ObjectPropertyAssertion(_, _, Individual::Anonymous(_))
    )
}

fn anonymous_from(axioms: &Vec<AnnotatedAxiom>, index: usize) -> bool {
    if index < axioms.len() {
        anonymous_assertion(&axioms[index]) || anonymous_from(axioms, index + 1)
    } else {
        false
    }
}

/// Whether some object property assertion has an anonymous endpoint. Without
/// one, the anonymous individual graph has no edges and no anonymous individual
/// has an assertion with a named one, so only the positional restriction can
/// fail and the quadratic graph checks can be skipped.
pub fn has_anonymous_assertion(axioms: &Vec<AnnotatedAxiom>) -> bool {
    anonymous_from(axioms, 0)
}

fn anonymous_graph_stage(ontology: &RawOntology) -> DlCheck<'_> {
    match check_anonymous(&ontology.axioms) {
        AnonymousCheck::Allowed => DlCheck::Valid,
        AnonymousCheck::ForbiddenPosition(item) => DlCheck::AnonymousPosition(item),
        AnonymousCheck::SelfLoop(value) => DlCheck::AnonymousSelfLoop(value),
        AnonymousCheck::Cycle { left, right } => DlCheck::AnonymousCycle { left, right },
        AnonymousCheck::MultipleAssertions { first, second } => {
            DlCheck::AnonymousMultipleAssertions { first, second }
        }
        AnonymousCheck::NoBoundaryRoot(value) => DlCheck::AnonymousNoBoundaryRoot(value),
    }
}

fn anonymous_stage(ontology: &RawOntology) -> DlCheck<'_> {
    if has_anonymous_assertion(&ontology.axioms) {
        anonymous_graph_stage(ontology)
    } else {
        match check_positions(&ontology.axioms) {
            Some(item) => DlCheck::AnonymousPosition(item),
            None => DlCheck::Valid,
        }
    }
}

fn hierarchy_stage(ontology: &RawOntology) -> DlCheck<'_> {
    if has_chain(&ontology.axioms) {
        match check_regularity(&ontology.axioms) {
            RegularityCheck::Regular(_) => anonymous_stage(ontology),
            RegularityCheck::HierarchyConflict { sub, sup } => {
                DlCheck::IrregularHierarchy { sub, sup }
            }
            // The component proofs exclude both outcomes for raw axioms.
            RegularityCheck::MissingPair { sub, sup } => DlCheck::IrregularHierarchy { sub, sup },
            RegularityCheck::MissingHierarchyNode(role) => DlCheck::IrregularHierarchy {
                sub: Role {
                    iri: role.iri,
                    inverse: role.inverse,
                },
                sup: role,
            },
        }
    } else {
        anonymous_stage(ontology)
    }
}

fn role_stage(ontology: &RawOntology) -> DlCheck<'_> {
    match check_simplicity(&ontology.axioms) {
        SimplicityCheck::Allowed => hierarchy_stage(ontology),
        SimplicityCheck::ForbiddenRole(role) => DlCheck::NonSimpleRole(role),
        // The component proof excludes this outcome for raw axioms.
        SimplicityCheck::MissingNode(role) => DlCheck::NonSimpleRole(role),
    }
}

fn datatype_stage(ontology: &RawOntology) -> DlCheck<'_> {
    match check_structural_datatypes(ontology) {
        StructuralDatatypeCheck::Allowed => role_stage(ontology),
        StructuralDatatypeCheck::MissingDefinition(iri) => DlCheck::MissingDatatypeDefinition(iri),
        StructuralDatatypeCheck::PredefinedRedefined(item) => {
            DlCheck::PredefinedDatatypeRedefined(item)
        }
        StructuralDatatypeCheck::MultipleDefinitions { first, second } => {
            DlCheck::MultipleDatatypeDefinitions { first, second }
        }
        StructuralDatatypeCheck::Cycle { smaller, larger } => {
            DlCheck::DatatypeCycle { smaller, larger }
        }
        StructuralDatatypeCheck::ForbiddenOntologyAnnotation(item) => {
            DlCheck::DefinedDatatypeInOntologyAnnotation(item)
        }
        StructuralDatatypeCheck::ForbiddenAxiomPosition(item) => {
            DlCheck::DefinedDatatypePosition(item)
        }
    }
}

fn global_stage(ontology: &RawOntology) -> DlCheck<'_> {
    match check_top_data(&ontology.axioms) {
        Some(item) => DlCheck::TopDataProperty(item),
        None => datatype_stage(ontology),
    }
}

fn typing_stage(ontology: &RawOntology) -> DlCheck<'_> {
    match check_typing(ontology) {
        TypingCheck::Valid => global_stage(ontology),
        TypingCheck::ConflictingDeclarations { iri, kind, other } => {
            DlCheck::ConflictingDeclarations { iri, kind, other }
        }
        TypingCheck::MissingDeclaration { iri, kind } => DlCheck::MissingDeclaration { iri, kind },
    }
}

fn vocabulary_stage(ontology: &RawOntology) -> DlCheck<'_> {
    match check_reserved_vocabulary(ontology) {
        VocabularyResult::Valid => typing_stage(ontology),
        VocabularyResult::ReservedOntologyIri(iri) => DlCheck::ReservedOntologyIri(iri),
        VocabularyResult::ReservedVersionIri(iri) => DlCheck::ReservedVersionIri(iri),
        VocabularyResult::ForbiddenEntity { iri, kind } => DlCheck::ReservedEntity { iri, kind },
    }
}

/// Decide the OWL 2 DL restrictions listed in the module documentation on the
/// supplied ontology, whose axioms are taken as its complete axiom closure.
/// `Valid` is not a consistency result, and literal lexical forms and facet
/// values are not checked.
pub fn check_ontology(ontology: &RawOntology) -> DlCheck<'_> {
    match check_keys(&ontology.axioms) {
        Some(item) => DlCheck::EmptyKey(item),
        None => match check_arities(&ontology.axioms) {
            Some(item) => DlCheck::Arity(item),
            None => vocabulary_stage(ontology),
        },
    }
}
