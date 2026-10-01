//! OWL 2 DL declaration typing for symbol-indexed occurrence tables (§5.8.1).
//!
//! This low-level operation requires complete tables for the relevant axiom
//! closure, including implicit built-in declarations. `indexing` now derives
//! these tables directly from a supplied raw ontology. Import assembly, lexical
//! validity and the remaining global restrictions are separate obligations.
//! Success here is not an OWL 2 DL validity or consistency certificate.

use crate::model::Entity;

pub enum EntityKind {
    Class,
    Datatype,
    ObjectProperty,
    DataProperty,
    AnnotationProperty,
    NamedIndividual,
}

pub enum Occurrences {
    Empty,
    Entry {
        symbol: u32,
        kind: EntityKind,
        next: Box<Occurrences>,
    },
}

pub enum TypingResult {
    Valid,
    ConflictingDeclarations(u32),
    MissingDeclaration(u32),
}

pub fn entity_kind(entity: &Entity) -> EntityKind {
    match entity {
        Entity::Class(_) => EntityKind::Class,
        Entity::Datatype(_) => EntityKind::Datatype,
        Entity::ObjectProperty(_) => EntityKind::ObjectProperty,
        Entity::DataProperty(_) => EntityKind::DataProperty,
        Entity::AnnotationProperty(_) => EntityKind::AnnotationProperty,
        Entity::NamedIndividual(_) => EntityKind::NamedIndividual,
    }
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

fn conflicting_kinds(left: &EntityKind, right: &EntityKind) -> bool {
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

fn declared(declarations: &Occurrences, symbol: u32, kind: &EntityKind) -> bool {
    match declarations {
        Occurrences::Empty => false,
        Occurrences::Entry {
            symbol: here,
            kind: here_kind,
            next,
        } => (*here == symbol && same_kind(here_kind, kind)) || declared(next, symbol, kind),
    }
}

fn has_conflict(declarations: &Occurrences, symbol: u32, kind: &EntityKind) -> bool {
    match declarations {
        Occurrences::Empty => false,
        Occurrences::Entry {
            symbol: here,
            kind: here_kind,
            next,
        } => {
            (*here == symbol && conflicting_kinds(here_kind, kind))
                || has_conflict(next, symbol, kind)
        }
    }
}

fn first_conflict(declarations: &Occurrences) -> Option<u32> {
    match declarations {
        Occurrences::Empty => None,
        Occurrences::Entry { symbol, kind, next } => {
            if has_conflict(next, *symbol, kind) {
                Some(*symbol)
            } else {
                first_conflict(next)
            }
        }
    }
}

fn first_missing(declarations: &Occurrences, uses: &Occurrences) -> Option<u32> {
    match uses {
        Occurrences::Empty => None,
        Occurrences::Entry { symbol, kind, next } => {
            if matches!(kind, EntityKind::NamedIndividual) || declared(declarations, *symbol, kind)
            {
                first_missing(declarations, next)
            } else {
                Some(*symbol)
            }
        }
    }
}

/// All property kinds are disjoint, as are Class and Datatype. Other reuse is
/// allowed. Named-individual declarations are optional. Repeated declarations
/// of one kind are harmless; logical consistency is a separate question.
pub fn validate_typing(declarations: &Occurrences, uses: &Occurrences) -> TypingResult {
    match first_conflict(declarations) {
        Some(symbol) => TypingResult::ConflictingDeclarations(symbol),
        None => match first_missing(declarations, uses) {
            Some(symbol) => TypingResult::MissingDeclaration(symbol),
            None => TypingResult::Valid,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(symbol: u32, kind: EntityKind, next: Occurrences) -> Occurrences {
        Occurrences::Entry {
            symbol,
            kind,
            next: Box::new(next),
        }
    }

    #[test]
    fn class_individual_and_class_property_punning_are_allowed() {
        let declarations = entry(
            1,
            EntityKind::Class,
            entry(
                1,
                EntityKind::ObjectProperty,
                entry(1, EntityKind::Class, Occurrences::Empty),
            ),
        );
        let uses = entry(
            1,
            EntityKind::Class,
            entry(
                1,
                EntityKind::ObjectProperty,
                entry(
                    1,
                    EntityKind::NamedIndividual,
                    entry(2, EntityKind::NamedIndividual, Occurrences::Empty),
                ),
            ),
        );
        assert!(matches!(
            validate_typing(&declarations, &uses),
            TypingResult::Valid
        ));
    }

    #[test]
    fn incompatible_declarations_are_rejected_even_when_not_used() {
        let declarations = entry(
            1,
            EntityKind::Class,
            entry(1, EntityKind::Datatype, Occurrences::Empty),
        );
        assert!(matches!(
            validate_typing(&declarations, &Occurrences::Empty),
            TypingResult::ConflictingDeclarations(1)
        ));
        let declarations = entry(
            2,
            EntityKind::ObjectProperty,
            entry(2, EntityKind::DataProperty, Occurrences::Empty),
        );
        assert!(matches!(
            validate_typing(&declarations, &Occurrences::Empty),
            TypingResult::ConflictingDeclarations(2)
        ));
    }

    #[test]
    fn required_declarations_can_be_elsewhere_in_the_supplied_closure() {
        let declarations = entry(
            7,
            EntityKind::AnnotationProperty,
            entry(8, EntityKind::Datatype, Occurrences::Empty),
        );
        let uses = entry(
            8,
            EntityKind::Datatype,
            entry(7, EntityKind::AnnotationProperty, Occurrences::Empty),
        );
        assert!(matches!(
            validate_typing(&declarations, &uses),
            TypingResult::Valid
        ));
        let wrong = entry(8, EntityKind::Class, Occurrences::Empty);
        assert!(matches!(
            validate_typing(&declarations, &wrong),
            TypingResult::MissingDeclaration(8)
        ));
    }
}
