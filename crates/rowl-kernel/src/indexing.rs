//! Connect raw OWL entity collection to exact byte symbols and declaration typing.
//! No supplied numeric occurrence table is trusted. Implicit built-in roles
//! are injected before checking; lexical validity and the remaining global DL
//! restrictions are separate checks.
use crate::builtins::builtin_kind;
use crate::collection::{axiom_closure_entities, CollectedEntities, EntityUses};
use crate::model::{Iri, RawOntology};
use crate::symbols::{empty, intern, key_of, InternResult, SymbolTable};
use crate::typing::{validate_typing, Occurrences, TypingResult};

pub enum IndexResult<'a> {
    Complete {
        table: SymbolTable<'a>,
        declarations: Occurrences,
        uses: Occurrences,
    },
    CapacityExceeded {
        table: SymbolTable<'a>,
        iri: &'a Iri,
    },
}

pub enum IndexedTyping<'a> {
    Checked {
        table: SymbolTable<'a>,
        declarations: Occurrences,
        uses: Occurrences,
        result: TypingResult,
    },
    CapacityExceeded {
        table: SymbolTable<'a>,
        iri: &'a Iri,
    },
}

enum Indexed<'a> {
    Complete(Occurrences),
    CapacityExceeded(&'a Iri),
}

fn index_uses<'a>(
    source: EntityUses<'a>,
    table: SymbolTable<'a>,
) -> (Indexed<'a>, SymbolTable<'a>) {
    match source {
        EntityUses::Empty => (Indexed::Complete(Occurrences::Empty), table),
        EntityUses::Entry { iri, kind, next } => {
            let (outcome, table) = intern(table, &iri.spelling);
            match outcome {
                InternResult::Existing(symbol) | InternResult::Inserted(symbol) => {
                    let (tail, table) = index_uses(*next, table);
                    match tail {
                        Indexed::Complete(next) => (
                            Indexed::Complete(Occurrences::Entry {
                                symbol,
                                kind,
                                next: Box::new(next),
                            }),
                            table,
                        ),
                        Indexed::CapacityExceeded(failed) => {
                            (Indexed::CapacityExceeded(failed), table)
                        }
                    }
                }
                InternResult::CapacityExceeded => (Indexed::CapacityExceeded(iri), table),
            }
        }
    }
}

/// Index declarations before uses, preserving every role, repetition and order.
/// Capacity failure identifies the first spelling that cannot receive a symbol.
pub fn index_entities<'a>(entities: CollectedEntities<'a>, limit: u32) -> IndexResult<'a> {
    let (declarations, table) = index_uses(entities.declarations, empty(limit));
    match declarations {
        Indexed::CapacityExceeded(iri) => IndexResult::CapacityExceeded { table, iri },
        Indexed::Complete(declarations) => {
            let (uses, table) = index_uses(entities.uses, table);
            match uses {
                Indexed::CapacityExceeded(iri) => IndexResult::CapacityExceeded { table, iri },
                Indexed::Complete(uses) => IndexResult::Complete {
                    table,
                    declarations,
                    uses,
                },
            }
        }
    }
}

/// Collect and intern all supplied axioms and their nested annotations. Ontology
/// annotations and untyped IRI positions do not become axiom-closure entity
/// occurrences. This does not parse IRIs or assemble imports.
pub fn index_ontology(ontology: &RawOntology, limit: u32) -> IndexResult<'_> {
    index_entities(axiom_closure_entities(ontology), limit)
}

/// Add the implicit declaration for each relevant built-in spelling. Repeated
/// occurrences remain repeated, and explicit declarations retain their order.
/// Keys not used by this ontology do not need a symbol or a virtual declaration.
pub fn add_builtin_declarations(
    table: &SymbolTable<'_>,
    uses: &Occurrences,
    declarations: Occurrences,
) -> Occurrences {
    match uses {
        Occurrences::Empty => declarations,
        Occurrences::Entry { symbol, next, .. } => {
            let tail = add_builtin_declarations(table, next, declarations);
            match key_of(table, *symbol) {
                Some(key) => match builtin_kind(key) {
                    Some(kind) => Occurrences::Entry {
                        symbol: *symbol,
                        kind,
                        next: Box::new(tail),
                    },
                    None => tail,
                },
                None => tail,
            }
        }
    }
}

/// Check declaration constraints directly from the complete raw ontology,
/// including OWL's implicit built-in roles. Success here is not a full OWL 2 DL
/// validity or consistency conclusion; no external numeric table is accepted.
pub fn check_ontology_typing(ontology: &RawOntology, limit: u32) -> IndexedTyping<'_> {
    match index_ontology(ontology, limit) {
        IndexResult::CapacityExceeded { table, iri } => {
            IndexedTyping::CapacityExceeded { table, iri }
        }
        IndexResult::Complete {
            table,
            declarations,
            uses,
        } => {
            let declarations = add_builtin_declarations(&table, &uses, declarations);
            let result = validate_typing(&declarations, &uses);
            IndexedTyping::Checked {
                table,
                declarations,
                uses,
                result,
            }
        }
    }
}
