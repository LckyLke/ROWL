//! Answers for Functional Syntax source bytes: the verified document reader,
//! the mapping into the raw OWL model, and the verified SHI queries on the
//! completion graph tableau.
//!
//! A document error is returned as `Err`. Every document the reader accepts
//! maps into the model, so `Ok(None)` means the document's axioms or the query
//! are outside the reasoner's supported fragment.
#![allow(clippy::ptr_arg, clippy::question_mark)]
use crate::functional_document::{read_document, DocumentError, DocumentLimits};
use crate::functional_model::document_ontology;
use crate::model::{ClassExpression, NamedIndividual};
use crate::shi_ontology::{class_satisfiable, consistent, instance_of, subsumed};

/// Whether the document's axioms have a model.
pub fn source_consistent(
    bytes: &Vec<u8>,
    limits: &DocumentLimits,
    scope: &Vec<u8>,
) -> Result<Option<bool>, DocumentError> {
    let document = match read_document(bytes, limits) {
        Ok(document) => document,
        Err(error) => return Err(error),
    };
    match document_ontology(&document, scope) {
        Some(ontology) => Ok(consistent(&ontology.axioms)),
        None => Ok(None),
    }
}
/// Whether some model of the document's axioms has an instance of `class`.
pub fn source_class_satisfiable(
    bytes: &Vec<u8>,
    limits: &DocumentLimits,
    scope: &Vec<u8>,
    class: &ClassExpression,
) -> Result<Option<bool>, DocumentError> {
    let document = match read_document(bytes, limits) {
        Ok(document) => document,
        Err(error) => return Err(error),
    };
    match document_ontology(&document, scope) {
        Some(ontology) => Ok(class_satisfiable(&ontology.axioms, class)),
        None => Ok(None),
    }
}
/// Whether every instance of `sub` is an instance of `sup` in every model of the
/// document's axioms.
pub fn source_subsumed(
    bytes: &Vec<u8>,
    limits: &DocumentLimits,
    scope: &Vec<u8>,
    sub: &ClassExpression,
    sup: &ClassExpression,
) -> Result<Option<bool>, DocumentError> {
    let document = match read_document(bytes, limits) {
        Ok(document) => document,
        Err(error) => return Err(error),
    };
    match document_ontology(&document, scope) {
        Some(ontology) => Ok(subsumed(&ontology.axioms, sub, sup)),
        None => Ok(None),
    }
}
/// Whether the named individual is an instance of `class` in every model of the
/// document's axioms.
pub fn source_instance_of(
    bytes: &Vec<u8>,
    limits: &DocumentLimits,
    scope: &Vec<u8>,
    individual: &NamedIndividual,
    class: &ClassExpression,
) -> Result<Option<bool>, DocumentError> {
    let document = match read_document(bytes, limits) {
        Ok(document) => document,
        Err(error) => return Err(error),
    };
    match document_ontology(&document, scope) {
        Some(ontology) => Ok(instance_of(&ontology.axioms, individual, class)),
        None => Ok(None),
    }
}
