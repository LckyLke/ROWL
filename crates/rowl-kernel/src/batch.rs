//! Ordered semantic preparation with caller-supplied source provenance.
//! These identities are retained metadata, not verified parser locations yet.

use crate::model::AnnotatedAxiom;
use crate::prepare::{prepare_axiom, PreparedAnnotatedAxiom};

pub struct AxiomOrigin {
    pub document: u32,
    pub ordinal: u32,
}

pub enum SourceAxioms {
    Empty,
    Cons {
        origin: AxiomOrigin,
        axiom: Box<AnnotatedAxiom>,
        next: Box<SourceAxioms>,
    },
}

pub enum PreparedAxioms {
    Empty,
    Cons {
        origin: AxiomOrigin,
        axiom: Box<PreparedAnnotatedAxiom>,
        next: Box<PreparedAxioms>,
    },
}

/// Prepare every axiom exactly once, retaining order, provenance and annotations.
pub fn prepare_all(source: SourceAxioms) -> PreparedAxioms {
    match source {
        SourceAxioms::Empty => PreparedAxioms::Empty,
        SourceAxioms::Cons {
            origin,
            axiom,
            next,
        } => PreparedAxioms::Cons {
            origin,
            axiom: Box::new(prepare_axiom(*axiom)),
            next: Box::new(prepare_all(*next)),
        },
    }
}
