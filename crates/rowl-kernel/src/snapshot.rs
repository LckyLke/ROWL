//! Compose indexed closure discovery with byte validation of reachable sources.
//! Import metadata remains explicit; this is not an OWL document parser.

use crate::imports::{resolve, DocumentCatalog, Resolution};
use crate::unicode::{read_text, TextError, TextScan};

pub enum SourceCheck {
    Valid,
    Invalid { document: u32, error: TextError },
}

pub enum TextResolution {
    Complete(DocumentCatalog),
    MissingDocument(u32),
    DuplicateDocument(u32),
    InvalidText { document: u32, error: TextError },
}

/// Check sources in catalog order, returning the first document/text error.
pub fn check_sources(catalog: &DocumentCatalog) -> SourceCheck {
    match catalog {
        DocumentCatalog::Empty => SourceCheck::Valid,
        DocumentCatalog::Document {
            key, bytes, next, ..
        } => match read_text(bytes) {
            TextScan::Valid(_) => check_sources(next),
            TextScan::Invalid(error) => SourceCheck::Invalid {
                document: *key,
                error,
            },
        },
    }
}

/// Resolve the supplied topology, then validate only reachable document bytes.
/// A successful result retains exactly the resolver's verbatim records/order.
pub fn resolve_texts(root: u32, catalog: DocumentCatalog) -> TextResolution {
    match resolve(root, catalog) {
        Resolution::MissingDocument(key) => TextResolution::MissingDocument(key),
        Resolution::DuplicateDocument(key) => TextResolution::DuplicateDocument(key),
        Resolution::Complete(closure) => match check_sources(&closure) {
            SourceCheck::Valid => TextResolution::Complete(closure),
            SourceCheck::Invalid { document, error } => {
                TextResolution::InvalidText { document, error }
            }
        },
    }
}
