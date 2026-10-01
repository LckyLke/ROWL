//! Frontend stages for immutable input snapshots.
//!
//! Import topology operates on document symbols and explicitly supplied import
//! metadata. Exact byte-key interning and complete IRI lexical validation are
//! proved separately. Their composition with format parsers remains pending.
//! This is not yet an OWL document parser.

pub mod imports;
pub mod snapshot;

pub mod unicode;

pub mod rdf;

pub mod regular;

pub mod iri;

pub mod encoding;
pub mod functional;
pub mod functional_annotations;
pub mod functional_declarations;
pub mod functional_header;
pub mod functional_iris;
pub mod functional_lexer;
pub mod functional_literals;
pub mod functional_names;
pub mod functional_payload;
pub mod functional_prefixes;
pub mod langtag;
pub mod longest;
pub mod names;
pub mod ntriples;
pub mod prefixes;
