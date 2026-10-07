//! Frontend stages for immutable input snapshots.
//!
//! The stages are compiled and verified inside `rowl-kernel`, so that parsing,
//! document assembly and reasoning share one extraction; this crate re-exports
//! them under their historical paths. Import topology operates on document
//! symbols and explicitly supplied import metadata. This is not yet a complete
//! OWL document parser.

pub use rowl_kernel::compiled;
pub use rowl_kernel::encoding;
pub use rowl_kernel::functional;
pub use rowl_kernel::functional_annotation_axioms;
pub use rowl_kernel::functional_annotations;
pub use rowl_kernel::functional_assertions;
pub use rowl_kernel::functional_class_axioms;
pub use rowl_kernel::functional_classes;
pub use rowl_kernel::functional_data_axioms;
pub use rowl_kernel::functional_declarations;
pub use rowl_kernel::functional_document;
pub use rowl_kernel::functional_header;
pub use rowl_kernel::functional_individuals;
pub use rowl_kernel::functional_iris;
pub use rowl_kernel::functional_lexer;
pub use rowl_kernel::functional_literals;
pub use rowl_kernel::functional_model;
pub use rowl_kernel::functional_names;
pub use rowl_kernel::functional_payload;
pub use rowl_kernel::functional_prefixes;
pub use rowl_kernel::functional_property_axioms;
pub use rowl_kernel::functional_ranges;
pub use rowl_kernel::imports;
pub use rowl_kernel::iri;
pub use rowl_kernel::langtag;
pub use rowl_kernel::longest;
pub use rowl_kernel::names;
pub use rowl_kernel::ntriples;
pub use rowl_kernel::prefixes;
pub use rowl_kernel::rdf;
pub use rowl_kernel::regular;
pub use rowl_kernel::snapshot;
pub use rowl_kernel::turtle;
pub use rowl_kernel::unicode;
