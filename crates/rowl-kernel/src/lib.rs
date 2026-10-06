//! Internal reasoning kernel and verified frontend stages. Full OWL 2 DL is not
//! implemented yet.
//!
//! The frontend stages (text, IRI, RDF and Functional Syntax reading) live in
//! this crate so that parsing, document assembly and reasoning are extracted to
//! one Lean development; `rowl-frontend` re-exports them under their historical
//! paths. The prototype is deliberately isolated: its finite Boolean
//! interpretations do not provide a decision procedure for arbitrary OWL
//! ontologies.

pub mod batch;
pub mod collection;
pub mod model;
pub mod prepare;
pub mod probes;
pub mod prototype;
pub mod typing;

pub mod symbols;

pub mod indexing;

pub mod builtins;

pub mod vocabulary;

pub mod anonymous;
pub mod topdata;

pub mod roles;

pub mod role_order;

pub mod anonymous_graph;

pub mod anonymous_multiplicity;
pub mod assertion_equality;

pub mod anonymous_boundary;

pub mod anonymous_restrictions;

pub mod range_equality;

pub mod datatype_definitions;

pub mod datatype_order;

pub mod datatype_restrictions;

pub mod datatype_positions;

pub mod class_equality;

pub mod keys;

pub mod arity;

pub mod axiom_equality;

pub mod axiom_set;

pub mod decimal;

pub mod nnf;

pub mod tableau;

pub mod role_box;

pub mod tbox;

pub mod abox;

pub mod alc_ontology;

pub mod concepts;

pub mod hierarchy;

pub mod concept_table;

pub mod completion;

pub mod forest;

pub mod role_chains;

pub mod universal;

pub mod shi_ontology;

pub mod datatypes;

pub mod data_ontology;

pub mod source_reasoning;

// Frontend stages: text, IRI, RDF and Functional Syntax reading.
pub mod encoding;
pub mod functional;
pub mod functional_annotation_axioms;
pub mod functional_annotations;
pub mod functional_assertions;
pub mod functional_class_axioms;
pub mod functional_classes;
pub mod functional_data_axioms;
pub mod functional_declarations;
pub mod functional_document;
pub mod functional_header;
pub mod functional_individuals;
pub mod functional_iris;
pub mod functional_lexer;
pub mod functional_literals;
pub mod functional_model;
pub mod functional_names;
pub mod functional_payload;
pub mod functional_prefixes;
pub mod functional_property_axioms;
pub mod functional_ranges;
pub mod imports;
pub mod iri;
pub mod langtag;
pub mod longest;
pub mod names;
pub mod ntriples;
pub mod prefixes;
pub mod rdf;
pub mod rdf_mapping;
pub mod references;
pub mod regular;

pub mod compiled;

pub mod classification;
pub mod saturation;
pub mod snapshot;
pub mod unicode;
