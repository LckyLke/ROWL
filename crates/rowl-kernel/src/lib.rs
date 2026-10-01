//! Internal reasoning kernel. Full OWL 2 DL is not implemented yet.
//!
//! The prototype is deliberately isolated: its finite Boolean interpretations
//! do not provide a decision procedure for arbitrary OWL ontologies.

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
