//! ROWL research prototype; no full OWL 2 DL entry point exists yet.

/// Internal experiments. Not a stable OWL reasoning API.
pub mod experimental {
    pub use rowl_frontend::encoding;
    pub use rowl_frontend::functional;
    pub use rowl_frontend::functional_annotations;
    pub use rowl_frontend::functional_header;
    pub use rowl_frontend::functional_iris;
    pub use rowl_frontend::functional_lexer;
    pub use rowl_frontend::functional_literals;
    pub use rowl_frontend::functional_names;
    pub use rowl_frontend::functional_payload;
    pub use rowl_frontend::functional_prefixes;
    pub use rowl_frontend::imports;
    pub use rowl_frontend::iri;
    pub use rowl_frontend::langtag;
    pub use rowl_frontend::longest;
    pub use rowl_frontend::names;
    pub use rowl_frontend::ntriples;
    pub use rowl_frontend::prefixes;
    pub use rowl_frontend::rdf;
    pub use rowl_frontend::regular;
    pub use rowl_frontend::snapshot;
    pub use rowl_frontend::unicode;
    pub use rowl_kernel::anonymous;
    pub use rowl_kernel::anonymous_boundary;
    pub use rowl_kernel::anonymous_graph;
    pub use rowl_kernel::anonymous_multiplicity;
    pub use rowl_kernel::anonymous_restrictions;
    pub use rowl_kernel::arity;
    pub use rowl_kernel::assertion_equality;
    pub use rowl_kernel::axiom_equality;
    pub use rowl_kernel::axiom_set;
    pub use rowl_kernel::batch;
    pub use rowl_kernel::builtins;
    pub use rowl_kernel::class_equality;
    pub use rowl_kernel::collection;
    pub use rowl_kernel::datatype_definitions;
    pub use rowl_kernel::datatype_order;
    pub use rowl_kernel::datatype_positions;
    pub use rowl_kernel::datatype_restrictions;
    pub use rowl_kernel::decimal;
    pub use rowl_kernel::indexing;
    pub use rowl_kernel::keys;
    pub use rowl_kernel::model;
    pub use rowl_kernel::prepare;
    pub use rowl_kernel::probes::Natural;
    pub use rowl_kernel::prototype::{decide, evaluate, Atom, Decision, Formula, Valuation};
    pub use rowl_kernel::range_equality;
    pub use rowl_kernel::role_order;
    pub use rowl_kernel::roles;
    pub use rowl_kernel::symbols;
    pub use rowl_kernel::topdata;
    pub use rowl_kernel::typing;
    pub use rowl_kernel::vocabulary;
}
