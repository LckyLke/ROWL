//! Import closures, first part: the headers of a catalog of documents and the
//! catalog of their imports (OWL 2 Structural Specification §3.2 and §3.4).
//!
//! The caller supplies every document, as bytes with their syntax; nothing is
//! fetched. Each document is read whole by its verified reader: Functional
//! Syntax by `source_reasoning::source_ontology`, N-Triples by `ntriples::read`
//! and Turtle by `turtle::read`, each followed by the reverse RDF mapping
//! `rdf_mapping::map_graph`. Its node IDs or blank nodes become anonymous
//! individuals of a scope of its own, the eight bytes of its position in the
//! catalog, so that the anonymous individuals of different documents stay
//! apart (§5.6.2). The ontology IRI, version IRI and import IRIs of a document
//! are those of its read ontology.
//!
//! An import IRI names a document when it is the document's ontology IRI or its
//! version IRI, compared byte by byte. The catalog lists every document under
//! its position, with the documents its import IRIs name, import by import, so
//! `imports::resolve` computes the import closure over it.
#![allow(clippy::ptr_arg, clippy::question_mark)]

use crate::dl_validity::same_bytes;
use crate::functional_document::{DocumentError, DocumentLimits};
use crate::imports::{DocumentCatalog, DocumentIds};
use crate::model::{Iri, OntologyIdentity, RawOntology};
use crate::ntriples::{read, ReadError, ReadResult};
use crate::rdf::RawGraph;
use crate::rdf_mapping::map_graph;
use crate::source_reasoning::source_ontology;
use crate::turtle;

/// The syntax of a document.
pub enum Format {
    /// OWL 2 Functional-Style Syntax.
    Functional,
    /// An N-Triples document of the RDF graph of an ontology.
    NTriples,
    /// A Turtle document of the RDF graph of an ontology, whose relative IRIs
    /// resolve against this base IRI until the document declares its own.
    Turtle(Vec<u8>),
}

/// A document of the catalog: its syntax and its bytes.
pub struct Source {
    pub format: Format,
    pub bytes: Vec<u8>,
}

/// Why a document could not be read.
pub enum SourceError {
    /// The verified Functional Syntax reader rejected the document.
    Functional(DocumentError),
    /// A read Functional Syntax document has no raw OWL model; the reader's
    /// proofs exclude this.
    Unmapped,
    /// The verified N-Triples reader rejected the document.
    Triples(ReadError),
    /// The verified Turtle reader rejected the document.
    Turtle(turtle::ReadError),
    /// The graph is not the RDF mapping of an ontology that the verified
    /// reverse mapping reads.
    Graph,
}

/// The first document of a catalog that could not be read.
pub struct Unread {
    pub document: usize,
    pub error: SourceError,
}

/// How many documents an import IRI names.
pub enum Lookup {
    /// No document has the IRI as its ontology or version IRI.
    Missing,
    /// Exactly the document at this position has it.
    Unique(u32),
    /// The first two of several documents that have it.
    Ambiguous(u32, u32),
}

fn scope_bytes(value: usize, count: usize, mut out: Vec<u8>) -> Vec<u8> {
    if count < 8 {
        out.push((value % 256) as u8);
        scope_bytes(value / 256, count + 1, out)
    } else {
        out
    }
}

/// The scope of the anonymous individuals of the document at `index`: the
/// eight bytes of the position, least significant first.
pub fn document_scope(index: usize) -> Vec<u8> {
    scope_bytes(index, 0, Vec::new())
}

/// The ontology of a Functional Syntax document.
fn read_functional(
    bytes: &Vec<u8>,
    limits: &DocumentLimits,
    scope: &Vec<u8>,
) -> Result<RawOntology, SourceError> {
    match source_ontology(bytes, limits, scope) {
        Ok(Some(ontology)) => Ok(ontology),
        Ok(None) => Err(SourceError::Unmapped),
        Err(error) => Err(SourceError::Functional(error)),
    }
}

/// The ontology an RDF graph is the mapping of.
fn graph_ontology(graph: &RawGraph) -> Result<RawOntology, SourceError> {
    match map_graph(graph) {
        Some(mapped) => Ok(mapped.ontology),
        None => Err(SourceError::Graph),
    }
}

/// The ontology of an N-Triples document.
fn read_ntriples(bytes: &Vec<u8>, scope: &Vec<u8>) -> Result<RawOntology, SourceError> {
    match read(bytes, scope) {
        ReadResult::Graph(graph) => graph_ontology(&graph),
        ReadResult::Error(error) => Err(SourceError::Triples(error)),
    }
}

/// The ontology of a Turtle document read against `base`.
fn read_turtle(
    bytes: &Vec<u8>,
    scope: &Vec<u8>,
    base: &Vec<u8>,
) -> Result<RawOntology, SourceError> {
    match turtle::read(bytes, scope, base) {
        turtle::ReadResult::Graph(graph) => graph_ontology(&graph),
        turtle::ReadResult::Error(error) => Err(SourceError::Turtle(error)),
    }
}

/// Read one document with its verified reader; its node IDs or blank nodes
/// become anonymous individuals of `scope`.
pub fn read_source(
    source: &Source,
    limits: &DocumentLimits,
    scope: &Vec<u8>,
) -> Result<RawOntology, SourceError> {
    match &source.format {
        Format::Functional => read_functional(&source.bytes, limits, scope),
        Format::NTriples => read_ntriples(&source.bytes, scope),
        Format::Turtle(base) => read_turtle(&source.bytes, scope, base),
    }
}

/// The document at `index`, in the scope of its position.
fn read_at(
    sources: &Vec<Source>,
    limits: &DocumentLimits,
    index: usize,
) -> Result<RawOntology, SourceError> {
    read_source(&sources[index], limits, &document_scope(index))
}

/// The ontologies of `sources[index..]` after `out`.
fn read_from(
    sources: &Vec<Source>,
    limits: &DocumentLimits,
    index: usize,
    mut out: Vec<RawOntology>,
) -> Result<Vec<RawOntology>, Unread> {
    if index < sources.len() {
        match read_at(sources, limits, index) {
            Ok(ontology) => {
                out.push(ontology);
                read_from(sources, limits, index + 1, out)
            }
            Err(error) => Err(Unread {
                document: index,
                error,
            }),
        }
    } else {
        Ok(out)
    }
}

/// Read every document of the catalog, in order, each in the scope of its
/// position; the first document that cannot be read is the error.
pub fn read_sources(
    sources: &Vec<Source>,
    limits: &DocumentLimits,
) -> Result<Vec<RawOntology>, Unread> {
    read_from(sources, limits, 0, Vec::new())
}

/// Whether the import IRI names the ontology: it is its ontology IRI or its
/// version IRI (§3.2, §3.4).
pub fn names(identity: &OntologyIdentity, iri: &Iri) -> bool {
    match identity {
        OntologyIdentity::Anonymous => false,
        OntologyIdentity::Named { ontology, version } => {
            if same_bytes(&ontology.spelling, &iri.spelling) {
                true
            } else {
                match version {
                    Some(version) => same_bytes(&version.spelling, &iri.spelling),
                    None => false,
                }
            }
        }
    }
}

/// The positions of the documents of `ontologies[index..]` that the IRI names,
/// in order.
fn targets_from(ontologies: &Vec<RawOntology>, iri: &Iri, index: usize) -> DocumentIds {
    if index < ontologies.len() {
        let rest = targets_from(ontologies, iri, index + 1);
        if names(&ontologies[index].identity, iri) {
            DocumentIds::Cons(index as u32, Box::new(rest))
        } else {
            rest
        }
    } else {
        DocumentIds::Empty
    }
}

/// The positions of the documents that the IRI names, in order.
pub fn targets(ontologies: &Vec<RawOntology>, iri: &Iri) -> DocumentIds {
    targets_from(ontologies, iri, 0)
}

/// Whether the IRI names no document, exactly one or several.
pub fn lookup(ontologies: &Vec<RawOntology>, iri: &Iri) -> Lookup {
    match targets_from(ontologies, iri, 0) {
        DocumentIds::Empty => Lookup::Missing,
        DocumentIds::Cons(first, rest) => match *rest {
            DocumentIds::Empty => Lookup::Unique(first),
            DocumentIds::Cons(second, _) => Lookup::Ambiguous(first, second),
        },
    }
}

fn append(left: DocumentIds, right: DocumentIds) -> DocumentIds {
    match left {
        DocumentIds::Empty => right,
        DocumentIds::Cons(key, tail) => DocumentIds::Cons(key, Box::new(append(*tail, right))),
    }
}

/// The documents the IRIs of `iris[index..]` name, import by import.
fn dependencies_from(ontologies: &Vec<RawOntology>, iris: &Vec<Iri>, index: usize) -> DocumentIds {
    if index < iris.len() {
        append(
            targets_from(ontologies, &iris[index], 0),
            dependencies_from(ontologies, iris, index + 1),
        )
    } else {
        DocumentIds::Empty
    }
}

/// The catalog of `ontologies[index..]`: each document under its position,
/// without bytes, with the documents its import IRIs name.
fn catalog_from(ontologies: &Vec<RawOntology>, index: usize) -> DocumentCatalog {
    if index < ontologies.len() {
        DocumentCatalog::Document {
            key: index as u32,
            bytes: Vec::new(),
            dependencies: dependencies_from(ontologies, &ontologies[index].imports, 0),
            next: Box::new(catalog_from(ontologies, index + 1)),
        }
    } else {
        DocumentCatalog::Empty
    }
}

/// The catalog of the documents for `imports::resolve`; `None` when there are
/// more documents than `u32` keys.
pub fn catalog(ontologies: &Vec<RawOntology>) -> Option<DocumentCatalog> {
    if ontologies.len() <= u32::MAX as usize {
        Some(catalog_from(ontologies, 0))
    } else {
        None
    }
}
