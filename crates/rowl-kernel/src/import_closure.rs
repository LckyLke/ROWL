//! Import closures, second part: the import closure of a root document and
//! its axiom closure (OWL 2 Structural Specification §3.4).
//!
//! `assemble` takes the ontologies of a catalog, each read in the scope of its
//! position (`import_catalog::read_sources`), and a root position. The catalog
//! of `import_catalog::catalog` lists the documents every import IRI names, and
//! `imports::resolve` computes the documents reachable from the root over it:
//! the import closure. Every import IRI of a document of the closure must name
//! exactly one document, by its ontology IRI or version IRI; the first that
//! names none or several is the error, naming the IRI. Every anonymous
//! individual of a document of the closure must have the document's scope,
//! which keeps the anonymous individuals of different documents apart
//! (§5.6.2). The closure then holds the root's ontology IRI, version IRI and
//! imports, and the ontology annotations and the axioms of every document of
//! the closure in catalog order, each axiom with its document and position
//! (its provenance). The documents' records are moved, not copied.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::mem_replace_with_default
)] // `mem::take` lacks a model in the pinned extraction.

use crate::anonymous_scopes::scoped_ontology;
use crate::functional_document::DocumentLimits;
use crate::import_catalog::{
    catalog, document_scope, lookup, read_sources, Lookup, Source, Unread,
};
use crate::imports::{resolve, DocumentCatalog, Resolution};
use crate::model::{
    AnnotatedAxiom, Annotation, AnnotationProperty, AnnotationValue, Axiom, Class, Entity, Iri,
    OntologyIdentity, RawOntology,
};
use crate::nnf::copy_iri;

/// Where an axiom of a closure comes from: its document and its position among
/// the document's axioms.
pub struct Origin {
    pub document: usize,
    pub position: usize,
}

/// The axiom closure of an import closure.
pub struct Closure {
    /// The positions of the documents of the import closure, in catalog order.
    pub documents: Vec<usize>,
    /// The root's identity and imports, and the ontology annotations and axioms
    /// of every document of the closure, in catalog order.
    pub ontology: RawOntology,
    /// The document and position of every axiom, in the axioms' order.
    pub origins: Vec<Origin>,
}

/// Why there is no closure.
pub enum ClosureError {
    /// A document could not be read.
    Unread(Unread),
    /// The root is not a position of the catalog.
    NoRoot,
    /// There are more documents than `u32` keys.
    TooManyDocuments,
    /// The resolver found a missing or repeated key; the catalog rules both out.
    Unresolved,
    /// A document of the import closure imports an IRI that is no document's
    /// ontology IRI or version IRI.
    MissingImport { document: usize, iri: Iri },
    /// A document of the import closure imports an IRI that several documents
    /// have as their ontology IRI or version IRI; the first two are given.
    AmbiguousImport {
        document: usize,
        iri: Iri,
        first: usize,
        second: usize,
    },
    /// A document of the closure has an anonymous individual outside its scope;
    /// documents read by `read_sources` have none.
    OutOfScope { document: usize },
    /// The closure has more axioms or ontology annotations than a vector holds.
    TooLarge,
}

fn falses(count: usize, mut out: Vec<bool>) -> Vec<bool> {
    if out.len() < count {
        out.push(false);
        falses(count, out)
    } else {
        out
    }
}

/// `included` with the positions of the closure's keys set.
fn mark(closure: &DocumentCatalog, mut included: Vec<bool>) -> Vec<bool> {
    match closure {
        DocumentCatalog::Empty => included,
        DocumentCatalog::Document { key, next, .. } => {
            let index = *key as usize;
            if index < included.len() {
                included[index] = true;
            }
            mark(next, included)
        }
    }
}

fn included_at(included: &Vec<bool>, index: usize) -> bool {
    if index < included.len() {
        included[index]
    } else {
        false
    }
}

/// The first import IRI of `iris[index..]` that names no document or
/// several.
fn unresolved_import(
    ontologies: &Vec<RawOntology>,
    iris: &Vec<Iri>,
    document: usize,
    index: usize,
) -> Option<ClosureError> {
    if index < iris.len() {
        match lookup(ontologies, &iris[index]) {
            Lookup::Unique(_) => unresolved_import(ontologies, iris, document, index + 1),
            Lookup::Missing => Some(ClosureError::MissingImport {
                document,
                iri: copy_iri(&iris[index]),
            }),
            Lookup::Ambiguous(first, second) => Some(ClosureError::AmbiguousImport {
                document,
                iri: copy_iri(&iris[index]),
                first: first as usize,
                second: second as usize,
            }),
        }
    } else {
        None
    }
}

/// The first unresolved import of the included documents of
/// `ontologies[index..]`.
fn check_imports(
    ontologies: &Vec<RawOntology>,
    included: &Vec<bool>,
    index: usize,
) -> Option<ClosureError> {
    if index < ontologies.len() {
        if included_at(included, index) {
            match unresolved_import(ontologies, &ontologies[index].imports, index, 0) {
                Some(error) => Some(error),
                None => check_imports(ontologies, included, index + 1),
            }
        } else {
            check_imports(ontologies, included, index + 1)
        }
    } else {
        None
    }
}

/// The first included document of `ontologies[index..]` with an anonymous
/// individual outside the scope of its position.
fn check_scopes(
    ontologies: &Vec<RawOntology>,
    included: &Vec<bool>,
    index: usize,
) -> Option<usize> {
    if index < ontologies.len() {
        if included_at(included, index) {
            if scoped_ontology(&document_scope(index), &ontologies[index]) {
                check_scopes(ontologies, included, index + 1)
            } else {
                Some(index)
            }
        } else {
            check_scopes(ontologies, included, index + 1)
        }
    } else {
        None
    }
}

fn empty_ontology() -> RawOntology {
    RawOntology {
        identity: OntologyIdentity::Anonymous,
        imports: Vec::new(),
        annotations: Vec::new(),
        axioms: Vec::new(),
    }
}

fn placeholder_axiom() -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: Vec::new(),
        axiom: Axiom::Declaration(Entity::Class(Class {
            iri: Iri {
                spelling: Vec::new(),
            },
        })),
    }
}

fn placeholder_annotation() -> Annotation {
    Annotation {
        annotations: Vec::new(),
        property: AnnotationProperty {
            iri: Iri {
                spelling: Vec::new(),
            },
        },
        value: AnnotationValue::Iri(Iri {
            spelling: Vec::new(),
        }),
    }
}

/// Move `source[position..]` to the end of `out`; `None` when `out` is full.
fn move_annotations(
    mut source: Vec<Annotation>,
    position: usize,
    mut out: Vec<Annotation>,
) -> Option<Vec<Annotation>> {
    if position < source.len() {
        if out.len() < usize::MAX {
            let item = std::mem::replace(&mut source[position], placeholder_annotation());
            out.push(item);
            move_annotations(source, position + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}

/// Move the axioms `source[position..]` of the document at `document` to the
/// end of `out`, each with its origin; `None` when `out` is full.
fn move_axioms(
    mut source: Vec<AnnotatedAxiom>,
    position: usize,
    document: usize,
    mut out: Vec<AnnotatedAxiom>,
    mut origins: Vec<Origin>,
) -> Option<(Vec<AnnotatedAxiom>, Vec<Origin>)> {
    if position < source.len() {
        if out.len() < usize::MAX {
            let item = std::mem::replace(&mut source[position], placeholder_axiom());
            out.push(item);
            origins.push(Origin { document, position });
            move_axioms(source, position + 1, document, out, origins)
        } else {
            None
        }
    } else {
        Some((out, origins))
    }
}

/// The documents, ontology annotations, axioms and origins gathered so far.
struct Gathered {
    documents: Vec<usize>,
    annotations: Vec<Annotation>,
    axioms: Vec<AnnotatedAxiom>,
    origins: Vec<Origin>,
}

/// Move the ontology annotations and axioms of the document at `index` to the
/// end of `out`.
fn gather_one(document: RawOntology, index: usize, mut out: Gathered) -> Option<Gathered> {
    out.documents.push(index);
    match move_annotations(document.annotations, 0, out.annotations) {
        Some(annotations) => {
            match move_axioms(document.axioms, 0, index, out.axioms, out.origins) {
                Some((axioms, origins)) => Some(Gathered {
                    documents: out.documents,
                    annotations,
                    axioms,
                    origins,
                }),
                None => None,
            }
        }
        None => None,
    }
}

/// Gather the included documents of `ontologies[index..]`, in order.
fn gather(
    mut ontologies: Vec<RawOntology>,
    included: &Vec<bool>,
    index: usize,
    out: Gathered,
) -> Option<Gathered> {
    if index < ontologies.len() {
        if included_at(included, index) {
            let document = std::mem::replace(&mut ontologies[index], empty_ontology());
            match gather_one(document, index, out) {
                Some(out) => gather(ontologies, included, index + 1, out),
                None => None,
            }
        } else {
            gather(ontologies, included, index + 1, out)
        }
    } else {
        Some(out)
    }
}

/// The root's identity and imports, taken out of the catalog.
fn take_header(
    mut ontologies: Vec<RawOntology>,
    root: usize,
) -> (Vec<RawOntology>, OntologyIdentity, Vec<Iri>) {
    let identity = std::mem::replace(&mut ontologies[root].identity, OntologyIdentity::Anonymous);
    let iris = std::mem::replace(&mut ontologies[root].imports, Vec::new());
    (ontologies, identity, iris)
}

/// Check the imports and scopes of the included documents and gather them.
fn finish(
    ontologies: Vec<RawOntology>,
    included: &Vec<bool>,
    root: usize,
) -> Result<Closure, ClosureError> {
    match check_imports(&ontologies, included, 0) {
        Some(error) => Err(error),
        None => match check_scopes(&ontologies, included, 0) {
            Some(document) => Err(ClosureError::OutOfScope { document }),
            None => {
                let (ontologies, identity, iris) = take_header(ontologies, root);
                let start = Gathered {
                    documents: Vec::new(),
                    annotations: Vec::new(),
                    axioms: Vec::new(),
                    origins: Vec::new(),
                };
                match gather(ontologies, included, 0, start) {
                    Some(out) => Ok(Closure {
                        documents: out.documents,
                        ontology: RawOntology {
                            identity,
                            imports: iris,
                            annotations: out.annotations,
                            axioms: out.axioms,
                        },
                        origins: out.origins,
                    }),
                    None => Err(ClosureError::TooLarge),
                }
            }
        },
    }
}

/// The axiom closure of the import closure of the document at `root`, from the
/// ontologies of a catalog read by `import_catalog::read_sources`.
pub fn assemble(ontologies: Vec<RawOntology>, root: usize) -> Result<Closure, ClosureError> {
    if root < ontologies.len() {
        match catalog(&ontologies) {
            Some(built) => match resolve(root as u32, built) {
                Resolution::Complete(closure) => {
                    let included = mark(&closure, falses(ontologies.len(), Vec::new()));
                    finish(ontologies, &included, root)
                }
                _ => Err(ClosureError::Unresolved),
            },
            None => Err(ClosureError::TooManyDocuments),
        }
    } else {
        Err(ClosureError::NoRoot)
    }
}

/// Read every document of a catalog with its verified reader, each in the
/// scope of its position, and assemble the axiom closure of the import closure
/// of the document at `root`. Nothing is fetched: an import IRI that names no
/// document of the catalog is an error.
pub fn source_closure(
    sources: &Vec<Source>,
    root: usize,
    limits: &DocumentLimits,
) -> Result<Closure, ClosureError> {
    match read_sources(sources, limits) {
        Ok(ontologies) => assemble(ontologies, root),
        Err(unread) => Err(ClosureError::Unread(unread)),
    }
}
