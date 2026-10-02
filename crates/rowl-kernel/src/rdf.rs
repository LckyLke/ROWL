//! Raw RDF 1.1 terms/datasets and explicit, lossless graph selection.
//!
//! Term positions are enforced by constructors. UTF-8, absolute IRI grammar,
//! language-tag well-formedness and parser-assigned blank-node scopes are not
//! certified by these raw structures. Triple vectors denote sets while keeping
//! source order and repetitions. No RDF/OWL byte parser or serializer is implied.

#![allow(clippy::ptr_arg)]

pub struct RdfIri {
    pub spelling: Vec<u8>,
}

/// Scope/label are opaque internal identity keys, not semantic names. A parser
/// must assign one scope to the dataset, rather than a new scope to each graph.
pub struct BlankNode {
    pub scope: Vec<u8>,
    pub label: Vec<u8>,
}

pub enum LiteralKind {
    Datatype(RdfIri),
    /// The datatype is implicitly rdf:langString; the raw tag is unvalidated.
    Language(Vec<u8>),
}

pub struct RdfLiteral {
    pub lexical: Vec<u8>,
    pub kind: LiteralKind,
}

pub enum Subject {
    Iri(RdfIri),
    Blank(BlankNode),
}

pub enum Object {
    Iri(RdfIri),
    Blank(BlankNode),
    Literal(RdfLiteral),
}

pub struct Triple {
    pub subject: Subject,
    pub predicate: RdfIri,
    pub object: Object,
}

pub struct RawGraph {
    pub triples: Vec<Triple>,
}

pub enum GraphName {
    Iri(RdfIri),
    Blank(BlankNode),
}

/// Raw named-graph records can contain duplicate names. Selection checks this
/// before returning any graph, including when the default graph is requested.
pub enum NamedGraphs {
    Empty,
    Entry {
        name: GraphName,
        graph: RawGraph,
        next: Box<NamedGraphs>,
    },
}

/// Empty named graphs are retained as records and differ from missing graphs.
pub struct RawDataset {
    pub default: RawGraph,
    pub named: NamedGraphs,
}

pub enum GraphChoice {
    Default,
    Named(GraphName),
}

/// Keeps an immutable borrow of the entire input alongside the chosen graph.
/// Only `select_graph` constructs selections; no implicit graph union occurs.
pub struct DatasetSelection<'a> {
    dataset: &'a RawDataset,
    graph: &'a RawGraph,
}

pub enum SelectionResult<'a> {
    Selected(DatasetSelection<'a>),
    MissingGraph,
    DuplicateGraphName(&'a GraphName),
}

fn equal_from(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> bool {
    if index >= left.len() {
        true
    } else if left[index] != right[index] {
        false
    } else {
        equal_from(left, right, index + 1)
    }
}

fn same_bytes(left: &Vec<u8>, right: &Vec<u8>) -> bool {
    if left.len() != right.len() {
        false
    } else {
        equal_from(left, right, 0)
    }
}

/// Exact structural name identity; IRIs and blank nodes remain distinct.
pub fn same_graph_name(left: &GraphName, right: &GraphName) -> bool {
    match (left, right) {
        (GraphName::Iri(left), GraphName::Iri(right)) => {
            same_bytes(&left.spelling, &right.spelling)
        }
        (GraphName::Blank(left), GraphName::Blank(right)) => {
            same_bytes(&left.scope, &right.scope) && same_bytes(&left.label, &right.label)
        }
        _ => false,
    }
}

fn find_graph<'a>(graphs: &'a NamedGraphs, name: &GraphName) -> Option<&'a RawGraph> {
    match graphs {
        NamedGraphs::Empty => None,
        NamedGraphs::Entry {
            name: here,
            graph,
            next,
        } => {
            if same_graph_name(here, name) {
                Some(graph)
            } else {
                find_graph(next, name)
            }
        }
    }
}

fn first_duplicate(graphs: &NamedGraphs) -> Option<&GraphName> {
    match graphs {
        NamedGraphs::Empty => None,
        NamedGraphs::Entry { name, next, .. } => {
            if find_graph(next, name).is_some() {
                Some(name)
            } else {
                first_duplicate(next)
            }
        }
    }
}

/// The caller must explicitly request the default graph or one exact name.
/// Repeated graph names invalidate the raw dataset; absence differs from empty.
pub fn select_graph<'a>(dataset: &'a RawDataset, choice: &GraphChoice) -> SelectionResult<'a> {
    if let Some(name) = first_duplicate(&dataset.named) {
        return SelectionResult::DuplicateGraphName(name);
    }
    let graph = match choice {
        GraphChoice::Default => &dataset.default,
        GraphChoice::Named(name) => match find_graph(&dataset.named, name) {
            Some(graph) => graph,
            None => return SelectionResult::MissingGraph,
        },
    };
    SelectionResult::Selected(DatasetSelection { dataset, graph })
}

pub fn selected_graph<'a>(selection: &DatasetSelection<'a>) -> &'a RawGraph {
    selection.graph
}

pub fn original_dataset<'a>(selection: &DatasetSelection<'a>) -> &'a RawDataset {
    selection.dataset
}
