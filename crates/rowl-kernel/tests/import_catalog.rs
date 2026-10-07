use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::DocumentLimits;
use rowl_kernel::import_catalog::{
    catalog, document_scope, lookup, names, read_source, read_sources, targets, Format, Lookup,
    Source, SourceError,
};
use rowl_kernel::imports::{resolve, DocumentCatalog, DocumentIds, Resolution};
use rowl_kernel::model::{Axiom, Individual, Iri, OntologyIdentity, RawOntology};

fn limits() -> DocumentLimits {
    DocumentLimits {
        tokens: 2000,
        prefixes: 10,
        prefix_value: 100,
        imports: 10,
        iri: 100,
        axioms: 100,
        annotations: AnnotationLimits {
            depth: 2,
            count: 10,
            iri: 100,
            lexical: 100,
        },
        classes: ClassLimits {
            depth: 10,
            count: 10,
            iri: 100,
        },
    }
}

fn iri(value: &str) -> Iri {
    Iri {
        spelling: value.as_bytes().to_vec(),
    }
}

fn functional(text: &str) -> Source {
    Source {
        format: Format::Functional,
        bytes: text.as_bytes().to_vec(),
    }
}

fn turtle(text: &str, base: &str) -> Source {
    Source {
        format: Format::Turtle(base.as_bytes().to_vec()),
        bytes: text.as_bytes().to_vec(),
    }
}

fn ntriples(text: &str) -> Source {
    Source {
        format: Format::NTriples,
        bytes: text.as_bytes().to_vec(),
    }
}

const A: &str = "Prefix(ex:=<http://example.org/>)
Ontology(<http://example.org/a>
 Import(<http://example.org/b>)
 Declaration(Class(ex:A))
 ClassAssertion(ex:A _:x)
)";

const B: &str = "<http://example.org/b> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Ontology> .
<http://example.org/b> <http://www.w3.org/2002/07/owl#imports> <http://example.org/c/1.0> .
<http://example.org/B> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .
";

const C: &str = "Ontology(<http://example.org/c> <http://example.org/c/1.0>
 Import(<http://example.org/a>)
 Declaration(Class(<http://example.org/C>))
)";

const C_TURTLE: &str = "@prefix owl: <http://www.w3.org/2002/07/owl#> .
<c> a owl:Ontology ; owl:versionIRI <c/1.0> ; owl:imports <a> .
<C> a owl:Class .
";

const UNRELATED: &str = "Ontology(<http://example.org/d>
 Import(<http://example.org/nowhere>)
)";

fn ids(list: &DocumentIds) -> Vec<u32> {
    match list {
        DocumentIds::Empty => vec![],
        DocumentIds::Cons(key, tail) => {
            let mut out = vec![*key];
            out.extend(ids(tail));
            out
        }
    }
}

fn rows(list: &DocumentCatalog) -> Vec<(u32, Vec<u32>)> {
    match list {
        DocumentCatalog::Empty => vec![],
        DocumentCatalog::Document {
            key,
            bytes,
            dependencies,
            next,
        } => {
            assert!(bytes.is_empty());
            let mut out = vec![(*key, ids(dependencies))];
            out.extend(rows(next));
            out
        }
    }
}

fn identity(ontology: &RawOntology) -> (Option<Vec<u8>>, Option<Vec<u8>>) {
    match &ontology.identity {
        OntologyIdentity::Anonymous => (None, None),
        OntologyIdentity::Named { ontology, version } => (
            Some(ontology.spelling.clone()),
            version.as_ref().map(|v| v.spelling.clone()),
        ),
    }
}

#[test]
fn scopes_are_the_eight_bytes_of_the_position() {
    assert_eq!(document_scope(0), vec![0; 8]);
    assert_eq!(document_scope(258), vec![2, 1, 0, 0, 0, 0, 0, 0]);
    assert_ne!(document_scope(1), document_scope(256));
}

#[test]
fn headers_come_from_the_verified_readers() {
    let sources = vec![functional(A), ntriples(B), functional(C)];
    let Ok(ontologies) = read_sources(&sources, &limits()) else {
        panic!("every document reads")
    };
    assert_eq!(ontologies.len(), 3);
    assert_eq!(
        identity(&ontologies[0]),
        (Some(b"http://example.org/a".to_vec()), None)
    );
    assert_eq!(
        identity(&ontologies[1]),
        (Some(b"http://example.org/b".to_vec()), None)
    );
    assert_eq!(
        identity(&ontologies[2]),
        (
            Some(b"http://example.org/c".to_vec()),
            Some(b"http://example.org/c/1.0".to_vec())
        )
    );
    let imports: Vec<Vec<Vec<u8>>> = ontologies
        .iter()
        .map(|o| o.imports.iter().map(|i| i.spelling.clone()).collect())
        .collect();
    assert_eq!(
        imports,
        vec![
            vec![b"http://example.org/b".to_vec()],
            vec![b"http://example.org/c/1.0".to_vec()],
            vec![b"http://example.org/a".to_vec()],
        ]
    );
    // The node ID of the first document is an anonymous individual of its scope.
    let anonymous = ontologies[0]
        .axioms
        .iter()
        .find_map(|item| match &item.axiom {
            Axiom::ClassAssertion(_, Individual::Anonymous(a)) => Some(a),
            _ => None,
        })
        .expect("an assertion about _:x");
    assert_eq!(anonymous.scope, document_scope(0));
    assert_eq!(anonymous.label, b"x".to_vec());
}

#[test]
fn ontology_and_version_iris_name_documents() {
    let sources = vec![functional(A), ntriples(B), functional(C)];
    let Ok(ontologies) = read_sources(&sources, &limits()) else {
        panic!("every document reads")
    };
    assert!(names(&ontologies[2].identity, &iri("http://example.org/c")));
    assert!(names(
        &ontologies[2].identity,
        &iri("http://example.org/c/1.0")
    ));
    assert!(!names(
        &ontologies[2].identity,
        &iri("http://example.org/c/")
    ));
    assert!(matches!(
        lookup(&ontologies, &iri("http://example.org/c/1.0")),
        Lookup::Unique(2)
    ));
    assert!(matches!(
        lookup(&ontologies, &iri("http://example.org/nowhere")),
        Lookup::Missing
    ));
    let twice = vec![functional(C), functional(A), functional(C)];
    let Ok(ontologies) = read_sources(&twice, &limits()) else {
        panic!("every document reads")
    };
    assert_eq!(
        ids(&targets(&ontologies, &iri("http://example.org/c"))),
        vec![0, 2]
    );
    assert!(matches!(
        lookup(&ontologies, &iri("http://example.org/c")),
        Lookup::Ambiguous(0, 2)
    ));
}

#[test]
fn catalog_edges_are_the_import_references() {
    let sources = vec![
        functional(A),
        ntriples(B),
        functional(C),
        functional(UNRELATED),
    ];
    let Ok(ontologies) = read_sources(&sources, &limits()) else {
        panic!("every document reads")
    };
    let Some(built) = catalog(&ontologies) else {
        panic!("four documents fit")
    };
    assert_eq!(
        rows(&built),
        vec![(0, vec![1]), (1, vec![2]), (2, vec![0]), (3, vec![])]
    );
    // The cycle a -> b -> c(1.0) -> a resolves once; the unrelated document,
    // whose import names no document, is not in the closure.
    let Resolution::Complete(closure) = resolve(1, built) else {
        panic!("the closure resolves")
    };
    let mut keys: Vec<u32> = rows(&closure).into_iter().map(|(key, _)| key).collect();
    keys.sort_unstable();
    assert_eq!(keys, vec![0, 1, 2]);
}

#[test]
fn the_first_unreadable_document_is_reported() {
    let sources = vec![
        functional(A),
        ntriples("<http://example.org/s> <http://example.org/p> ."),
        functional("Ontology("),
    ];
    match read_sources(&sources, &limits()) {
        Err(unread) => {
            assert_eq!(unread.document, 1);
            assert!(matches!(unread.error, SourceError::Triples(_)));
        }
        Ok(_) => panic!("the second document is not N-Triples"),
    }
    let undeclared =
        ntriples("<http://example.org/s> <http://example.org/p> <http://example.org/o> .\n");
    assert!(matches!(
        read_source(&undeclared, &limits(), &document_scope(0)),
        Err(SourceError::Graph)
    ));
    assert!(matches!(
        read_source(&functional("Ontology("), &limits(), &document_scope(0)),
        Err(SourceError::Functional(_))
    ));
}

#[test]
fn turtle_documents_resolve_against_their_base() {
    let sources = vec![
        functional(A),
        ntriples(B),
        turtle(C_TURTLE, "http://example.org/"),
    ];
    let Ok(ontologies) = read_sources(&sources, &limits()) else {
        panic!("every document reads")
    };
    assert_eq!(
        identity(&ontologies[2]),
        (
            Some(b"http://example.org/c".to_vec()),
            Some(b"http://example.org/c/1.0".to_vec())
        )
    );
    let Some(built) = catalog(&ontologies) else {
        panic!("three documents fit")
    };
    assert_eq!(rows(&built), vec![(0, vec![1]), (1, vec![2]), (2, vec![0])]);
    let relative = vec![turtle(C_TURTLE, "")];
    match read_sources(&relative, &limits()) {
        Err(unread) => {
            assert_eq!(unread.document, 0);
            assert!(matches!(unread.error, SourceError::Turtle(_)));
        }
        Ok(_) => panic!("a relative IRI needs a base"),
    }
}
