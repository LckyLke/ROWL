use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::DocumentLimits;
use rowl_kernel::import_catalog::{document_scope, read_sources, Format, Source};
use rowl_kernel::import_closure::{assemble, source_closure, Closure, ClosureError};
use rowl_kernel::model::{
    AnnotatedAxiom, AnonymousIndividual, Axiom, Class, ClassExpression, Entity, Individual, Iri,
    OntologyIdentity, RawOntology,
};

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

fn functional(text: &str) -> Source {
    Source {
        format: Format::Functional,
        bytes: text.as_bytes().to_vec(),
    }
}

fn ntriples(text: &str) -> Source {
    Source {
        format: Format::NTriples,
        bytes: text.as_bytes().to_vec(),
    }
}

fn spelling(iri: &Iri) -> String {
    String::from_utf8(iri.spelling.clone()).unwrap()
}

/// The declared classes of the closure's axioms, in order.
fn declared(closure: &Closure) -> Vec<String> {
    closure
        .ontology
        .axioms
        .iter()
        .filter_map(|item| match &item.axiom {
            Axiom::Declaration(Entity::Class(class)) => Some(spelling(&class.iri)),
            _ => None,
        })
        .collect()
}

fn anonymous(item: &AnnotatedAxiom) -> Option<&AnonymousIndividual> {
    match &item.axiom {
        Axiom::ClassAssertion(_, Individual::Anonymous(a)) => Some(a),
        _ => None,
    }
}

const A: &str = "Ontology(<http://example.org/a>
 Import(<http://example.org/b>)
 Declaration(Class(<http://example.org/A>))
 ClassAssertion(<http://example.org/A> _:x)
)";

const B: &str = "<http://example.org/b> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Ontology> .
<http://example.org/b> <http://www.w3.org/2002/07/owl#imports> <http://example.org/c/1.0> .
<http://example.org/B> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .
";

const C: &str = "Ontology(<http://example.org/c> <http://example.org/c/1.0>
 Import(<http://example.org/a>)
 Declaration(Class(<http://example.org/C>))
 ClassAssertion(<http://example.org/C> _:x)
)";

const UNRELATED: &str = "Ontology(<http://example.org/d>
 Import(<http://example.org/nowhere>)
 Declaration(Class(<http://example.org/D>))
)";

#[test]
fn a_cyclic_closure_of_three_documents_assembles_once() {
    let sources = vec![
        functional(UNRELATED),
        functional(A),
        ntriples(B),
        functional(C),
    ];
    let Ok(closure) = source_closure(&sources, 2, &limits()) else {
        panic!("the closure assembles")
    };
    // b imports c by its version IRI, c imports a, a imports b: every document
    // once, in catalog order, without the unrelated one whose import is missing.
    assert_eq!(closure.documents, vec![1, 2, 3]);
    assert_eq!(
        declared(&closure),
        vec![
            "http://example.org/A".to_string(),
            "http://example.org/B".to_string(),
            "http://example.org/C".to_string()
        ]
    );
    match &closure.ontology.identity {
        OntologyIdentity::Named { ontology, version } => {
            assert_eq!(spelling(ontology), "http://example.org/b");
            assert!(version.is_none());
        }
        OntologyIdentity::Anonymous => panic!("the root is named"),
    }
    assert_eq!(closure.ontology.imports.len(), 1);
    let origins: Vec<(usize, usize)> = closure
        .origins
        .iter()
        .map(|origin| (origin.document, origin.position))
        .collect();
    assert_eq!(origins, vec![(1, 0), (1, 1), (2, 0), (3, 0), (3, 1)]);
}

#[test]
fn colliding_node_ids_stay_apart() {
    let sources = vec![functional(A), ntriples(B), functional(C)];
    let Ok(closure) = source_closure(&sources, 0, &limits()) else {
        panic!("the closure assembles")
    };
    let individuals: Vec<&AnonymousIndividual> = closure
        .ontology
        .axioms
        .iter()
        .filter_map(anonymous)
        .collect();
    assert_eq!(individuals.len(), 2);
    assert_eq!(individuals[0].label, b"x".to_vec());
    assert_eq!(individuals[1].label, b"x".to_vec());
    assert_eq!(individuals[0].scope, document_scope(0));
    assert_eq!(individuals[1].scope, document_scope(2));
    assert_ne!(individuals[0].scope, individuals[1].scope);
}

#[test]
fn a_missing_import_names_its_iri() {
    let sources = vec![functional(A), functional(UNRELATED)];
    match source_closure(&sources, 0, &limits()) {
        Err(ClosureError::MissingImport { document, iri }) => {
            assert_eq!(document, 0);
            assert_eq!(spelling(&iri), "http://example.org/b");
        }
        _ => panic!("b is missing"),
    }
    // The unrelated document's missing import does not matter when it is not imported.
    let sources = vec![
        functional(UNRELATED),
        functional(C),
        functional(A),
        ntriples(B),
    ];
    assert!(source_closure(&sources, 1, &limits()).is_ok());
    match source_closure(&sources, 0, &limits()) {
        Err(ClosureError::MissingImport { document, iri }) => {
            assert_eq!(document, 0);
            assert_eq!(spelling(&iri), "http://example.org/nowhere");
        }
        _ => panic!("nowhere is missing"),
    }
}

#[test]
fn an_import_named_by_two_documents_is_ambiguous() {
    let sources = vec![functional(A), ntriples(B), functional(C), functional(C)];
    match source_closure(&sources, 0, &limits()) {
        Err(ClosureError::AmbiguousImport {
            document,
            iri,
            first,
            second,
        }) => {
            assert_eq!(document, 1);
            assert_eq!(spelling(&iri), "http://example.org/c/1.0");
            assert_eq!((first, second), (2, 3));
        }
        _ => panic!("c/1.0 names two documents"),
    }
}

#[test]
fn roots_outside_the_catalog_and_foreign_scopes_are_errors() {
    let sources = vec![functional(A)];
    assert!(matches!(
        source_closure(&sources, 1, &limits()),
        Err(ClosureError::NoRoot)
    ));
    // Documents read in another scope than their position's are refused.
    let Ok(mut ontologies) = read_sources(&vec![functional(C)], &limits()) else {
        panic!("c reads")
    };
    ontologies.push(RawOntology {
        identity: OntologyIdentity::Anonymous,
        imports: vec![],
        annotations: vec![],
        axioms: vec![AnnotatedAxiom {
            annotations: vec![],
            axiom: Axiom::ClassAssertion(
                ClassExpression::Class(Class {
                    iri: Iri {
                        spelling: b"http://example.org/C".to_vec(),
                    },
                }),
                Individual::Anonymous(AnonymousIndividual {
                    scope: document_scope(0),
                    label: b"x".to_vec(),
                }),
            ),
        }],
    });
    assert!(matches!(
        assemble(ontologies, 1),
        Err(ClosureError::OutOfScope { document: 1 })
    ));
    let unreadable = vec![functional(A), functional("Ontology(")];
    assert!(matches!(
        source_closure(&unreadable, 0, &limits()),
        Err(ClosureError::Unread(unread)) if unread.document == 1
    ));
}
