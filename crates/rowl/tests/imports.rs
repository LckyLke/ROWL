use rowl::reasoner::{default_limits, named, Document, LoadError, Reasoner, Syntax};

const MED: &str = "https://example.org/medication/";

fn example(path: &str) -> Vec<u8> {
    std::fs::read(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples")
            .join(path),
    )
    .unwrap()
}

fn functional(name: &str, text: &str) -> Document {
    Document {
        name: name.to_string(),
        syntax: Syntax::Functional,
        bytes: text.as_bytes().to_vec(),
    }
}

fn ntriples(name: &str, text: &str) -> Document {
    Document {
        name: name.to_string(),
        syntax: Syntax::NTriples,
        bytes: text.as_bytes().to_vec(),
    }
}

fn load(documents: Vec<Document>) -> Result<Reasoner, LoadError> {
    Reasoner::from_documents(documents, 0, &default_limits())
}

fn medication() -> Vec<Document> {
    vec![
        Document {
            name: "medication-prescriptions.ofn".into(),
            syntax: Syntax::Functional,
            bytes: example("imports/medication-prescriptions.ofn"),
        },
        Document {
            name: "medication-vocabulary.ttl".into(),
            syntax: Syntax::Turtle(Vec::new()),
            bytes: example("imports/medication-vocabulary.ttl"),
        },
    ]
}

#[test]
fn the_split_medication_example_gives_the_same_answers() {
    let Ok(closure) = load(medication()) else {
        panic!("the import closure is read")
    };
    let Ok(whole) = Reasoner::from_functional(&example("medication-safety.ofn"), &default_limits())
    else {
        panic!("the whole example is read")
    };
    assert_eq!(
        closure.documents(),
        vec!["medication-prescriptions.ofn", "medication-vocabulary.ttl"]
    );
    assert_eq!(closure.consistent(), Some(true));
    let alert = named(&format!("{MED}AllergyAlert"));
    for person in ["alice", "bob", "carol"] {
        let who = format!("{MED}{person}");
        assert_eq!(
            closure.instance_of(&who, &alert),
            whole.instance_of(&who, &alert),
            "{person}"
        );
    }
    assert_eq!(
        closure.instance_of(&format!("{MED}alice"), &alert),
        Some(true)
    );
    assert_eq!(closure.classes(), whole.classes());
    assert_eq!(closure.individuals(), whole.individuals());
    // The prescriptions alone use undeclared classes; with the imported
    // declarations the closure is OWL 2 DL.
    assert_eq!(closure.dl_violation(), None);
    let Ok(alone) = Reasoner::from_functional(
        &example("imports/medication-prescriptions.ofn"),
        &default_limits(),
    ) else {
        panic!("the prescriptions are read")
    };
    assert!(alone
        .dl_violation()
        .is_some_and(|violation| violation.contains("not declared")));
    assert_eq!(
        alone.instance_of(&format!("{MED}alice"), &alert),
        Some(false)
    );
}

const A: &str = "Prefix(:=<http://example.org/>)
Ontology(<http://example.org/a>
 Import(<http://example.org/b>)
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 SubClassOf(:A :B)
)";

const B: &str = "<http://example.org/b> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Ontology> .
<http://example.org/b> <http://www.w3.org/2002/07/owl#imports> <http://example.org/c/2.0> .
<http://example.org/B> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .
<http://example.org/C> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .
<http://example.org/B> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/C> .
";

const C: &str = "Prefix(:=<http://example.org/>)
Ontology(<http://example.org/c> <http://example.org/c/2.0>
 Import(<http://example.org/a>)
 Declaration(Class(:C)) Declaration(Class(:D))
 SubClassOf(:C :D)
)";

#[test]
fn a_cyclic_closure_of_three_documents_reaches_every_axiom() {
    let Ok(closure) = load(vec![
        functional("a", A),
        ntriples("b", B),
        functional("c", C),
    ]) else {
        panic!("the closure is read")
    };
    assert_eq!(closure.documents(), vec!["a", "b", "c"]);
    let a = named("http://example.org/A");
    let d = named("http://example.org/D");
    assert_eq!(closure.subsumed(&a, &d), Some(true));
    // From the middle of the cycle the same documents are reached.
    let Ok(middle) = Reasoner::from_documents(
        vec![functional("a", A), ntriples("b", B), functional("c", C)],
        1,
        &default_limits(),
    ) else {
        panic!("the closure is read")
    };
    assert_eq!(middle.documents(), vec!["a", "b", "c"]);
    assert_eq!(middle.subsumed(&a, &d), Some(true));
}

#[test]
fn an_import_by_version_iri_is_found_and_a_missing_one_is_named() {
    // b imports c by its version IRI c/2.0; without c, the import is missing.
    match load(vec![functional("a", A), ntriples("b", B)]) {
        Err(LoadError::MissingImport { document, iri }) => {
            assert_eq!(document, "b");
            assert_eq!(iri, "http://example.org/c/2.0");
        }
        _ => panic!("c/2.0 is missing"),
    }
    let wrong_version = C.replace("c/2.0", "c/1.0");
    assert!(matches!(
        load(vec![
            functional("a", A),
            ntriples("b", B),
            functional("c", &wrong_version)
        ]),
        Err(LoadError::MissingImport { .. })
    ));
    match load(vec![
        functional("a", A),
        ntriples("b", B),
        functional("c", C),
        functional("c again", C),
    ]) {
        Err(LoadError::AmbiguousImport {
            document,
            iri,
            first,
            second,
        }) => {
            assert_eq!(document, "b");
            assert_eq!(iri, "http://example.org/c/2.0");
            assert_eq!((first.as_str(), second.as_str()), ("c", "c again"));
        }
        _ => panic!("c/2.0 names two documents"),
    }
    match load(vec![functional("a", A), functional("broken", "Ontology(")]) {
        Err(LoadError::InDocument { document, error }) => {
            assert_eq!(document, "broken");
            assert!(matches!(*error, LoadError::Document(_)));
        }
        _ => panic!("the second document is broken"),
    }
}

const BOUND: &str = "Prefix(:=<http://example.org/>)
Ontology(<http://example.org/bound>
 Import(<http://example.org/other>)
 Declaration(Class(:Left)) Declaration(Class(:Right))
 DisjointClasses(:Left :Right)
 ClassAssertion(:Left _:x)
)";

const OTHER: &str = "Prefix(:=<http://example.org/>)
Ontology(<http://example.org/other>
 ClassAssertion(:Right _:x)
)";

const OTHER_NT: &str = "<http://example.org/other> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Ontology> .
<http://example.org/Right> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/2002/07/owl#Class> .
_:x <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Right> .
";

#[test]
fn colliding_blank_node_labels_denote_different_individuals() {
    // Each document has its own _:x; were they one individual, it would be in
    // two disjoint classes.
    for other in [functional("other", OTHER), ntriples("other", OTHER_NT)] {
        let Ok(closure) = load(vec![functional("bound", BOUND), other]) else {
            panic!("the closure is read")
        };
        assert_eq!(closure.consistent(), Some(true));
    }
    let merged = BOUND.replace(
        " ClassAssertion(:Left _:x)\n",
        " ClassAssertion(:Left _:x)\n ClassAssertion(:Right _:x)\n",
    );
    let Ok(alone) = Reasoner::from_functional(merged.as_bytes(), &default_limits()) else {
        panic!("the merged document is read")
    };
    assert_eq!(alone.consistent(), Some(false));
}
