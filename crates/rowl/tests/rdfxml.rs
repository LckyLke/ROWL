//! Reasoning over RDF/XML documents: the verified XML and RDF/XML readers,
//! the verified reverse RDF mapping and the verified queries, through
//! `Reasoner::from_rdfxml` and import catalogs.
use rowl::reasoner::{default_limits, named, Document, LoadError, Reasoner, Syntax};

fn same_answers(left: &Reasoner, right: &Reasoner) {
    let classes = left.classes();
    assert_eq!(right.classes(), classes);
    assert_eq!(right.individuals(), left.individuals());
    assert_eq!(right.consistent(), left.consistent());
    let a = left.classify().expect("the example classifies");
    let b = right.classify().expect("the example classifies");
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(&b) {
        assert_eq!(x.class, y.class);
        assert_eq!(x.satisfiable, y.satisfiable);
        assert_eq!(x.superclasses, y.superclasses);
    }
    for individual in left.individuals() {
        for class in &classes {
            assert_eq!(
                right.instance_of(&individual, &named(class)),
                left.instance_of(&individual, &named(class))
            );
        }
    }
}

#[test]
fn rdfxml_examples_answer_as_their_ntriples_graphs() {
    for (owl, nt) in [
        (
            &include_bytes!("../../../examples/medication-safety.owl")[..],
            &include_bytes!("../../../examples/medication-safety.nt")[..],
        ),
        (
            &include_bytes!("../../../examples/maintenance.owl")[..],
            &include_bytes!("../../../examples/maintenance.nt")[..],
        ),
    ] {
        let Ok(rdfxml) = Reasoner::from_rdfxml(owl) else {
            panic!("the RDF/XML example must load");
        };
        let Ok(ntriples) = Reasoner::from_ntriples(nt) else {
            panic!("the N-Triples example must load");
        };
        assert_eq!(rdfxml.consistent(), Some(true));
        same_answers(&ntriples, &rdfxml);
    }
}

const RELATIVE: &[u8] = br##"<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#">
  <owl:Class rdf:about="#Drug"/>
  <owl:Class rdf:about="#Opioid">
    <rdfs:subClassOf rdf:resource="#Drug"/>
  </owl:Class>
</rdf:RDF>
"##;

#[test]
fn relative_iris_resolve_against_the_base() {
    // Without a base, "#Drug" has nothing to resolve against.
    assert!(matches!(
        Reasoner::from_rdfxml(RELATIVE),
        Err(LoadError::RdfXml(_))
    ));
    let Ok(reasoner) = Reasoner::from_rdfxml_with_base(RELATIVE, b"https://example.org/drugs")
    else {
        panic!("with a base the document loads");
    };
    assert_eq!(
        reasoner.classes(),
        vec![
            "https://example.org/drugs#Drug".to_string(),
            "https://example.org/drugs#Opioid".to_string()
        ]
    );
    assert_eq!(
        reasoner.subsumed(
            &named("https://example.org/drugs#Opioid"),
            &named("https://example.org/drugs#Drug")
        ),
        Some(true)
    );
}

#[test]
fn rdfxml_loading_reports_why_it_fails() {
    // Not well-formed XML: the end tag does not match.
    assert!(matches!(
        Reasoner::from_rdfxml(b"<a></b>"),
        Err(LoadError::Xml(_))
    ));
    // Well-formed XML whose element tree has no RDF/XML graph.
    let literal = br#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
        xmlns:ex="https://example.org/"><rdf:Description rdf:about="https://example.org/a">
        <ex:p rdf:parseType="Literal"><b>bold</b></ex:p></rdf:Description></rdf:RDF>"#;
    assert!(matches!(
        Reasoner::from_rdfxml(literal),
        Err(LoadError::RdfXml(_))
    ));
    // A graph that declares nothing encodes no OWL ontology.
    let undeclared = br#"<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
        xmlns:ex="https://example.org/"><rdf:Description rdf:about="https://example.org/a">
        <ex:p rdf:resource="https://example.org/b"/></rdf:Description></rdf:RDF>"#;
    assert!(matches!(
        Reasoner::from_rdfxml(undeclared),
        Err(LoadError::Graph)
    ));
}

#[test]
fn import_catalogs_read_rdfxml_documents() {
    let vocabulary = br#"<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#">
  <owl:Ontology rdf:about="https://example.org/vocabulary"/>
  <owl:Class rdf:about="https://example.org/Drug"/>
  <owl:Class rdf:about="https://example.org/Opioid">
    <rdfs:subClassOf rdf:resource="https://example.org/Drug"/>
  </owl:Class>
</rdf:RDF>
"#;
    let prescriptions = b"Prefix(:=<https://example.org/>)\n\
        Ontology(<https://example.org/prescriptions>\n\
        Import(<https://example.org/vocabulary>)\n\
        Declaration(Class(:Opioid)) Declaration(NamedIndividual(:morphine))\n\
        ClassAssertion(:Opioid :morphine))\n";
    let documents = vec![
        Document {
            name: "prescriptions.ofn".into(),
            syntax: Syntax::Functional,
            bytes: prescriptions.to_vec(),
        },
        Document {
            name: "vocabulary.owl".into(),
            syntax: Syntax::RdfXml(Vec::new()),
            bytes: vocabulary.to_vec(),
        },
    ];
    let Ok(reasoner) = Reasoner::from_documents(documents, 0, &default_limits()) else {
        panic!("the closure loads");
    };
    assert_eq!(
        reasoner.documents(),
        vec![
            "prescriptions.ofn".to_string(),
            "vocabulary.owl".to_string()
        ]
    );
    assert_eq!(
        reasoner.instance_of(
            "https://example.org/morphine",
            &named("https://example.org/Drug")
        ),
        Some(true)
    );
}
