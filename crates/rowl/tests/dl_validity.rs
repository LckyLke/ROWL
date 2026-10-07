use rowl::reasoner::{default_limits, Reasoner};
use std::path::Path;

/// A Functional Syntax document with prefix `:` and the given axioms.
fn document(axioms: &str) -> Reasoner {
    let source = format!(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n{axioms}\n)\n"
    );
    Reasoner::from_functional(source.as_bytes(), &default_limits())
        .ok()
        .expect("the fixture document loads")
}

#[test]
fn every_example_document_is_owl_2_dl() {
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut checked = 0;
    for entry in std::fs::read_dir(&examples).expect("the examples directory") {
        let path = entry.expect("a directory entry").path();
        // examples/imports holds documents that are OWL 2 DL only with their
        // imports; the import tests check them.
        if !path.is_file() {
            continue;
        }
        let bytes = std::fs::read(&path).expect("a readable example");
        let loaded = match path.extension().and_then(|extension| extension.to_str()) {
            Some("ofn") => Reasoner::from_functional(&bytes, &default_limits()),
            Some("nt") => Reasoner::from_ntriples(&bytes),
            Some("ttl") => Reasoner::from_turtle(&bytes),
            Some("owl") => Reasoner::from_rdfxml(&bytes),
            _ => continue,
        };
        let reasoner = loaded
            .ok()
            .unwrap_or_else(|| panic!("{} loads", path.display()));
        assert_eq!(reasoner.dl_violation(), None, "{}", path.display());
        checked += 1;
    }
    assert!(checked >= 10, "the examples were found");
}

const DECLARED: &str = "Declaration(Class(:A)) Declaration(Class(:B)) \
     Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(DataProperty(:p))";

#[test]
fn each_restriction_reports_its_first_violation_in_words() {
    let cases = [
        ("HasKey(:A () ())", "has neither an object nor a data property (keys, §9.5)"),
        ("DisjointClasses(:A :A)", "the DisjointClasses axiom at position 6"),
        (
            "Declaration(Class(owl:Unknown))",
            "http://www.w3.org/2002/07/owl#Unknown is in the reserved vocabulary and cannot be used as a class",
        ),
        (
            "Declaration(Datatype(:A))",
            "https://example.org/A is declared as a class but is also a datatype",
        ),
        (
            "SubClassOf(:A :C)",
            "https://example.org/C is used as a class but not declared as one",
        ),
        (
            "DataPropertyAssertion(owl:topDataProperty :i \"1\"^^xsd:integer)",
            "uses owl:topDataProperty other than as the superproperty",
        ),
        (
            "Declaration(Datatype(:D)) DataPropertyRange(:p :D)",
            "the datatype https://example.org/D is neither built in nor defined",
        ),
        (
            "DatatypeDefinition(xsd:integer xsd:string)",
            "redefines a built-in datatype",
        ),
        (
            "Declaration(Datatype(:D)) DatatypeDefinition(:D xsd:integer) DatatypeDefinition(:D xsd:string)",
            "define one datatype differently",
        ),
        (
            "Declaration(Datatype(:D)) Declaration(Datatype(:E)) DatatypeDefinition(:D :E) \
             DatatypeDefinition(:E :D)",
            "the datatype definitions are cyclic",
        ),
        (
            "Declaration(Datatype(:D)) DatatypeDefinition(:D xsd:integer) DataPropertyAssertion(:p :i \"1\"^^:D)",
            "uses a defined datatype in a literal or a datatype restriction (§9.4)",
        ),
        (
            "TransitiveObjectProperty(:r) FunctionalObjectProperty(:r)",
            "https://example.org/r is not simple",
        ),
        (
            "Declaration(ObjectProperty(:t)) Declaration(ObjectProperty(:u)) \
             SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t) SubObjectPropertyOf(ObjectPropertyChain(:u :t) :s)",
            "the property hierarchy is not regular",
        ),
        (
            "SameIndividual(_:a :i)",
            "uses an anonymous individual where OWL 2 DL forbids one",
        ),
        (
            "ObjectPropertyAssertion(:r _:a _:a)",
            "connects the anonymous individual _:a with itself",
        ),
        (
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:r _:b _:c) \
             ObjectPropertyAssertion(:r _:c _:a)",
            "form a cycle",
        ),
        (
            "ObjectPropertyAssertion(:r _:a _:b) ObjectPropertyAssertion(:s _:a _:b)",
            "connect the same two anonymous individuals",
        ),
        (
            "ObjectPropertyAssertion(:r :i _:a) ObjectPropertyAssertion(:r :j _:a)",
            "has at most one assertion with a named individual",
        ),
    ];
    for (axioms, expected) in cases {
        let violation = document(&format!("{DECLARED} {axioms}"))
            .dl_violation()
            .unwrap_or_else(|| panic!("{axioms} is not OWL 2 DL"));
        assert!(violation.contains(expected), "{axioms}: {violation}");
    }
}

#[test]
fn header_and_annotation_violations_are_reported() {
    let source = "Prefix(:=<https://example.org/>)\n\
                  Ontology(<http://www.w3.org/2002/07/owl#o> Declaration(Class(:A)))\n";
    let reserved = Reasoner::from_functional(source.as_bytes(), &default_limits())
        .ok()
        .expect("loads");
    assert!(reserved
        .dl_violation()
        .expect("a reserved ontology IRI")
        .contains(
            "the ontology IRI http://www.w3.org/2002/07/owl#o is in the reserved vocabulary"
        ));
    let annotation = document(
        "Annotation(rdfs:comment \"1\"^^:D) Declaration(Datatype(:D)) DatatypeDefinition(:D xsd:integer)",
    );
    assert!(annotation
        .dl_violation()
        .expect("a defined datatype in an ontology annotation")
        .contains("an ontology annotation has a literal of a defined datatype"));
}

#[test]
fn loading_never_rejects_a_document_for_its_dl_restrictions() {
    let invalid = document("SubClassOf(:A :B) ClassAssertion(:A :i)");
    assert!(invalid.dl_violation().is_some());
    assert_eq!(invalid.consistent(), Some(true));
    assert_eq!(document(DECLARED).dl_violation(), None);
}
