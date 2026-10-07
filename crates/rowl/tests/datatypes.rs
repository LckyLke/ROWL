use rowl::reasoner::{default_limits, Reasoner};

/// Whether the document, with the axioms added to a small header, is consistent.
fn consistent(axioms: &str) -> Option<bool> {
    let text = format!(
        "Prefix(:=<https://example.org/d/>)\nOntology(<https://example.org/d/onto>\n{axioms}\n)\n"
    );
    let Ok(reasoner) = Reasoner::from_functional(text.as_bytes(), &default_limits()) else {
        panic!("the document must load: {axioms}");
    };
    reasoner.consistent()
}

#[test]
fn iris_and_octets_are_reasoned_about_by_value() {
    // OWL 2 Structural Specification, section 4.5: the binary datatypes are disjoint.
    assert_eq!(
        consistent("DataPropertyRange(:personID xsd:base64Binary)\nDataPropertyAssertion(:personID :Meg \"0203\"^^xsd:hexBinary)"),
        Some(false)
    );
    assert_eq!(
        consistent("DataPropertyRange(:personID xsd:base64Binary)\nDataPropertyAssertion(:personID :Meg \"AgM=\"^^xsd:base64Binary)"),
        Some(true)
    );
    // Lexical forms of one value are one value.
    assert_eq!(
        consistent("FunctionalDataProperty(:id)\nDataPropertyAssertion(:id :a \"0FB7\"^^xsd:hexBinary)\nDataPropertyAssertion(:id :a \"0fb7\"^^xsd:hexBinary)"),
        Some(true)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:id)\nDataPropertyAssertion(:id :a \"0FB7\"^^xsd:hexBinary)\nDataPropertyAssertion(:id :a \"0FB8\"^^xsd:hexBinary)"),
        Some(false)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:id)\nDataPropertyAssertion(:id :a \"AQID\"^^xsd:base64Binary)\nDataPropertyAssertion(:id :a \"A Q I D\"^^xsd:base64Binary)"),
        Some(true)
    );
    // Section 4.6: IRIs are not strings.
    assert_eq!(
        consistent("DataPropertyRange(:home xsd:anyURI)\nDataPropertyAssertion(:home :a \"http://example.org/\"^^xsd:string)"),
        Some(false)
    );
    assert_eq!(
        consistent("DataPropertyRange(:home xsd:anyURI)\nDataPropertyAssertion(:home :a \"http://example.org/\"^^xsd:anyURI)"),
        Some(true)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:home)\nDataPropertyAssertion(:home :a \"http://example.org/\"^^xsd:anyURI)\nDataPropertyAssertion(:home :a \"http://example.org/\"^^xsd:string)"),
        Some(false)
    );
    // Infinitely many values: three different IRIs fit a range of IRIs.
    assert_eq!(
        consistent(
            "SubClassOf(:Page DataMinCardinality(3 :link xsd:anyURI))\nClassAssertion(:Page :p)"
        ),
        Some(true)
    );
    // A literal outside the lexical space gets no answer.
    assert_eq!(
        consistent("DataPropertyAssertion(:id :a \"0G\"^^xsd:hexBinary)"),
        None
    );
}

#[test]
fn instance_questions_see_the_datatypes_of_iris_and_octets() {
    let text = "Prefix(:=<https://example.org/d/>)
Ontology(<https://example.org/d/onto>
EquivalentClasses(:Linked DataSomeValuesFrom(:home xsd:anyURI))
EquivalentClasses(:Signed DataSomeValuesFrom(:signature xsd:base64Binary))
DataPropertyAssertion(:home :a \"http://example.org/\"^^xsd:anyURI)
DataPropertyAssertion(:home :b \"http://example.org/\")
DataPropertyAssertion(:signature :a \"AQID\"^^xsd:base64Binary)
DataPropertyAssertion(:signature :b \"010203\"^^xsd:hexBinary)
)
";
    let Ok(reasoner) = Reasoner::from_functional(text.as_bytes(), &default_limits()) else {
        panic!("the document must load");
    };
    let linked = rowl::reasoner::named("https://example.org/d/Linked");
    let signed = rowl::reasoner::named("https://example.org/d/Signed");
    assert_eq!(
        reasoner.instance_of("https://example.org/d/a", &linked),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/d/b", &linked),
        Some(false)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/d/a", &signed),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/d/b", &signed),
        Some(false)
    );
}
