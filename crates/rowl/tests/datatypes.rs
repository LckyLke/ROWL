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

#[test]
fn the_subtypes_of_strings_are_reasoned_about_by_value() {
    // A language range admits language tags only.
    assert_eq!(
        consistent(
            "DataPropertyRange(:code xsd:language)\nDataPropertyAssertion(:code :a \"en GB\")"
        ),
        Some(false)
    );
    assert_eq!(
        consistent(
            "DataPropertyRange(:code xsd:language)\nDataPropertyAssertion(:code :a \"en-GB\")"
        ),
        Some(true)
    );
    // A language tag is a token: the subtypes nest.
    assert_eq!(
        consistent("DataPropertyRange(:code xsd:token)\nDataPropertyAssertion(:code :a \"en-GB\"^^xsd:language)"),
        Some(true)
    );
    // The value of a token is the string: one value, not two.
    assert_eq!(
        consistent("FunctionalDataProperty(:id)\nDataPropertyAssertion(:id :a \"abc\"^^xsd:token)\nDataPropertyAssertion(:id :a \"abc\"^^xsd:string)"),
        Some(true)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:id)\nDataPropertyAssertion(:id :a \"abc\"^^xsd:token)\nDataPropertyAssertion(:id :a \"abd\"^^xsd:NCName)"),
        Some(false)
    );
    // Every value of a datatype the closure names gets its subtypes right.
    assert_eq!(
        consistent("DataPropertyRange(:id DataComplementOf(xsd:NCName))\nDataPropertyAssertion(:id :a \"xml:lang\"^^xsd:Name)"),
        Some(true)
    );
    assert_eq!(
        consistent("DataPropertyRange(:id DataComplementOf(xsd:Name))\nDataPropertyAssertion(:id :a \"lang\"^^xsd:NMTOKEN)"),
        Some(false)
    );
    // Infinitely many language tags, and differences of subtypes that are not empty.
    assert_eq!(
        consistent(
            "SubClassOf(:Page DataMinCardinality(3 :code xsd:language))\nClassAssertion(:Page :p)"
        ),
        Some(true)
    );
    for (inside, outside, empty) in [
        ("xsd:NMTOKEN", "xsd:Name", false),
        ("xsd:Name", "xsd:NCName", false),
        ("xsd:NCName", "xsd:language", false),
        ("xsd:token", "xsd:NMTOKEN", false),
        ("xsd:normalizedString", "xsd:token", false),
        ("xsd:string", "xsd:normalizedString", false),
        ("xsd:language", "xsd:NCName", true),
        ("xsd:NCName", "xsd:token", true),
        ("xsd:language", "xsd:normalizedString", true),
    ] {
        let axioms = format!(
            "SubClassOf(:C DataMinCardinality(2 :code DataIntersectionOf({inside} DataComplementOf({outside}))))\nClassAssertion(:C :c)"
        );
        assert_eq!(
            consistent(&axioms),
            Some(!empty),
            "{inside} without {outside}"
        );
    }
    // Strings are no numbers.
    assert_eq!(
        consistent("DataPropertyRange(:code xsd:integer)\nDataPropertyAssertion(:code :a \"12\"^^xsd:NMTOKEN)"),
        Some(false)
    );
    // A lexical form outside the subtype gets no answer.
    assert_eq!(
        consistent("DataPropertyAssertion(:id :a \"a\tb\"^^xsd:token)"),
        None
    );
}

#[test]
fn subsumption_follows_the_subtypes_of_strings() {
    let text = "Prefix(:=<https://example.org/d/>)
Ontology(<https://example.org/d/onto>
EquivalentClasses(:Tagged DataSomeValuesFrom(:code xsd:language))
EquivalentClasses(:Named DataSomeValuesFrom(:code xsd:Name))
EquivalentClasses(:Coded DataSomeValuesFrom(:code xsd:token))
DataPropertyAssertion(:code :a \"en-GB\")
DataPropertyAssertion(:code :b \"x:y\")
)
";
    let Ok(reasoner) = Reasoner::from_functional(text.as_bytes(), &default_limits()) else {
        panic!("the document must load");
    };
    let tagged = rowl::reasoner::named("https://example.org/d/Tagged");
    let named = rowl::reasoner::named("https://example.org/d/Named");
    let coded = rowl::reasoner::named("https://example.org/d/Coded");
    assert_eq!(reasoner.subsumed(&tagged, &named), Some(true));
    assert_eq!(reasoner.subsumed(&named, &coded), Some(true));
    assert_eq!(reasoner.subsumed(&named, &tagged), Some(false));
    assert_eq!(
        reasoner.instance_of("https://example.org/d/a", &tagged),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/d/b", &named),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/d/b", &tagged),
        Some(false)
    );
}
