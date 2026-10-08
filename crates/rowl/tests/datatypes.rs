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

#[test]
fn time_instants_are_reasoned_about_by_value() {
    // OWL 2 Structural Specification, section 4.7: one instant at two offsets is
    // two values, so a functional property cannot take both.
    assert_eq!(
        consistent("FunctionalDataProperty(:admitted)\nDataPropertyAssertion(:admitted :a \"1956-06-25T04:00:00-05:00\"^^xsd:dateTime)\nDataPropertyAssertion(:admitted :a \"1956-06-25T10:00:00+01:00\"^^xsd:dateTime)"),
        Some(false)
    );
    // Lexical forms of one value: fractions of zero, -00:00 for Z and the end of a day.
    assert_eq!(
        consistent("FunctionalDataProperty(:admitted)\nDataPropertyAssertion(:admitted :a \"2024-03-01T08:30:00Z\"^^xsd:dateTime)\nDataPropertyAssertion(:admitted :a \"2024-03-01T08:30:00.000-00:00\"^^xsd:dateTimeStamp)"),
        Some(true)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:admitted)\nDataPropertyAssertion(:admitted :a \"2024-02-29T24:00:00Z\"^^xsd:dateTime)\nDataPropertyAssertion(:admitted :a \"2024-03-01T00:00:00Z\"^^xsd:dateTime)"),
        Some(true)
    );
    // A time stamp needs a time zone; time instants are no strings.
    assert_eq!(
        consistent("DataPropertyRange(:admitted xsd:dateTimeStamp)\nDataPropertyAssertion(:admitted :a \"2024-03-01T08:30:00\"^^xsd:dateTime)"),
        Some(false)
    );
    assert_eq!(
        consistent("DataPropertyRange(:admitted xsd:dateTimeStamp)\nDataPropertyAssertion(:admitted :a \"2024-03-01T08:30:00+01:00\"^^xsd:dateTime)"),
        Some(true)
    );
    assert_eq!(
        consistent("DataPropertyRange(:admitted xsd:dateTime)\nDataPropertyAssertion(:admitted :a \"2024-03-01T08:30:00Z\"^^xsd:string)"),
        Some(false)
    );
    // Infinitely many instants, with a time zone or without one.
    assert_eq!(
        consistent("SubClassOf(:Stay DataMinCardinality(3 :visit DataIntersectionOf(xsd:dateTime DataComplementOf(xsd:dateTimeStamp))))\nClassAssertion(:Stay :s)"),
        Some(true)
    );
    // Restrictions of time instants by facets, and literals outside the
    // lexical space, get no answer.
    assert_eq!(
        consistent("DataPropertyRange(:admitted DatatypeRestriction(xsd:dateTime xsd:minInclusive \"2000-01-01T00:00:00Z\"^^xsd:dateTime))"),
        None
    );
    assert_eq!(
        consistent("DataPropertyAssertion(:admitted :a \"2023-02-29T00:00:00Z\"^^xsd:dateTime)"),
        None
    );
}

#[test]
fn subsumption_follows_the_time_stamps() {
    let text = "Prefix(:=<https://example.org/d/>)
Ontology(<https://example.org/d/onto>
EquivalentClasses(:Stamped DataSomeValuesFrom(:admitted xsd:dateTimeStamp))
EquivalentClasses(:Dated DataSomeValuesFrom(:admitted xsd:dateTime))
DataPropertyAssertion(:admitted :a \"2024-03-01T08:30:00Z\"^^xsd:dateTime)
DataPropertyAssertion(:admitted :b \"2024-03-01T08:30:00\"^^xsd:dateTime)
)
";
    let Ok(reasoner) = Reasoner::from_functional(text.as_bytes(), &default_limits()) else {
        panic!("the document must load");
    };
    let stamped = rowl::reasoner::named("https://example.org/d/Stamped");
    let dated = rowl::reasoner::named("https://example.org/d/Dated");
    assert_eq!(reasoner.subsumed(&stamped, &dated), Some(true));
    assert_eq!(reasoner.subsumed(&dated, &stamped), Some(false));
    assert_eq!(
        reasoner.instance_of("https://example.org/d/a", &stamped),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/d/b", &dated),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/d/b", &stamped),
        Some(false)
    );
}

#[test]
fn floating_point_numbers_are_reasoned_about_by_value() {
    // OWL 2 Structural Specification, section 4.2: floating-point numbers are
    // no integers, and the two zeros are two values.
    assert_eq!(
        consistent("DataPropertyRange(:hasAge xsd:integer)\nDataPropertyAssertion(:hasAge :Meg \"17\"^^xsd:double)"),
        Some(false)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:children)\nDataPropertyAssertion(:children :Meg \"+0\"^^xsd:float)\nDataPropertyAssertion(:children :Meg \"-0\"^^xsd:float)"),
        Some(false)
    );
    // Lexical forms of one value are one value, after rounding.
    assert_eq!(
        consistent("FunctionalDataProperty(:dose)\nDataPropertyAssertion(:dose :a \"1.0\"^^xsd:double)\nDataPropertyAssertion(:dose :a \"1E0\"^^xsd:double)"),
        Some(true)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:dose)\nDataPropertyAssertion(:dose :a \"0.1\"^^xsd:float)\nDataPropertyAssertion(:dose :a \"0.10000000149011612\"^^xsd:float)"),
        Some(true)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:dose)\nDataPropertyAssertion(:dose :a \"0.1\"^^xsd:double)\nDataPropertyAssertion(:dose :a \"0.10000000149011612\"^^xsd:double)"),
        Some(false)
    );
    assert_eq!(
        consistent("FunctionalDataProperty(:dose)\nDataPropertyAssertion(:dose :a \"NaN\"^^xsd:double)\nDataPropertyAssertion(:dose :a \"NaN\"^^xsd:double)"),
        Some(true)
    );
    // xsd:double, xsd:float and xsd:decimal are pairwise disjoint.
    assert_eq!(
        consistent(
            "DataPropertyRange(:dose xsd:double)\nDataPropertyAssertion(:dose :a \"1\"^^xsd:float)"
        ),
        Some(false)
    );
    assert_eq!(
        consistent("DataPropertyRange(:dose xsd:decimal)\nDataPropertyAssertion(:dose :a \"1\"^^xsd:double)"),
        Some(false)
    );
    assert_eq!(
        consistent("DataPropertyRange(:dose xsd:double)\nDataPropertyAssertion(:dose :a \"1.5e-3\"^^xsd:double)"),
        Some(true)
    );
    // Many values: three different doubles fit a range of doubles.
    assert_eq!(
        consistent("SubClassOf(:Series DataMinCardinality(3 :reading xsd:double))\nClassAssertion(:Series :s)"),
        Some(true)
    );
    // Literals outside the lexical space get no answer.
    assert_eq!(
        consistent("DataPropertyAssertion(:dose :a \"1,5\"^^xsd:double)"),
        None
    );
}

/// A document where `:a` has a value of `:dose` in the data range.
fn dose_in(range: &str, value: &str) -> Option<bool> {
    consistent(&format!(
        "DataPropertyRange(:dose {range})\nDataPropertyAssertion(:dose :a {value})"
    ))
}

/// A document where `:a` has `count` values of `:dose` in the data range.
fn doses_in(count: usize, range: &str) -> Option<bool> {
    consistent(&format!(
        "SubClassOf(:A DataMinCardinality({count} :dose {range}))\nClassAssertion(:A :a)"
    ))
}

#[test]
fn floating_point_ranges_follow_the_order_of_xml_schema() {
    // XML Schema 1.1 Part 2, section 3.3.5: the order of the values, with the
    // two zeros equal, the infinities at the ends and NaN incomparable.
    let at_least_zero = "DatatypeRestriction(xsd:double xsd:minInclusive \"0.0\"^^xsd:double)";
    assert_eq!(dose_in(at_least_zero, "\"0.5\"^^xsd:double"), Some(true));
    assert_eq!(dose_in(at_least_zero, "\"-1.5\"^^xsd:double"), Some(false));
    assert_eq!(dose_in(at_least_zero, "\"-0\"^^xsd:double"), Some(true));
    assert_eq!(dose_in(at_least_zero, "\"INF\"^^xsd:double"), Some(true));
    assert_eq!(dose_in(at_least_zero, "\"-INF\"^^xsd:double"), Some(false));
    assert_eq!(dose_in(at_least_zero, "\"NaN\"^^xsd:double"), Some(false));
    assert_eq!(dose_in(at_least_zero, "\"0.5\"^^xsd:float"), Some(false));
    let below_zero = "DatatypeRestriction(xsd:double xsd:maxExclusive \"0\"^^xsd:double)";
    assert_eq!(dose_in(below_zero, "\"-0\"^^xsd:double"), Some(false));
    assert_eq!(dose_in(below_zero, "\"-1E-320\"^^xsd:double"), Some(true));
    assert_eq!(dose_in(below_zero, "\"-INF\"^^xsd:double"), Some(true));
    assert_eq!(dose_in(below_zero, "\"NaN\"^^xsd:double"), Some(false));
    let up_to_nan = "DatatypeRestriction(xsd:double xsd:maxInclusive \"NaN\"^^xsd:double)";
    assert_eq!(dose_in(up_to_nan, "\"NaN\"^^xsd:double"), Some(false));
    assert_eq!(doses_in(1, up_to_nan), Some(false));
    // A bound of another datatype leaves no values (Direct Semantics, Table 4).
    assert_eq!(
        doses_in(
            1,
            "DatatypeRestriction(xsd:float xsd:minInclusive \"1\"^^xsd:double)"
        ),
        Some(false)
    );
    assert_eq!(
        doses_in(
            1,
            "DatatypeRestriction(xsd:double xsd:minInclusive \"1\"^^xsd:decimal)"
        ),
        Some(false)
    );
    assert_eq!(
        doses_in(
            1,
            "DatatypeRestriction(xsd:decimal xsd:minInclusive \"1\"^^xsd:double)"
        ),
        Some(false)
    );
    // The values are counted exactly: one float lies between 1 and the
    // float of 1.0000002, two values are equal to zero and one is infinite.
    let between = "DatatypeRestriction(xsd:float xsd:minExclusive \"1\"^^xsd:float xsd:maxExclusive \"1.0000002\"^^xsd:float)";
    assert_eq!(doses_in(1, between), Some(true));
    assert_eq!(doses_in(2, between), Some(false));
    let zeros = "DatatypeRestriction(xsd:double xsd:minInclusive \"0\"^^xsd:double xsd:maxInclusive \"-0\"^^xsd:double)";
    assert_eq!(doses_in(2, zeros), Some(true));
    assert_eq!(doses_in(3, zeros), Some(false));
    let infinite = "DatatypeRestriction(xsd:double xsd:minInclusive \"INF\"^^xsd:double)";
    assert_eq!(doses_in(1, infinite), Some(true));
    assert_eq!(doses_in(2, infinite), Some(false));
    assert_eq!(
        doses_in(
            0,
            "DatatypeRestriction(xsd:double xsd:minExclusive \"INF\"^^xsd:double)"
        ),
        Some(true)
    );
    assert_eq!(
        doses_in(
            1,
            "DatatypeRestriction(xsd:double xsd:minExclusive \"INF\"^^xsd:double)"
        ),
        Some(false)
    );
    // Literal values count among the values of their place.
    assert_eq!(
        consistent(&format!(
            "SubClassOf(:A DataMinCardinality(2 :dose {zeros}))\nClassAssertion(:A :a)\nDataPropertyAssertion(:dose :b \"-0\"^^xsd:double)"
        )),
        Some(true)
    );
    // Large ranges have room for many values.
    assert_eq!(
        doses_in(20, "DatatypeRestriction(xsd:float xsd:minInclusive \"1\"^^xsd:float xsd:maxInclusive \"2\"^^xsd:float)"),
        Some(true)
    );
}
