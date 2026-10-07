use rowl::reasoner::{default_limits, named, Reasoner};

/// The document with the axioms added to a small header, loaded.
fn reasoner(axioms: &str) -> Reasoner {
    let text = format!(
        "Prefix(:=<https://example.org/t/>)\nOntology(<https://example.org/t/onto>\n{axioms}\n)\n"
    );
    let Ok(reasoner) = Reasoner::from_functional(text.as_bytes(), &default_limits()) else {
        panic!("the document must load: {axioms}");
    };
    reasoner
}

/// Whether the document is consistent.
fn consistent(axioms: &str) -> Option<bool> {
    reasoner(axioms).consistent()
}

const AGE: &str = "Declaration(Datatype(:age))\nDatatypeDefinition(:age xsd:nonNegativeInteger)\nDataPropertyRange(:hasAge :age)";

#[test]
fn a_defined_datatype_is_its_data_range() {
    // OWL 2 Structural Specification, section 9.4: :age stands for the
    // non-negative integers.
    assert_eq!(
        consistent(&format!(
            "{AGE}\nDataPropertyAssertion(:hasAge :ann \"-1\"^^xsd:integer)"
        )),
        Some(false)
    );
    assert_eq!(
        consistent(&format!(
            "{AGE}\nDataPropertyAssertion(:hasAge :ann \"42\"^^xsd:integer)"
        )),
        Some(true)
    );
    // Definitions unfold in turn, in intersections, unions, complements and
    // enumerations.
    let adult = "Declaration(Datatype(:adultAge))\nDatatypeDefinition(:adultAge DataIntersectionOf(:age DatatypeRestriction(xsd:integer xsd:minInclusive \"18\"^^xsd:integer)))\nDataPropertyRange(:adultAgeOf :adultAge)";
    assert_eq!(
        consistent(&format!(
            "{AGE}\n{adult}\nDataPropertyAssertion(:adultAgeOf :ann \"17\"^^xsd:integer)"
        )),
        Some(false)
    );
    assert_eq!(
        consistent(&format!(
            "{AGE}\n{adult}\nDataPropertyAssertion(:adultAgeOf :ann \"30\"^^xsd:integer)"
        )),
        Some(true)
    );
    let weekday = "Declaration(Datatype(:weekday))\nDatatypeDefinition(:weekday DataOneOf(\"mon\" \"tue\" \"wed\" \"thu\" \"fri\"))\nDeclaration(Datatype(:weekend))\nDatatypeDefinition(:weekend DataComplementOf(:weekday))";
    assert_eq!(
        consistent(&format!(
            "{weekday}\nDataPropertyRange(:workday :weekday)\nDataPropertyAssertion(:workday :shift \"sun\")"
        )),
        Some(false)
    );
    assert_eq!(
        consistent(&format!(
            "{weekday}\nDataPropertyRange(:restday :weekend)\nDataPropertyAssertion(:restday :shift \"sun\")"
        )),
        Some(true)
    );
    assert_eq!(
        consistent(&format!(
            "{weekday}\nDataPropertyRange(:restday DataIntersectionOf(:weekday :weekend))\nDataPropertyAssertion(:restday :shift \"sun\")"
        )),
        Some(false)
    );
    // A definition that no axiom uses changes nothing.
    assert_eq!(
        consistent("Declaration(Datatype(:code))\nDatatypeDefinition(:code xsd:string)\nClassAssertion(:Patient :ann)"),
        Some(true)
    );
}

#[test]
fn questions_may_use_defined_datatypes() {
    let reasoner = reasoner(&format!(
        "{AGE}\nDeclaration(Datatype(:adultAge))\nDatatypeDefinition(:adultAge DataIntersectionOf(:age DatatypeRestriction(xsd:integer xsd:minInclusive \"18\"^^xsd:integer)))\nEquivalentClasses(:Adult DataSomeValuesFrom(:hasAge :adultAge))\nEquivalentClasses(:Aged DataSomeValuesFrom(:hasAge :age))\nDataPropertyAssertion(:hasAge :ann \"30\"^^xsd:integer)\nDataPropertyAssertion(:hasAge :bob \"7\"^^xsd:integer)"
    ));
    let adult = named("https://example.org/t/Adult");
    let aged = named("https://example.org/t/Aged");
    assert_eq!(reasoner.subsumed(&adult, &aged), Some(true));
    assert_eq!(reasoner.subsumed(&aged, &adult), Some(false));
    assert_eq!(
        reasoner.instance_of("https://example.org/t/ann", &adult),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/t/bob", &adult),
        Some(false)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/t/bob", &aged),
        Some(true)
    );
}

#[test]
fn improper_definitions_get_no_answer() {
    // Cyclic definitions.
    assert_eq!(
        consistent("Declaration(Datatype(:a))\nDeclaration(Datatype(:b))\nDatatypeDefinition(:a :b)\nDatatypeDefinition(:b :a)\nDataPropertyRange(:p :a)"),
        None
    );
    // A defined datatype restricted by facets.
    assert_eq!(
        consistent(&format!(
            "{AGE}\nDataPropertyRange(:p DatatypeRestriction(:age xsd:minInclusive \"1\"^^xsd:integer))"
        )),
        None
    );
    // Two definitions of one datatype.
    assert_eq!(
        consistent(&format!("{AGE}\nDatatypeDefinition(:age xsd:integer)")),
        None
    );
}
