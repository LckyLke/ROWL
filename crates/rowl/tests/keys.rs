use rowl::experimental::model::{AtLeastTwo, Axiom, Individual, Iri, NamedIndividual};
use rowl::reasoner::{default_limits, Reasoner};

/// The reasoner of the axioms with a small header.
fn reasoner(axioms: &str) -> Reasoner {
    let text = format!(
        "Prefix(:=<https://example.org/k/>)\nOntology(<https://example.org/k/onto>\n{axioms}\n)\n"
    );
    let Ok(reasoner) = Reasoner::from_functional(text.as_bytes(), &default_limits()) else {
        panic!("the document must load: {axioms}");
    };
    reasoner
}
fn consistent(axioms: &str) -> Option<bool> {
    reasoner(axioms).consistent()
}
fn individual(local: &str) -> Individual {
    Individual::Named(NamedIndividual {
        iri: Iri {
            spelling: format!("https://example.org/k/{local}").into_bytes(),
        },
    })
}
fn same(a: &str, b: &str) -> Axiom {
    Axiom::SameIndividual(AtLeastTwo {
        first: individual(a),
        second: individual(b),
        rest: Vec::new(),
    })
}

const SHARED_ID: &str = "HasKey(:Patient () (:ssn))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
DataPropertyAssertion(:ssn :a \"123-45\")
DataPropertyAssertion(:ssn :b \"123-45\")";

#[test]
fn records_that_share_a_data_value_are_one() {
    assert_eq!(consistent(SHARED_ID), Some(true));
    assert_eq!(
        consistent(&format!("{SHARED_ID}\nDifferentIndividuals(:a :b)")),
        Some(false)
    );
    assert_eq!(reasoner(SHARED_ID).entails(&same("a", "b")), Some(true));
    // Values count, not spellings: 07 and 7 are one integer.
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:id))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
DataPropertyAssertion(:id :a \"07\"^^xsd:integer)
DataPropertyAssertion(:id :b \"7\"^^xsd:integer)
DifferentIndividuals(:a :b)"
        ),
        Some(false)
    );
    // Different values, or one of them outside the key class: no merge.
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:ssn))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
DataPropertyAssertion(:ssn :a \"1\")
DataPropertyAssertion(:ssn :b \"2\")
DifferentIndividuals(:a :b)"
        ),
        Some(true)
    );
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:ssn))
ClassAssertion(:Patient :a)
DataPropertyAssertion(:ssn :a \"123-45\")
DataPropertyAssertion(:ssn :b \"123-45\")
DifferentIndividuals(:a :b)"
        ),
        Some(true)
    );
    assert_eq!(
        reasoner(
            "HasKey(:Patient () (:ssn))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
DataPropertyAssertion(:ssn :a \"1\")
DataPropertyAssertion(:ssn :b \"2\")"
        )
        .entails(&same("a", "b")),
        Some(false)
    );
}

#[test]
fn keys_never_apply_to_anonymous_individuals() {
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:ssn))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient _:x)
DataPropertyAssertion(:ssn :a \"123-45\")
DataPropertyAssertion(:ssn _:x \"123-45\")
ClassAssertion(ObjectComplementOf(ObjectOneOf(:a)) _:x)"
        ),
        Some(true)
    );
}

#[test]
fn values_that_no_literal_names_count_too() {
    // Two truth values for three distinct patients: two of them share one.
    let flags = "HasKey(:Patient () (:flag))
SubClassOf(:Patient DataSomeValuesFrom(:flag xsd:boolean))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)";
    assert_eq!(
        consistent(&format!(
            "{flags}\nClassAssertion(:Patient :c)\nDifferentIndividuals(:a :b :c)"
        )),
        Some(false)
    );
    assert_eq!(
        consistent(&format!("{flags}\nDifferentIndividuals(:a :b)")),
        Some(true)
    );
    // Strings are infinitely many: distinct patients get distinct ones.
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:ssn))
SubClassOf(:Patient DataSomeValuesFrom(:ssn xsd:string))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
ClassAssertion(:Patient :c)
DifferentIndividuals(:a :b :c)"
        ),
        Some(true)
    );
}

#[test]
fn keys_with_object_and_data_properties_need_every_value() {
    let ward = "HasKey(:Patient (:ward) (:bed))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
ObjectPropertyAssertion(:ward :a :w1)
ObjectPropertyAssertion(:ward :b :w1)
DataPropertyAssertion(:bed :a \"3\"^^xsd:integer)
DifferentIndividuals(:a :b)";
    assert_eq!(
        consistent(&format!(
            "{ward}\nDataPropertyAssertion(:bed :b \"3\"^^xsd:integer)"
        )),
        Some(false)
    );
    assert_eq!(
        consistent(&format!(
            "{ward}\nDataPropertyAssertion(:bed :b \"4\"^^xsd:integer)"
        )),
        Some(true)
    );
    // Two data properties: both values must be shared.
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:first :last))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
DataPropertyAssertion(:first :a \"Ann\")
DataPropertyAssertion(:first :b \"Ann\")
DataPropertyAssertion(:last :a \"Lee\")
DataPropertyAssertion(:last :b \"Lee\")
DifferentIndividuals(:a :b)"
        ),
        Some(false)
    );
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:first :last))
ClassAssertion(:Patient :a)
ClassAssertion(:Patient :b)
DataPropertyAssertion(:first :a \"Ann\")
DataPropertyAssertion(:first :b \"Ann\")
DataPropertyAssertion(:last :a \"Lee\")
DataPropertyAssertion(:last :b \"Li\")
DifferentIndividuals(:a :b)"
        ),
        Some(true)
    );
}

#[test]
fn some_data_keys_get_no_answer() {
    // Ordered numbers: a bounded run of integers would need every value named.
    assert_eq!(
        consistent(
            "HasKey(:Patient () (:age))
DataPropertyRange(:age xsd:byte)
ClassAssertion(:Patient :a)"
        ),
        None
    );
    assert_eq!(
        consistent(
            "HasKey(:Patient () (owl:topDataProperty))
ClassAssertion(:Patient :a)"
        ),
        None
    );
    assert_eq!(
        consistent(
            "HasKey(:Patient () (owl:bottomDataProperty))
ClassAssertion(:Patient :a)"
        ),
        None
    );
}
