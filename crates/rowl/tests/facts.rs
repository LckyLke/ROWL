use rowl::experimental::data_ontology::consistent;
use rowl::experimental::facts::{entails_fact, negation};
use rowl::experimental::model::ObjectProperty;
use rowl::experimental::model::{
    AnonymousIndividual, AtLeastTwo, Axiom, DataProperty, Datatype, Individual, Iri, Literal,
    NamedIndividual, ObjectPropertyExpression,
};
use rowl::reasoner::{default_limits, named, Reasoner};

const FAMILY: &str = "Prefix(:=<https://example.org/f/>)
Ontology(<https://example.org/f/onto>
SubObjectPropertyOf(:hasMother :hasParent)
InverseObjectProperties(:hasParent :hasChild)
FunctionalObjectProperty(:hasMother)
FunctionalDataProperty(:age)
ObjectPropertyAssertion(:hasMother :ann :beth)
ObjectPropertyAssertion(:hasMother :ann :mum)
ObjectPropertyAssertion(:hasParent :carl :dora)
DataPropertyAssertion(:age :ann \"7\"^^xsd:integer)
DifferentIndividuals(:carl :dora)
NegativeObjectPropertyAssertion(:hasParent :dora :carl)
ClassAssertion(:Person :ann)
)
";

fn iri(local: &str) -> Iri {
    Iri {
        spelling: format!("https://example.org/f/{local}").into_bytes(),
    }
}
fn person(local: &str) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(local) })
}
fn role(local: &str) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(local) })
}
fn related(property: &str, source: &str, target: &str) -> Axiom {
    Axiom::ObjectPropertyAssertion(role(property), person(source), person(target))
}
fn unrelated(property: &str, source: &str, target: &str) -> Axiom {
    Axiom::NegativeObjectPropertyAssertion(role(property), person(source), person(target))
}
fn integer(lexical: &str) -> Literal {
    Literal {
        lexical: lexical.as_bytes().to_vec(),
        datatype: Datatype {
            iri: Iri {
                spelling: b"http://www.w3.org/2001/XMLSchema#integer".to_vec(),
            },
        },
    }
}
fn aged(source: &str, years: &str) -> Axiom {
    Axiom::DataPropertyAssertion(
        DataProperty { iri: iri("age") },
        person(source),
        integer(years),
    )
}
fn not_aged(source: &str, years: &str) -> Axiom {
    Axiom::NegativeDataPropertyAssertion(
        DataProperty { iri: iri("age") },
        person(source),
        integer(years),
    )
}
fn pair(first: &str, second: &str) -> AtLeastTwo<Individual> {
    AtLeastTwo {
        first: person(first),
        second: person(second),
        rest: Vec::new(),
    }
}

#[test]
fn named_facts_are_entailed_exactly_when_their_negation_has_no_model() {
    let Ok(reasoner) = Reasoner::from_functional(FAMILY.as_bytes(), &default_limits()) else {
        panic!("the family must load");
    };
    assert_eq!(reasoner.consistent(), Some(true));
    let cases = [
        // A sub-property and an inverse carry the asserted mother.
        (related("hasParent", "ann", "beth"), Some(true)),
        (related("hasChild", "beth", "ann"), Some(true)),
        // Two mothers of one child are one individual.
        (Axiom::SameIndividual(pair("beth", "mum")), Some(true)),
        // Without the unique name assumption, names may denote one individual.
        (
            Axiom::DifferentIndividuals(pair("ann", "carl")),
            Some(false),
        ),
        (Axiom::SameIndividual(pair("ann", "carl")), Some(false)),
        (
            Axiom::DifferentIndividuals(pair("carl", "dora")),
            Some(true),
        ),
        (related("hasParent", "carl", "ann"), Some(false)),
        (unrelated("hasParent", "dora", "carl"), Some(true)),
        (unrelated("hasParent", "carl", "dora"), Some(false)),
        (unrelated("hasParent", "carl", "ann"), Some(false)),
        // Data values: 07 and 7 are one integer, and the age is functional.
        (aged("ann", "7"), Some(true)),
        (aged("ann", "07"), Some(true)),
        (aged("ann", "8"), Some(false)),
        (not_aged("ann", "8"), Some(true)),
        (not_aged("ann", "7"), Some(false)),
        // A class assertion is an instance question.
        (
            Axiom::ClassAssertion(named("https://example.org/f/Person"), person("ann")),
            Some(true),
        ),
    ];
    for (fact, expected) in cases {
        assert_eq!(reasoner.entails(&fact), expected);
        if !matches!(fact, Axiom::ClassAssertion(..)) {
            assert_eq!(entails_fact(&reasoner.ontology().axioms, &fact), expected);
            // The negation of the negation is the fact again.
            let negated = negation(&fact).expect("a named fact has a negation");
            let again = negation(&negated).expect("a negation has a negation");
            assert_eq!(entails_fact(&reasoner.ontology().axioms, &again), expected);
        }
    }
    // The same question asked of the whole closure with the negation added.
    let negated = FAMILY.replace(
        "ClassAssertion(:Person :ann)",
        "ClassAssertion(:Person :ann)\nNegativeObjectPropertyAssertion(:hasChild :beth :ann)",
    );
    let Ok(whole) = Reasoner::from_functional(negated.as_bytes(), &default_limits()) else {
        panic!("the negated family must load");
    };
    assert_eq!(consistent(&whole.ontology().axioms), Some(false));
}

#[test]
fn other_facts_get_no_answer_and_contradictions_entail_everything() {
    let Ok(reasoner) = Reasoner::from_functional(FAMILY.as_bytes(), &default_limits()) else {
        panic!("the family must load");
    };
    let anonymous = Individual::Anonymous(AnonymousIndividual {
        scope: Vec::new(),
        label: b"x".to_vec(),
    });
    let about_anonymous =
        Axiom::ObjectPropertyAssertion(role("hasParent"), anonymous, person("ann"));
    assert_eq!(reasoner.entails(&about_anonymous), None);
    let three = Axiom::SameIndividual(AtLeastTwo {
        first: person("ann"),
        second: person("beth"),
        rest: vec![person("carl")],
    });
    assert_eq!(reasoner.entails(&three), None);
    let contradiction = FAMILY.replace(
        "ClassAssertion(:Person :ann)",
        "ClassAssertion(owl:Nothing :ann)",
    );
    let Ok(inconsistent) = Reasoner::from_functional(contradiction.as_bytes(), &default_limits())
    else {
        panic!("the contradiction must load");
    };
    assert_eq!(inconsistent.consistent(), Some(false));
    assert_eq!(
        inconsistent.entails(&related("hasParent", "carl", "ann")),
        Some(true)
    );
    assert_eq!(
        inconsistent.entails(&Axiom::SameIndividual(pair("ann", "carl"))),
        Some(true)
    );
    assert_eq!(inconsistent.entails(&aged("ann", "8")), Some(true));
}
