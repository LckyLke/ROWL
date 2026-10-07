use rowl::reasoner::{default_limits, named, LoadError, Reasoner};

const EXAMPLES: [&[u8]; 5] = [
    include_bytes!("../../../examples/medication-safety.ofn"),
    include_bytes!("../../../examples/medication-dose.ofn"),
    include_bytes!("../../../examples/maintenance-classes.ofn"),
    include_bytes!("../../../examples/maintenance-individuals.ofn"),
    include_bytes!("../../../examples/maintenance-roles.ofn"),
];

#[test]
fn classification_lists_exactly_the_pairwise_answers() {
    let mut compared = 0;
    for source in EXAMPLES {
        let Ok(reasoner) = Reasoner::from_functional(source, &default_limits()) else {
            panic!("the example must load");
        };
        let classes = reasoner.classes();
        let classified = reasoner.classify().expect("the example must classify");
        assert_eq!(classified.len(), classes.len());
        for (entry, class) in classified.iter().zip(&classes) {
            assert_eq!(&entry.class, class);
            let sub = named(class);
            assert_eq!(reasoner.satisfiable(&sub), Some(entry.satisfiable));
            for other in &classes {
                if other == class || !entry.satisfiable {
                    continue;
                }
                let listed = entry.superclasses.contains(other);
                assert_eq!(reasoner.subsumed(&sub, &named(other)), Some(listed));
                compared += 1;
            }
        }
    }
    assert!(compared > 50, "the examples must have classes to compare");
}

#[test]
fn medication_classification_finds_the_drug_families() {
    let source = include_bytes!("../../../examples/medication-safety.ofn");
    let Ok(reasoner) = Reasoner::from_functional(source, &default_limits()) else {
        panic!("the example must load");
    };
    let classified = reasoner.classify().expect("the example must classify");
    let supers = |iri: &str| {
        classified
            .iter()
            .find(|entry| entry.class == iri)
            .map(|entry| entry.superclasses.clone())
            .unwrap_or_default()
    };
    assert!(supers("https://example.org/medication/Amoxicillin")
        .contains(&"https://example.org/medication/Penicillin".to_string()));
    assert!(supers("https://example.org/medication/Azithromycin")
        .contains(&"https://example.org/medication/Macrolide".to_string()));
}

#[test]
fn ntriples_and_functional_syntax_give_the_same_answers() {
    let Ok(functional) = Reasoner::from_functional(
        include_bytes!("../../../examples/medication-safety.ofn"),
        &default_limits(),
    ) else {
        panic!("the Functional Syntax example must load");
    };
    let Ok(triples) =
        Reasoner::from_ntriples(include_bytes!("../../../examples/medication-safety.nt"))
    else {
        panic!("the N-Triples example must load");
    };
    let classes = functional.classes();
    assert_eq!(triples.classes(), classes);
    assert_eq!(triples.individuals(), functional.individuals());
    assert_eq!(triples.consistent(), Some(true));
    let left = functional.classify().expect("the example must classify");
    let right = triples.classify().expect("the example must classify");
    assert_eq!(left.len(), right.len());
    for (a, b) in left.iter().zip(&right) {
        assert_eq!(a.class, b.class);
        assert_eq!(a.satisfiable, b.satisfiable);
        assert_eq!(a.superclasses, b.superclasses);
    }
    for individual in functional.individuals() {
        for class in &classes {
            assert_eq!(
                triples.instance_of(&individual, &named(class)),
                functional.instance_of(&individual, &named(class))
            );
        }
    }
}

#[test]
fn ntriples_loading_reports_why_it_fails() {
    assert!(matches!(
        Reasoner::from_ntriples(b"<a> <b> ."),
        Err(LoadError::Triples(_))
    ));
    // The property is never declared, so the graph encodes no OWL ontology.
    let undeclared = b"<https://example.org/a> <https://example.org/p> <https://example.org/b> .\n";
    assert!(matches!(
        Reasoner::from_ntriples(undeclared),
        Err(LoadError::Graph)
    ));
}

#[test]
fn doses_are_checked_against_their_limits() {
    let source = include_bytes!("../../../examples/medication-dose.ofn");
    let Ok(reasoner) = Reasoner::from_functional(source, &default_limits()) else {
        panic!("the example must load");
    };
    let dose = |local: &str| format!("https://example.org/dose/{local}");
    assert_eq!(reasoner.consistent(), Some(true));
    let alert = named(&dose("DoseAlert"));
    // rx1: 3000 mg for a child of 8; rx3: 4000.5 mg; rx4: 8001/2 mg, the same.
    for (rx, expected) in [("rx1", true), ("rx2", false), ("rx3", true), ("rx4", true)] {
        assert_eq!(
            reasoner.instance_of(&dose(rx), &alert),
            Some(expected),
            "{rx}"
        );
    }
    assert_eq!(
        reasoner.instance_of(&dose("rx1"), &named(&dose("Child"))),
        Some(true)
    );
    // A hard daily maximum of 4000 mg makes the records inconsistent.
    let text = std::str::from_utf8(source).expect("the example is UTF-8");
    let limited = text.trim_end().trim_end_matches(')').to_string()
        + "SubClassOf(:Paracetamol DataAllValuesFrom(:dailyDoseMg \
           DatatypeRestriction(xsd:decimal xsd:maxInclusive \"4000\"^^xsd:decimal)))\n)\n";
    let Ok(strict) = Reasoner::from_functional(limited.as_bytes(), &default_limits()) else {
        panic!("the limited example must load");
    };
    assert_eq!(strict.consistent(), Some(false));
}
