use rowl::reasoner::{default_limits, named, LoadError, Reasoner};

const EXAMPLES: [&[u8]; 4] = [
    include_bytes!("../../../examples/medication-safety.ofn"),
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
fn turtle_and_functional_syntax_give_the_same_answers() {
    let Ok(functional) = Reasoner::from_functional(
        include_bytes!("../../../examples/medication-safety.ofn"),
        &default_limits(),
    ) else {
        panic!("the Functional Syntax example must load");
    };
    let Ok(turtle) =
        Reasoner::from_turtle(include_bytes!("../../../examples/medication-safety.ttl"))
    else {
        panic!("the Turtle example must load");
    };
    let classes = functional.classes();
    assert_eq!(turtle.classes(), classes);
    assert_eq!(turtle.individuals(), functional.individuals());
    assert_eq!(turtle.consistent(), Some(true));
    let left = functional.classify().expect("the example must classify");
    let right = turtle.classify().expect("the example must classify");
    assert_eq!(left.len(), right.len());
    for (a, b) in left.iter().zip(&right) {
        assert_eq!(a.class, b.class);
        assert_eq!(a.satisfiable, b.satisfiable);
        assert_eq!(a.superclasses, b.superclasses);
    }
    for individual in functional.individuals() {
        for class in &classes {
            assert_eq!(
                turtle.instance_of(&individual, &named(class)),
                functional.instance_of(&individual, &named(class))
            );
        }
    }
}

#[test]
fn turtle_loading_reports_why_it_fails() {
    // A relative IRI with no base to resolve it against.
    assert!(matches!(
        Reasoner::from_turtle(b"<a> <b> <c> ."),
        Err(LoadError::Turtle(_))
    ));
    // With a base, the same document is a graph, but it declares nothing.
    assert!(matches!(
        Reasoner::from_turtle_with_base(b"<a> <b> <c> .", b"https://example.org/"),
        Err(LoadError::Graph)
    ));
    let declared =
        b"@base <https://example.org/> .\n<C> a <http://www.w3.org/2002/07/owl#Class> .\n";
    let Ok(reasoner) = Reasoner::from_turtle(declared) else {
        panic!("a declared class must load");
    };
    assert_eq!(
        reasoner.classes(),
        vec!["https://example.org/C".to_string()]
    );
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
