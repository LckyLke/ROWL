use rowl::reasoner::{default_limits, named, Reasoner};

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
