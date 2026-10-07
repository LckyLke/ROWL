use rowl::experimental::components::{component_closure, plain_question};
use rowl::experimental::data_ontology::{prepare, prepared_instance_of};
use rowl::experimental::model::{Iri, NamedIndividual};
use rowl::reasoner::{default_limits, named, Reasoner};

/// Records of independent prescriptions, linked to their own age and dose
/// groups, with equivalences that make every node branch.
fn records(count: usize) -> String {
    let mut text = String::from(
        "Prefix(:=<https://example.org/r/>)\nOntology(<https://example.org/r/onto>\n\
         EquivalentClasses(:Child ObjectSomeValuesFrom(:ageGroup :Young))\n\
         EquivalentClasses(:HighDose ObjectSomeValuesFrom(:doseGroup :Large))\n\
         DisjointClasses(:Young :Old)\nDisjointClasses(:Large :Small)\n\
         SubClassOf(ObjectIntersectionOf(:Child :HighDose) :Overdose)\n\
         SubClassOf(:OnParacetamol :Prescription)\n",
    );
    for i in 0..count {
        let age = if i % 3 == 0 { "Young" } else { "Old" };
        let dose = if i % 2 == 0 { "Large" } else { "Small" };
        text.push_str(&format!(
            "ClassAssertion(:OnParacetamol :p{i})\nObjectPropertyAssertion(:ageGroup :p{i} :a{i})\n\
             ClassAssertion(:{age} :a{i})\nObjectPropertyAssertion(:doseGroup :p{i} :d{i})\n\
             ClassAssertion(:{dose} :d{i})\n"
        ));
    }
    text.push_str(")\n");
    text
}

#[test]
fn parts_answer_like_the_whole_closure() {
    let generated = records(6);
    let sources: [&[u8]; 4] = [
        include_bytes!("../../../examples/medication-dose.ofn"),
        include_bytes!("../../../examples/medication-safety.ofn"),
        include_bytes!("../../../examples/maintenance-individuals.ofn"),
        generated.as_bytes(),
    ];
    let mut compared = 0;
    let mut split = 0;
    for source in sources {
        let Ok(reasoner) = Reasoner::from_functional(source, &default_limits()) else {
            panic!("the example must load");
        };
        assert_eq!(reasoner.consistent(), Some(true));
        let axioms = &reasoner.ontology().axioms;
        let whole = prepare(axioms).expect("the example must be prepared");
        for individual in reasoner.individuals() {
            let individual = NamedIndividual {
                iri: Iri {
                    spelling: individual.into_bytes(),
                },
            };
            let Some(part) = component_closure(axioms, &individual) else {
                continue;
            };
            split += 1;
            assert!(part.len() <= axioms.len());
            let prepared = prepare(&part).expect("a part must be prepared");
            for class in reasoner.classes() {
                let class = named(&class);
                assert!(plain_question(&class));
                assert_eq!(
                    prepared_instance_of(&prepared, &individual, &class),
                    prepared_instance_of(&whole, &individual, &class)
                );
                compared += 1;
            }
        }
    }
    assert!(split > 20, "the examples must have parts");
    assert!(
        compared > 200,
        "the examples must have questions to compare"
    );
}

#[test]
fn a_part_holds_only_the_records_of_the_individual() {
    let generated = records(10);
    let Ok(reasoner) = Reasoner::from_functional(generated.as_bytes(), &default_limits()) else {
        panic!("the records must load");
    };
    let axioms = &reasoner.ontology().axioms;
    let individual = NamedIndividual {
        iri: Iri {
            spelling: b"https://example.org/r/p3".to_vec(),
        },
    };
    let part = component_closure(axioms, &individual).expect("the records fall apart");
    // The six axioms other than assertions and the five assertions of p3.
    assert_eq!(part.len(), 11);
    let overdose = named("https://example.org/r/Overdose");
    assert_eq!(
        reasoner.instance_of("https://example.org/r/p0", &overdose),
        Some(true)
    );
    assert_eq!(
        reasoner.instance_of("https://example.org/r/p3", &overdose),
        Some(false)
    );
}

#[test]
fn closures_that_do_not_fall_apart_have_no_part() {
    let source = b"Prefix(:=<https://example.org/n/>)\nOntology(<https://example.org/n/onto>\n\
        EquivalentClasses(:Weekend ObjectOneOf(:saturday :sunday))\nClassAssertion(:Day :monday)\n)\n";
    let Ok(reasoner) = Reasoner::from_functional(source, &default_limits()) else {
        panic!("the document must load");
    };
    let individual = NamedIndividual {
        iri: Iri {
            spelling: b"https://example.org/n/monday".to_vec(),
        },
    };
    assert!(component_closure(&reasoner.ontology().axioms, &individual).is_none());
}
