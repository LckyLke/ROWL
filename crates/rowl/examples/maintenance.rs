//! Construct an ontology using the raw structural API. This does not run an OWL
//! reasoner. The corresponding conditional semantic consequence is checked by
//! Rowl.Owl.maintenance_follows in verification/Rowl/OwlLaws.lean.
use rowl::experimental::anonymous_graph::{check_forest, ForestCheck};
use rowl::experimental::anonymous_multiplicity::{check_multiplicity, MultiplicityCheck};
use rowl::experimental::anonymous_restrictions::{check_anonymous, AnonymousCheck};
use rowl::experimental::arity::check_arities;
use rowl::experimental::axiom_equality::{same_axiom, same_body};
use rowl::experimental::axiom_set::{
    build, originals, representative_indices, representative_of, representatives, AxiomOccurrence,
    BuildResult,
};
use rowl::experimental::batch::AxiomOrigin;
use rowl::experimental::class_equality::same_class;
use rowl::experimental::collection::{ontology_entities, EntityUses};
use rowl::experimental::datatype_definitions::{check_definitions, DefinitionCheck};
use rowl::experimental::datatype_restrictions::{
    check_definition_rules, check_structural_datatypes, DatatypeDefinitionCheck,
    StructuralDatatypeCheck,
};
use rowl::experimental::indexing::{check_ontology_typing, IndexedTyping};
use rowl::experimental::keys::check_keys;
use rowl::experimental::model::*;
use rowl::experimental::role_order::{check_regularity, RegularityCheck};
use rowl::experimental::roles::{check_simplicity, SimplicityCheck};
use rowl::experimental::symbols::key_of;
use rowl::experimental::topdata::check_axioms;
use rowl::experimental::typing::{EntityKind, TypingResult};
use rowl::experimental::vocabulary::{check_reserved_vocabulary, VocabularyResult};

fn iri(name: &str) -> Iri {
    Iri {
        spelling: format!("urn:maintenance:{name}").into_bytes(),
    }
}
fn class(name: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(name) })
}
fn person_or_asset(name: &str) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(name) })
}
fn has_part() -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty {
        iri: iri("hasPart"),
    })
}
fn axiom(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom,
    }
}

fn check(ontology: &RawOntology) {
    match check_ontology_typing(ontology, 32) {
        IndexedTyping::CapacityExceeded { iri, .. } => {
            println!(
                "Symbol capacity exceeded for {}",
                String::from_utf8_lossy(&iri.spelling)
            );
        }
        IndexedTyping::Checked { table, result, .. } => match result {
            TypingResult::Valid => {
                println!("Rust declaration check: valid, including implicit built-ins.")
            }
            TypingResult::MissingDeclaration(symbol) => println!(
                "Rust declaration check: missing role declaration for {}",
                String::from_utf8_lossy(key_of(&table, symbol).unwrap())
            ),
            TypingResult::ConflictingDeclarations(symbol) => println!(
                "Rust declaration check: conflicting declarations for {}",
                String::from_utf8_lossy(key_of(&table, symbol).unwrap())
            ),
        },
    }
    match check_reserved_vocabulary(ontology) {
        VocabularyResult::Valid => println!("Rust reserved-vocabulary/header check: valid."),
        VocabularyResult::ReservedOntologyIri(iri) => println!(
            "Rust vocabulary check: reserved ontology IRI {}",
            String::from_utf8_lossy(&iri.spelling)
        ),
        VocabularyResult::ReservedVersionIri(iri) => println!(
            "Rust vocabulary check: reserved version IRI {}",
            String::from_utf8_lossy(&iri.spelling)
        ),
        VocabularyResult::ForbiddenEntity { iri, .. } => println!(
            "Rust vocabulary check: forbidden reserved entity role for {}",
            String::from_utf8_lossy(&iri.spelling)
        ),
    }
}

fn main() {
    let mut ontology = RawOntology {
        identity: OntologyIdentity::Named {
            ontology: iri("ontology"),
            version: None,
        },
        imports: vec![],
        annotations: vec![],
        axioms: vec![
            axiom(Axiom::SubClassOf(
                ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
                    first: class("Machine"),
                    second: ClassExpression::ObjectSomeValuesFrom(
                        has_part(),
                        Box::new(class("FaultyPart")),
                    ),
                    rest: vec![],
                })),
                class("NeedsInspection"),
            )),
            axiom(Axiom::ClassAssertion(
                class("Machine"),
                person_or_asset("pump1"),
            )),
            axiom(Axiom::ObjectPropertyAssertion(
                has_part(),
                person_or_asset("pump1"),
                person_or_asset("motor1"),
            )),
            axiom(Axiom::ClassAssertion(
                class("FaultyPart"),
                person_or_asset("motor1"),
            )),
        ],
    };
    println!("Constructed {} raw axioms:", ontology.axioms.len());
    println!("  Machines with a faulty part need inspection.");
    println!("  pump1 is a Machine; pump1 hasPart motor1; motor1 is a FaultyPart.");
    println!("Lean proves: these premises imply pump1 is a NeedsInspection instance.");
    let collected = ontology_entities(&ontology);
    println!("The Rust collector finds these explicit entity occurrences:");
    let mut cursor = &collected.uses;
    while let EntityUses::Entry { iri, kind, next } = cursor {
        let role = match kind {
            EntityKind::Class => "Class",
            EntityKind::Datatype => "Datatype",
            EntityKind::ObjectProperty => "ObjectProperty",
            EntityKind::DataProperty => "DataProperty",
            EntityKind::AnnotationProperty => "AnnotationProperty",
            EntityKind::NamedIndividual => "NamedIndividual",
        };
        println!("  {} — {role}", String::from_utf8_lossy(&iri.spelling));
        cursor = next;
    }
    drop(collected);
    println!("Adding Machine/NeedsInspection/hasPart declarations, initially omitting FaultyPart:");
    for name in ["Machine", "NeedsInspection"] {
        ontology
            .axioms
            .push(axiom(Axiom::Declaration(Entity::Class(Class {
                iri: iri(name),
            }))));
    }
    ontology
        .axioms
        .push(axiom(Axiom::Declaration(Entity::ObjectProperty(
            ObjectProperty {
                iri: iri("hasPart"),
            },
        ))));
    check(&ontology);
    ontology
        .axioms
        .push(axiom(Axiom::Declaration(Entity::Class(Class {
            iri: iri("FaultyPart"),
        }))));
    println!("Adding the missing FaultyPart declaration:");
    check(&ontology);
    println!("Trying to reuse owl:Thing as an object property:");
    ontology
        .axioms
        .push(axiom(Axiom::Declaration(Entity::ObjectProperty(
            ObjectProperty {
                iri: Iri {
                    spelling: b"http://www.w3.org/2002/07/owl#Thing".to_vec(),
                },
            },
        ))));
    check(&ontology);
    println!("Using owl:topDataProperty as a superproperty for faultCode:");
    let top = || DataProperty {
        iri: Iri {
            spelling: b"http://www.w3.org/2002/07/owl#topDataProperty".to_vec(),
        },
    };
    let mut data_axioms = vec![axiom(Axiom::SubDataPropertyOf(
        DataProperty {
            iri: iri("faultCode"),
        },
        top(),
    ))];
    println!(
        "Rust top-data-property occurrence check: {}.",
        if check_axioms(&data_axioms).is_none() {
            "valid"
        } else {
            "invalid"
        }
    );
    println!("Trying to make owl:topDataProperty functional:");
    data_axioms.push(axiom(Axiom::FunctionalDataProperty(top())));
    println!(
        "Rust top-data-property occurrence check: {}.",
        if check_axioms(&data_axioms).is_none() {
            "valid"
        } else {
            "forbidden occurrence"
        }
    );
    println!("Checking a cardinality restriction on transitive hasPart:");
    let part = || {
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri("hasPart"),
        })
    };
    let mut role_axioms = vec![
        axiom(Axiom::TransitiveObjectProperty(part())),
        axiom(Axiom::SubClassOf(
            ClassExpression::Class(Class {
                iri: iri("Machine"),
            }),
            ClassExpression::ObjectMaxCardinality(rowl::experimental::Natural::Zero, part(), None),
        )),
    ];
    match check_simplicity(&role_axioms) {
        SimplicityCheck::ForbiddenRole(role) => println!(
            "Rust simple-role check: forbidden cardinality property {} (inverse={}).",
            String::from_utf8_lossy(&role.iri.spelling),
            role.inverse,
        ),
        SimplicityCheck::Allowed => println!("Rust simple-role check: allowed."),
        SimplicityCheck::MissingNode(_) => unreachable!("proved complete raw collector"),
    }
    role_axioms.remove(0);
    println!(
        "Removing transitivity: Rust simple-role check is {}.",
        if matches!(check_simplicity(&role_axioms), SimplicityCheck::Allowed) {
            "allowed"
        } else {
            "forbidden"
        }
    );
    println!("Checking hasPart followed by hasPart as a nestedPart chain:");
    let nested = || {
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri("nestedPart"),
        })
    };
    let mut chain_axioms = vec![axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(AtLeastTwo {
            first: has_part(),
            second: has_part(),
            rest: vec![],
        }),
        nested(),
    ))];
    println!(
        "Rust chain regularity check: {}.",
        if matches!(check_regularity(&chain_axioms), RegularityCheck::Regular(_)) {
            "valid order found"
        } else {
            "conflict"
        }
    );
    println!("Adding nestedPart as a subproperty of hasPart:");
    chain_axioms.push(axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Single(nested()),
        has_part(),
    )));
    match check_regularity(&chain_axioms) {
        RegularityCheck::HierarchyConflict { sub, sup } => println!(
            "Rust chain regularity check: forced {} < {} conflicts with reverse hierarchy reachability.",
            String::from_utf8_lossy(&sub.iri.spelling), String::from_utf8_lossy(&sup.iri.spelling),
        ),
        RegularityCheck::Regular(_) => println!("Rust chain regularity check: valid order found."),
        RegularityCheck::MissingPair { .. } | RegularityCheck::MissingHierarchyNode(_) => unreachable!("proved complete raw collector"),
    }
    let unknown = |label: &str| {
        Individual::Anonymous(AnonymousIndividual {
            scope: b"maintenance-document".to_vec(),
            label: label.as_bytes().to_vec(),
        })
    };
    let mut anonymous_parts = vec![
        axiom(Axiom::ObjectPropertyAssertion(
            has_part(),
            unknown("assembly"),
            unknown("motor"),
        )),
        axiom(Axiom::ObjectPropertyAssertion(
            has_part(),
            unknown("motor"),
            unknown("bearing"),
        )),
    ];
    println!(
        "Unknown assembly → motor → bearing: anonymous graph is {}.",
        if matches!(check_forest(&anonymous_parts), ForestCheck::Forest) {
            "a forest"
        } else {
            "invalid"
        }
    );
    anonymous_parts.push(axiom(Axiom::ObjectPropertyAssertion(
        has_part(),
        unknown("bearing"),
        unknown("assembly"),
    )));
    println!(
        "Adding bearing → assembly: anonymous graph check reports {}.",
        if matches!(check_forest(&anonymous_parts), ForestCheck::Cycle { .. }) {
            "an undirected cycle"
        } else {
            "another result"
        }
    );
    let mut repeated_part = vec![
        axiom(Axiom::ObjectPropertyAssertion(
            has_part(),
            unknown("assembly"),
            unknown("motor"),
        )),
        axiom(Axiom::ObjectPropertyAssertion(
            has_part(),
            unknown("assembly"),
            unknown("motor"),
        )),
    ];
    println!(
        "Repeating the same unknown-part assertion: multiplicity check is {}.",
        if matches!(
            check_multiplicity(&repeated_part),
            MultiplicityCheck::Allowed
        ) {
            "allowed: one structural axiom"
        } else {
            "invalid"
        }
    );
    repeated_part.push(axiom(Axiom::ObjectPropertyAssertion(
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri("containsPart"),
        }),
        unknown("assembly"),
        unknown("motor"),
    )));
    println!(
        "Adding containsPart between those same unknown parts: multiplicity check reports {}.",
        if matches!(
            check_multiplicity(&repeated_part),
            MultiplicityCheck::MultipleAssertions { .. }
        ) {
            "two distinct assertions on one anonymous edge"
        } else {
            "another result"
        }
    );
    let mut connected_parts = vec![
        axiom(Axiom::ObjectPropertyAssertion(
            has_part(),
            unknown("assembly"),
            person_or_asset("pump1"),
        )),
        axiom(Axiom::ObjectPropertyAssertion(
            has_part(),
            unknown("assembly"),
            person_or_asset("pump2"),
        )),
        axiom(Axiom::ObjectPropertyAssertion(
            has_part(),
            unknown("assembly"),
            unknown("motor"),
        )),
    ];
    println!(
        "Unknown assembly attached to two named pumps, with an unknown motor: all anonymous restrictions are {}.",
        if matches!(check_anonymous(&connected_parts), AnonymousCheck::Allowed) {
            "allowed: motor supplies the component root"
        } else { "invalid" }
    );
    connected_parts.push(axiom(Axiom::ObjectPropertyAssertion(
        has_part(),
        unknown("motor"),
        person_or_asset("pump1"),
    )));
    connected_parts.push(axiom(Axiom::ObjectPropertyAssertion(
        has_part(),
        unknown("motor"),
        person_or_asset("pump2"),
    )));
    println!(
        "Attaching that motor to both named pumps: combined checker reports {}.",
        if matches!(
            check_anonymous(&connected_parts),
            AnonymousCheck::NoBoundaryRoot(_)
        ) {
            "no qualifying root in the anonymous component"
        } else {
            "another result"
        }
    );
    let decimal = || Datatype {
        iri: Iri {
            spelling: b"http://www.w3.org/2001/XMLSchema#decimal".to_vec(),
        },
    };
    let safe_temperature = || Datatype {
        iri: iri("SafeTemperature"),
    };
    let lower = || FacetRestriction {
        facet: Iri {
            spelling: b"http://www.w3.org/2001/XMLSchema#minInclusive".to_vec(),
        },
        value: Literal {
            lexical: b"0".to_vec(),
            datatype: decimal(),
        },
    };
    let upper = || FacetRestriction {
        facet: Iri {
            spelling: b"http://www.w3.org/2001/XMLSchema#maxInclusive".to_vec(),
        },
        value: Literal {
            lexical: b"90".to_vec(),
            datatype: decimal(),
        },
    };
    let definition = axiom(Axiom::DatatypeDefinition(
        safe_temperature(),
        DataRange::Restriction(
            decimal(),
            NonEmpty {
                first: lower(),
                rest: vec![upper()],
            },
        ),
    ));
    let mut temperatures = RawOntology {
        identity: OntologyIdentity::Anonymous,
        imports: vec![],
        annotations: vec![],
        axioms: vec![axiom(Axiom::Declaration(Entity::Datatype(
            safe_temperature(),
        )))],
    };
    assert!(matches!(
        check_definitions(&temperatures),
        DefinitionCheck::MissingDefinition(_)
    ));
    println!("SafeTemperature declared without a definition: datatype availability reports its missing definition.");
    temperatures.axioms.push(definition);
    assert!(matches!(
        check_definitions(&temperatures),
        DefinitionCheck::Allowed
    ));
    temperatures.axioms.push(axiom(Axiom::DatatypeDefinition(
        safe_temperature(),
        DataRange::Restriction(
            decimal(),
            NonEmpty {
                first: upper(),
                rest: vec![lower()],
            },
        ),
    )));
    assert!(matches!(
        check_definitions(&temperatures),
        DefinitionCheck::Allowed
    ));
    println!("Adding its 0–90 decimal range and a copy with reordered facets: one structural definition, allowed.");
    temperatures.axioms.push(axiom(Axiom::DatatypeDefinition(
        safe_temperature(),
        DataRange::Datatype(decimal()),
    )));
    assert!(matches!(
        check_definitions(&temperatures),
        DefinitionCheck::MultipleDefinitions { .. }
    ));
    println!("Adding a second definition covering all decimals: conflicting original definitions are reported.");
    temperatures.axioms = vec![axiom(Axiom::DatatypeDefinition(
        decimal(),
        DataRange::Datatype(decimal()),
    ))];
    assert!(matches!(
        check_definitions(&temperatures),
        DefinitionCheck::PredefinedRedefined(_)
    ));
    println!("Trying to redefine xsd:decimal: rejected as a predefined datatype redefinition.");
    let recorded_temperature = || Datatype {
        iri: iri("RecordedTemperature"),
    };
    temperatures.axioms = vec![
        axiom(Axiom::Declaration(Entity::Datatype(safe_temperature()))),
        axiom(Axiom::Declaration(Entity::Datatype(recorded_temperature()))),
        axiom(Axiom::DatatypeDefinition(
            safe_temperature(),
            DataRange::Datatype(recorded_temperature()),
        )),
        axiom(Axiom::DatatypeDefinition(
            recorded_temperature(),
            DataRange::Datatype(decimal()),
        )),
    ];
    assert!(matches!(
        check_definition_rules(&temperatures),
        DatatypeDefinitionCheck::Allowed
    ));
    println!("SafeTemperature defined using RecordedTemperature, which uses decimal: availability and dependency order both pass.");
    temperatures.axioms[3] = axiom(Axiom::DatatypeDefinition(
        recorded_temperature(),
        DataRange::Datatype(safe_temperature()),
    ));
    assert!(matches!(
        check_definition_rules(&temperatures),
        DatatypeDefinitionCheck::Cycle { .. }
    ));
    println!("Changing RecordedTemperature to use SafeTemperature: the combined definition checker reports a circular dependency.");
    temperatures.axioms[3] = axiom(Axiom::DatatypeDefinition(
        recorded_temperature(),
        DataRange::Datatype(decimal()),
    ));
    let reading = || DataProperty {
        iri: iri("hasTemperature"),
    };
    temperatures
        .axioms
        .push(axiom(Axiom::Declaration(Entity::DataProperty(reading()))));
    temperatures.axioms.push(axiom(Axiom::DataPropertyRange(
        reading(),
        DataRange::Datatype(safe_temperature()),
    )));
    assert!(matches!(
        check_structural_datatypes(&temperatures),
        StructuralDatatypeCheck::Allowed
    ));
    println!("Using SafeTemperature as the named range of hasTemperature: all structural datatype checks pass.");
    temperatures.axioms.push(axiom(Axiom::DataPropertyAssertion(
        reading(),
        person_or_asset("pump1"),
        Literal {
            lexical: b"30".to_vec(),
            datatype: safe_temperature(),
        },
    )));
    assert!(matches!(
        check_structural_datatypes(&temperatures),
        StructuralDatatypeCheck::ForbiddenAxiomPosition(_)
    ));
    println!("Typing the literal 30 as SafeTemperature: rejected because defined datatypes have no lexical space.");
    let last = temperatures.axioms.len() - 1;
    temperatures.axioms[last] = axiom(Axiom::DataPropertyAssertion(
        reading(),
        person_or_asset("pump1"),
        Literal {
            lexical: b"30".to_vec(),
            datatype: decimal(),
        },
    ));
    assert!(matches!(
        check_structural_datatypes(&temperatures),
        StructuralDatatypeCheck::Allowed
    ));
    println!("Typing that literal as decimal, while retaining the SafeTemperature range: structural checks pass.");
    println!("These are structural datatype checks; concrete lexical/facet/value validation, full DL validation, complete OWL byte parsing and automatic OWL reasoning remain pending.");

    let condition = || {
        ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
            first: class("Machine"),
            second: ClassExpression::ObjectSomeValuesFrom(
                has_part(),
                Box::new(class("FaultyPart")),
            ),
            rest: vec![],
        }))
    };
    let reordered = ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first: ClassExpression::ObjectSomeValuesFrom(has_part(), Box::new(class("FaultyPart"))),
        second: class("Machine"),
        rest: vec![class("Machine")],
    }));
    assert!(same_class(&condition(), &reordered));
    println!("Machine AND hasPart SOME FaultyPart compares structurally equal after reordering or repeating members.");
    let unqualified = ClassExpression::ObjectMinCardinality(
        rowl::experimental::Natural::Succ(Box::new(rowl::experimental::Natural::Zero)),
        has_part(),
        None,
    );
    let qualified = ClassExpression::ObjectMinCardinality(
        rowl::experimental::Natural::Succ(Box::new(rowl::experimental::Natural::Zero)),
        has_part(),
        Some(Box::new(ClassExpression::Class(Class {
            iri: Iri {
                spelling: b"http://www.w3.org/2002/07/owl#Thing".to_vec(),
            },
        }))),
    );
    assert!(same_class(&unqualified, &qualified));
    println!("At least one hasPart, with an omitted filler or explicit owl:Thing: structurally equal after inserting the default.");
    let mut machine_keys = vec![axiom(Axiom::HasKey(class("Machine"), vec![], vec![]))];
    assert!(std::ptr::eq(
        check_keys(&machine_keys).unwrap(),
        &machine_keys[0]
    ));
    println!("An empty Machine key is rejected, retaining the original axiom.");
    machine_keys[0] = axiom(Axiom::HasKey(
        class("Machine"),
        vec![],
        vec![DataProperty {
            iri: iri("serialNumber"),
        }],
    ));
    assert!(check_keys(&machine_keys).is_none());
    println!("Adding serialNumber as a data key member passes the nonempty-key rule; automatic identity reasoning remains pending.");

    let mut association = vec![axiom(Axiom::EquivalentClasses(AtLeastTwo {
        first: class("Machine"),
        second: class("Machine"),
        rest: vec![],
    }))];
    assert!(check_arities(&association).is_some());
    println!("EquivalentClasses(Machine Machine) fails: two written members give only one distinct class.");
    association[0] = axiom(Axiom::EquivalentClasses(AtLeastTwo {
        first: class("Machine"),
        second: class("Machine"),
        rest: vec![class("Asset")],
    }));
    assert!(check_arities(&association).is_none());
    println!("Adding Asset supplies a second distinct class; the ordinary association may retain repeated Machine occurrences.");
    association[0] = axiom(Axiom::DisjointClasses(AtLeastTwo {
        first: class("SafeMachine"),
        second: class("FaultyMachine"),
        rest: vec![class("SafeMachine")],
    }));
    assert!(std::ptr::eq(
        check_arities(&association).unwrap(),
        &association[0]
    ));
    println!("DisjointClasses(SafeMachine FaultyMachine SafeMachine) fails the adopted duplicate-disjointness rule before any duplicate removal.");
    association[0] = axiom(Axiom::DisjointClasses(AtLeastTwo {
        first: class("SafeMachine"),
        second: class("FaultyMachine"),
        rest: vec![],
    }));
    assert!(check_arities(&association).is_none());
    println!("Removing the repeated member passes the structural arity stage; logical consistency and complete DL validation remain separate.");
    association[0] = axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(AtLeastTwo {
            first: has_part(),
            second: has_part(),
            rest: vec![],
        }),
        has_part(),
    ));
    assert!(check_arities(&association).is_none());
    println!("An ordered hasPart/hasPart chain passes the arity stage with its repetitions preserved; hierarchy regularity has its own checker.");

    let source = || Annotation {
        annotations: vec![],
        property: AnnotationProperty { iri: iri("source") },
        value: AnnotationValue::Iri(iri("inspectionManual")),
    };
    let policy = AnnotatedAxiom {
        annotations: vec![source()],
        axiom: Axiom::SubClassOf(condition(), class("NeedsInspection")),
    };
    let mut imported_policy = AnnotatedAxiom {
        annotations: vec![source(), source()],
        axiom: Axiom::SubClassOf(reordered, class("NeedsInspection")),
    };
    assert!(same_axiom(&policy, &imported_policy));
    println!("The inspection policy and an imported copy compare as the same complete axiom despite reordered class members and repeated source annotations.");
    imported_policy.annotations[0].value = AnnotationValue::Iri(iri("differentManual"));
    assert!(same_body(&policy.axiom, &imported_policy.axiom));
    assert!(!same_axiom(&policy, &imported_policy));
    println!("Adding a different source annotation preserves body identity but makes the complete annotated policy distinct; provenance is retained.");
    let installed_in = || {
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri("installedIn"),
        })
    };
    let forward = axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(AtLeastTwo {
            first: has_part(),
            second: installed_in(),
            rest: vec![],
        }),
        installed_in(),
    ));
    let backward = axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(AtLeastTwo {
            first: installed_in(),
            second: has_part(),
            rest: vec![],
        }),
        installed_in(),
    ));
    assert!(!same_axiom(&forward, &backward));
    println!("hasPart followed by installedIn is structurally different from the reversed chain; this comparison does not execute either reasoning rule.");

    let original_occurrences = vec![
        AxiomOccurrence {
            origin: AxiomOrigin {
                document: 0,
                ordinal: 17,
            },
            axiom: policy,
        },
        AxiomOccurrence {
            origin: AxiomOrigin {
                document: 1,
                ordinal: 2,
            },
            axiom: imported_policy,
        },
        AxiomOccurrence {
            origin: AxiomOrigin {
                document: 2,
                ordinal: 8,
            },
            axiom: AnnotatedAxiom {
                annotations: vec![source(), source()],
                axiom: Axiom::SubClassOf(condition(), class("NeedsInspection")),
            },
        },
    ];
    match build(&original_occurrences) {
        BuildResult::Set(set) => {
            assert_eq!(representatives(&set), &[0, 1]);
            assert_eq!(representative_indices(&set), &[0, 1, 0]);
            assert_eq!(originals(&set).len(), 3);
            assert!(std::ptr::eq(
                representative_of(&set, 2).unwrap(),
                &original_occurrences[0]
            ));
            assert_eq!(originals(&set)[2].origin.document, 2);
            assert_eq!(originals(&set)[2].origin.ordinal, 8);
            println!("The actual axiom-set builder groups three policy occurrences into two complete axiom classes: the imported equivalent copy points to the first policy, while changed source metadata stays distinct. All three original document/ordinal records remain accessible. The source-linked proofs establish earliest representatives, total lookups and model/consistency/entailment preservation for this supplied arity-valid closure; this does not run an OWL solver.");
        }
        BuildResult::InvalidArity(_) => panic!("maintenance policies should pass arity checking"),
    }
}
