use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::{read_document, DocumentError, DocumentLimits};
use rowl_kernel::functional_model::document_ontology;
use rowl_kernel::model::{
    AnnotationSubject, AnnotationValue, AtLeastTwo, Axiom, Class, ClassExpression, Entity,
    Individual, Iri, NamedIndividual, ObjectProperty, ObjectPropertyExpression, OntologyIdentity,
    RawOntology,
};
use rowl_kernel::shi_ontology::{prepared_consistent, prepared_instance_of};
use rowl_kernel::source_reasoning::{
    source_class_satisfiable, source_consistent, source_instance_of, source_ontology,
    source_prepared, source_subsumed,
};

const EX: &str = "https://example.org/maintenance/";

fn limits() -> DocumentLimits {
    DocumentLimits {
        tokens: 2000,
        prefixes: 10,
        prefix_value: 100,
        imports: 10,
        iri: 100,
        axioms: 100,
        annotations: AnnotationLimits {
            depth: 2,
            count: 10,
            iri: 100,
            lexical: 100,
        },
        classes: ClassLimits {
            depth: 10,
            count: 10,
            iri: 100,
        },
    }
}
fn iri(value: &str) -> Iri {
    Iri {
        spelling: value.as_bytes().to_vec(),
    }
}
fn named(local: &str) -> ClassExpression {
    ClassExpression::Class(Class {
        iri: iri(&format!("{EX}{local}")),
    })
}
fn both(first: ClassExpression, second: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first,
        second,
        rest: Vec::new(),
    }))
}
fn some_part(filler: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri(&format!("{EX}hasPart")),
        }),
        Box::new(filler),
    )
}
fn class_name(expression: &ClassExpression) -> &[u8] {
    match expression {
        ClassExpression::Class(class) => &class.iri.spelling,
        _ => panic!("a named class"),
    }
}
fn ontology(source: &str, scope: &[u8]) -> RawOntology {
    let document = read_document(&source.as_bytes().to_vec(), &limits())
        .unwrap_or_else(|_| panic!("fixture document"));
    document_ontology(&document, &scope.to_vec())
        .unwrap_or_else(|| panic!("every read document maps"))
}
fn answer(result: Result<Option<bool>, DocumentError>) -> Option<bool> {
    result.unwrap_or_else(|_| panic!("the document reads"))
}

#[test]
fn maintenance_questions_are_answered_from_the_original_bytes() {
    let bytes = include_bytes!("../../../examples/maintenance-classes.ofn").to_vec();
    let scope = b"maintenance".to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    assert_eq!(
        answer(source_subsumed(
            &bytes,
            &limits(),
            &scope,
            &named("Pump"),
            &some_part(named("Part"))
        )),
        Some(true)
    );
    assert_eq!(
        answer(source_subsumed(
            &bytes,
            &limits(),
            &scope,
            &both(named("Pump"), some_part(named("FaultyPart"))),
            &ClassExpression::ObjectComplementOf(Box::new(named("InService")))
        )),
        Some(true)
    );
    assert_eq!(
        answer(source_class_satisfiable(
            &bytes,
            &limits(),
            &scope,
            &both(named("Motor"), named("Valve"))
        )),
        Some(false)
    );
    assert_eq!(
        answer(source_subsumed(
            &bytes,
            &limits(),
            &scope,
            &named("Machine"),
            &named("NeedsInspection")
        )),
        Some(false)
    );
}

#[test]
fn the_model_keeps_every_source_record() {
    let model = ontology(
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o> <https://example.org/o/1>\n Import(<https://example.org/base>)\n Annotation(Annotation(rdfs:comment \"nested\") rdfs:label \"o\")\n Declaration(Class(:A))\n AnnotationAssertion(rdfs:seeAlso _:x :A)\n SubClassOf(Annotation(rdfs:comment \"why\") :A ObjectIntersectionOf(:B :C :D))\n ObjectPropertyDomain(ObjectInverseOf(:p) :A)\n ClassAssertion(:A _:y)\n ObjectPropertyAssertion(ObjectInverseOf(:p) :a :b)\n)",
        b"doc-1",
    );
    match &model.identity {
        OntologyIdentity::Named {
            ontology,
            version: Some(version),
        } => {
            assert_eq!(ontology.spelling, b"https://example.org/o");
            assert_eq!(version.spelling, b"https://example.org/o/1");
        }
        _ => panic!("the named identity with its version"),
    }
    assert_eq!(model.imports.len(), 1);
    assert_eq!(model.imports[0].spelling, b"https://example.org/base");
    assert_eq!(model.annotations.len(), 1);
    let label = &model.annotations[0];
    assert_eq!(
        label.property.iri.spelling,
        b"http://www.w3.org/2000/01/rdf-schema#label"
    );
    assert_eq!(label.annotations.len(), 1);
    match &label.value {
        AnnotationValue::Literal(literal) => {
            // A plain literal abbreviates "o@"^^rdf:PlainLiteral.
            assert_eq!(literal.lexical, b"o@");
            assert_eq!(
                literal.datatype.iri.spelling,
                b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"
            );
        }
        _ => panic!("a literal label"),
    }
    assert_eq!(model.axioms.len(), 6);
    match &model.axioms[0].axiom {
        Axiom::Declaration(Entity::Class(class)) => {
            assert_eq!(class.iri.spelling, b"https://example.org/A")
        }
        _ => panic!("the class declaration"),
    }
    match &model.axioms[1].axiom {
        Axiom::AnnotationAssertion(property, AnnotationSubject::Anonymous(node), value) => {
            assert_eq!(
                property.iri.spelling,
                b"http://www.w3.org/2000/01/rdf-schema#seeAlso"
            );
            assert_eq!(node.scope, b"doc-1");
            assert_eq!(node.label, b"x");
            match value {
                AnnotationValue::Iri(target) => {
                    assert_eq!(target.spelling, b"https://example.org/A")
                }
                _ => panic!("an IRI value"),
            }
        }
        _ => panic!("the annotation assertion on a node ID"),
    }
    assert_eq!(model.axioms[2].annotations.len(), 1);
    match &model.axioms[2].axiom {
        Axiom::SubClassOf(sub, ClassExpression::ObjectIntersectionOf(members)) => {
            assert_eq!(class_name(sub), b"https://example.org/A");
            assert_eq!(class_name(&members.first), b"https://example.org/B");
            assert_eq!(class_name(&members.second), b"https://example.org/C");
            assert_eq!(members.rest.len(), 1);
            assert_eq!(class_name(&members.rest[0]), b"https://example.org/D");
        }
        _ => panic!("the subclass axiom with its intersection"),
    }
    match &model.axioms[3].axiom {
        Axiom::ObjectPropertyDomain(ObjectPropertyExpression::Inverse(property), domain) => {
            assert_eq!(property.iri.spelling, b"https://example.org/p");
            assert_eq!(class_name(domain), b"https://example.org/A");
        }
        _ => panic!("the domain of an inverse property"),
    }
    match &model.axioms[4].axiom {
        Axiom::ClassAssertion(class, Individual::Anonymous(node)) => {
            assert_eq!(class_name(class), b"https://example.org/A");
            assert_eq!(node.scope, b"doc-1");
            assert_eq!(node.label, b"y");
        }
        _ => panic!("the class assertion on a node ID"),
    }
    match &model.axioms[5].axiom {
        Axiom::ObjectPropertyAssertion(
            ObjectPropertyExpression::Inverse(property),
            Individual::Named(source),
            Individual::Named(target),
        ) => {
            assert_eq!(property.iri.spelling, b"https://example.org/p");
            assert_eq!(source.iri.spelling, b"https://example.org/a");
            assert_eq!(target.iri.spelling, b"https://example.org/b");
        }
        _ => panic!("the property assertion through an inverse property"),
    }
}

#[test]
fn equalities_and_individual_classes_map_with_their_individuals() {
    let model = ontology(
        "Prefix(:=<https://example.org/>)\nOntology(\n SameIndividual(:a _:x :c)\n DifferentIndividuals(:a :b)\n SubClassOf(ObjectOneOf(:a _:y) ObjectHasValue(ObjectInverseOf(:p) :b))\n)",
        b"doc-2",
    );
    let name = |individual: &Individual| match individual {
        Individual::Named(named) => named.iri.spelling.clone(),
        Individual::Anonymous(node) => {
            assert_eq!(node.scope, b"doc-2");
            [b"_:".to_vec(), node.label.clone()].concat()
        }
    };
    assert_eq!(model.axioms.len(), 3);
    match &model.axioms[0].axiom {
        Axiom::SameIndividual(members) => {
            assert_eq!(name(&members.first), b"https://example.org/a");
            assert_eq!(name(&members.second), b"_:x");
            assert_eq!(members.rest.len(), 1);
            assert_eq!(name(&members.rest[0]), b"https://example.org/c");
        }
        _ => panic!("the individual equality"),
    }
    match &model.axioms[1].axiom {
        Axiom::DifferentIndividuals(members) => {
            assert_eq!(name(&members.first), b"https://example.org/a");
            assert_eq!(name(&members.second), b"https://example.org/b");
            assert!(members.rest.is_empty());
        }
        _ => panic!("the individual inequality"),
    }
    match &model.axioms[2].axiom {
        Axiom::SubClassOf(
            ClassExpression::ObjectOneOf(members),
            ClassExpression::ObjectHasValue(ObjectPropertyExpression::Inverse(property), value),
        ) => {
            assert_eq!(name(&members.first), b"https://example.org/a");
            assert_eq!(members.rest.len(), 1);
            assert_eq!(name(&members.rest[0]), b"_:y");
            assert_eq!(property.iri.spelling, b"https://example.org/p");
            assert_eq!(name(value), b"https://example.org/b");
        }
        _ => panic!("the enumeration and the value restriction"),
    }
}

#[test]
fn errors_and_unsupported_axioms_give_no_answer() {
    let scope = b"s".to_vec();
    // A document error is the reader's first error.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A :B)\n HasKey(:A () ())\n)"
        .as_bytes()
        .to_vec();
    assert!(matches!(
        source_consistent(&bytes, &limits(), &scope),
        Err(DocumentError::UnsupportedAxiom { .. })
    ));
    // Enumerations of named individuals are answered from the bytes, and
    // those of anonymous individuals get no answer.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n ClassAssertion(ObjectOneOf(:a) :b)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n ClassAssertion(ObjectOneOf(:a) :b)\n DifferentIndividuals(:a :b)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(false)
    );
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n ClassAssertion(ObjectOneOf(_:x) :b)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(answer(source_consistent(&bytes, &limits(), &scope)), None);
    // Individual equalities and inequalities are answered from the bytes.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SameIndividual(:pump1 :p1)\n DifferentIndividuals(:p1 :pump2)\n ClassAssertion(:Pump :pump1)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    let p1 = NamedIndividual {
        iri: Iri {
            spelling: b"https://example.org/p1".to_vec(),
        },
    };
    let pump = ClassExpression::Class(Class {
        iri: Iri {
            spelling: b"https://example.org/Pump".to_vec(),
        },
    });
    assert_eq!(
        answer(source_instance_of(&bytes, &limits(), &scope, &p1, &pump)),
        Some(true)
    );
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SameIndividual(:pump1 :p1)\n DifferentIndividuals(:p1 :pump1)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(false)
    );
    // Role axioms with built-in object properties are read but not answered.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A :B)\n SubObjectPropertyOf(:p owl:topObjectProperty)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(answer(source_consistent(&bytes, &limits(), &scope)), None);
    // A functional property merges two values, which then clash.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n FunctionalObjectProperty(:p)\n ObjectPropertyAssertion(:p :a :b)\n ObjectPropertyAssertion(:p :a :c)\n ClassAssertion(:B :b)\n ClassAssertion(ObjectComplementOf(:B) :c)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(false)
    );
    // A negative property assertion next to a role axiom is answered too.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SymmetricObjectProperty(:p)\n NegativeObjectPropertyAssertion(:p :a :b)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SymmetricObjectProperty(:p)\n ObjectPropertyAssertion(:p :b :a)\n NegativeObjectPropertyAssertion(:p :a :b)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(false)
    );
    // Domains of inverse properties and inverse role axioms are answered.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n ObjectPropertyDomain(ObjectInverseOf(:p) :A)\n InverseObjectProperties(:p :q)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    // A consistent document with an unsatisfiable class: E ⊑ D ⊑ B ⊑ A ⊑ ¬A.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A ObjectComplementOf(:A))\n EquivalentClasses(:A ObjectUnionOf(:B :C))\n SubClassOf(:B :A)\n DisjointUnion(:D :B :E)\n SubClassOf(:D :B)\n SubClassOf(:E :D)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_class_satisfiable(
            &bytes,
            &limits(),
            &scope,
            &ClassExpression::Class(Class {
                iri: iri("https://example.org/E")
            })
        )),
        Some(false)
    );
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
}

#[test]
fn individuals_are_reasoned_about_from_the_original_bytes() {
    let bytes = include_bytes!("../../../examples/maintenance-individuals.ofn").to_vec();
    let scope = b"fleet".to_vec();
    let individual = |name: &str| NamedIndividual {
        iri: iri(&format!("{EX}{name}")),
    };
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &individual("pump1"),
            &named("NeedsInspection")
        )),
        Some(true)
    );
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &individual("pump2"),
            &named("NeedsInspection")
        )),
        Some(false)
    );
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &individual("pump2"),
            &named("Machine")
        )),
        Some(true)
    );
}

#[test]
fn role_axioms_are_reasoned_about_from_the_original_bytes() {
    let bytes = include_bytes!("../../../examples/maintenance-roles.ofn").to_vec();
    let scope = b"plant".to_vec();
    let individual = |name: &str| NamedIndividual {
        iri: iri(&format!("{EX}{name}")),
    };
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    // bearing1 is a component of a component of pump1, so a part of it.
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &individual("pump1"),
            &named("NeedsInspection")
        )),
        Some(true)
    );
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &individual("motor1"),
            &named("NeedsInspection")
        )),
        Some(false)
    );
}

#[test]
fn medication_alerts_are_derived_from_the_original_bytes() {
    let bytes = include_bytes!("../../../examples/medication-safety.ofn").to_vec();
    let scope = b"records".to_vec();
    let medication = "https://example.org/medication/";
    let patient = |name: &str| NamedIndividual {
        iri: iri(&format!("{medication}{name}")),
    };
    let alert = ClassExpression::Class(Class {
        iri: iri(&format!("{medication}AllergyAlert")),
    });
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    // The penicillin is an active ingredient of a capsule inside the pack.
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &patient("alice"),
            &alert
        )),
        Some(true)
    );
    // The same pack without a recorded allergy needs no alert.
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &patient("bob"),
            &alert
        )),
        Some(false)
    );
    // Azithromycin is a macrolide, and macrolides are no penicillins.
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &patient("carol"),
            &alert
        )),
        Some(false)
    );
    let ingredient = ObjectPropertyExpression::Property(ObjectProperty {
        iri: iri(&format!("{medication}hasActiveIngredient")),
    });
    let penicillin = ClassExpression::Class(Class {
        iri: iri(&format!("{medication}Penicillin")),
    });
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &patient("tablet"),
            &ClassExpression::ObjectSomeValuesFrom(
                ingredient,
                Box::new(ClassExpression::ObjectComplementOf(Box::new(penicillin)))
            )
        )),
        Some(true)
    );
}

#[test]
fn inverse_properties_are_reasoned_about_from_the_original_bytes() {
    let bytes = "Prefix(:=<https://example.org/family/>)\nOntology(<https://example.org/family>\n InverseObjectProperties(:hasParent :hasChild)\n SubClassOf(ObjectSomeValuesFrom(ObjectInverseOf(:hasChild) :Person) :Child)\n SymmetricObjectProperty(:hasSibling)\n ClassAssertion(:Person :ada)\n ObjectPropertyAssertion(:hasChild :ada :ben)\n ObjectPropertyAssertion(:hasSibling :cy :ben)\n)"
        .as_bytes()
        .to_vec();
    let scope = b"family".to_vec();
    let person = |name: &str| NamedIndividual {
        iri: iri(&format!("https://example.org/family/{name}")),
    };
    let child = ClassExpression::Class(Class {
        iri: iri("https://example.org/family/Child"),
    });
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    // ben's parent ada is recorded only as having ben as a child.
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &person("ben"),
            &child
        )),
        Some(true)
    );
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &person("ada"),
            &child
        )),
        Some(false)
    );
    // ben's sibling is recorded only from cy's side.
    let sibling = ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Property(ObjectProperty {
            iri: iri("https://example.org/family/hasSibling"),
        }),
        Box::new(ClassExpression::Class(Class {
            iri: iri("http://www.w3.org/2002/07/owl#Thing"),
        })),
    );
    assert_eq!(
        answer(source_instance_of(
            &bytes,
            &limits(),
            &scope,
            &person("ben"),
            &sibling
        )),
        Some(true)
    );
}

#[test]
fn one_reading_answers_many_questions() {
    let bytes = include_bytes!("../../../examples/medication-safety.ofn").to_vec();
    let scope = b"records".to_vec();
    let medication = "https://example.org/medication/";
    let alert = ClassExpression::Class(Class {
        iri: iri(&format!("{medication}AllergyAlert")),
    });
    let read = source_ontology(&bytes, &limits(), &scope)
        .unwrap_or_else(|_| panic!("the document reads"))
        .unwrap_or_else(|| panic!("every read document maps"));
    assert_eq!(read.axioms.len(), 30);
    let prepared = source_prepared(&bytes, &limits(), &scope)
        .unwrap_or_else(|_| panic!("the document reads"))
        .unwrap_or_else(|| panic!("supported axioms"));
    assert_eq!(prepared_consistent(&prepared), Some(true));
    for (name, expected) in [("alice", true), ("bob", false), ("carol", false)] {
        let patient = NamedIndividual {
            iri: iri(&format!("{medication}{name}")),
        };
        assert_eq!(
            prepared_instance_of(&prepared, &patient, &alert),
            Some(expected)
        );
    }
    // A document error is the reader's first error, for reading and preparing alike.
    let bytes =
        "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n HasKey(:A () ())\n)"
            .as_bytes()
            .to_vec();
    assert!(matches!(
        source_ontology(&bytes, &limits(), &scope),
        Err(DocumentError::UnsupportedAxiom { .. })
    ));
    assert!(matches!(
        source_prepared(&bytes, &limits(), &scope),
        Err(DocumentError::UnsupportedAxiom { .. })
    ));
    // Axioms outside the supported fragment are read but not prepared.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubObjectPropertyOf(:p owl:topObjectProperty)\n)"
        .as_bytes()
        .to_vec();
    assert!(matches!(
        source_ontology(&bytes, &limits(), &scope),
        Ok(Some(_))
    ));
    assert!(matches!(
        source_prepared(&bytes, &limits(), &scope),
        Ok(None)
    ));
}

#[test]
fn role_chains_are_answered_from_source_bytes() {
    let scope = b"family".to_vec();
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubObjectPropertyOf(ObjectPropertyChain(:hasParent :hasBrother) :hasUncle)\n ObjectPropertyAssertion(:hasParent :ann :bob)\n ObjectPropertyAssertion(:hasBrother :bob :carl)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubObjectPropertyOf(ObjectPropertyChain(:hasParent :hasBrother) :hasUncle)\n ObjectPropertyAssertion(:hasParent :ann :bob)\n ObjectPropertyAssertion(:hasBrother :bob :carl)\n NegativeObjectPropertyAssertion(:hasUncle :ann :carl)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(false)
    );
}

#[test]
fn the_empty_role_is_answered_from_source_bytes() {
    let scope = b"roles".to_vec();
    // A property included in owl:bottomObjectProperty relates nothing.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubObjectPropertyOf(:p owl:bottomObjectProperty)\n ObjectPropertyAssertion(:p :a :b)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(false)
    );
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubObjectPropertyOf(:p owl:bottomObjectProperty)\n NegativeObjectPropertyAssertion(owl:bottomObjectProperty :a :b)\n ClassAssertion(:A :a)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(
        answer(source_consistent(&bytes, &limits(), &scope)),
        Some(true)
    );
}
