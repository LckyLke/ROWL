use rowl_kernel::functional_annotations::AnnotationLimits;
use rowl_kernel::functional_classes::ClassLimits;
use rowl_kernel::functional_document::{read_document, DocumentError, DocumentLimits};
use rowl_kernel::functional_model::document_ontology;
use rowl_kernel::model::{
    AnnotationSubject, AnnotationValue, AtLeastTwo, Axiom, Class, ClassExpression, Entity,
    Individual, Iri, NamedIndividual, ObjectProperty, ObjectPropertyExpression, OntologyIdentity,
    RawOntology,
};
use rowl_kernel::source_reasoning::{
    source_class_satisfiable, source_consistent, source_instance_of, source_subsumed,
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
fn errors_and_unsupported_axioms_give_no_answer() {
    let scope = b"s".to_vec();
    // A document error is the reader's first error.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A :B)\n SameIndividual(:a :b)\n)"
        .as_bytes()
        .to_vec();
    assert!(matches!(
        source_consistent(&bytes, &limits(), &scope),
        Err(DocumentError::UnsupportedAxiom { .. })
    ));
    // Object property axioms outside the supported role axioms are read but not answered.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n SubClassOf(:A :B)\n InverseObjectProperties(:p :q)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(answer(source_consistent(&bytes, &limits(), &scope)), None);
    // A read axiom outside the ALC fragment gives no answer.
    let bytes = "Prefix(:=<https://example.org/>)\nOntology(<https://example.org/o>\n ObjectPropertyDomain(ObjectInverseOf(:p) :A)\n)"
        .as_bytes()
        .to_vec();
    assert_eq!(answer(source_consistent(&bytes, &limits(), &scope)), None);
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
