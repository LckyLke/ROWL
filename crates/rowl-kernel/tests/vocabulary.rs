use rowl_kernel::indexing::{check_ontology_typing, IndexedTyping};
use rowl_kernel::model::*;
use rowl_kernel::typing::{EntityKind, TypingResult};
use rowl_kernel::vocabulary::*;

fn iri(spelling: &str) -> Iri {
    Iri {
        spelling: spelling.as_bytes().to_vec(),
    }
}

fn ontology(identity: OntologyIdentity, axioms: Vec<Axiom>) -> RawOntology {
    RawOntology {
        identity,
        imports: vec![],
        annotations: vec![],
        axioms: axioms
            .into_iter()
            .map(|axiom| AnnotatedAxiom {
                annotations: vec![],
                axiom,
            })
            .collect(),
    }
}

#[test]
fn reserved_namespace_matching_is_exact_and_includes_unknown_terms() {
    for spelling in [
        "http://www.w3.org/1999/02/22-rdf-syntax-ns#unknown",
        "http://www.w3.org/2000/01/rdf-schema#",
        "http://www.w3.org/2001/XMLSchema#notAnOwlDatatype",
        "http://www.w3.org/2002/07/owl#NotARealBuiltin",
    ] {
        assert!(reserved_iri(&spelling.as_bytes().to_vec()));
        assert!(!entity_iri_allowed(&iri(spelling), &EntityKind::Class));
    }
    for spelling in [
        "",
        "http://www.w3.org/2002/07/owl",
        "HTTP://www.w3.org/2002/07/owl#Thing",
        "http://www.w3.org/2002/07/owl%23Thing",
        "http://www.w3.org/2002/07/owl-other#Thing",
        "urn:custom:Thing",
    ] {
        assert!(!reserved_iri(&spelling.as_bytes().to_vec()));
        assert!(entity_iri_allowed(&iri(spelling), &EntityKind::Class));
    }
}

#[test]
fn builtins_have_exactly_their_permitted_entity_roles() {
    let examples = [
        ("http://www.w3.org/2002/07/owl#Thing", EntityKind::Class),
        (
            "http://www.w3.org/2002/07/owl#topObjectProperty",
            EntityKind::ObjectProperty,
        ),
        (
            "http://www.w3.org/2002/07/owl#bottomDataProperty",
            EntityKind::DataProperty,
        ),
        (
            "http://www.w3.org/2001/XMLSchema#integer",
            EntityKind::Datatype,
        ),
        (
            "http://www.w3.org/2000/01/rdf-schema#label",
            EntityKind::AnnotationProperty,
        ),
    ];
    for (spelling, role) in examples {
        assert!(entity_iri_allowed(&iri(spelling), &role));
        assert!(!entity_iri_allowed(
            &iri(spelling),
            &EntityKind::NamedIndividual
        ));
    }
    assert!(!entity_iri_allowed(
        &iri("http://www.w3.org/2002/07/owl#Thing"),
        &EntityKind::ObjectProperty
    ));
}

#[test]
fn declaration_punning_cannot_authorize_a_reserved_iri_in_the_wrong_role() {
    let input = ontology(
        OntologyIdentity::Anonymous,
        vec![Axiom::Declaration(Entity::ObjectProperty(ObjectProperty {
            iri: iri("http://www.w3.org/2002/07/owl#Thing"),
        }))],
    );
    // Generic typing permits Class/ObjectProperty punning. The additional
    // vocabulary restriction must reject this same actual ontology.
    assert!(matches!(
        check_ontology_typing(&input, 8),
        IndexedTyping::Checked {
            result: TypingResult::Valid,
            ..
        }
    ));
    let VocabularyResult::ForbiddenEntity {
        iri: bad,
        kind: EntityKind::ObjectProperty,
    } = check_reserved_vocabulary(&input)
    else {
        panic!("reserved-role violation was hidden by allowed punning")
    };
    assert_eq!(bad.spelling, b"http://www.w3.org/2002/07/owl#Thing");
}

#[test]
fn ontology_and_version_headers_are_checked_before_entity_uses() {
    let input = ontology(
        OntologyIdentity::Named {
            ontology: iri("http://www.w3.org/2002/07/owl#Thing"),
            version: Some(iri("http://www.w3.org/2002/07/owl#v1")),
        },
        vec![],
    );
    assert!(matches!(
        check_reserved_vocabulary(&input),
        VocabularyResult::ReservedOntologyIri(_)
    ));
    let input = ontology(
        OntologyIdentity::Named {
            ontology: iri("urn:maintenance"),
            version: Some(iri("http://www.w3.org/2002/07/owl#v1")),
        },
        vec![],
    );
    assert!(matches!(
        check_reserved_vocabulary(&input),
        VocabularyResult::ReservedVersionIri(_)
    ));
    let input = ontology(
        OntologyIdentity::Named {
            ontology: iri("urn:maintenance"),
            version: Some(iri("urn:maintenance:version:1")),
        },
        vec![],
    );
    assert!(matches!(
        check_reserved_vocabulary(&input),
        VocabularyResult::Valid
    ));
}

#[test]
fn ontology_annotations_are_checked_but_untyped_iri_values_are_unrestricted() {
    let mut input = ontology(OntologyIdentity::Anonymous, vec![]);
    input.annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri("urn:custom:annotation"),
        },
        value: AnnotationValue::Iri(iri("http://www.w3.org/2002/07/owl#anything")),
    });
    assert!(matches!(
        check_reserved_vocabulary(&input),
        VocabularyResult::Valid
    ));
    // Typing excludes ontology-level annotations; reserved-vocabulary validity
    // still applies to their typed properties, including nested annotations.
    input.annotations[0].annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri("http://www.w3.org/2002/07/owl#Thing"),
        },
        value: AnnotationValue::Iri(iri("urn:value")),
    });
    assert!(matches!(
        check_ontology_typing(&input, 8),
        IndexedTyping::Checked {
            result: TypingResult::Valid,
            ..
        }
    ));
    assert!(matches!(
        check_reserved_vocabulary(&input),
        VocabularyResult::ForbiddenEntity {
            kind: EntityKind::AnnotationProperty,
            ..
        }
    ));
}
