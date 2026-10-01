use rowl_kernel::indexing::{check_ontology_typing, index_ontology, IndexResult, IndexedTyping};
use rowl_kernel::model::*;
use rowl_kernel::symbols::{key_of, lookup};
use rowl_kernel::typing::{EntityKind, Occurrences, TypingResult};
fn iri(s: &str) -> Iri {
    Iri {
        spelling: s.as_bytes().to_vec(),
    }
}
fn class(s: &str) -> Class {
    Class { iri: iri(s) }
}
fn bare(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom,
    }
}
fn ontology(axioms: Vec<AnnotatedAxiom>) -> RawOntology {
    RawOntology {
        identity: OntologyIdentity::Anonymous,
        imports: vec![],
        annotations: vec![],
        axioms,
    }
}
fn role(kind: &EntityKind) -> u8 {
    match kind {
        EntityKind::Class => 0,
        EntityKind::Datatype => 1,
        EntityKind::ObjectProperty => 2,
        EntityKind::DataProperty => 3,
        EntityKind::AnnotationProperty => 4,
        EntityKind::NamedIndividual => 5,
    }
}
fn rows(
    table: &rowl_kernel::symbols::SymbolTable<'_>,
    indexed: &Occurrences,
) -> Vec<(Vec<u8>, u8)> {
    let mut cursor = indexed;
    let mut out = vec![];
    while let Occurrences::Entry { symbol, kind, next } = cursor {
        out.push((key_of(table, *symbol).unwrap().clone(), role(kind)));
        cursor = next;
    }
    out
}
#[test]
fn actual_ontology_typing_does_not_require_caller_supplied_symbols() {
    let make = |declare| {
        let mut axioms = vec![bare(Axiom::Declaration(Entity::Class(class(
            "urn:Machine",
        ))))];
        if declare {
            axioms.push(bare(Axiom::Declaration(Entity::Class(class("urn:Asset")))));
        }
        axioms.push(bare(Axiom::SubClassOf(
            ClassExpression::Class(class("urn:Machine")),
            ClassExpression::Class(class("urn:Asset")),
        )));
        ontology(axioms)
    };
    let raw = make(false);
    let IndexedTyping::Checked { table, result, .. } = check_ontology_typing(&raw, 10) else {
        panic!("unexpected capacity");
    };
    let TypingResult::MissingDeclaration(symbol) = result else {
        panic!("missing declaration not diagnosed");
    };
    assert_eq!(key_of(&table, symbol).unwrap(), b"urn:Asset");
    let raw = make(true);
    assert!(matches!(
        check_ontology_typing(&raw, 10),
        IndexedTyping::Checked {
            result: TypingResult::Valid,
            ..
        }
    ));
}
#[test]
fn punning_uses_one_identity_and_retains_every_role_and_repeat() {
    let raw = ontology(vec![
        bare(Axiom::Declaration(Entity::Class(class("urn:A")))),
        bare(Axiom::Declaration(Entity::ObjectProperty(ObjectProperty {
            iri: iri("urn:A"),
        }))),
        bare(Axiom::Declaration(Entity::Class(class("urn:A")))),
        bare(Axiom::ClassAssertion(
            ClassExpression::Class(class("urn:A")),
            Individual::Named(NamedIndividual { iri: iri("urn:A") }),
        )),
    ]);
    let IndexedTyping::Checked {
        table,
        declarations,
        uses,
        result,
    } = check_ontology_typing(&raw, 1)
    else {
        panic!("same key exceeded budget");
    };
    assert!(matches!(result, TypingResult::Valid));
    assert_eq!(lookup(&table, &b"urn:A".to_vec()), Some(0));
    assert_eq!(
        rows(&table, &declarations)
            .iter()
            .map(|x| x.1)
            .collect::<Vec<_>>(),
        vec![0, 2, 0]
    );
    assert_eq!(
        rows(&table, &uses).iter().map(|x| x.1).collect::<Vec<_>>(),
        vec![0, 2, 0, 0, 5]
    );
    assert!(key_of(&table, 1).is_none());
}
#[test]
fn conflict_is_about_spelling_across_distinct_iri_allocations() {
    let raw = ontology(vec![
        bare(Axiom::Declaration(Entity::Class(class("urn:X")))),
        bare(Axiom::Declaration(Entity::Datatype(Datatype {
            iri: iri("urn:X"),
        }))),
    ]);
    let IndexedTyping::Checked { table, result, .. } = check_ontology_typing(&raw, 1) else {
        panic!("unexpected capacity");
    };
    let TypingResult::ConflictingDeclarations(symbol) = result else {
        panic!("wrong result");
    };
    assert_eq!(key_of(&table, symbol).unwrap(), b"urn:X");
}
#[test]
fn capacity_failure_in_declarations_and_uses_never_truncates_successfully() {
    for declared in [false, true] {
        let mut axioms = vec![bare(Axiom::Declaration(Entity::Class(class("urn:A"))))];
        if declared {
            axioms.push(bare(Axiom::Declaration(Entity::Class(class("urn:B")))));
        } else {
            axioms.push(bare(Axiom::ClassAssertion(
                ClassExpression::Class(class("urn:A")),
                Individual::Named(NamedIndividual { iri: iri("urn:B") }),
            )));
        }
        let raw = ontology(axioms);
        let IndexResult::CapacityExceeded { table, iri: failed } = index_ontology(&raw, 1) else {
            panic!("partial result accepted");
        };
        assert_eq!(failed.spelling, b"urn:B");
        assert_eq!(key_of(&table, 0).unwrap(), b"urn:A");
        assert!(key_of(&table, 1).is_none());
    }
    let raw = ontology(vec![]);
    assert!(matches!(
        check_ontology_typing(&raw, 0),
        IndexedTyping::Checked {
            result: TypingResult::Valid,
            ..
        }
    ));
}
#[test]
fn exact_spelling_is_not_case_percent_or_unicode_normalized() {
    let names = ["urn:X", "urn:x", "urn:%58", "urn:é", "urn:e\u{301}"];
    let raw = ontology(
        names
            .iter()
            .map(|s| bare(Axiom::Declaration(Entity::Class(class(s)))))
            .collect(),
    );
    let IndexResult::Complete {
        table,
        declarations,
        ..
    } = index_ontology(&raw, 5)
    else {
        panic!("unexpected capacity");
    };
    assert_eq!(
        rows(&table, &declarations)
            .iter()
            .map(|x| x.0.clone())
            .collect::<Vec<_>>(),
        names
            .iter()
            .map(|s| s.as_bytes().to_vec())
            .collect::<Vec<_>>()
    );
    for (id, key) in names.iter().enumerate() {
        assert_eq!(lookup(&table, &key.as_bytes().to_vec()), Some(id as u32));
    }
}

#[test]
fn built_in_class_property_datatype_and_annotation_roles_are_implicit() {
    let raw = ontology(vec![
        bare(Axiom::ClassAssertion(
            ClassExpression::Class(class("http://www.w3.org/2002/07/owl#Thing")),
            Individual::Named(NamedIndividual {
                iri: iri("urn:item"),
            }),
        )),
        bare(Axiom::FunctionalObjectProperty(
            ObjectPropertyExpression::Property(ObjectProperty {
                iri: iri("http://www.w3.org/2002/07/owl#bottomObjectProperty"),
            }),
        )),
        bare(Axiom::FunctionalDataProperty(DataProperty {
            iri: iri("http://www.w3.org/2002/07/owl#bottomDataProperty"),
        })),
        bare(Axiom::Declaration(Entity::Class(class("urn:hasValue")))),
        bare(Axiom::Declaration(Entity::DataProperty(DataProperty {
            iri: iri("urn:value"),
        }))),
        bare(Axiom::DataPropertyRange(
            DataProperty {
                iri: iri("urn:value"),
            },
            DataRange::Datatype(Datatype {
                iri: iri("http://www.w3.org/2001/XMLSchema#integer"),
            }),
        )),
        AnnotatedAxiom {
            annotations: vec![Annotation {
                annotations: vec![],
                property: AnnotationProperty {
                    iri: iri("http://www.w3.org/2000/01/rdf-schema#label"),
                },
                value: AnnotationValue::Literal(Literal {
                    lexical: "exact label".as_bytes().to_vec(),
                    datatype: Datatype {
                        iri: iri("http://www.w3.org/2001/XMLSchema#string"),
                    },
                }),
            }],
            axiom: Axiom::Declaration(Entity::Class(class("urn:hasValue"))),
        },
    ]);
    let IndexedTyping::Checked {
        table,
        declarations,
        result,
        ..
    } = check_ontology_typing(&raw, 20)
    else {
        panic!("unexpected capacity");
    };
    assert!(matches!(result, TypingResult::Valid));
    let declared = rows(&table, &declarations);
    assert!(declared.contains(&(b"http://www.w3.org/2001/XMLSchema#integer".to_vec(), 1)));
    assert!(declared.contains(&(b"http://www.w3.org/2000/01/rdf-schema#label".to_vec(), 4)));
    assert!(declared.contains(&(b"http://www.w3.org/2001/XMLSchema#string".to_vec(), 1)));
}

#[test]
fn implicit_builtin_declaration_conflicts_cannot_be_hidden_by_explicit_retyping() {
    for name in [
        "http://www.w3.org/2001/XMLSchema#integer",
        "http://www.w3.org/2000/01/rdf-schema#Literal",
    ] {
        let raw = ontology(vec![bare(Axiom::Declaration(Entity::Class(class(name))))]);
        let IndexedTyping::Checked { table, result, .. } = check_ontology_typing(&raw, 1) else {
            panic!("unexpected capacity");
        };
        let TypingResult::ConflictingDeclarations(symbol) = result else {
            panic!("implicit datatype declaration ignored");
        };
        assert_eq!(key_of(&table, symbol).unwrap(), name.as_bytes());
    }
    let raw = ontology(vec![bare(Axiom::Declaration(Entity::DataProperty(
        DataProperty {
            iri: iri("http://www.w3.org/2000/01/rdf-schema#label"),
        },
    )))]);
    assert!(matches!(
        check_ontology_typing(&raw, 1),
        IndexedTyping::Checked {
            result: TypingResult::ConflictingDeclarations(_),
            ..
        }
    ));
}

#[test]
fn ontology_annotations_do_not_create_axiom_closure_declaration_requirements() {
    let mut raw = ontology(vec![]);
    raw.annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri("urn:metadata-only"),
        },
        value: AnnotationValue::Iri(iri("urn:annotation-value")),
    });
    let IndexResult::Complete { table, uses, .. } = index_ontology(&raw, 0) else {
        panic!("metadata consumed axiom symbol capacity");
    };
    assert!(matches!(uses, Occurrences::Empty));
    assert!(key_of(&table, 0).is_none());
    assert!(matches!(
        check_ontology_typing(&raw, 0),
        IndexedTyping::Checked {
            result: TypingResult::Valid,
            ..
        }
    ));
    raw.axioms.push(AnnotatedAxiom {
        annotations: vec![Annotation {
            annotations: vec![],
            property: AnnotationProperty {
                iri: iri("urn:metadata-only"),
            },
            value: AnnotationValue::Iri(iri("urn:annotation-value")),
        }],
        axiom: Axiom::Declaration(Entity::NamedIndividual(NamedIndividual {
            iri: iri("urn:item"),
        })),
    });
    let IndexedTyping::Checked { table, result, .. } = check_ontology_typing(&raw, 2) else {
        panic!("unexpected capacity");
    };
    let TypingResult::MissingDeclaration(symbol) = result else {
        panic!("axiom annotation property was ignored");
    };
    assert_eq!(key_of(&table, symbol).unwrap(), b"urn:metadata-only");
}
