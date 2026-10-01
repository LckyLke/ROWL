use rowl_kernel::datatype_definitions::{check_definitions, defines, predefined, DefinitionCheck};
use rowl_kernel::model::*;
const STRING: &[u8] = b"http://www.w3.org/2001/XMLSchema#string";
const INTEGER: &[u8] = b"http://www.w3.org/2001/XMLSchema#integer";
fn iri(text: &[u8]) -> Iri {
    Iri {
        spelling: text.to_vec(),
    }
}
fn dtype(text: &[u8]) -> Datatype {
    Datatype { iri: iri(text) }
}
fn atom(text: &[u8]) -> DataRange {
    DataRange::Datatype(dtype(text))
}
fn axiom(body: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom: body,
    }
}
fn definition(dt: &[u8], range: DataRange) -> AnnotatedAxiom {
    axiom(Axiom::DatatypeDefinition(dtype(dt), range))
}
fn declaration(dt: &[u8]) -> AnnotatedAxiom {
    axiom(Axiom::Declaration(Entity::Datatype(dtype(dt))))
}
fn ontology(axioms: Vec<AnnotatedAxiom>) -> RawOntology {
    RawOntology {
        identity: OntologyIdentity::Anonymous,
        imports: vec![],
        annotations: vec![],
        axioms,
    }
}
fn note(dt: &[u8]) -> Annotation {
    Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"http://www.w3.org/2000/01/rdf-schema#comment"),
        },
        value: AnnotationValue::Literal(Literal {
            lexical: b"text".to_vec(),
            datatype: dtype(dt),
        }),
    }
}
fn allowed(o: &RawOntology) -> bool {
    matches!(check_definitions(o), DefinitionCheck::Allowed)
}
#[test]
fn predefined_vocabulary_is_exact_and_permits_no_defining_axiom() {
    assert!(predefined(&iri(STRING)));
    assert!(predefined(&iri(INTEGER)));
    assert!(predefined(&iri(
        b"http://www.w3.org/2000/01/rdf-schema#Literal"
    )));
    assert!(!predefined(&iri(b"http://www.w3.org/2002/07/owl#Thing")));
    assert!(!predefined(&iri(
        b"http://www.w3.org/2001/XMLSchema#String"
    )));
    assert!(allowed(&ontology(vec![
        declaration(STRING),
        declaration(INTEGER)
    ])));
    let o = ontology(vec![
        definition(STRING, atom(INTEGER)),
        definition(STRING, atom(STRING)),
    ]);
    let DefinitionCheck::PredefinedRedefined(item) = check_definitions(&o) else {
        panic!("expected redefinition")
    };
    assert!(std::ptr::eq(item, &o.axioms[0]));
}
#[test]
fn custom_datatype_declaration_without_definition_is_rejected() {
    let o = ontology(vec![declaration(b"urn:Code")]);
    let DefinitionCheck::MissingDefinition(dt) = check_definitions(&o) else {
        panic!("expected missing")
    };
    assert_eq!(dt.spelling, b"urn:Code");
    assert!(allowed(&ontology(vec![])));
    assert!(allowed(&ontology(vec![
        declaration(b"urn:Code"),
        definition(b"urn:Code", atom(STRING))
    ])));
}
#[test]
fn equivalent_reordered_nested_raw_definition_copies_count_once() {
    let a = DataRange::Union(Box::new(AtLeastTwo {
        first: atom(STRING),
        second: DataRange::Complement(Box::new(atom(INTEGER))),
        rest: vec![],
    }));
    let b = DataRange::Union(Box::new(AtLeastTwo {
        first: DataRange::Complement(Box::new(atom(INTEGER))),
        second: atom(STRING),
        rest: vec![atom(STRING)],
    }));
    let o = ontology(vec![definition(b"urn:Code", a), definition(b"urn:Code", b)]);
    assert!(allowed(&o));
    assert!(defines(&o.axioms[0], &iri(b"urn:Code")));
    assert!(!defines(&declaration(b"urn:Code"), &iri(b"urn:Code")));
}
#[test]
fn different_ranges_or_metadata_are_multiple_structural_definitions() {
    let o = ontology(vec![
        definition(b"urn:Code", atom(STRING)),
        definition(b"urn:Code", atom(INTEGER)),
    ]);
    let DefinitionCheck::MultipleDefinitions { first, second } = check_definitions(&o) else {
        panic!("expected multiple")
    };
    assert!(std::ptr::eq(first, &o.axioms[0]));
    assert!(std::ptr::eq(second, &o.axioms[1]));
    let mut b = definition(b"urn:Code", atom(STRING));
    b.annotations.push(note(STRING));
    assert!(!allowed(&ontology(vec![
        definition(b"urn:Code", atom(STRING)),
        b
    ])));
}
#[test]
fn missing_datatypes_in_literals_and_nested_annotations_are_not_ignored() {
    let mut item = axiom(Axiom::Declaration(Entity::Class(Class {
        iri: iri(b"urn:Machine"),
    })));
    let mut outer = note(STRING);
    outer.annotations.push(note(b"urn:AnnotationCode"));
    item.annotations.push(outer);
    let o = ontology(vec![item]);
    let DefinitionCheck::MissingDefinition(dt) = check_definitions(&o) else {
        panic!("expected nested missing")
    };
    assert_eq!(dt.spelling, b"urn:AnnotationCode");
    let o = ontology(vec![definition(
        b"urn:Code",
        DataRange::OneOf(NonEmpty {
            first: Literal {
                lexical: b"x".to_vec(),
                datatype: dtype(b"urn:MissingLiteralType"),
            },
            rest: vec![],
        }),
    )]);
    let DefinitionCheck::MissingDefinition(dt) = check_definitions(&o) else {
        panic!("expected literal missing")
    };
    assert_eq!(dt.spelling, b"urn:MissingLiteralType");
}
#[test]
fn ontology_annotations_are_outside_the_axiom_closure() {
    let mut o = ontology(vec![]);
    o.annotations.push(note(b"urn:OnlyOntologyMetadata"));
    assert!(allowed(&o));
}
#[test]
fn definition_presence_does_not_claim_acyclicity_or_lexical_validity() {
    let o = ontology(vec![
        definition(b"urn:A", atom(b"urn:B")),
        definition(b"urn:B", atom(b"urn:A")),
    ]);
    assert!(allowed(&o)); // separate dependency checker must reject the cycle
    let o = ontology(vec![definition(
        b"urn:A",
        DataRange::OneOf(NonEmpty {
            first: Literal {
                lexical: b"invalid integer".to_vec(),
                datatype: dtype(INTEGER),
            },
            rest: vec![],
        }),
    )]);
    assert!(allowed(&o)); // separate lexical/value/facet checking
}
