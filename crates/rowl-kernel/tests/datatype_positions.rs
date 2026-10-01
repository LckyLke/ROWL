use rowl_kernel::datatype_positions::*;
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
const STRING: &[u8] = b"http://www.w3.org/2001/XMLSchema#string";
fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn datatype(s: &[u8]) -> Datatype {
    Datatype { iri: iri(s) }
}
fn literal(s: &[u8]) -> Literal {
    Literal {
        lexical: b"value".to_vec(),
        datatype: datatype(s),
    }
}
fn atom(s: &[u8]) -> DataRange {
    DataRange::Datatype(datatype(s))
}
fn annotated(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom,
    }
}
fn definition() -> AnnotatedAxiom {
    annotated(Axiom::DatatypeDefinition(datatype(b"Custom"), atom(STRING)))
}
fn property() -> DataProperty {
    DataProperty { iri: iri(b"p") }
}
fn op() -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(b"op") })
}
fn individual() -> Individual {
    Individual::Named(NamedIndividual { iri: iri(b"x") })
}
fn note(s: &[u8]) -> Annotation {
    Annotation {
        annotations: vec![],
        property: AnnotationProperty { iri: iri(b"note") },
        value: AnnotationValue::Literal(literal(s)),
    }
}
fn restriction(base: &[u8], value: &[u8]) -> DataRange {
    DataRange::Restriction(
        datatype(base),
        NonEmpty {
            first: FacetRestriction {
                facet: iri(b"facet"),
                value: literal(value),
            },
            rest: vec![],
        },
    )
}
fn ontology(axioms: Vec<AnnotatedAxiom>, annotations: Vec<Annotation>) -> RawOntology {
    RawOntology {
        identity: OntologyIdentity::Anonymous,
        imports: vec![],
        annotations,
        axioms,
    }
}

#[test]
fn definition_identity_uses_actual_definitions_not_declarations_or_other_iris() {
    let axioms = vec![
        definition(),
        annotated(Axiom::Declaration(Entity::Datatype(datatype(
            b"DeclarationOnly",
        )))),
        annotated(Axiom::AnnotationAssertion(
            AnnotationProperty {
                iri: iri(b"Custom"),
            },
            AnnotationSubject::Iri(iri(b"subject")),
            AnnotationValue::Iri(iri(b"Other")),
        )),
    ];
    assert!(defined_datatype(&axioms, &iri(b"Custom")));
    assert!(!defined_datatype(&axioms, &iri(b"custom")));
    assert!(!defined_datatype(&axioms, &iri(b"DeclarationOnly")));
    assert!(!defined_datatype(&axioms, &iri(b"Other")));
    assert!(!defined_datatype(&vec![], &iri(b"Custom")));
}
#[test]
fn named_ranges_are_allowed_but_literal_and_restriction_base_positions_are_not() {
    let axioms = vec![definition()];
    assert!(range_allowed(&axioms, &atom(b"Custom")));
    assert!(!literal_allowed(&axioms, &literal(b"Custom")));
    assert!(!range_allowed(&axioms, &restriction(b"Custom", STRING)));
    assert!(!range_allowed(&axioms, &restriction(STRING, b"Custom")));
    assert!(range_allowed(&axioms, &restriction(STRING, STRING)));
    assert!(literal_allowed(&axioms, &literal(b"undefined"))); // Availability/lexical validity are separate.
}
#[test]
fn every_range_constructor_checks_nested_positions_and_all_association_members() {
    let axioms = vec![definition()];
    let ranges = vec![
        DataRange::OneOf(NonEmpty {
            first: literal(STRING),
            rest: vec![literal(b"Custom")],
        }),
        DataRange::Complement(Box::new(restriction(b"Custom", STRING))),
        DataRange::Intersection(Box::new(AtLeastTwo {
            first: atom(STRING),
            second: atom(b"Custom"),
            rest: vec![restriction(STRING, b"Custom")],
        })),
        DataRange::Union(Box::new(AtLeastTwo {
            first: atom(b"Custom"),
            second: restriction(b"Custom", STRING),
            rest: vec![],
        })),
    ];
    for range in ranges {
        assert!(!range_allowed(&axioms, &range));
    }
    assert!(range_allowed(
        &axioms,
        &DataRange::Union(Box::new(AtLeastTwo {
            first: atom(b"Custom"),
            second: atom(STRING),
            rest: vec![]
        }))
    ));
}
#[test]
fn data_class_forms_object_nesting_and_optional_fillers_are_covered() {
    let axioms = vec![definition()];
    let bad = vec![
        ClassExpression::DataSomeValuesFrom(property(), restriction(b"Custom", STRING)),
        ClassExpression::DataAllValuesFrom(property(), restriction(STRING, b"Custom")),
        ClassExpression::DataHasValue(property(), literal(b"Custom")),
        ClassExpression::DataMinCardinality(
            Natural::Zero,
            property(),
            Some(restriction(b"Custom", STRING)),
        ),
        ClassExpression::DataMaxCardinality(
            Natural::Zero,
            property(),
            Some(restriction(b"Custom", STRING)),
        ),
        ClassExpression::DataExactCardinality(
            Natural::Zero,
            property(),
            Some(restriction(b"Custom", STRING)),
        ),
    ];
    for expression in bad {
        assert!(!class_allowed(
            &axioms,
            &ClassExpression::ObjectAllValuesFrom(op(), Box::new(expression))
        ));
    }
    let inner = || {
        Box::new(ClassExpression::DataHasValue(
            property(),
            literal(b"Custom"),
        ))
    };
    for expression in [
        ClassExpression::ObjectMinCardinality(Natural::Zero, op(), Some(inner())),
        ClassExpression::ObjectMaxCardinality(Natural::Zero, op(), Some(inner())),
        ClassExpression::ObjectExactCardinality(Natural::Zero, op(), Some(inner())),
        ClassExpression::ObjectComplementOf(inner()),
        ClassExpression::ObjectSomeValuesFrom(op(), inner()),
    ] {
        assert!(!class_allowed(&axioms, &expression));
    }
    assert!(class_allowed(
        &axioms,
        &ClassExpression::DataMinCardinality(Natural::Zero, property(), None)
    ));
    assert!(class_allowed(
        &axioms,
        &ClassExpression::ObjectMaxCardinality(Natural::Zero, op(), None)
    ));
}
#[test]
fn recursive_axiom_and_ontology_annotations_are_checked_with_original_priority() {
    let mut outer = note(STRING);
    outer.annotations.push(note(b"Custom"));
    let mut bad = annotated(Axiom::Declaration(Entity::Class(Class { iri: iri(b"C") })));
    bad.annotations.push(outer);
    let o = ontology(vec![definition(), bad], vec![note(b"Custom")]);
    match check_ontology_positions(&o) {
        PositionCheck::OntologyAnnotation(a) => assert!(std::ptr::eq(a, &o.annotations[0])),
        _ => panic!("expected original ontology annotation before bad axiom"),
    }
    let o = ontology(o.axioms, vec![note(STRING)]);
    assert!(
        matches!(check_ontology_positions(&o),PositionCheck::Axiom(item) if std::ptr::eq(item,&o.axioms[1]))
    );
}
#[test]
fn every_literal_axiom_position_and_range_body_is_checked() {
    let defs = vec![definition()];
    for body in [
        Axiom::DataPropertyAssertion(property(), individual(), literal(b"Custom")),
        Axiom::NegativeDataPropertyAssertion(property(), individual(), literal(b"Custom")),
        Axiom::AnnotationAssertion(
            AnnotationProperty { iri: iri(b"p") },
            AnnotationSubject::Iri(iri(b"x")),
            AnnotationValue::Literal(literal(b"Custom")),
        ),
        Axiom::DataPropertyRange(property(), restriction(b"Custom", STRING)),
        Axiom::DatatypeDefinition(datatype(b"Other"), restriction(STRING, b"Custom")),
    ] {
        assert!(!body_allowed(&defs, &body));
    }
    assert!(body_allowed(
        &defs,
        &Axiom::DataPropertyRange(property(), atom(b"Custom"))
    ));
}
#[test]
fn definitions_after_uses_and_first_original_offender_are_not_missed() {
    let o = ontology(
        vec![
            annotated(Axiom::DataPropertyRange(property(), atom(b"Custom"))),
            annotated(Axiom::DataPropertyAssertion(
                property(),
                individual(),
                literal(b"Custom"),
            )),
            definition(),
            annotated(Axiom::DataPropertyAssertion(
                property(),
                individual(),
                literal(b"Custom"),
            )),
        ],
        vec![],
    );
    assert!(matches!(check_positions(&o.axioms),Some(item) if std::ptr::eq(item,&o.axioms[1])));
    assert!(
        matches!(check_ontology_positions(&o),PositionCheck::Axiom(item) if std::ptr::eq(item,&o.axioms[1]))
    );
    let o = ontology(
        vec![
            definition(),
            annotated(Axiom::DataPropertyRange(property(), atom(b"Custom"))),
        ],
        vec![],
    );
    assert!(check_positions(&o.axioms).is_none());
    assert!(matches!(
        check_ontology_positions(&o),
        PositionCheck::Allowed
    ));
}
