use rowl_kernel::datatype_restrictions::{check_definition_rules, DatatypeDefinitionCheck};
use rowl_kernel::datatype_restrictions::{check_structural_datatypes, StructuralDatatypeCheck};
use rowl_kernel::model::*;
const STRING: &[u8] = b"http://www.w3.org/2001/XMLSchema#string";
fn datatype(s: &[u8]) -> Datatype {
    Datatype {
        iri: Iri {
            spelling: s.to_vec(),
        },
    }
}
fn definition(name: &[u8], child: &[u8]) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::DatatypeDefinition(datatype(name), DataRange::Datatype(datatype(child))),
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
#[test]
fn availability_diagnostics_precede_cycles_and_preserve_original_axioms() {
    let o = ontology(vec![
        definition(b"A", b"B"),
        definition(b"B", b"A"),
        definition(b"C", b"missing"),
    ]);
    assert!(
        matches!(check_definition_rules(&o),DatatypeDefinitionCheck::MissingDefinition(iri) if iri.spelling==b"missing")
    );
    let o = ontology(vec![
        definition(b"A", b"B"),
        definition(b"B", b"A"),
        definition(b"A", STRING),
    ]);
    match check_definition_rules(&o) {
        DatatypeDefinitionCheck::MultipleDefinitions { first, second } => {
            assert!(std::ptr::eq(first, &o.axioms[0]));
            assert!(std::ptr::eq(second, &o.axioms[2]));
        }
        _ => panic!("expected original conflicting definitions before the cycle"),
    }
    let o = ontology(vec![definition(STRING, STRING)]);
    assert!(
        matches!(check_definition_rules(&o),DatatypeDefinitionCheck::PredefinedRedefined(item) if std::ptr::eq(item,&o.axioms[0]))
    );
}
#[test]
fn fully_available_cycle_reports_original_dependency_endpoints() {
    let o = ontology(vec![definition(b"A", b"B"), definition(b"B", b"A")]);
    match check_definition_rules(&o) {
        DatatypeDefinitionCheck::Cycle { smaller, larger } => {
            let Axiom::DatatypeDefinition(defined, DataRange::Datatype(child)) = &o.axioms[0].axiom
            else {
                unreachable!()
            };
            assert!(std::ptr::eq(smaller, &child.iri));
            assert!(std::ptr::eq(larger, &defined.iri));
        }
        _ => panic!("expected an actual original dependency on the cycle"),
    }
}
#[test]
fn acyclic_complete_definition_chain_and_structural_copies_pass() {
    let o = ontology(vec![
        definition(b"A", b"B"),
        definition(b"B", STRING),
        definition(b"A", b"B"),
    ]);
    assert!(matches!(
        check_definition_rules(&o),
        DatatypeDefinitionCheck::Allowed
    ));
    assert!(matches!(
        check_definition_rules(&ontology(vec![])),
        DatatypeDefinitionCheck::Allowed
    ));
}

fn assertion(datatype_name: &[u8]) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::DataPropertyAssertion(
            DataProperty {
                iri: Iri {
                    spelling: b"p".to_vec(),
                },
            },
            Individual::Named(NamedIndividual {
                iri: Iri {
                    spelling: b"x".to_vec(),
                },
            }),
            Literal {
                lexical: b"text".to_vec(),
                datatype: datatype(datatype_name),
            },
        ),
    }
}

#[test]
fn combined_definition_and_position_checker_preserves_original_forbidden_axiom() {
    let o = ontology(vec![definition(b"Custom", STRING), assertion(b"Custom")]);
    assert!(matches!(
        check_definition_rules(&o),
        DatatypeDefinitionCheck::Allowed
    ));
    assert!(
        matches!(check_structural_datatypes(&o),StructuralDatatypeCheck::ForbiddenAxiomPosition(item) if std::ptr::eq(item,&o.axioms[1]))
    );
    let o = ontology(vec![definition(b"Custom", STRING), assertion(STRING)]);
    assert!(matches!(
        check_structural_datatypes(&o),
        StructuralDatatypeCheck::Allowed
    ));
}

#[test]
fn structural_checker_reports_definition_errors_before_positions() {
    let o = ontology(vec![
        definition(b"A", b"B"),
        definition(b"B", b"A"),
        assertion(b"A"),
    ]);
    assert!(matches!(
        check_structural_datatypes(&o),
        StructuralDatatypeCheck::Cycle { .. }
    ));
    let o = ontology(vec![definition(b"A", b"missing"), assertion(b"A")]);
    assert!(matches!(
        check_structural_datatypes(&o),
        StructuralDatatypeCheck::MissingDefinition(_)
    ));
}

#[test]
fn structural_checker_checks_ontology_annotation_before_axiom_positions() {
    let mut o = ontology(vec![definition(b"Custom", STRING), assertion(b"Custom")]);
    o.annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: Iri {
                spelling: b"note".to_vec(),
            },
        },
        value: AnnotationValue::Literal(Literal {
            lexical: b"text".to_vec(),
            datatype: datatype(b"Custom"),
        }),
    });
    assert!(
        matches!(check_structural_datatypes(&o),StructuralDatatypeCheck::ForbiddenOntologyAnnotation(item) if std::ptr::eq(item,&o.annotations[0]))
    );
}
