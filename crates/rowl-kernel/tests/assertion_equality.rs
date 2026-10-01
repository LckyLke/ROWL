use rowl_kernel::assertion_equality::*;
use rowl_kernel::model::*;
use std::collections::BTreeSet;

fn iri(bytes: &[u8]) -> Iri {
    Iri {
        spelling: bytes.to_vec(),
    }
}
fn literal(text: &[u8], datatype: &[u8]) -> Literal {
    Literal {
        lexical: text.to_vec(),
        datatype: Datatype { iri: iri(datatype) },
    }
}
fn anonymous(scope: &[u8], label: &[u8]) -> AnonymousIndividual {
    AnonymousIndividual {
        scope: scope.to_vec(),
        label: label.to_vec(),
    }
}
fn annotation(text: &[u8], children: Vec<Annotation>) -> Annotation {
    Annotation {
        annotations: children,
        property: AnnotationProperty {
            iri: iri(b"urn:note"),
        },
        value: AnnotationValue::Literal(literal(text, b"urn:string")),
    }
}
fn assertion(
    property: &[u8],
    inverse: bool,
    source: &[u8],
    target: &[u8],
    notes: Vec<Annotation>,
) -> AnnotatedAxiom {
    let property = ObjectProperty { iri: iri(property) };
    AnnotatedAxiom {
        annotations: notes,
        axiom: Axiom::ObjectPropertyAssertion(
            if inverse {
                ObjectPropertyExpression::Inverse(property)
            } else {
                ObjectPropertyExpression::Property(property)
            },
            Individual::Anonymous(anonymous(b"doc", source)),
            Individual::Anonymous(anonymous(b"doc", target)),
        ),
    }
}

#[test]
fn literals_compare_structure_instead_of_datatype_values() {
    assert!(same_literal(
        &literal(b"01", b"urn:integer"),
        &literal(b"01", b"urn:integer")
    ));
    assert!(!same_literal(
        &literal(b"01", b"urn:integer"),
        &literal(b"1", b"urn:integer")
    ));
    assert!(!same_literal(
        &literal(b"1", b"urn:integer"),
        &literal(b"1", b"urn:string")
    ));
    assert!(same_literal(
        &literal(&[0xff, 0], b""),
        &literal(&[0xff, 0], b"")
    ));
    assert!(!same_literal(&literal(b"ab", b"c"), &literal(b"a", b"bc")));
}

#[test]
fn value_variants_and_individual_kinds_stay_distinct() {
    let values = [
        AnnotationValue::Iri(iri(b"x")),
        AnnotationValue::Anonymous(anonymous(b"doc", b"x")),
        AnnotationValue::Literal(literal(b"x", b"urn:string")),
    ];
    for (a, left) in values.iter().enumerate() {
        for (b, right) in values.iter().enumerate() {
            assert_eq!(same_annotation_value(left, right), a == b);
        }
    }
    let named = Individual::Named(NamedIndividual { iri: iri(b"x") });
    let anon = Individual::Anonymous(anonymous(b"doc", b"x"));
    assert!(!same_individual_value(&named, &anon));
    assert!(!same_individual_value(&anon, &named));
    assert!(same_individual_value(
        &anon,
        &Individual::Anonymous(anonymous(b"doc", b"x"))
    ));
    assert!(!same_individual_value(
        &anon,
        &Individual::Anonymous(anonymous(b"other", b"x"))
    ));
}

#[test]
fn direct_and_inverse_property_expressions_are_structurally_distinct() {
    let direct = ObjectPropertyExpression::Property(ObjectProperty { iri: iri(b"urn:p") });
    let inverse = ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(b"urn:p") });
    assert!(same_property(&direct, &direct));
    assert!(same_property(&inverse, &inverse));
    assert!(!same_property(&direct, &inverse));
    assert!(!same_property(&inverse, &direct));
}

#[test]
fn annotation_order_and_duplicates_are_ignored_at_each_nesting_level() {
    let left = annotation(
        b"root",
        vec![annotation(b"a", vec![]), annotation(b"b", vec![])],
    );
    let right = annotation(
        b"root",
        vec![
            annotation(b"b", vec![]),
            annotation(b"a", vec![]),
            annotation(b"a", vec![]),
        ],
    );
    assert!(same_annotation(&left, &right));
    assert!(same_annotation(&right, &left));
    let lists_left = vec![left, annotation(b"tail", vec![])];
    let lists_right = vec![
        annotation(b"tail", vec![]),
        right,
        annotation(b"tail", vec![]),
    ];
    assert!(same_annotation_set(&lists_left, &lists_right));
    assert!(same_annotation_set(&vec![], &vec![]));
    assert!(!same_annotation_set(&lists_left, &vec![]));
    assert!(!same_annotation_set(&vec![], &lists_right));
}

#[test]
fn annotation_nesting_and_all_atomic_fields_are_preserved() {
    let nested = annotation(b"root", vec![annotation(b"child", vec![])]);
    let flattened = vec![annotation(b"root", vec![]), annotation(b"child", vec![])];
    assert!(!same_annotation_set(&vec![nested], &flattened));
    let mut other_property = annotation(b"root", vec![]);
    other_property.property.iri = iri(b"urn:other");
    assert!(!same_annotation(
        &annotation(b"root", vec![]),
        &other_property
    ));
    let note = |scope: &[u8]| Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"urn:note"),
        },
        value: AnnotationValue::Anonymous(anonymous(scope, b"x")),
    };
    assert!(!same_annotation(&note(b"one"), &note(b"two")));
}

#[test]
fn assertion_comparison_includes_ordered_body_and_unordered_annotations() {
    let first = assertion(
        b"urn:p",
        false,
        b"a",
        b"b",
        vec![annotation(b"x", vec![]), annotation(b"y", vec![])],
    );
    let same = assertion(
        b"urn:p",
        false,
        b"a",
        b"b",
        vec![
            annotation(b"y", vec![]),
            annotation(b"x", vec![]),
            annotation(b"x", vec![]),
        ],
    );
    assert!(same_object_assertion(&first, &same));
    for different in [
        assertion(b"urn:q", false, b"a", b"b", vec![]),
        assertion(b"urn:p", true, b"a", b"b", vec![]),
        assertion(b"urn:p", false, b"b", b"a", vec![]),
        assertion(
            b"urn:p",
            false,
            b"a",
            b"b",
            vec![annotation(b"different", vec![])],
        ),
    ] {
        assert!(!same_object_assertion(&first, &different));
    }
    let other_kind = AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::NegativeObjectPropertyAssertion(
            ObjectPropertyExpression::Property(ObjectProperty { iri: iri(b"urn:p") }),
            Individual::Anonymous(anonymous(b"doc", b"a")),
            Individual::Anonymous(anonymous(b"doc", b"b")),
        ),
    };
    assert!(!same_object_assertion(&first, &other_kind));
    assert!(!same_object_assertion(&other_kind, &other_kind));
}

#[derive(Eq, PartialEq, Ord, PartialOrd)]
enum ValueForm {
    Iri(Vec<u8>),
    Anonymous(Vec<u8>, Vec<u8>),
    Literal(Vec<u8>, Vec<u8>),
}
#[derive(Eq, PartialEq, Ord, PartialOrd)]
struct AnnotationForm(Vec<u8>, ValueForm, BTreeSet<AnnotationForm>);
fn canonical(value: &Annotation) -> AnnotationForm {
    let atomic = match &value.value {
        AnnotationValue::Iri(iri) => ValueForm::Iri(iri.spelling.clone()),
        AnnotationValue::Anonymous(individual) => {
            ValueForm::Anonymous(individual.scope.clone(), individual.label.clone())
        }
        AnnotationValue::Literal(literal) => ValueForm::Literal(
            literal.lexical.clone(),
            literal.datatype.iri.spelling.clone(),
        ),
    };
    AnnotationForm(
        value.property.iri.spelling.clone(),
        atomic,
        value.annotations.iter().map(canonical).collect(),
    )
}
#[test]
fn recursive_comparison_matches_independent_ordered_set_normal_forms() {
    let mut samples = vec![annotation(b"a", vec![]), annotation(b"b", vec![])];
    for mask in 0..16 {
        let children = (0..4)
            .filter(|bit| mask & (1 << bit) != 0)
            .map(|bit| annotation(if bit % 2 == 0 { b"a" } else { b"b" }, vec![]))
            .collect();
        samples.push(annotation(b"root", children));
    }
    samples.push(annotation(
        b"root",
        vec![annotation(b"root", vec![annotation(b"a", vec![])])],
    ));
    samples.push(annotation(b"root", vec![annotation(b"a", vec![])]));
    for left in &samples {
        for right in &samples {
            assert_eq!(
                same_annotation(left, right),
                canonical(left) == canonical(right)
            );
        }
    }
}
