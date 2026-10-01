use rowl_kernel::keys::{axiom_allowed, check_keys};
use rowl_kernel::model::*;
fn iri(text: &[u8]) -> Iri {
    Iri {
        spelling: text.to_vec(),
    }
}
fn class() -> ClassExpression {
    ClassExpression::Class(Class {
        iri: iri(b"urn:Machine"),
    })
}
fn op(inverse: bool) -> ObjectPropertyExpression {
    let p = ObjectProperty {
        iri: iri(b"urn:owner"),
    };
    if inverse {
        ObjectPropertyExpression::Inverse(p)
    } else {
        ObjectPropertyExpression::Property(p)
    }
}
fn dp() -> DataProperty {
    DataProperty {
        iri: iri(b"urn:serialNumber"),
    }
}
fn key(objects: Vec<ObjectPropertyExpression>, data: Vec<DataProperty>) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::HasKey(class(), objects, data),
    }
}
#[test]
fn empty_keys_fail_but_each_permitted_property_kind_suffices() {
    assert!(!axiom_allowed(&key(vec![], vec![])));
    assert!(axiom_allowed(&key(vec![op(false)], vec![])));
    assert!(axiom_allowed(&key(vec![op(true)], vec![])));
    assert!(axiom_allowed(&key(vec![], vec![dp()])));
    assert!(axiom_allowed(&key(vec![op(false)], vec![dp()])));
    assert!(axiom_allowed(&key(
        vec![op(false), op(false)],
        vec![dp(), dp()]
    )));
}
#[test]
fn closure_scan_retains_the_first_original_annotated_empty_key() {
    let mut bad = key(vec![], vec![]);
    bad.annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"urn:note"),
        },
        value: AnnotationValue::Literal(Literal {
            lexical: b"missing serial number".to_vec(),
            datatype: Datatype {
                iri: iri(b"urn:string"),
            },
        }),
    });
    let values = vec![key(vec![], vec![dp()]), bad, key(vec![], vec![])];
    let found = check_keys(&values).expect("the empty key must fail");
    assert!(std::ptr::eq(found, &values[1]));
    assert_eq!(found.annotations.len(), 1);
    let repaired = vec![key(vec![], vec![dp()]), key(vec![op(false)], vec![])];
    assert!(check_keys(&repaired).is_none());
    assert!(check_keys(&vec![]).is_none());
}
#[test]
fn unrelated_axioms_and_metadata_do_not_invent_key_members() {
    let unrelated = AnnotatedAxiom {
        annotations: vec![],
        axiom: Axiom::SubClassOf(class(), class()),
    };
    assert!(axiom_allowed(&unrelated));
    let mut empty = key(vec![], vec![]);
    empty.annotations.push(Annotation {
        annotations: vec![],
        property: AnnotationProperty {
            iri: iri(b"urn:serialNumber"),
        },
        value: AnnotationValue::Iri(iri(b"urn:owner")),
    });
    assert!(!axiom_allowed(&empty));
    let values = vec![unrelated, empty];
    assert!(std::ptr::eq(check_keys(&values).unwrap(), &values[1]));
}
