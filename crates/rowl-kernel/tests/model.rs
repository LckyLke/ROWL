use rowl_kernel::model::*;

fn property(name: &str) -> ObjectProperty {
    ObjectProperty {
        iri: Iri {
            spelling: name.as_bytes().to_vec(),
        },
    }
}
fn spelling(expression: &ObjectPropertyExpression) -> &[u8] {
    match expression {
        ObjectPropertyExpression::Property(p) | ObjectPropertyExpression::Inverse(p) => {
            &p.iri.spelling
        }
    }
}

#[test]
fn inversion_preserves_identity_in_both_orientations() {
    let inverse = invert(ObjectPropertyExpression::Property(property("urn:hasPart")));
    assert!(matches!(&inverse, ObjectPropertyExpression::Inverse(_)));
    assert_eq!(spelling(&inverse), b"urn:hasPart");
    let original = invert(inverse);
    assert!(matches!(&original, ObjectPropertyExpression::Property(_)));
    assert_eq!(spelling(&original), b"urn:hasPart");
    let inverse_again = invert(invert(ObjectPropertyExpression::Inverse(property(
        "urn:owns",
    ))));
    assert!(matches!(
        &inverse_again,
        ObjectPropertyExpression::Inverse(_)
    ));
    assert_eq!(spelling(&inverse_again), b"urn:owns");
}

#[test]
fn chains_preserve_order_and_repeated_properties() {
    let chain = SubObjectPropertyExpression::Chain(AtLeastTwo {
        first: ObjectPropertyExpression::Property(property("urn:parent")),
        second: ObjectPropertyExpression::Property(property("urn:sibling")),
        rest: vec![ObjectPropertyExpression::Property(property("urn:parent"))],
    });
    let SubObjectPropertyExpression::Chain(chain) = chain else {
        unreachable!()
    };
    assert_eq!(spelling(&chain.first), b"urn:parent");
    assert_eq!(spelling(&chain.second), b"urn:sibling");
    assert_eq!(spelling(&chain.rest[0]), b"urn:parent");
}

#[test]
fn anonymous_identity_keeps_ontology_scope() {
    let first = AnonymousIndividual {
        scope: b"urn:first".to_vec(),
        label: b"x".to_vec(),
    };
    let second = AnonymousIndividual {
        scope: b"urn:second".to_vec(),
        label: b"x".to_vec(),
    };
    assert_eq!(first.label, second.label);
    assert_ne!(first.scope, second.scope);
    // This is structural identity, not an assertion of logical inequality.
}
