use rowl_kernel::data_ontology::{
    class_satisfiable, consistent, instance_of, prepare, prepared_consistent, prepared_instance_of,
    subsumed,
};
use rowl_kernel::key_ontology::{complex_roles, has_keys};
use rowl_kernel::model::*;

const TOP_OBJECT: &[u8] = b"http://www.w3.org/2002/07/owl#topObjectProperty";

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn class(s: &[u8]) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(s) })
}
fn property(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(s) })
}
fn inverse(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(s) })
}
fn named(s: &[u8]) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(s) })
}
fn anonymous(s: &[u8]) -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: b"test".to_vec(),
        label: s.to_vec(),
    })
}
fn individual(s: &[u8]) -> NamedIndividual {
    NamedIndividual { iri: iri(s) }
}
fn two<T>(first: T, second: T, rest: Vec<T>) -> AtLeastTwo<T> {
    AtLeastTwo {
        first,
        second,
        rest,
    }
}
fn or(a: ClassExpression, b: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectUnionOf(Box::new(two(a, b, Vec::new())))
}
fn one_of(first: &[u8], rest: &[&[u8]]) -> ClassExpression {
    ClassExpression::ObjectOneOf(NonEmpty {
        first: named(first),
        rest: rest.iter().map(|s| named(s)).collect(),
    })
}
fn some(p: ObjectPropertyExpression, c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(p, Box::new(c))
}
fn has_value(p: &[u8], a: &[u8]) -> ClassExpression {
    ClassExpression::ObjectHasValue(property(p), named(a))
}
fn axiom(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: Vec::new(),
        axiom,
    }
}
fn sub(a: ClassExpression, b: ClassExpression) -> AnnotatedAxiom {
    axiom(Axiom::SubClassOf(a, b))
}
fn asserted(c: ClassExpression, a: Individual) -> AnnotatedAxiom {
    axiom(Axiom::ClassAssertion(c, a))
}
fn related(p: &[u8], a: Individual, b: Individual) -> AnnotatedAxiom {
    axiom(Axiom::ObjectPropertyAssertion(property(p), a, b))
}
fn different(a: Individual, b: Individual) -> AnnotatedAxiom {
    axiom(Axiom::DifferentIndividuals(two(a, b, Vec::new())))
}
fn key(c: ClassExpression, objects: Vec<ObjectPropertyExpression>) -> AnnotatedAxiom {
    axiom(Axiom::HasKey(c, objects, Vec::new()))
}
fn transitive(p: &[u8]) -> AnnotatedAxiom {
    axiom(Axiom::TransitiveObjectProperty(property(p)))
}

/// Two patients with the named insurance id `id1`; the key on
/// `hasInsuranceId` makes them one patient.
fn shared_id() -> Vec<AnnotatedAxiom> {
    vec![
        key(class(b"ex:Patient"), vec![property(b"ex:hasInsuranceId")]),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
        asserted(class(b"ex:Patient"), named(b"ex:anna")),
        related(b"ex:hasInsuranceId", named(b"ex:ann"), named(b"ex:id1")),
        related(b"ex:hasInsuranceId", named(b"ex:anna"), named(b"ex:id1")),
    ]
}

#[test]
fn patients_sharing_a_named_insurance_id_are_equal() {
    let items = shared_id();
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(&items, &individual(b"ex:anna"), &one_of(b"ex:ann", &[])),
        Some(true)
    );
    let mut apart = shared_id();
    apart.push(different(named(b"ex:ann"), named(b"ex:anna")));
    assert_eq!(consistent(&apart), Some(false));
}

#[test]
fn without_the_key_they_may_differ() {
    let mut items = shared_id();
    items.remove(0);
    assert_eq!(
        instance_of(&items, &individual(b"ex:anna"), &one_of(b"ex:ann", &[])),
        Some(false)
    );
    items.push(different(named(b"ex:ann"), named(b"ex:anna")));
    assert_eq!(consistent(&items), Some(true));
}

#[test]
fn equal_patients_share_their_classes() {
    let mut items = shared_id();
    items.push(asserted(class(b"ex:Allergic"), named(b"ex:ann")));
    assert_eq!(
        instance_of(&items, &individual(b"ex:anna"), &class(b"ex:Allergic")),
        Some(true)
    );
}

#[test]
fn keys_apply_only_to_instances_of_the_key_class() {
    let mut items = shared_id();
    items[2] = asserted(class(b"ex:Doctor"), named(b"ex:anna"));
    items.push(different(named(b"ex:ann"), named(b"ex:anna")));
    assert_eq!(consistent(&items), Some(true));
    // Membership the closure entails is enough.
    items.push(sub(class(b"ex:Doctor"), class(b"ex:Patient")));
    assert_eq!(consistent(&items), Some(false));
}

#[test]
fn keys_never_apply_to_anonymous_individuals() {
    let items = vec![
        key(class(b"ex:Patient"), vec![property(b"ex:hasInsuranceId")]),
        asserted(class(b"ex:Patient"), anonymous(b"a")),
        asserted(class(b"ex:Patient"), anonymous(b"b")),
        related(b"ex:hasInsuranceId", anonymous(b"a"), named(b"ex:id1")),
        related(b"ex:hasInsuranceId", anonymous(b"b"), named(b"ex:id1")),
        different(anonymous(b"a"), anonymous(b"b")),
    ];
    assert_eq!(consistent(&items), Some(true));
}

#[test]
fn keys_never_apply_to_unnamed_values() {
    // The shared value is an anonymous individual.
    let items = vec![
        key(class(b"ex:Patient"), vec![property(b"ex:hasInsuranceId")]),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
        asserted(class(b"ex:Patient"), named(b"ex:anna")),
        related(b"ex:hasInsuranceId", named(b"ex:ann"), anonymous(b"id")),
        related(b"ex:hasInsuranceId", named(b"ex:anna"), anonymous(b"id")),
        different(named(b"ex:ann"), named(b"ex:anna")),
    ];
    assert_eq!(consistent(&items), Some(true));
    // Nor to a value that only an existential restriction gives: every
    // patient has an id with the one named issuer, which they may share
    // without being equal.
    let unnamed = vec![
        key(class(b"ex:Patient"), vec![property(b"ex:hasInsuranceId")]),
        sub(
            class(b"ex:Patient"),
            some(
                property(b"ex:hasInsuranceId"),
                has_value(b"ex:issuedBy", b"ex:acme"),
            ),
        ),
        axiom(Axiom::InverseFunctionalObjectProperty(property(
            b"ex:issuedBy",
        ))),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
        asserted(class(b"ex:Patient"), named(b"ex:anna")),
        different(named(b"ex:ann"), named(b"ex:anna")),
    ];
    assert_eq!(consistent(&unnamed), Some(true));
}

#[test]
fn a_key_resolves_a_disjunction() {
    // Anna has insurance id1 or is uninsured; she differs from Ann, who has
    // id1, so she is uninsured.
    let items = vec![
        key(class(b"ex:Patient"), vec![property(b"ex:hasInsuranceId")]),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
        asserted(class(b"ex:Patient"), named(b"ex:anna")),
        related(b"ex:hasInsuranceId", named(b"ex:ann"), named(b"ex:id1")),
        asserted(
            or(
                has_value(b"ex:hasInsuranceId", b"ex:id1"),
                class(b"ex:Uninsured"),
            ),
            named(b"ex:anna"),
        ),
        different(named(b"ex:ann"), named(b"ex:anna")),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"ex:anna"), &class(b"ex:Uninsured")),
        Some(true)
    );
    let mut keyless = items;
    keyless.remove(0);
    assert_eq!(
        instance_of(&keyless, &individual(b"ex:anna"), &class(b"ex:Uninsured")),
        Some(false)
    );
}

#[test]
fn keys_with_several_properties_need_every_value() {
    let both = vec![
        key(
            class(b"ex:Patient"),
            vec![property(b"ex:hasInsuranceId"), property(b"ex:bornOn")],
        ),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
        asserted(class(b"ex:Patient"), named(b"ex:anna")),
        related(b"ex:hasInsuranceId", named(b"ex:ann"), named(b"ex:id1")),
        related(b"ex:hasInsuranceId", named(b"ex:anna"), named(b"ex:id1")),
        related(b"ex:bornOn", named(b"ex:ann"), named(b"ex:day1")),
        related(b"ex:bornOn", named(b"ex:anna"), named(b"ex:day1")),
    ];
    assert_eq!(
        instance_of(&both, &individual(b"ex:anna"), &one_of(b"ex:ann", &[])),
        Some(true)
    );
    let mut apart = both;
    apart.push(different(named(b"ex:ann"), named(b"ex:anna")));
    assert_eq!(consistent(&apart), Some(false));
    // Another birthday: one shared value is not enough.
    apart[6] = related(b"ex:bornOn", named(b"ex:anna"), named(b"ex:day2"));
    assert_eq!(consistent(&apart), Some(true));
}

#[test]
fn keys_on_inverse_and_transitive_properties() {
    // Two insurance ids of one named patient are one id.
    let inverse_key = vec![
        key(class(b"ex:Id"), vec![inverse(b"ex:hasInsuranceId")]),
        asserted(class(b"ex:Id"), named(b"ex:id1")),
        asserted(class(b"ex:Id"), named(b"ex:id2")),
        related(b"ex:hasInsuranceId", named(b"ex:ann"), named(b"ex:id1")),
        related(b"ex:hasInsuranceId", named(b"ex:ann"), named(b"ex:id2")),
        different(named(b"ex:id1"), named(b"ex:id2")),
    ];
    assert_eq!(consistent(&inverse_key), Some(false));
    // A transitive key property: two parts of one named whole are equal.
    let transitive_key = vec![
        key(class(b"ex:Part"), vec![property(b"ex:partOf")]),
        transitive(b"ex:partOf"),
        asserted(class(b"ex:Part"), named(b"ex:p1")),
        asserted(class(b"ex:Part"), named(b"ex:p2")),
        related(b"ex:partOf", named(b"ex:p1"), named(b"ex:m")),
        related(b"ex:partOf", named(b"ex:m"), named(b"ex:w")),
        related(b"ex:partOf", named(b"ex:p2"), named(b"ex:w")),
        different(named(b"ex:p1"), named(b"ex:p2")),
    ];
    assert!(complex_roles(&transitive_key, 0));
    assert_eq!(consistent(&transitive_key), Some(false));
}

#[test]
fn key_class_nominals_are_named_individuals() {
    // The key's class names the individuals; they share the value.
    let items = vec![
        key(
            one_of(b"ex:ann", &[b"ex:anna"]),
            vec![property(b"ex:hasInsuranceId")],
        ),
        related(b"ex:hasInsuranceId", named(b"ex:ann"), named(b"ex:id1")),
        related(b"ex:hasInsuranceId", named(b"ex:anna"), named(b"ex:id1")),
        different(named(b"ex:ann"), named(b"ex:anna")),
    ];
    assert_eq!(consistent(&items), Some(false));
}

#[test]
fn queries_about_closures_with_keys() {
    let items = shared_id();
    // Every instance of the key class is an instance of the key class.
    assert_eq!(
        subsumed(&items, &class(b"ex:Patient"), &class(b"ex:Patient")),
        Some(true)
    );
    assert_eq!(class_satisfiable(&items, &class(b"ex:Patient")), Some(true));
    let prepared = prepare(&items).expect("prepared");
    assert_eq!(prepared_consistent(&prepared), Some(true));
    // An individual the closure does not mention gets no answer.
    assert_eq!(
        prepared_instance_of(&prepared, &individual(b"ex:bob"), &class(b"ex:Patient")),
        None
    );
}

#[test]
fn declined_keys_get_no_answer() {
    let universal = vec![
        key(class(b"ex:Patient"), vec![property(TOP_OBJECT)]),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
    ];
    assert_eq!(consistent(&universal), None);
    let empty = vec![
        key(class(b"ex:Patient"), Vec::new()),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
    ];
    assert_eq!(consistent(&empty), None);
    let data = vec![
        axiom(Axiom::HasKey(
            class(b"ex:Patient"),
            Vec::new(),
            vec![DataProperty {
                iri: iri(b"ex:ssn"),
            }],
        )),
        asserted(class(b"ex:Patient"), named(b"ex:ann")),
    ];
    assert_eq!(consistent(&data), None);
    assert!(has_keys(&data, 0));
    assert!(!has_keys(&data, 1));
}

const XSD_INTEGER: &[u8] = b"http://www.w3.org/2001/XMLSchema#integer";
const XSD_MIN_INCLUSIVE: &[u8] = b"http://www.w3.org/2001/XMLSchema#minInclusive";

fn integer(lexical: &[u8]) -> Literal {
    Literal {
        lexical: lexical.to_vec(),
        datatype: Datatype {
            iri: iri(XSD_INTEGER),
        },
    }
}
/// The class of the elements with a `p`-value of at least `low`.
fn at_least(p: &[u8], low: &[u8]) -> ClassExpression {
    ClassExpression::DataSomeValuesFrom(
        DataProperty { iri: iri(p) },
        DataRange::Restriction(
            Datatype {
                iri: iri(XSD_INTEGER),
            },
            NonEmpty {
                first: FacetRestriction {
                    facet: iri(XSD_MIN_INCLUSIVE),
                    value: integer(low),
                },
                rest: Vec::new(),
            },
        ),
    )
}
fn dose(a: &[u8], value: &[u8]) -> AnnotatedAxiom {
    axiom(Axiom::DataPropertyAssertion(
        DataProperty {
            iri: iri(b"ex:dose"),
        },
        named(a),
        integer(value),
    ))
}

#[test]
fn keys_on_classes_of_numeric_ranges() {
    // High doses are identified by their prescription: two orders with doses of
    // at least 500 that share a prescription are one order.
    let high_orders = || {
        vec![
            key(
                at_least(b"ex:dose", b"500"),
                vec![property(b"ex:prescription")],
            ),
            dose(b"ex:order1", b"600"),
            dose(b"ex:order2", b"700"),
            related(b"ex:prescription", named(b"ex:order1"), named(b"ex:rx1")),
            related(b"ex:prescription", named(b"ex:order2"), named(b"ex:rx1")),
            asserted(class(b"ex:Checked"), named(b"ex:order1")),
        ]
    };
    let orders = high_orders();
    assert_eq!(consistent(&orders), Some(true));
    assert_eq!(
        instance_of(&orders, &individual(b"ex:order2"), &class(b"ex:Checked")),
        Some(true)
    );
    let mut apart = high_orders();
    apart.push(different(named(b"ex:order1"), named(b"ex:order2")));
    assert_eq!(consistent(&apart), Some(false));
    // A low dose is outside the key class, so the orders may differ.
    let mut low = vec![
        key(
            at_least(b"ex:dose", b"500"),
            vec![property(b"ex:prescription")],
        ),
        dose(b"ex:order1", b"600"),
        dose(b"ex:order2", b"100"),
        related(b"ex:prescription", named(b"ex:order1"), named(b"ex:rx1")),
        related(b"ex:prescription", named(b"ex:order2"), named(b"ex:rx1")),
    ];
    low.push(axiom(Axiom::FunctionalDataProperty(DataProperty {
        iri: iri(b"ex:dose"),
    })));
    low.push(different(named(b"ex:order1"), named(b"ex:order2")));
    assert_eq!(consistent(&low), Some(true));
}
