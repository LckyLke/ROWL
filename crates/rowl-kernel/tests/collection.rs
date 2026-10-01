use rowl_kernel::collection::*;
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
use rowl_kernel::typing::EntityKind;

fn iri(s: &str) -> Iri {
    Iri {
        spelling: s.as_bytes().to_vec(),
    }
}
fn class(s: &str) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(s) })
}
fn datatype(s: &str) -> Datatype {
    Datatype { iri: iri(s) }
}
fn range(s: &str) -> DataRange {
    DataRange::Datatype(datatype(s))
}
fn object(s: &str) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(s) })
}
fn data(s: &str) -> DataProperty {
    DataProperty { iri: iri(s) }
}
fn individual(s: &str) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(s) })
}
fn anonymous() -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: b"scope".to_vec(),
        label: b"label".to_vec(),
    })
}
fn literal(s: &str) -> Literal {
    Literal {
        lexical: "a\r\nβ\0".as_bytes().to_vec(),
        datatype: datatype(s),
    }
}
fn two<T>(first: T, second: T, rest: Vec<T>) -> AtLeastTwo<T> {
    AtLeastTwo {
        first,
        second,
        rest,
    }
}
fn bare(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom,
    }
}
fn annotation(property: &str, value: AnnotationValue, annotations: Vec<Annotation>) -> Annotation {
    Annotation {
        property: AnnotationProperty { iri: iri(property) },
        value,
        annotations,
    }
}
fn role_number(kind: &EntityKind) -> u8 {
    match kind {
        EntityKind::Class => 0,
        EntityKind::Datatype => 1,
        EntityKind::ObjectProperty => 2,
        EntityKind::DataProperty => 3,
        EntityKind::AnnotationProperty => 4,
        EntityKind::NamedIndividual => 5,
    }
}
fn rows(uses: EntityUses<'_>) -> Vec<(Vec<u8>, u8)> {
    let mut out = vec![];
    let mut cursor = &uses;
    while let EntityUses::Entry { iri, kind, next } = cursor {
        out.push((iri.spelling.clone(), role_number(kind)));
        cursor = next;
    }
    out
}
fn expected(values: &[(&str, EntityKind)]) -> Vec<(Vec<u8>, u8)> {
    values
        .iter()
        .map(|(iri, role)| (iri.as_bytes().to_vec(), role_number(role)))
        .collect()
}

#[test]
fn every_class_form_collects_its_explicit_roles() {
    use ClassExpression as C;
    use EntityKind::{
        Class as Cl, DataProperty as Dp, Datatype as Dt, NamedIndividual as Ni,
        ObjectProperty as Op,
    };
    let cases = vec![
        (class("C"), vec![("C", Cl)]),
        (
            C::ObjectIntersectionOf(Box::new(two(class("A"), class("B"), vec![class("A")]))),
            vec![("A", Cl), ("B", Cl), ("A", Cl)],
        ),
        (
            C::ObjectUnionOf(Box::new(two(class("A"), class("B"), vec![class("A")]))),
            vec![("A", Cl), ("B", Cl), ("A", Cl)],
        ),
        (C::ObjectComplementOf(Box::new(class("C"))), vec![("C", Cl)]),
        (
            C::ObjectOneOf(NonEmpty {
                first: anonymous(),
                rest: vec![individual("i"), individual("i")],
            }),
            vec![("i", Ni), ("i", Ni)],
        ),
        (
            C::ObjectSomeValuesFrom(object("p"), Box::new(class("C"))),
            vec![("p", Op), ("C", Cl)],
        ),
        (
            C::ObjectAllValuesFrom(object("p"), Box::new(class("C"))),
            vec![("p", Op), ("C", Cl)],
        ),
        (
            C::ObjectHasValue(object("p"), individual("i")),
            vec![("p", Op), ("i", Ni)],
        ),
        (C::ObjectHasSelf(object("p")), vec![("p", Op)]),
        (
            C::ObjectMinCardinality(Natural::Zero, object("p"), Some(Box::new(class("C")))),
            vec![("p", Op), ("C", Cl)],
        ),
        (
            C::ObjectMaxCardinality(Natural::Zero, object("p"), None),
            vec![("p", Op)],
        ),
        (
            C::ObjectExactCardinality(Natural::Zero, object("p"), Some(Box::new(class("C")))),
            vec![("p", Op), ("C", Cl)],
        ),
        (
            C::DataSomeValuesFrom(data("p"), range("D")),
            vec![("p", Dp), ("D", Dt)],
        ),
        (
            C::DataAllValuesFrom(data("p"), range("D")),
            vec![("p", Dp), ("D", Dt)],
        ),
        (
            C::DataHasValue(data("p"), literal("D")),
            vec![("p", Dp), ("D", Dt)],
        ),
        (
            C::DataMinCardinality(Natural::Zero, data("p"), Some(range("D"))),
            vec![("p", Dp), ("D", Dt)],
        ),
        (
            C::DataMaxCardinality(Natural::Zero, data("p"), None),
            vec![("p", Dp)],
        ),
        (
            C::DataExactCardinality(Natural::Zero, data("p"), Some(range("D"))),
            vec![("p", Dp), ("D", Dt)],
        ),
    ];
    assert_eq!(cases.len(), 18);
    for (expression, roles) in cases {
        assert_eq!(rows(class_entities(&expression)), expected(&roles));
    }
}

#[test]
fn all_data_ranges_include_literal_datatypes_but_not_facet_iris() {
    use EntityKind::Datatype as Dt;
    let cases = vec![
        (range("D"), vec![("D", Dt)]),
        (
            DataRange::Intersection(Box::new(two(range("A"), range("B"), vec![range("A")]))),
            vec![("A", Dt), ("B", Dt), ("A", Dt)],
        ),
        (
            DataRange::Union(Box::new(two(range("A"), range("B"), vec![range("A")]))),
            vec![("A", Dt), ("B", Dt), ("A", Dt)],
        ),
        (DataRange::Complement(Box::new(range("D"))), vec![("D", Dt)]),
        (
            DataRange::OneOf(NonEmpty {
                first: literal("A"),
                rest: vec![literal("B"), literal("A")],
            }),
            vec![("A", Dt), ("B", Dt), ("A", Dt)],
        ),
        (
            DataRange::Restriction(
                datatype("base"),
                NonEmpty {
                    first: FacetRestriction {
                        facet: iri("ignored:min"),
                        value: literal("bound"),
                    },
                    rest: vec![FacetRestriction {
                        facet: iri("ignored:max"),
                        value: literal("bound"),
                    }],
                },
            ),
            vec![("base", Dt), ("bound", Dt), ("bound", Dt)],
        ),
    ];
    assert_eq!(cases.len(), 6);
    for (range, roles) in cases {
        assert_eq!(rows(range_entities(&range)), expected(&roles));
    }
}

#[test]
fn every_axiom_form_keeps_role_order_and_context() {
    use Axiom as A;
    use EntityKind::{
        AnnotationProperty as Ap, Class as Cl, DataProperty as Dp, Datatype as Dt,
        NamedIndividual as Ni, ObjectProperty as Op,
    };
    let cs = || two(class("A"), class("B"), vec![class("A")]);
    let ps = || two(object("p"), object("q"), vec![object("p")]);
    let ds = || two(data("p"), data("q"), vec![data("p")]);
    let is = || {
        two(
            individual("a"),
            anonymous(),
            vec![individual("b"), individual("a")],
        )
    };
    let cases = vec![
        (
            A::Declaration(Entity::Class(Class { iri: iri("C") })),
            vec![("C", Cl)],
        ),
        (
            A::SubClassOf(class("A"), class("B")),
            vec![("A", Cl), ("B", Cl)],
        ),
        (
            A::EquivalentClasses(cs()),
            vec![("A", Cl), ("B", Cl), ("A", Cl)],
        ),
        (
            A::DisjointClasses(cs()),
            vec![("A", Cl), ("B", Cl), ("A", Cl)],
        ),
        (
            A::DisjointUnion(Class { iri: iri("C") }, cs()),
            vec![("C", Cl), ("A", Cl), ("B", Cl), ("A", Cl)],
        ),
        (
            A::SubObjectPropertyOf(SubObjectPropertyExpression::Chain(ps()), object("r")),
            vec![("p", Op), ("q", Op), ("p", Op), ("r", Op)],
        ),
        (
            A::EquivalentObjectProperties(ps()),
            vec![("p", Op), ("q", Op), ("p", Op)],
        ),
        (
            A::DisjointObjectProperties(ps()),
            vec![("p", Op), ("q", Op), ("p", Op)],
        ),
        (
            A::InverseObjectProperties(object("p"), object("q")),
            vec![("p", Op), ("q", Op)],
        ),
        (
            A::ObjectPropertyDomain(object("p"), class("C")),
            vec![("p", Op), ("C", Cl)],
        ),
        (
            A::ObjectPropertyRange(object("p"), class("C")),
            vec![("p", Op), ("C", Cl)],
        ),
        (A::FunctionalObjectProperty(object("p")), vec![("p", Op)]),
        (
            A::InverseFunctionalObjectProperty(object("p")),
            vec![("p", Op)],
        ),
        (A::ReflexiveObjectProperty(object("p")), vec![("p", Op)]),
        (A::IrreflexiveObjectProperty(object("p")), vec![("p", Op)]),
        (A::SymmetricObjectProperty(object("p")), vec![("p", Op)]),
        (A::AsymmetricObjectProperty(object("p")), vec![("p", Op)]),
        (A::TransitiveObjectProperty(object("p")), vec![("p", Op)]),
        (
            A::SubDataPropertyOf(data("p"), data("q")),
            vec![("p", Dp), ("q", Dp)],
        ),
        (
            A::EquivalentDataProperties(ds()),
            vec![("p", Dp), ("q", Dp), ("p", Dp)],
        ),
        (
            A::DisjointDataProperties(ds()),
            vec![("p", Dp), ("q", Dp), ("p", Dp)],
        ),
        (
            A::DataPropertyDomain(data("p"), class("C")),
            vec![("p", Dp), ("C", Cl)],
        ),
        (
            A::DataPropertyRange(data("p"), range("D")),
            vec![("p", Dp), ("D", Dt)],
        ),
        (A::FunctionalDataProperty(data("p")), vec![("p", Dp)]),
        (
            A::DatatypeDefinition(datatype("D"), range("E")),
            vec![("D", Dt), ("E", Dt)],
        ),
        (
            A::HasKey(class("C"), vec![object("p"), object("p")], vec![data("p")]),
            vec![("C", Cl), ("p", Op), ("p", Op), ("p", Dp)],
        ),
        (
            A::SameIndividual(is()),
            vec![("a", Ni), ("b", Ni), ("a", Ni)],
        ),
        (
            A::DifferentIndividuals(is()),
            vec![("a", Ni), ("b", Ni), ("a", Ni)],
        ),
        (
            A::ClassAssertion(class("C"), individual("i")),
            vec![("C", Cl), ("i", Ni)],
        ),
        (
            A::ObjectPropertyAssertion(object("p"), individual("a"), individual("b")),
            vec![("p", Op), ("a", Ni), ("b", Ni)],
        ),
        (
            A::NegativeObjectPropertyAssertion(object("p"), individual("a"), individual("b")),
            vec![("p", Op), ("a", Ni), ("b", Ni)],
        ),
        (
            A::DataPropertyAssertion(data("p"), individual("i"), literal("D")),
            vec![("p", Dp), ("i", Ni), ("D", Dt)],
        ),
        (
            A::NegativeDataPropertyAssertion(data("p"), individual("i"), literal("D")),
            vec![("p", Dp), ("i", Ni), ("D", Dt)],
        ),
        (
            A::AnnotationAssertion(
                AnnotationProperty { iri: iri("p") },
                AnnotationSubject::Iri(iri("ignored:subject")),
                AnnotationValue::Literal(literal("D")),
            ),
            vec![("p", Ap), ("D", Dt)],
        ),
        (
            A::SubAnnotationPropertyOf(
                AnnotationProperty { iri: iri("p") },
                AnnotationProperty { iri: iri("q") },
            ),
            vec![("p", Ap), ("q", Ap)],
        ),
        (
            A::AnnotationPropertyDomain(
                AnnotationProperty { iri: iri("p") },
                iri("ignored:domain"),
            ),
            vec![("p", Ap)],
        ),
        (
            A::AnnotationPropertyRange(AnnotationProperty { iri: iri("p") }, iri("ignored:range")),
            vec![("p", Ap)],
        ),
    ];
    assert_eq!(cases.len(), 37);
    for (item, roles) in cases {
        assert_eq!(rows(axiom_entities(&bare(item))), expected(&roles));
    }
    let single = bare(A::SubObjectPropertyOf(
        SubObjectPropertyExpression::Single(object("p")),
        object("q"),
    ));
    assert_eq!(
        rows(axiom_entities(&single)),
        expected(&[("p", Op), ("q", Op)])
    );
    let empty_key = bare(A::HasKey(class("C"), vec![], vec![]));
    assert_eq!(rows(axiom_entities(&empty_key)), expected(&[("C", Cl)]));
}

#[test]
fn collection_separates_declarations_and_preserves_nested_annotation_uses() {
    use EntityKind::{AnnotationProperty as Ap, Class as Cl, Datatype as Dt};
    let ontology = RawOntology {
        identity: OntologyIdentity::Named {
            ontology: iri("ignored:ontology"),
            version: Some(iri("ignored:version")),
        },
        imports: vec![iri("ignored:import")],
        annotations: vec![annotation(
            "ont",
            AnnotationValue::Iri(iri("ignored:value")),
            vec![],
        )],
        axioms: vec![
            AnnotatedAxiom {
                annotations: vec![annotation(
                    "outer",
                    AnnotationValue::Literal(literal("D")),
                    vec![annotation(
                        "inner",
                        AnnotationValue::Anonymous(AnonymousIndividual {
                            scope: b"ignored".to_vec(),
                            label: b"ignored".to_vec(),
                        }),
                        vec![],
                    )],
                )],
                axiom: Axiom::Declaration(Entity::Class(Class { iri: iri("C") })),
            },
            bare(Axiom::SubClassOf(class("C"), class("C"))),
        ],
    };
    let collected = ontology_entities(&ontology);
    assert_eq!(rows(collected.declarations), expected(&[("C", Cl)]));
    assert_eq!(
        rows(collected.uses),
        expected(&[
            ("ont", Ap),
            ("inner", Ap),
            ("outer", Ap),
            ("D", Dt),
            ("C", Cl),
            ("C", Cl),
            ("C", Cl)
        ])
    );
    let named = bare(Axiom::AnnotationAssertion(
        AnnotationProperty { iri: iri("p") },
        AnnotationSubject::Iri(iri("ignored:subject")),
        AnnotationValue::Iri(iri("ignored:value")),
    ));
    assert_eq!(rows(axiom_entities(&named)), expected(&[("p", Ap)]));
}

#[test]
fn all_entity_roles_borrow_the_exact_original_iri() {
    use EntityKind as K;
    let cases = vec![
        (Entity::Class(Class { iri: iri("urn:C") }), K::Class),
        (Entity::Datatype(datatype("urn:D")), K::Datatype),
        (
            Entity::ObjectProperty(ObjectProperty { iri: iri("urn:p") }),
            K::ObjectProperty,
        ),
        (Entity::DataProperty(data("urn:d")), K::DataProperty),
        (
            Entity::AnnotationProperty(AnnotationProperty { iri: iri("urn:a") }),
            K::AnnotationProperty,
        ),
        (
            Entity::NamedIndividual(NamedIndividual {
                iri: iri("urn:β\r\n\0"),
            }),
            K::NamedIndividual,
        ),
    ];
    for (entity, expected_kind) in cases {
        let original = match &entity {
            Entity::Class(c) => &c.iri,
            Entity::Datatype(d) => &d.iri,
            Entity::ObjectProperty(p) => &p.iri,
            Entity::DataProperty(p) => &p.iri,
            Entity::AnnotationProperty(p) => &p.iri,
            Entity::NamedIndividual(i) => &i.iri,
        };
        let EntityUses::Entry { iri, kind, next } = entity_entities(&entity) else {
            panic!("lost entity");
        };
        assert!(std::ptr::eq(iri, original));
        assert_eq!(role_number(&kind), role_number(&expected_kind));
        assert!(matches!(*next, EntityUses::Empty));
    }
}
