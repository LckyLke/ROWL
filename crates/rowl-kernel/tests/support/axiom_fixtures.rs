use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
pub fn iri(n: usize) -> Iri {
    Iri {
        spelling: format!("urn:item:{n}").into_bytes(),
    }
}
pub fn op(n: usize) -> ObjectPropertyExpression {
    let p = ObjectProperty { iri: iri(n / 2) };
    if n.is_multiple_of(2) {
        ObjectPropertyExpression::Property(p)
    } else {
        ObjectPropertyExpression::Inverse(p)
    }
}
pub fn dp(n: usize) -> DataProperty {
    DataProperty { iri: iri(n) }
}
pub fn ap(n: usize) -> AnnotationProperty {
    AnnotationProperty { iri: iri(n) }
}
pub fn named(n: usize) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(n) })
}
pub fn literal(n: usize) -> Literal {
    Literal {
        lexical: n.to_string().into_bytes(),
        datatype: Datatype { iri: iri(40) },
    }
}
pub fn atom(n: usize) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(n) })
}
pub fn qualifier(v: usize) -> ClassExpression {
    ClassExpression::ObjectMinCardinality(
        Natural::Zero,
        op(0),
        if v == 0 {
            None
        } else {
            Some(Box::new(ClassExpression::Class(Class {
                iri: Iri {
                    spelling: b"http://www.w3.org/2002/07/owl#Thing".to_vec(),
                },
            })))
        },
    )
}
pub fn cls(v: usize) -> ClassExpression {
    let n = if v == 2 { 1 } else { 0 };
    ClassExpression::ObjectIntersectionOf(Box::new(if v == 1 {
        AtLeastTwo {
            first: qualifier(v),
            second: atom(n),
            rest: vec![atom(n)],
        }
    } else {
        AtLeastTwo {
            first: atom(n),
            second: qualifier(v),
            rest: vec![],
        }
    }))
}
pub fn range(v: usize) -> DataRange {
    let n = if v == 2 { 1 } else { 0 };
    DataRange::OneOf(if v == 1 {
        NonEmpty {
            first: literal(9),
            rest: vec![literal(n), literal(9)],
        }
    } else {
        NonEmpty {
            first: literal(n),
            rest: vec![literal(9)],
        }
    })
}
pub fn two<T>(a: T, b: T, rest: Vec<T>) -> AtLeastTwo<T> {
    AtLeastTwo {
        first: a,
        second: b,
        rest,
    }
}
pub fn classes(v: usize) -> AtLeastTwo<ClassExpression> {
    if v == 1 {
        two(atom(9), cls(v), vec![atom(9)])
    } else {
        two(cls(v), atom(9), vec![])
    }
}
pub fn properties(v: usize) -> AtLeastTwo<ObjectPropertyExpression> {
    let n = if v == 2 { 2 } else { 0 };
    if v == 1 {
        two(op(1), op(n), vec![op(n)])
    } else {
        two(op(n), op(1), vec![])
    }
}
pub fn datas(v: usize) -> AtLeastTwo<DataProperty> {
    let n = if v == 2 { 1 } else { 0 };
    if v == 1 {
        two(dp(9), dp(n), vec![dp(n)])
    } else {
        two(dp(n), dp(9), vec![])
    }
}
pub fn individuals(v: usize) -> AtLeastTwo<Individual> {
    let n = if v == 2 { 1 } else { 0 };
    if v == 1 {
        two(named(9), named(n), vec![named(n)])
    } else {
        two(named(n), named(9), vec![])
    }
}
pub fn annotation(n: usize, nested: bool) -> Annotation {
    Annotation {
        annotations: if nested {
            vec![annotation(9, false)]
        } else {
            vec![]
        },
        property: ap(n),
        value: AnnotationValue::Iri(iri(n)),
    }
}
pub fn metadata(v: usize) -> Vec<Annotation> {
    if v == 1 {
        vec![
            annotation(1, true),
            annotation(0, false),
            annotation(1, true),
        ]
    } else {
        vec![annotation(0, false), annotation(1, true)]
    }
}
pub fn body(tag: usize, v: usize) -> Axiom {
    let n = if v == 2 { 1 } else { 0 };
    match tag {
        0 => Axiom::Declaration(Entity::Class(Class { iri: iri(n) })),
        1 => Axiom::SubClassOf(cls(v), cls(v)),
        2 => Axiom::EquivalentClasses(classes(v)),
        3 => Axiom::DisjointClasses(classes(v)),
        4 => Axiom::DisjointUnion(Class { iri: iri(n) }, classes(v)),
        5 => Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Chain(two(op(0), op(1), vec![op(n)])),
            op(n),
        ),
        6 => Axiom::EquivalentObjectProperties(properties(v)),
        7 => Axiom::DisjointObjectProperties(properties(v)),
        8 => Axiom::InverseObjectProperties(op(n), op(n)),
        9 => Axiom::ObjectPropertyDomain(op(n), cls(v)),
        10 => Axiom::ObjectPropertyRange(op(n), cls(v)),
        11 => Axiom::FunctionalObjectProperty(op(n)),
        12 => Axiom::InverseFunctionalObjectProperty(op(n)),
        13 => Axiom::ReflexiveObjectProperty(op(n)),
        14 => Axiom::IrreflexiveObjectProperty(op(n)),
        15 => Axiom::SymmetricObjectProperty(op(n)),
        16 => Axiom::AsymmetricObjectProperty(op(n)),
        17 => Axiom::TransitiveObjectProperty(op(n)),
        18 => Axiom::SubDataPropertyOf(dp(n), dp(n)),
        19 => Axiom::EquivalentDataProperties(datas(v)),
        20 => Axiom::DisjointDataProperties(datas(v)),
        21 => Axiom::DataPropertyDomain(dp(n), cls(v)),
        22 => Axiom::DataPropertyRange(dp(n), range(v)),
        23 => Axiom::FunctionalDataProperty(dp(n)),
        24 => Axiom::DatatypeDefinition(Datatype { iri: iri(n) }, range(v)),
        25 => Axiom::HasKey(
            cls(v),
            if v == 1 {
                vec![op(1), op(n), op(n)]
            } else {
                vec![op(n), op(1)]
            },
            if v == 1 {
                vec![dp(9), dp(n), dp(n)]
            } else {
                vec![dp(n), dp(9)]
            },
        ),
        26 => Axiom::SameIndividual(individuals(v)),
        27 => Axiom::DifferentIndividuals(individuals(v)),
        28 => Axiom::ClassAssertion(cls(v), named(n)),
        29 => Axiom::ObjectPropertyAssertion(op(n), named(n), named(n)),
        30 => Axiom::NegativeObjectPropertyAssertion(op(n), named(n), named(n)),
        31 => Axiom::DataPropertyAssertion(dp(n), named(n), literal(n)),
        32 => Axiom::NegativeDataPropertyAssertion(dp(n), named(n), literal(n)),
        33 => Axiom::AnnotationAssertion(
            ap(n),
            AnnotationSubject::Iri(iri(n)),
            AnnotationValue::Iri(iri(n)),
        ),
        34 => Axiom::SubAnnotationPropertyOf(ap(n), ap(n)),
        35 => Axiom::AnnotationPropertyDomain(ap(n), iri(n)),
        36 => Axiom::AnnotationPropertyRange(ap(n), iri(n)),
        _ => unreachable!(),
    }
}
pub fn annotated(tag: usize, v: usize) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: metadata(v),
        axiom: body(tag, v),
    }
}
