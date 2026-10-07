use rowl_kernel::data_ontology::{class_satisfiable, consistent, instance_of, subsumed};
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;

const THING: &[u8] = b"http://www.w3.org/2002/07/owl#Thing";
const TOP_OBJECT: &[u8] = b"http://www.w3.org/2002/07/owl#topObjectProperty";
const INTEGER: &[u8] = b"http://www.w3.org/2001/XMLSchema#integer";
const DECIMAL: &[u8] = b"http://www.w3.org/2001/XMLSchema#decimal";
const STRING: &[u8] = b"http://www.w3.org/2001/XMLSchema#string";
const PLAIN: &[u8] = b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const BOOLEAN: &[u8] = b"http://www.w3.org/2001/XMLSchema#boolean";
const LITERAL: &[u8] = b"http://www.w3.org/2000/01/rdf-schema#Literal";
const XML_LITERAL: &[u8] = b"http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";

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
fn data(s: &[u8]) -> DataProperty {
    DataProperty { iri: iri(s) }
}
fn datatype(s: &[u8]) -> DataRange {
    DataRange::Datatype(Datatype { iri: iri(s) })
}
fn literal(lexical: &[u8], dt: &[u8]) -> Literal {
    Literal {
        lexical: lexical.to_vec(),
        datatype: Datatype { iri: iri(dt) },
    }
}
fn int(lexical: &[u8]) -> Literal {
    literal(lexical, INTEGER)
}
fn two<T>(first: T, second: T, rest: Vec<T>) -> AtLeastTwo<T> {
    AtLeastTwo {
        first,
        second,
        rest,
    }
}
fn and(a: ClassExpression, b: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(two(a, b, Vec::new())))
}
fn not(a: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(a))
}
fn not_range(a: DataRange) -> DataRange {
    DataRange::Complement(Box::new(a))
}
fn one_of(first: Literal, rest: Vec<Literal>) -> DataRange {
    DataRange::OneOf(NonEmpty { first, rest })
}
fn some(p: &[u8], r: DataRange) -> ClassExpression {
    ClassExpression::DataSomeValuesFrom(data(p), r)
}
fn all(p: &[u8], r: DataRange) -> ClassExpression {
    ClassExpression::DataAllValuesFrom(data(p), r)
}
fn has(p: &[u8], lt: Literal) -> ClassExpression {
    ClassExpression::DataHasValue(data(p), lt)
}
fn natural(n: usize) -> Natural {
    if n == 0 {
        Natural::Zero
    } else {
        Natural::Succ(Box::new(natural(n - 1)))
    }
}
fn at_least(n: usize, p: &[u8], r: Option<DataRange>) -> ClassExpression {
    ClassExpression::DataMinCardinality(natural(n), data(p), r)
}
fn at_most(n: usize, p: &[u8], r: Option<DataRange>) -> ClassExpression {
    ClassExpression::DataMaxCardinality(natural(n), data(p), r)
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
fn named(s: &[u8]) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(s) })
}
fn individual(s: &[u8]) -> NamedIndividual {
    NamedIndividual { iri: iri(s) }
}
fn asserted(c: ClassExpression, a: &[u8]) -> AnnotatedAxiom {
    axiom(Axiom::ClassAssertion(c, named(a)))
}
fn valued(p: &[u8], a: &[u8], lt: Literal) -> AnnotatedAxiom {
    axiom(Axiom::DataPropertyAssertion(data(p), named(a), lt))
}
fn unvalued(p: &[u8], a: &[u8], lt: Literal) -> AnnotatedAxiom {
    axiom(Axiom::NegativeDataPropertyAssertion(data(p), named(a), lt))
}
fn functional(p: &[u8]) -> AnnotatedAxiom {
    axiom(Axiom::FunctionalDataProperty(data(p)))
}

#[test]
fn a_functional_value_is_unique_by_value() {
    let two_values = vec![
        functional(b"ex:age"),
        valued(b"ex:age", b"ex:ann", int(b"42")),
        valued(b"ex:age", b"ex:ann", int(b"43")),
    ];
    assert_eq!(consistent(&two_values), Some(false));
    let one_value = vec![
        functional(b"ex:age"),
        valued(b"ex:age", b"ex:ann", int(b"42")),
        valued(b"ex:age", b"ex:ann", int(b"+042")),
        valued(b"ex:age", b"ex:ann", literal(b"42.000", DECIMAL)),
    ];
    assert_eq!(consistent(&one_value), Some(true));
}

#[test]
fn ill_formed_literals_and_other_datatypes_give_no_answer() {
    let ill = vec![valued(b"ex:age", b"ex:ann", int(b"4 2"))];
    assert_eq!(consistent(&ill), None);
    let other = vec![valued(b"ex:age", b"ex:ann", literal(b"<a/>", XML_LITERAL))];
    assert_eq!(consistent(&other), None);
    let ranged = vec![sub(class(b"ex:A"), some(b"ex:p", datatype(XML_LITERAL)))];
    assert_eq!(consistent(&ranged), None);
}

#[test]
fn numbers_strings_and_truth_values_are_apart() {
    let items = vec![];
    let both = and(
        some(b"ex:p", datatype(INTEGER)),
        all(b"ex:p", datatype(STRING)),
    );
    assert_eq!(class_satisfiable(&items, &both), Some(false));
    let decimal = and(
        some(b"ex:p", datatype(INTEGER)),
        all(b"ex:p", datatype(DECIMAL)),
    );
    assert_eq!(class_satisfiable(&items, &decimal), Some(true));
    assert_eq!(
        subsumed(
            &items,
            &some(b"ex:p", datatype(INTEGER)),
            &some(b"ex:p", datatype(DECIMAL))
        ),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &items,
            &some(b"ex:p", datatype(DECIMAL)),
            &some(b"ex:p", datatype(INTEGER))
        ),
        Some(false)
    );
    let fraction = and(
        some(b"ex:p", not_range(datatype(INTEGER))),
        all(b"ex:p", datatype(DECIMAL)),
    );
    assert_eq!(class_satisfiable(&items, &fraction), Some(true));
    let none = and(
        some(b"ex:p", not_range(datatype(INTEGER))),
        all(b"ex:p", datatype(INTEGER)),
    );
    assert_eq!(class_satisfiable(&items, &none), Some(false));
    let plain = and(
        some(b"ex:p", datatype(PLAIN)),
        all(b"ex:p", not_range(datatype(STRING))),
    );
    assert_eq!(class_satisfiable(&items, &plain), Some(true));
}

#[test]
fn literal_values_have_their_datatypes() {
    let items = vec![sub(class(b"ex:Adult"), all(b"ex:age", datatype(INTEGER)))];
    let half = and(
        class(b"ex:Adult"),
        has(b"ex:age", literal(b"18.5", DECIMAL)),
    );
    assert_eq!(class_satisfiable(&items, &half), Some(false));
    let whole = and(
        class(b"ex:Adult"),
        has(b"ex:age", literal(b"18.0", DECIMAL)),
    );
    assert_eq!(class_satisfiable(&items, &whole), Some(true));
    let text = and(class(b"ex:Adult"), has(b"ex:age", literal(b"18@", PLAIN)));
    assert_eq!(class_satisfiable(&items, &text), Some(false));
    let ranged = vec![
        axiom(Axiom::DataPropertyRange(data(b"ex:age"), datatype(INTEGER))),
        valued(b"ex:age", b"ex:ann", literal(b"old", STRING)),
    ];
    assert_eq!(consistent(&ranged), Some(false));
}

#[test]
fn plain_literals_without_a_tag_are_strings() {
    let items = vec![
        functional(b"ex:name"),
        valued(b"ex:name", b"ex:ann", literal(b"Ann@", PLAIN)),
        valued(b"ex:name", b"ex:ann", literal(b"Ann", STRING)),
    ];
    assert_eq!(consistent(&items), Some(true));
    let tagged = vec![
        functional(b"ex:name"),
        valued(b"ex:name", b"ex:ann", literal(b"Ann@en", PLAIN)),
        valued(b"ex:name", b"ex:ann", literal(b"Ann", STRING)),
    ];
    assert_eq!(consistent(&tagged), Some(false));
    let cased = vec![
        functional(b"ex:name"),
        valued(b"ex:name", b"ex:ann", literal(b"Ann@en-GB", PLAIN)),
        valued(b"ex:name", b"ex:ann", literal(b"Ann@EN-gb", PLAIN)),
    ];
    assert_eq!(consistent(&cased), Some(true));
}

#[test]
fn there_are_two_truth_values() {
    let items = vec![];
    let three = at_least(3, b"ex:flag", Some(datatype(BOOLEAN)));
    assert_eq!(class_satisfiable(&items, &three), Some(false));
    let two_flags = at_least(2, b"ex:flag", Some(datatype(BOOLEAN)));
    assert_eq!(class_satisfiable(&items, &two_flags), Some(true));
    let not_true = and(
        two_flags,
        all(
            b"ex:flag",
            not_range(one_of(literal(b"1", BOOLEAN), Vec::new())),
        ),
    );
    assert_eq!(class_satisfiable(&items, &not_true), Some(false));
}

#[test]
fn counting_values() {
    let items = vec![];
    let many = and(
        at_least(2, b"ex:p", Some(datatype(INTEGER))),
        at_most(1, b"ex:p", None),
    );
    assert_eq!(class_satisfiable(&items, &many), Some(false));
    let enumerated = and(
        at_least(3, b"ex:p", None),
        all(
            b"ex:p",
            one_of(int(b"1"), vec![int(b"2"), literal(b"1.0", DECIMAL)]),
        ),
    );
    assert_eq!(class_satisfiable(&items, &enumerated), Some(false));
    let literal_top = some(b"ex:p", datatype(LITERAL));
    assert_eq!(
        subsumed(&items, &literal_top, &at_least(1, b"ex:p", None)),
        Some(true)
    );
    assert_eq!(
        subsumed(&items, &at_least(1, b"ex:p", None), &literal_top),
        Some(true)
    );
}

#[test]
fn data_values_are_not_individuals() {
    let items = vec![
        sub(
            class(THING),
            ClassExpression::ObjectOneOf(NonEmpty {
                first: named(b"ex:only"),
                rest: Vec::new(),
            }),
        ),
        valued(b"ex:p", b"ex:only", int(b"1")),
        valued(b"ex:p", b"ex:only", int(b"2")),
        valued(b"ex:p", b"ex:only", int(b"3")),
    ];
    assert_eq!(consistent(&items), Some(true));
    let everything = vec![sub(
        class(THING),
        ClassExpression::ObjectAllValuesFrom(property(TOP_OBJECT), Box::new(class(b"ex:A"))),
    )];
    assert_eq!(
        class_satisfiable(
            &everything,
            &and(some(b"ex:p", datatype(INTEGER)), not(class(b"ex:A")))
        ),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&everything, &some(b"ex:p", datatype(INTEGER))),
        Some(true)
    );
}

#[test]
fn data_property_axioms() {
    let hierarchy = vec![
        axiom(Axiom::SubDataPropertyOf(data(b"ex:p"), data(b"ex:q"))),
        functional(b"ex:q"),
        valued(b"ex:p", b"ex:a", int(b"1")),
        valued(b"ex:q", b"ex:a", int(b"2")),
    ];
    assert_eq!(consistent(&hierarchy), Some(false));
    let disjoint = vec![
        axiom(Axiom::DisjointDataProperties(two(
            data(b"ex:p"),
            data(b"ex:q"),
            Vec::new(),
        ))),
        valued(b"ex:p", b"ex:a", int(b"1")),
        valued(b"ex:q", b"ex:a", int(b"01")),
    ];
    assert_eq!(consistent(&disjoint), Some(false));
    let apart = vec![
        axiom(Axiom::DisjointDataProperties(two(
            data(b"ex:p"),
            data(b"ex:q"),
            Vec::new(),
        ))),
        valued(b"ex:p", b"ex:a", int(b"1")),
        valued(b"ex:q", b"ex:a", int(b"2")),
    ];
    assert_eq!(consistent(&apart), Some(true));
    let domain = vec![
        axiom(Axiom::DataPropertyDomain(
            data(b"ex:age"),
            class(b"ex:Person"),
        )),
        valued(b"ex:age", b"ex:ann", int(b"7")),
    ];
    assert_eq!(
        instance_of(&domain, &individual(b"ex:ann"), &class(b"ex:Person")),
        Some(true)
    );
    let negative = vec![
        unvalued(b"ex:p", b"ex:a", int(b"1")),
        valued(b"ex:p", b"ex:a", literal(b"1.", DECIMAL)),
    ];
    assert_eq!(consistent(&negative), Some(false));
    let top = vec![axiom(Axiom::SubDataPropertyOf(
        data(b"ex:p"),
        data(b"http://www.w3.org/2002/07/owl#topDataProperty"),
    ))];
    assert_eq!(consistent(&top), Some(true));
    let bottom = vec![valued(
        b"http://www.w3.org/2002/07/owl#bottomDataProperty",
        b"ex:a",
        int(b"1"),
    )];
    assert_eq!(consistent(&bottom), Some(false));
}

#[test]
fn medication_doses() {
    // A drug with a maximum daily dose; an order of a drug at a dose that is
    // the drug's flagged dose needs review.
    let items = vec![
        functional(b"ex:maximumDailyDose"),
        sub(
            and(class(b"ex:Order"), has(b"ex:dose", literal(b"40", INTEGER))),
            class(b"ex:NeedsReview"),
        ),
        asserted(class(b"ex:Order"), b"ex:order1"),
        valued(b"ex:dose", b"ex:order1", literal(b"40.0", DECIMAL)),
        valued(
            b"ex:maximumDailyDose",
            b"ex:warfarin",
            literal(b"10", INTEGER),
        ),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"ex:order1"), &class(b"ex:NeedsReview")),
        Some(true)
    );
    let mut conflicting = items;
    conflicting.push(valued(
        b"ex:maximumDailyDose",
        b"ex:warfarin",
        literal(b"12", INTEGER),
    ));
    assert_eq!(consistent(&conflicting), Some(false));
}

#[test]
fn the_universal_role_outside_its_own_axioms_gives_no_answer() {
    let valued_item = || valued(b"ex:p", b"ex:ann", int(b"1"));
    let included = vec![
        valued_item(),
        axiom(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Single(property(TOP_OBJECT)),
            property(b"ex:r"),
        )),
    ];
    assert_eq!(consistent(&included), None);
    let chained = vec![
        valued_item(),
        axiom(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Chain(two(
                property(b"ex:r"),
                property(TOP_OBJECT),
                Vec::new(),
            )),
            property(b"ex:s"),
        )),
    ];
    assert_eq!(consistent(&chained), None);
    let functional_top = vec![
        valued_item(),
        axiom(Axiom::FunctionalObjectProperty(property(TOP_OBJECT))),
    ];
    assert_eq!(consistent(&functional_top), None);
    let inverse = vec![
        valued_item(),
        axiom(Axiom::InverseObjectProperties(
            property(b"ex:r"),
            property(TOP_OBJECT),
        )),
    ];
    assert_eq!(consistent(&inverse), None);
    let into_top = vec![
        valued_item(),
        axiom(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Single(property(b"ex:r")),
            property(TOP_OBJECT),
        )),
        axiom(Axiom::ObjectPropertyAssertion(
            property(b"ex:r"),
            named(b"ex:ann"),
            named(b"ex:bob"),
        )),
    ];
    assert_eq!(consistent(&into_top), Some(true));
}

#[test]
fn a_question_names_only_individuals_of_the_closure() {
    let items = vec![
        valued(b"ex:p", b"ex:ann", int(b"1")),
        asserted(class(b"ex:A"), b"ex:bob"),
    ];
    let bob = ClassExpression::ObjectOneOf(NonEmpty {
        first: named(b"ex:bob"),
        rest: Vec::new(),
    });
    let carl = || {
        ClassExpression::ObjectOneOf(NonEmpty {
            first: named(b"ex:carl"),
            rest: Vec::new(),
        })
    };
    assert_eq!(subsumed(&items, &bob, &class(b"ex:A")), Some(true));
    assert_eq!(class_satisfiable(&items, &not(carl())), None);
    assert_eq!(subsumed(&items, &carl(), &class(b"ex:A")), None);
    assert_eq!(
        instance_of(&items, &individual(b"ex:bob"), &class(b"ex:A")),
        Some(true)
    );
    assert_eq!(
        instance_of(&items, &individual(b"ex:carl"), &class(b"ex:A")),
        Some(false)
    );
}
