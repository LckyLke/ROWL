use rowl_kernel::data_ontology::{
    class_satisfiable, consistent, instance_of, prepare, prepared_class_satisfiable, subsumed,
};
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;

const XSD: &str = "http://www.w3.org/2001/XMLSchema#";
const OWL: &str = "http://www.w3.org/2002/07/owl#";

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn xsd(name: &str) -> Vec<u8> {
    format!("{XSD}{name}").into_bytes()
}
fn owl(name: &str) -> Vec<u8> {
    format!("{OWL}{name}").into_bytes()
}
fn class(s: &[u8]) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(s) })
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
    literal(lexical, &xsd("integer"))
}
fn dec(lexical: &[u8]) -> Literal {
    literal(lexical, &xsd("decimal"))
}
fn facet(name: &str, value: Literal) -> FacetRestriction {
    FacetRestriction {
        facet: iri(&xsd(name)),
        value,
    }
}
fn restricted(dt: &[u8], first: FacetRestriction, rest: Vec<FacetRestriction>) -> DataRange {
    DataRange::Restriction(Datatype { iri: iri(dt) }, NonEmpty { first, rest })
}
fn both(a: DataRange, b: DataRange) -> DataRange {
    DataRange::Intersection(Box::new(AtLeastTwo {
        first: a,
        second: b,
        rest: Vec::new(),
    }))
}
fn not_range(a: DataRange) -> DataRange {
    DataRange::Complement(Box::new(a))
}
fn one_of(value: Literal) -> DataRange {
    DataRange::OneOf(NonEmpty {
        first: value,
        rest: Vec::new(),
    })
}
fn and(a: ClassExpression, b: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first: a,
        second: b,
        rest: Vec::new(),
    }))
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
fn at_least(n: usize, p: &[u8], r: DataRange) -> ClassExpression {
    ClassExpression::DataMinCardinality(natural(n), data(p), Some(r))
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
fn valued(p: &[u8], a: &[u8], lt: Literal) -> AnnotatedAxiom {
    axiom(Axiom::DataPropertyAssertion(data(p), named(a), lt))
}
fn ranged(p: &[u8], r: DataRange) -> AnnotatedAxiom {
    axiom(Axiom::DataPropertyRange(data(p), r))
}
fn functional(p: &[u8]) -> AnnotatedAxiom {
    axiom(Axiom::FunctionalDataProperty(data(p)))
}
/// Run a test body on a thread with a large stack: the search recurses once per
/// rule application, and debug builds use large frames.
fn with_stack(body: fn()) {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(body)
        .expect("a test thread")
        .join()
        .expect("the test body passes");
}

#[test]
fn a_dose_above_the_daily_maximum_is_inconsistent() {
    let limit = || {
        ranged(
            b"ex:dailyDose",
            restricted(
                &xsd("decimal"),
                facet("maxInclusive", dec(b"4000")),
                Vec::new(),
            ),
        )
    };
    let over = vec![
        limit(),
        valued(b"ex:dailyDose", b"ex:prescription1", dec(b"4500.5")),
    ];
    assert_eq!(consistent(&over), Some(false));
    let within = vec![
        limit(),
        valued(b"ex:dailyDose", b"ex:prescription1", dec(b"3999.75")),
    ];
    assert_eq!(consistent(&within), Some(true));
    let exactly = vec![
        limit(),
        valued(b"ex:dailyDose", b"ex:prescription1", int(b"4000")),
    ];
    assert_eq!(consistent(&exactly), Some(true));
    let alert = vec![
        limit(),
        sub(
            some(
                b"ex:prescribed",
                restricted(
                    &xsd("decimal"),
                    facet("minExclusive", dec(b"4000")),
                    Vec::new(),
                ),
            ),
            class(b"ex:Overdose"),
        ),
        valued(
            b"ex:prescribed",
            b"ex:prescription2",
            literal(b"8001/2", &owl("rational")),
        ),
    ];
    assert_eq!(
        instance_of(
            &alert,
            &NamedIndividual {
                iri: iri(b"ex:prescription2")
            },
            &class(b"ex:Overdose")
        ),
        Some(true)
    );
}

#[test]
fn a_byte_has_256_values() {
    with_stack(byte_values);
}
fn byte_values() {
    let items = vec![];
    let many = at_least(300, b"ex:p", datatype(&xsd("byte")));
    assert_eq!(class_satisfiable(&items, &many), Some(false));
}
#[test]
fn a_byte_has_all_256_values() {
    with_stack(all_byte_values);
}
fn all_byte_values() {
    let items = vec![];
    let all_of_them = at_least(256, b"ex:p", datatype(&xsd("byte")));
    assert_eq!(class_satisfiable(&items, &all_of_them), Some(true));
}
#[test]
fn a_few_unsigned_bytes() {
    with_stack(few_bytes);
}
fn few_bytes() {
    let items = vec![];
    let unsigned = at_least(3, b"ex:p", datatype(&xsd("unsignedByte")));
    assert_eq!(class_satisfiable(&items, &unsigned), Some(true));
}

#[test]
fn reals_between_zero_and_one_need_not_be_rational() {
    let items = vec![];
    let open = restricted(
        &owl("real"),
        facet("minExclusive", int(b"0")),
        vec![facet("maxExclusive", int(b"1"))],
    );
    let irrational = some(b"ex:p", both(open, not_range(datatype(&owl("rational")))));
    assert_eq!(class_satisfiable(&items, &irrational), Some(true));
    let unit = restricted(
        &owl("rational"),
        facet("minExclusive", int(b"0")),
        vec![facet("maxExclusive", int(b"1"))],
    );
    let third = some(b"ex:p", both(unit, not_range(datatype(&xsd("decimal")))));
    assert_eq!(class_satisfiable(&items, &third), Some(true));
    let integers = restricted(
        &xsd("integer"),
        facet("minExclusive", int(b"0")),
        vec![facet("maxExclusive", int(b"1"))],
    );
    assert_eq!(
        class_satisfiable(&items, &some(b"ex:p", integers)),
        Some(false)
    );
}

#[test]
fn integers_between_bounds_are_counted() {
    let items = vec![];
    let small = || {
        restricted(
            &xsd("integer"),
            facet("minExclusive", int(b"0")),
            vec![facet("maxInclusive", dec(b"3.5"))],
        )
    };
    assert_eq!(
        class_satisfiable(&items, &at_least(3, b"ex:p", small())),
        Some(true)
    );
    assert_eq!(
        class_satisfiable(&items, &at_least(4, b"ex:p", small())),
        Some(false)
    );
    let point = restricted(
        &xsd("integer"),
        facet("minInclusive", int(b"5")),
        vec![facet("maxInclusive", dec(b"5.0"))],
    );
    assert_eq!(
        class_satisfiable(&items, &at_least(2, b"ex:p", point)),
        Some(false)
    );
}

#[test]
fn integer_subtypes_nest() {
    let items = vec![];
    assert_eq!(
        subsumed(
            &items,
            &some(b"ex:p", datatype(&xsd("unsignedByte"))),
            &some(b"ex:p", datatype(&xsd("short")))
        ),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &items,
            &some(b"ex:p", datatype(&xsd("short"))),
            &some(b"ex:p", datatype(&xsd("unsignedByte")))
        ),
        Some(false)
    );
    let apart = and(
        some(b"ex:p", datatype(&xsd("nonNegativeInteger"))),
        all(b"ex:p", datatype(&xsd("negativeInteger"))),
    );
    assert_eq!(class_satisfiable(&items, &apart), Some(false));
    let zero = and(
        some(b"ex:p", datatype(&xsd("nonNegativeInteger"))),
        all(b"ex:p", datatype(&xsd("nonPositiveInteger"))),
    );
    assert_eq!(class_satisfiable(&items, &zero), Some(true));
    let two_zeros = and(
        at_least(2, b"ex:p", datatype(&xsd("nonNegativeInteger"))),
        all(b"ex:p", datatype(&xsd("nonPositiveInteger"))),
    );
    assert_eq!(class_satisfiable(&items, &two_zeros), Some(false));
}

#[test]
fn rational_literals_are_values() {
    let items = vec![functional(b"ex:share")];
    let third = and(
        has(b"ex:share", literal(b"1/3", &owl("rational"))),
        all(b"ex:share", datatype(&xsd("decimal"))),
    );
    assert_eq!(class_satisfiable(&items, &third), Some(false));
    let quarter = and(
        has(b"ex:share", literal(b"1/4", &owl("rational"))),
        has(b"ex:share", dec(b"0.25")),
    );
    assert_eq!(class_satisfiable(&items, &quarter), Some(true));
    let ordered = and(
        has(b"ex:share", literal(b"1/3", &owl("rational"))),
        all(
            b"ex:share",
            restricted(
                &owl("rational"),
                facet("minExclusive", dec(b"0.3333")),
                vec![facet("maxExclusive", dec(b"0.3334"))],
            ),
        ),
    );
    assert_eq!(class_satisfiable(&items, &ordered), Some(true));
}

#[test]
fn facets_take_bounds_of_any_numeric_datatype() {
    let items = vec![];
    let above = restricted(
        &xsd("integer"),
        facet("minInclusive", dec(b"1.5")),
        Vec::new(),
    );
    let one = and(
        some(b"ex:p", above),
        all(
            b"ex:p",
            restricted(
                &xsd("integer"),
                facet("maxExclusive", int(b"2")),
                Vec::new(),
            ),
        ),
    );
    assert_eq!(class_satisfiable(&items, &one), Some(false));
    let text = restricted(
        &xsd("integer"),
        facet("minInclusive", literal(b"one", &xsd("string"))),
        Vec::new(),
    );
    assert_eq!(class_satisfiable(&items, &some(b"ex:p", text)), None);
}

#[test]
fn prepared_questions_have_room_for_64_values() {
    with_stack(prepared_room);
}
fn prepared_room() {
    let items = vec![sub(
        class(b"ex:A"),
        some(b"ex:p", datatype(&xsd("unsignedByte"))),
    )];
    let prepared = prepare(&items).unwrap();
    let fits = and(
        class(b"ex:A"),
        at_least(10, b"ex:p", datatype(&xsd("unsignedByte"))),
    );
    assert_eq!(prepared_class_satisfiable(&prepared, &fits), Some(true));
    let too_many = and(
        class(b"ex:A"),
        at_least(100, b"ex:p", datatype(&xsd("unsignedByte"))),
    );
    assert_eq!(prepared_class_satisfiable(&prepared, &too_many), None);
    assert_eq!(class_satisfiable(&items, &too_many), Some(true));
}

#[test]
fn every_integer_subtype_has_its_bounds() {
    with_stack(subtype_bounds);
}
/// A bound of a subtype: its value and the value just outside it.
type Bound = Option<(&'static [u8], &'static [u8])>;
fn subtype_bounds() {
    // Each subtype with its least and greatest value, when it has them, and a
    // value just outside each bound.
    let cases: [(&str, Bound, Bound); 12] = [
        ("nonNegativeInteger", Some((b"0", b"-1")), None),
        ("nonPositiveInteger", None, Some((b"0", b"1"))),
        ("positiveInteger", Some((b"1", b"0")), None),
        ("negativeInteger", None, Some((b"-1", b"0"))),
        (
            "long",
            Some((b"-9223372036854775808", b"-9223372036854775809")),
            Some((b"9223372036854775807", b"9223372036854775808")),
        ),
        (
            "int",
            Some((b"-2147483648", b"-2147483649")),
            Some((b"2147483647", b"2147483648")),
        ),
        (
            "short",
            Some((b"-32768", b"-32769")),
            Some((b"32767", b"32768")),
        ),
        ("byte", Some((b"-128", b"-129")), Some((b"127", b"128"))),
        (
            "unsignedLong",
            Some((b"0", b"-1")),
            Some((b"18446744073709551615", b"18446744073709551616")),
        ),
        (
            "unsignedInt",
            Some((b"0", b"-1")),
            Some((b"4294967295", b"4294967296")),
        ),
        (
            "unsignedShort",
            Some((b"0", b"-1")),
            Some((b"65535", b"65536")),
        ),
        ("unsignedByte", Some((b"0", b"-1")), Some((b"255", b"256"))),
    ];
    let items = vec![];
    for (name, lower, upper) in cases {
        let holds = |value: &[u8]| {
            class_satisfiable(
                &items,
                &and(has(b"ex:p", int(value)), all(b"ex:p", datatype(&xsd(name)))),
            )
        };
        for (inside, outside) in lower.into_iter().chain(upper) {
            assert_eq!(holds(inside), Some(true), "{name} contains {inside:?}");
            assert_eq!(holds(outside), Some(false), "{name} excludes {outside:?}");
        }
    }
}

#[test]
fn literal_values_take_integers_of_a_run() {
    with_stack(literal_run);
}
fn literal_run() {
    // ex:a has the value 5, one of the integers 4, 5 and 6 of [4, 6].
    let items = vec![valued(b"ex:q", b"ex:a", int(b"5"))];
    let run = || {
        restricted(
            &xsd("integer"),
            facet("minInclusive", int(b"4")),
            vec![facet("maxInclusive", int(b"6"))],
        )
    };
    assert_eq!(
        class_satisfiable(&items, &at_least(3, b"ex:p", run())),
        Some(true)
    );
    assert_eq!(
        class_satisfiable(&items, &at_least(4, b"ex:p", run())),
        Some(false)
    );
    let others = || both(run(), not_range(one_of(int(b"5"))));
    assert_eq!(
        class_satisfiable(&items, &at_least(2, b"ex:p", others())),
        Some(true)
    );
    assert_eq!(
        class_satisfiable(&items, &at_least(3, b"ex:p", others())),
        Some(false)
    );
    // Every integer of [4, 5] is a literal value.
    let pair = vec![
        valued(b"ex:q", b"ex:a", int(b"4")),
        valued(b"ex:q", b"ex:b", int(b"5")),
    ];
    let small = || {
        restricted(
            &xsd("integer"),
            facet("minInclusive", int(b"4")),
            vec![facet("maxInclusive", int(b"5"))],
        )
    };
    assert_eq!(
        class_satisfiable(&pair, &at_least(2, b"ex:p", small())),
        Some(true)
    );
    let neither = both(
        small(),
        both(not_range(one_of(int(b"4"))), not_range(one_of(int(b"5")))),
    );
    assert_eq!(
        class_satisfiable(&pair, &at_least(1, b"ex:p", neither)),
        Some(false)
    );
}
