use rowl_kernel::alc_ontology;
use rowl_kernel::concepts::Concept;
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
use rowl_kernel::shi_ontology::{
    class_parts, class_satisfiable, consistent, instance_of, prepare, prepared_class_satisfiable,
    prepared_consistent, prepared_instance_of, prepared_subsumed, subsumed,
};

const THING: &[u8] = b"http://www.w3.org/2002/07/owl#Thing";
const NOTHING: &[u8] = b"http://www.w3.org/2002/07/owl#Nothing";
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
fn or(a: ClassExpression, b: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectUnionOf(Box::new(two(a, b, Vec::new())))
}
fn not(a: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(a))
}
fn some_along(r: ObjectPropertyExpression, c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(r, Box::new(c))
}
fn all_along(r: ObjectPropertyExpression, c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectAllValuesFrom(r, Box::new(c))
}
fn some(r: &[u8], c: ClassExpression) -> ClassExpression {
    some_along(property(r), c)
}
fn all(r: &[u8], c: ClassExpression) -> ClassExpression {
    all_along(property(r), c)
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
fn asserted(c: ClassExpression, a: Individual) -> AnnotatedAxiom {
    axiom(Axiom::ClassAssertion(c, a))
}
fn related(r: ObjectPropertyExpression, a: Individual, b: Individual) -> AnnotatedAxiom {
    axiom(Axiom::ObjectPropertyAssertion(r, a, b))
}
fn included(sub: ObjectPropertyExpression, sup: ObjectPropertyExpression) -> AnnotatedAxiom {
    axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Single(sub),
        sup,
    ))
}
fn transitive(role: ObjectPropertyExpression) -> AnnotatedAxiom {
    axiom(Axiom::TransitiveObjectProperty(role))
}

#[test]
fn class_axioms_absorb_into_definitions() {
    // A named subclass, an existential restriction and an intersection on the
    // left absorb; a union on the left joins the TBox concept.
    let items = vec![
        sub(class(b"A"), class(b"B")),
        sub(some(b"r", class(b"C")), class(b"D")),
        sub(and(class(b"E"), some(b"r", class(b"F"))), class(b"G")),
        sub(or(class(b"H"), class(b"I")), class(b"J")),
        axiom(Axiom::DisjointClasses(two(
            class(b"B"),
            class(b"K"),
            Vec::new(),
        ))),
    ];
    let parts = class_parts(&items).expect("supported axioms");
    assert_eq!(parts.definitions.len(), 4);
    assert!(matches!(parts.axioms, Concept::And(_, _)));
    assert_eq!(subsumed(&items, &class(b"A"), &class(b"B")), Some(true));
    assert_eq!(
        subsumed(&items, &some(b"r", class(b"C")), &class(b"D")),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &items,
            &and(class(b"E"), some(b"r", and(class(b"F"), class(b"X")))),
            &class(b"G")
        ),
        Some(true)
    );
    assert_eq!(subsumed(&items, &class(b"E"), &class(b"G")), Some(false));
    assert_eq!(subsumed(&items, &class(b"I"), &class(b"J")), Some(true));
    assert_eq!(
        class_satisfiable(&items, &and(class(b"A"), class(b"K"))),
        Some(false)
    );
    assert_eq!(class_satisfiable(&items, &class(b"A")), Some(true));
    // owl:Thing on the left is no definition.
    let everything = vec![sub(class(THING), class(b"B"))];
    let parts = class_parts(&everything).expect("supported axioms");
    assert_eq!(parts.definitions.len(), 0);
    assert_eq!(
        subsumed(&everything, &class(b"X"), &class(b"B")),
        Some(true)
    );
}

#[test]
fn inverse_properties_reach_back() {
    // Whatever has a parent is a child; every parent has only happy children.
    let items = vec![
        axiom(Axiom::InverseObjectProperties(
            property(b"hasParent"),
            property(b"hasChild"),
        )),
        sub(class(b"Parent"), all(b"hasChild", class(b"Happy"))),
        asserted(class(b"Parent"), named(b"ann")),
        related(property(b"hasParent"), named(b"bea"), named(b"ann")),
    ];
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(&items, &individual(b"bea"), &class(b"Happy")),
        Some(true)
    );
    assert_eq!(
        instance_of(&items, &individual(b"ann"), &class(b"Happy")),
        Some(false)
    );
    // Without the inverse axiom, hasParent says nothing about hasChild.
    let unrelated: Vec<AnnotatedAxiom> = items.into_iter().skip(1).collect();
    assert_eq!(
        instance_of(&unrelated, &individual(b"bea"), &class(b"Happy")),
        Some(false)
    );
    // ObjectInverseOf in a restriction and in an assertion.
    let items = vec![
        sub(
            some_along(inverse(b"hasChild"), class(b"Parent")),
            class(b"Child"),
        ),
        related(inverse(b"hasChild"), named(b"bea"), named(b"ann")),
        asserted(class(b"Parent"), named(b"ann")),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"bea"), &class(b"Child")),
        Some(true)
    );
}

#[test]
fn symmetric_and_transitive_inverse_properties() {
    let items = vec![
        axiom(Axiom::SymmetricObjectProperty(property(b"near"))),
        sub(some(b"near", class(b"Fire")), class(b"Danger")),
        related(property(b"near"), named(b"fire1"), named(b"house")),
        asserted(class(b"Fire"), named(b"fire1")),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"house"), &class(b"Danger")),
        Some(true)
    );
    let one_way: Vec<AnnotatedAxiom> = items.into_iter().skip(1).collect();
    assert_eq!(
        instance_of(&one_way, &individual(b"house"), &class(b"Danger")),
        Some(false)
    );
    // A transitive inverse property makes its property transitive.
    let items = vec![
        transitive(inverse(b"partOf")),
        related(property(b"partOf"), named(b"a"), named(b"b")),
        related(property(b"partOf"), named(b"b"), named(b"c")),
        asserted(all(b"partOf", class(b"Small")), named(b"a")),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"c"), &class(b"Small")),
        Some(true)
    );
    // An inclusion between inverse properties.
    let items = vec![
        included(inverse(b"hasPart"), property(b"partOf")),
        related(property(b"hasPart"), named(b"car"), named(b"wheel")),
        asserted(all(b"partOf", class(b"Vehicle")), named(b"wheel")),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"car"), &class(b"Vehicle")),
        Some(true)
    );
}

#[test]
fn domains_and_ranges_of_inverse_properties() {
    let items = vec![
        axiom(Axiom::ObjectPropertyDomain(
            property(b"hasPart"),
            class(b"Machine"),
        )),
        axiom(Axiom::ObjectPropertyRange(
            inverse(b"hasPart"),
            class(b"Machine"),
        )),
        axiom(Axiom::ObjectPropertyDomain(
            inverse(b"hasPart"),
            class(b"Part"),
        )),
    ];
    let anything = || class(THING);
    assert_eq!(
        subsumed(&items, &some(b"hasPart", anything()), &class(b"Machine")),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &items,
            &some_along(inverse(b"hasPart"), anything()),
            &and(
                class(b"Part"),
                all_along(inverse(b"hasPart"), class(b"Machine"))
            )
        ),
        Some(true)
    );
    assert_eq!(
        subsumed(&items, &class(b"Part"), &some(b"hasPart", anything())),
        Some(false)
    );
}

#[test]
fn negative_assertions_and_unsupported_inputs() {
    let items = vec![
        related(property(b"r"), named(b"a"), named(b"b")),
        axiom(Axiom::NegativeObjectPropertyAssertion(
            inverse(b"r"),
            named(b"b"),
            named(b"a"),
        )),
    ];
    assert_eq!(consistent(&items), Some(false));
    let items = vec![
        related(property(b"r"), named(b"a"), named(b"b")),
        axiom(Axiom::NegativeObjectPropertyAssertion(
            property(b"r"),
            named(b"b"),
            named(b"a"),
        )),
    ];
    assert_eq!(consistent(&items), Some(true));
    // Negative assertions next to role axioms, property chains, built-in
    // properties and other constructors have no answer.
    let mut with_roles = items;
    with_roles.push(axiom(Axiom::SymmetricObjectProperty(property(b"r"))));
    assert_eq!(consistent(&with_roles), None);
    let chain = vec![axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(two(property(b"r"), property(b"r"), Vec::new())),
        property(b"r"),
    ))];
    assert_eq!(consistent(&chain), None);
    let builtin = vec![axiom(Axiom::InverseObjectProperties(
        property(b"r"),
        property(TOP_OBJECT),
    ))];
    assert_eq!(consistent(&builtin), None);
    let in_concept = vec![sub(class(b"A"), some(TOP_OBJECT, class(b"B")))];
    assert_eq!(consistent(&in_concept), None);
    let reflexive = vec![axiom(Axiom::ReflexiveObjectProperty(property(b"r")))];
    assert_eq!(consistent(&reflexive), None);
    let enumeration = ClassExpression::ObjectOneOf(NonEmpty {
        first: named(b"a"),
        rest: Vec::new(),
    });
    assert_eq!(class_satisfiable(&Vec::new(), &enumeration), None);
}

/// A deterministic pseudo-random ALC class expression over A, B, owl:Thing,
/// owl:Nothing and R, with inverse restrictions when `inverses` is set.
fn random_expression(seed: &mut u64, depth: u32, inverses: bool) -> ClassExpression {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 4 } else { 9 };
    let role = |seed: &u64| {
        if inverses && (*seed >> 45).is_multiple_of(2) {
            inverse(b"R")
        } else {
            property(b"R")
        }
    };
    match choice {
        0 => class(b"A"),
        1 => class(b"B"),
        2 => class(if (*seed >> 40).is_multiple_of(2) {
            THING
        } else {
            NOTHING
        }),
        3 => class(b"A"),
        4 => and(
            random_expression(seed, depth - 1, inverses),
            random_expression(seed, depth - 1, inverses),
        ),
        5 => or(
            random_expression(seed, depth - 1, inverses),
            random_expression(seed, depth - 1, inverses),
        ),
        6 => not(random_expression(seed, depth - 1, inverses)),
        7 => {
            let r = role(seed);
            some_along(r, random_expression(seed, depth - 1, inverses))
        }
        _ => {
            let r = role(seed);
            all_along(r, random_expression(seed, depth - 1, inverses))
        }
    }
}
fn random_axiom(seed: &mut u64, inverses: bool) -> AnnotatedAxiom {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let role = if inverses && (*seed >> 45).is_multiple_of(2) {
        inverse(b"R")
    } else {
        property(b"R")
    };
    match (*seed >> 33) % 7 {
        0 => sub(
            random_expression(seed, 2, inverses),
            random_expression(seed, 2, inverses),
        ),
        1 => axiom(Axiom::EquivalentClasses(two(
            random_expression(seed, 1, inverses),
            random_expression(seed, 1, inverses),
            vec![random_expression(seed, 1, inverses)],
        ))),
        2 => axiom(Axiom::DisjointClasses(two(
            random_expression(seed, 1, inverses),
            random_expression(seed, 1, inverses),
            vec![random_expression(seed, 1, inverses)],
        ))),
        3 => axiom(Axiom::DisjointUnion(
            Class { iri: iri(b"A") },
            two(
                random_expression(seed, 1, inverses),
                random_expression(seed, 1, inverses),
                Vec::new(),
            ),
        )),
        4 => axiom(Axiom::ObjectPropertyDomain(
            role,
            random_expression(seed, 1, inverses),
        )),
        5 => axiom(Axiom::ObjectPropertyRange(
            role,
            random_expression(seed, 1, inverses),
        )),
        _ => sub(
            and(
                some_along(role, random_expression(seed, 1, inverses)),
                random_expression(seed, 1, inverses),
            ),
            random_expression(seed, 1, inverses),
        ),
    }
}

/// A finite OWL interpretation with classes A and B and one role R.
struct Finite {
    size: usize,
    a: u32,
    b: u32,
    r: u32,
}
fn member(i: &Finite, name: &[u8], x: usize) -> bool {
    match name {
        b"A" => i.a >> x & 1 == 1,
        b"B" => i.b >> x & 1 == 1,
        THING => true,
        NOTHING => false,
        _ => panic!("unknown test class"),
    }
}
fn edge(i: &Finite, role: &ObjectPropertyExpression, x: usize, y: usize) -> bool {
    match role {
        ObjectPropertyExpression::Property(_) => i.r >> (x * i.size + y) & 1 == 1,
        ObjectPropertyExpression::Inverse(_) => i.r >> (y * i.size + x) & 1 == 1,
    }
}
/// The Direct Semantics of a class expression in the finite interpretation.
fn denotes(i: &Finite, e: &ClassExpression, x: usize) -> bool {
    match e {
        ClassExpression::Class(c) => member(i, &c.iri.spelling, x),
        ClassExpression::ObjectIntersectionOf(xs) => {
            denotes(i, &xs.first, x)
                && denotes(i, &xs.second, x)
                && xs.rest.iter().all(|e| denotes(i, e, x))
        }
        ClassExpression::ObjectUnionOf(xs) => {
            denotes(i, &xs.first, x)
                || denotes(i, &xs.second, x)
                || xs.rest.iter().any(|e| denotes(i, e, x))
        }
        ClassExpression::ObjectComplementOf(e) => !denotes(i, e, x),
        ClassExpression::ObjectSomeValuesFrom(r, e) => {
            (0..i.size).any(|y| edge(i, r, x, y) && denotes(i, e, y))
        }
        ClassExpression::ObjectAllValuesFrom(r, e) => {
            (0..i.size).all(|y| !edge(i, r, x, y) || denotes(i, e, y))
        }
        _ => panic!("outside the test fragment"),
    }
}
fn elements(xs: &AtLeastTwo<ClassExpression>) -> Vec<&ClassExpression> {
    let mut all = vec![&xs.first, &xs.second];
    all.extend(xs.rest.iter());
    all
}
/// The Direct Semantics of an axiom in the finite interpretation.
fn satisfied(i: &Finite, item: &AnnotatedAxiom) -> bool {
    let everywhere = |f: &dyn Fn(usize) -> bool| (0..i.size).all(f);
    let disjoint = |members: &Vec<&ClassExpression>| {
        (0..members.len()).all(|p| {
            (p + 1..members.len())
                .all(|q| everywhere(&|x| !(denotes(i, members[p], x) && denotes(i, members[q], x))))
        })
    };
    match &item.axiom {
        Axiom::SubClassOf(a, b) => everywhere(&|x| !denotes(i, a, x) || denotes(i, b, x)),
        Axiom::EquivalentClasses(xs) => {
            let members = elements(xs);
            members.iter().all(|a| {
                members
                    .iter()
                    .all(|b| everywhere(&|x| denotes(i, a, x) == denotes(i, b, x)))
            })
        }
        Axiom::DisjointClasses(xs) => disjoint(&elements(xs)),
        Axiom::DisjointUnion(c, xs) => {
            let members = elements(xs);
            let union = everywhere(&|x| {
                member(i, &c.iri.spelling, x) == members.iter().any(|e| denotes(i, e, x))
            });
            union && disjoint(&members)
        }
        Axiom::ObjectPropertyDomain(r, e) => {
            everywhere(&|x| (0..i.size).all(|y| !edge(i, r, x, y) || denotes(i, e, x)))
        }
        Axiom::ObjectPropertyRange(r, e) => {
            everywhere(&|x| (0..i.size).all(|y| !edge(i, r, x, y) || denotes(i, e, y)))
        }
        _ => panic!("outside the test axioms"),
    }
}
/// The meaning of a concept in the same interpretation.
fn holds(i: &Finite, c: &Concept, x: usize) -> bool {
    match c {
        Concept::Top => true,
        Concept::Bottom => false,
        Concept::Atom(a) => member(i, &a.iri.spelling, x),
        Concept::NotAtom(a) => !member(i, &a.iri.spelling, x),
        Concept::One(_) | Concept::NotOne(_) => panic!("the samples have no nominals"),
        Concept::And(a, b) => holds(i, a, x) && holds(i, b, x),
        Concept::Or(a, b) => holds(i, a, x) || holds(i, b, x),
        Concept::Exists(r, c) => (0..i.size).any(|y| edge(i, r, x, y) && holds(i, c, y)),
        Concept::Forall(r, c) => (0..i.size).all(|y| !edge(i, r, x, y) || holds(i, c, y)),
        Concept::AtLeast(n, r, c) => {
            (0..i.size)
                .filter(|&y| edge(i, r, x, y) && holds(i, c, y))
                .count()
                >= *n
        }
        Concept::AtMost(n, r, c) => {
            (0..i.size)
                .filter(|&y| edge(i, r, x, y) && holds(i, c, y))
                .count()
                <= *n
        }
    }
}
fn interpretations() -> Vec<Finite> {
    let mut all = Vec::new();
    for size in 1..=3usize {
        for a in 0..1u32 << size {
            for b in 0..1u32 << size {
                for r in 0..1u32 << (size * size) {
                    all.push(Finite { size, a, b, r });
                }
            }
        }
    }
    all
}

#[test]
fn class_parts_mean_the_axioms_in_small_interpretations() {
    let finite = interpretations();
    let mut seed = 5;
    for _ in 0..200 {
        let items: Vec<AnnotatedAxiom> = (0..2).map(|_| random_axiom(&mut seed, true)).collect();
        let parts = class_parts(&items).expect("supported axioms");
        for i in finite.iter().step_by(7) {
            let axioms_hold = items.iter().all(|item| satisfied(i, item));
            let tbox_holds = (0..i.size).all(|x| holds(i, &parts.axioms, x));
            let definitions_hold = parts.definitions.iter().all(|d| {
                (0..i.size).all(|x| !member(i, &d.class.iri.spelling, x) || holds(i, &d.concept, x))
            });
            assert_eq!(axioms_hold, tbox_holds && definitions_hold);
        }
    }
}

#[test]
fn every_class_with_a_small_model_of_the_axioms_is_satisfiable() {
    let finite = interpretations();
    let mut seed = 17;
    let mut with_model = 0;
    let mut without = 0;
    for _ in 0..200 {
        let items: Vec<AnnotatedAxiom> = (0..2).map(|_| random_axiom(&mut seed, true)).collect();
        let query = random_expression(&mut seed, 2, true);
        let answer = class_satisfiable(&items, &query).expect("supported input");
        let small_model = finite.iter().any(|i| {
            items.iter().all(|item| satisfied(i, item))
                && (0..i.size).any(|x| denotes(i, &query, x))
        });
        if small_model {
            assert!(answer, "a model exists, so the class must be satisfiable");
            with_model += 1;
        } else if !answer {
            without += 1;
        }
    }
    assert!(
        with_model > 30,
        "the sample must exercise satisfiable inputs"
    );
    assert!(
        without > 10,
        "the sample must exercise unsatisfiable inputs"
    );
}

#[test]
fn inverse_free_closures_agree_with_the_alc_queries() {
    // The verified ALC queries search without lazy unfolding, so the sample
    // keeps to one class axiom.
    let mut seed = 23;
    let mut negative = 0;
    for round in 0..200 {
        let mut items = vec![random_axiom(&mut seed, false)];
        items.push(asserted(
            random_expression(&mut seed, 1, false),
            named(b"a"),
        ));
        items.push(related(property(b"R"), named(b"a"), named(b"b")));
        if round % 3 == 0 {
            items.push(transitive(property(b"R")));
        }
        let query = random_expression(&mut seed, 1, false);
        assert_eq!(
            class_satisfiable(&items, &query),
            alc_ontology::class_satisfiable(&items, &query)
        );
        let old = alc_ontology::instance_of(&items, &individual(b"b"), &query);
        assert_eq!(instance_of(&items, &individual(b"b"), &query), old);
        if old == Some(false) {
            negative += 1;
        }
        assert_eq!(consistent(&items), alc_ontology::consistent(&items));
    }
    assert!(negative > 50, "the sample must exercise both answers");
}

#[test]
fn independent_choices_are_not_retried() {
    // The equivalence forces every element into A and gives each one an
    // R-successor outside A, so the closure is inconsistent. Every individual
    // branches on the same disjunctions; backjumping keeps the search linear in
    // the number of individuals instead of trying every combination of their
    // choices.
    let equivalence = || {
        axiom(Axiom::EquivalentClasses(two(
            some(b"R", class(NOTHING)),
            all(b"R", class(b"A")),
            vec![not(class(b"A"))],
        )))
    };
    let mut items = vec![equivalence()];
    for i in 0..8 {
        items.push(asserted(
            some(b"R", class(b"A")),
            named(format!("a{i}").as_bytes()),
        ));
    }
    assert_eq!(consistent(&items), Some(false));
    // Without the individuals the closure is still inconsistent.
    assert_eq!(consistent(&vec![equivalence()]), Some(false));
}

#[test]
fn one_preparation_answers_many_queries() {
    // A closure prepared once gives every query the answer it has on its own.
    let mut seed = 31;
    let b = individual(b"b");
    for _ in 0..60 {
        let mut items = vec![random_axiom(&mut seed, true), random_axiom(&mut seed, true)];
        items.push(asserted(random_expression(&mut seed, 1, true), named(b"a")));
        items.push(related(inverse(b"R"), named(b"b"), named(b"a")));
        let prepared = prepare(&items).expect("supported axioms");
        assert_eq!(prepared_consistent(&prepared), consistent(&items));
        for _ in 0..4 {
            let first = random_expression(&mut seed, 2, true);
            let second = random_expression(&mut seed, 2, true);
            assert_eq!(
                prepared_class_satisfiable(&prepared, &first),
                class_satisfiable(&items, &first)
            );
            assert_eq!(
                prepared_subsumed(&prepared, &first, &second),
                subsumed(&items, &first, &second)
            );
            assert_eq!(
                prepared_instance_of(&prepared, &b, &first),
                instance_of(&items, &b, &first)
            );
        }
    }
    // Axioms outside the supported fragment are not prepared.
    let unsupported = vec![axiom(Axiom::ReflexiveObjectProperty(property(b"R")))];
    assert!(prepare(&unsupported).is_none());
}

fn natural(n: usize) -> Natural {
    (0..n).fold(Natural::Zero, |previous, _| {
        Natural::Succ(Box::new(previous))
    })
}
fn at_least(n: usize, r: &[u8], c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectMinCardinality(natural(n), property(r), Some(Box::new(c)))
}
fn at_most(n: usize, r: &[u8], c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectMaxCardinality(natural(n), property(r), Some(Box::new(c)))
}
fn exactly(n: usize, r: &[u8], c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectExactCardinality(natural(n), property(r), Some(Box::new(c)))
}

/// Number restrictions and functional properties go to the completion forest,
/// which merges the individuals and anonymous elements that a maximum
/// restriction forces together.
#[test]
fn number_restrictions_and_functional_properties() {
    let a = || named(b"a");
    let b = || named(b"b");
    let c = || named(b"c");
    // A functional property merges its two values, which then clash.
    let functional = || axiom(Axiom::FunctionalObjectProperty(property(b"r")));
    let clash = vec![
        functional(),
        related(property(b"r"), a(), b()),
        related(property(b"r"), a(), c()),
        asserted(class(b"B"), b()),
        asserted(not(class(b"B")), c()),
    ];
    assert_eq!(consistent(&clash), Some(false));
    // Without the clash, the merged value carries the other's classes.
    let merged = vec![
        functional(),
        related(property(b"r"), a(), b()),
        related(property(b"r"), a(), c()),
        asserted(class(b"B"), b()),
    ];
    assert_eq!(consistent(&merged), Some(true));
    assert_eq!(
        instance_of(&merged, &individual(b"c"), &class(b"B")),
        Some(true)
    );
    assert_eq!(
        instance_of(&merged, &individual(b"a"), &class(b"B")),
        Some(false)
    );
    // An inverse functional property merges the individuals that point to one value.
    let inverse_clash = vec![
        axiom(Axiom::InverseFunctionalObjectProperty(property(b"r"))),
        related(property(b"r"), b(), a()),
        related(property(b"r"), c(), a()),
        asserted(class(b"B"), b()),
        asserted(not(class(b"B")), c()),
    ];
    assert_eq!(consistent(&inverse_clash), Some(false));
    // Cardinalities in class expressions, against the empty closure.
    let none: Vec<AnnotatedAxiom> = Vec::new();
    let thing = || class(THING);
    assert_eq!(
        class_satisfiable(
            &none,
            &and(at_least(2, b"r", thing()), at_most(1, b"r", thing()))
        ),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&none, &exactly(2, b"r", class(b"A"))),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &none,
            &at_least(3, b"r", class(b"A")),
            &at_least(2, b"r", class(b"A"))
        ),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &none,
            &at_least(2, b"r", class(b"A")),
            &at_least(3, b"r", class(b"A"))
        ),
        Some(false)
    );
    let squeezed = and(
        and(some(b"r", class(b"A")), some(b"r", class(b"B"))),
        at_most(1, b"r", thing()),
    );
    assert_eq!(
        subsumed(&none, &squeezed, &some(b"r", and(class(b"A"), class(b"B")))),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &none,
            &and(some(b"r", class(b"A")), some(b"r", class(b"B"))),
            &some(b"r", and(class(b"A"), class(b"B")))
        ),
        Some(false)
    );
    // Counting against an inverse: two children whose parent allows one child.
    let parent = vec![
        sub(class(b"Parent"), at_most(1, b"hasChild", thing())),
        asserted(class(b"Parent"), a()),
        related(property(b"hasChild"), a(), b()),
        related(property(b"hasChild"), a(), c()),
        asserted(class(b"B"), b()),
    ];
    assert_eq!(
        instance_of(&parent, &individual(b"c"), &class(b"B")),
        Some(true)
    );
    // A closure without counting still answers a question that counts.
    let plain = vec![
        related(property(b"r"), a(), b()),
        related(property(b"r"), a(), c()),
    ];
    assert_eq!(
        instance_of(&plain, &individual(b"a"), &at_least(1, b"r", thing())),
        Some(true)
    );
    assert_eq!(
        instance_of(&plain, &individual(b"a"), &at_least(2, b"r", thing())),
        Some(false)
    );
    // Negative assertions next to counting, and counting along a transitive
    // role, have no answer.
    let negative = vec![
        functional(),
        axiom(Axiom::NegativeObjectPropertyAssertion(
            property(b"r"),
            a(),
            b(),
        )),
    ];
    assert_eq!(consistent(&negative), None);
    let transitive = vec![
        axiom(Axiom::TransitiveObjectProperty(property(b"r"))),
        sub(class(b"A"), at_most(1, b"r", thing())),
    ];
    assert_eq!(consistent(&transitive), None);
}

fn same(members: Vec<Individual>) -> AnnotatedAxiom {
    let mut members = members.into_iter();
    let first = members.next().expect("two members");
    let second = members.next().expect("two members");
    axiom(Axiom::SameIndividual(two(first, second, members.collect())))
}
fn different(members: Vec<Individual>) -> AnnotatedAxiom {
    let mut members = members.into_iter();
    let first = members.next().expect("two members");
    let second = members.next().expect("two members");
    axiom(Axiom::DifferentIndividuals(two(
        first,
        second,
        members.collect(),
    )))
}

#[test]
fn equal_individuals_share_their_node() {
    let a = || named(b"a");
    let b = || named(b"b");
    let c = || named(b"c");
    // What holds of one holds of the other, in both directions.
    let items = vec![asserted(class(b"A"), a()), same(vec![b(), a()])];
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(&items, &individual(b"b"), &class(b"A")),
        Some(true)
    );
    // Links follow the shared node, and equality is transitive across axioms.
    let items = vec![
        related(property(b"r"), a(), named(b"d")),
        asserted(class(b"B"), named(b"d")),
        same(vec![a(), b()]),
        same(vec![c(), b()]),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"c"), &some(b"r", class(b"B"))),
        Some(true)
    );
    assert_eq!(
        instance_of(&items, &individual(b"d"), &class(b"A")),
        Some(false)
    );
    // Equal individuals with complementary classes clash.
    let items = vec![
        asserted(class(b"A"), a()),
        asserted(not(class(b"A")), c()),
        same(vec![a(), b(), c()]),
    ];
    assert_eq!(consistent(&items), Some(false));
    // A negative assertion is denied through the shared node.
    let items = vec![
        related(property(b"r"), a(), b()),
        axiom(Axiom::NegativeObjectPropertyAssertion(
            property(b"r"),
            c(),
            b(),
        )),
        same(vec![a(), c()]),
    ];
    assert_eq!(consistent(&items), Some(false));
    // A counting question merges equal individuals too.
    let items = vec![
        axiom(Axiom::FunctionalObjectProperty(property(b"r"))),
        related(property(b"r"), a(), b()),
        asserted(class(b"A"), b()),
        same(vec![a(), c()]),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"c"), &at_least(1, b"r", class(b"A"))),
        Some(true)
    );
    assert_eq!(
        instance_of(&items, &individual(b"b"), &at_least(1, b"r", class(b"A"))),
        Some(false)
    );
}

#[test]
fn different_individuals_stay_apart() {
    let a = || named(b"a");
    let b = || named(b"b");
    let c = || named(b"c");
    let items = vec![different(vec![a(), b(), c()])];
    assert_eq!(consistent(&items), Some(true));
    // An equality between two of them contradicts the inequality.
    let items = vec![different(vec![a(), b(), c()]), same(vec![c(), a()])];
    assert_eq!(consistent(&items), Some(false));
    assert_eq!(class_satisfiable(&items, &class(b"A")), Some(false));
    // A repeated member contradicts it too, since inequality compares
    // occurrences.
    let items = vec![different(vec![a(), b(), a()])];
    assert_eq!(consistent(&items), Some(false));
    // Without counting, different individuals keep their own facts.
    let items = vec![
        different(vec![a(), b()]),
        asserted(class(b"A"), a()),
        asserted(not(class(b"A")), b()),
    ];
    assert_eq!(consistent(&items), Some(true));
    // A counting question with an inequality gets no answer yet.
    let items = vec![
        axiom(Axiom::FunctionalObjectProperty(property(b"r"))),
        related(property(b"r"), c(), a()),
        related(property(b"r"), c(), b()),
        different(vec![a(), b()]),
    ];
    assert_eq!(consistent(&items), None);
    // One preparation answers questions about equal and different individuals.
    let items = vec![
        same(vec![a(), b()]),
        different(vec![b(), c()]),
        asserted(class(b"A"), a()),
    ];
    let prepared = prepare(&items).expect("supported axioms");
    assert_eq!(prepared_consistent(&prepared), Some(true));
    assert_eq!(
        prepared_instance_of(&prepared, &individual(b"b"), &class(b"A")),
        Some(true)
    );
    assert_eq!(
        prepared_instance_of(&prepared, &individual(b"c"), &class(b"A")),
        Some(false)
    );
}
