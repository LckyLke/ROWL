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
    // Next to role axioms the completion forest decides negative assertions.
    let mut with_roles = items;
    with_roles.push(axiom(Axiom::SymmetricObjectProperty(property(b"r"))));
    assert_eq!(consistent(&with_roles), Some(false));
    // A functional property that a chain reaches, built-in properties, other
    // constructors and nominals of individuals the closure does not have get
    // no answer.
    let chain = vec![
        axiom(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Chain(two(property(b"r"), property(b"r"), Vec::new())),
            property(b"r"),
        )),
        axiom(Axiom::FunctionalObjectProperty(property(b"r"))),
    ];
    assert_eq!(consistent(&chain), None);
    let builtin = vec![axiom(Axiom::InverseObjectProperties(
        property(b"r"),
        property(TOP_OBJECT),
    ))];
    assert_eq!(consistent(&builtin), None);
    let in_concept = vec![sub(class(b"A"), some(TOP_OBJECT, class(b"B")))];
    assert_eq!(consistent(&in_concept), None);
    let functional_data = vec![axiom(Axiom::FunctionalDataProperty(DataProperty {
        iri: iri(b"weight"),
    }))];
    assert_eq!(consistent(&functional_data), None);
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
        ClassExpression::ObjectHasSelf(r) => edge(i, r, x, x),
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
        Axiom::ReflexiveObjectProperty(r) => everywhere(&|x| edge(i, r, x, x)),
        Axiom::IrreflexiveObjectProperty(r) => everywhere(&|x| !edge(i, r, x, x)),
        Axiom::FunctionalObjectProperty(r) => {
            everywhere(&|x| (0..i.size).filter(|&y| edge(i, r, x, y)).count() <= 1)
        }
        Axiom::AsymmetricObjectProperty(r) => {
            everywhere(&|x| (0..i.size).all(|y| !edge(i, r, x, y) || !edge(i, r, y, x)))
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
        Concept::HasSelf(r) => edge(i, r, x, x),
        Concept::NotSelf(r) => !edge(i, r, x, x),
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
    let unsupported = vec![axiom(Axiom::FunctionalDataProperty(DataProperty {
        iri: iri(b"weight"),
    }))];
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
    // Negative assertions next to counting are decided; counting along a
    // transitive role has no answer.
    let negative = vec![
        functional(),
        related(property(b"r"), a(), named(b"c")),
        axiom(Axiom::NegativeObjectPropertyAssertion(
            property(b"r"),
            a(),
            b(),
        )),
    ];
    assert_eq!(consistent(&negative), Some(true));
    let mut merged = negative;
    merged.push(same(vec![b(), named(b"c")]));
    assert_eq!(consistent(&merged), Some(false));
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
    // A counting question keeps different individuals apart too.
    let items = vec![
        axiom(Axiom::FunctionalObjectProperty(property(b"r"))),
        related(property(b"r"), c(), a()),
        related(property(b"r"), c(), b()),
        different(vec![a(), b()]),
    ];
    assert_eq!(consistent(&items), Some(false));
    let items = vec![
        axiom(Axiom::FunctionalObjectProperty(property(b"r"))),
        related(property(b"r"), c(), a()),
        related(property(b"r"), c(), b()),
    ];
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(
            &items,
            &individual(b"a"),
            &ClassExpression::ObjectOneOf(NonEmpty {
                first: b(),
                rest: Vec::new(),
            })
        ),
        Some(true)
    );
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

fn one_of(members: Vec<Individual>) -> ClassExpression {
    let mut members = members.into_iter();
    let first = members.next().expect("one member");
    ClassExpression::ObjectOneOf(NonEmpty {
        first,
        rest: members.collect(),
    })
}
fn has_value(r: &[u8], a: Individual) -> ClassExpression {
    ClassExpression::ObjectHasValue(property(r), a)
}
fn refused(r: &[u8], a: Individual, b: Individual) -> AnnotatedAxiom {
    axiom(Axiom::NegativeObjectPropertyAssertion(property(r), a, b))
}

#[test]
fn nominals_name_their_individuals() {
    let a = || named(b"a");
    let b = || named(b"b");
    let c = || named(b"c");
    // An enumeration of one individual makes its instances that individual.
    let items = vec![
        sub(class(b"A"), one_of(vec![a()])),
        asserted(class(b"A"), b()),
        asserted(class(b"B"), a()),
    ];
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(&items, &individual(b"b"), &class(b"B")),
        Some(true)
    );
    assert_eq!(
        instance_of(&items, &individual(b"b"), &one_of(vec![a()])),
        Some(true)
    );
    let mut apart = items;
    apart.push(different(vec![a(), b()]));
    assert_eq!(consistent(&apart), Some(false));
    // A value restriction relates to the individual itself.
    let items = vec![
        asserted(has_value(b"r", a()), b()),
        asserted(class(b"A"), a()),
    ];
    assert_eq!(
        instance_of(&items, &individual(b"b"), &some(b"r", class(b"A"))),
        Some(true)
    );
    let mut refusing = items;
    refusing.push(refused(b"r", b(), a()));
    assert_eq!(consistent(&refusing), Some(false));
    // A domain of two individuals cannot hold three different successors.
    let items = vec![
        sub(class(THING), one_of(vec![a(), b()])),
        asserted(at_least(3, b"r", thing()), a()),
    ];
    assert_eq!(consistent(&items), Some(false));
    let items = vec![
        sub(class(THING), one_of(vec![a(), b()])),
        asserted(at_least(2, b"r", thing()), a()),
    ];
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(&items, &individual(b"a"), &has_value(b"r", b())),
        Some(true)
    );
    // Questions with nominals of the closure's individuals are decided, and
    // classes that differ only in their nominals are told apart.
    let items = vec![
        asserted(class(b"A"), a()),
        asserted(not(class(b"A")), b()),
        related(property(b"r"), c(), a()),
    ];
    assert_eq!(
        subsumed(&items, &one_of(vec![a()]), &class(b"A")),
        Some(true)
    );
    assert_eq!(
        subsumed(&items, &one_of(vec![a(), b()]), &class(b"A")),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&items, &and(one_of(vec![b()]), class(b"A"))),
        Some(false)
    );
    assert_eq!(
        instance_of(&items, &individual(b"c"), &has_value(b"r", a())),
        Some(true)
    );
    assert_eq!(
        instance_of(&items, &individual(b"c"), &has_value(b"r", b())),
        Some(false)
    );
    // One preparation answers questions with and without nominals.
    let prepared = prepare(&items).expect("supported axioms");
    assert_eq!(prepared_consistent(&prepared), Some(true));
    assert_eq!(
        prepared_subsumed(&prepared, &one_of(vec![b()]), &not(class(b"A"))),
        Some(true)
    );
    assert_eq!(
        prepared_instance_of(&prepared, &individual(b"a"), &class(b"A")),
        Some(true)
    );
    // Nominals of individuals the closure does not have, and of anonymous
    // individuals, get no answer.
    assert_eq!(class_satisfiable(&items, &one_of(vec![named(b"d")])), None);
    let anonymous = Individual::Anonymous(AnonymousIndividual {
        scope: Vec::new(),
        label: b"x".to_vec(),
    });
    assert_eq!(
        consistent(&vec![sub(class(b"A"), one_of(vec![anonymous]))]),
        None
    );
}

/// A maximum restriction of an individual that counts anonymous elements
/// reaching it through a nominal gets new named nodes for them.
#[test]
fn counting_through_nominals() {
    let a = || named(b"a");
    let b = || named(b"b");
    let reaches = |c: ClassExpression| some(b"r", and(c, has_value(b"r", b())));
    let predecessors = |n: usize| {
        ClassExpression::ObjectMaxCardinality(natural(n), inverse(b"r"), Some(Box::new(thing())))
    };
    // Two r-successors of a that differ in A both have b as an r-successor, but
    // b has at most one r-predecessor.
    let differing = || and(reaches(class(b"A")), reaches(not(class(b"A"))));
    let items = vec![asserted(differing(), a()), asserted(predecessors(1), b())];
    assert_eq!(consistent(&items), Some(false));
    let items = vec![asserted(differing(), a()), asserted(predecessors(2), b())];
    assert_eq!(consistent(&items), Some(true));
    // Successors that agree are then one element.
    let items = vec![
        asserted(and(reaches(class(b"A")), reaches(class(b"B"))), a()),
        asserted(predecessors(1), b()),
    ];
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(
            &items,
            &individual(b"a"),
            &some(b"r", and(class(b"A"), class(b"B")))
        ),
        Some(true)
    );
}

/// A finite OWL interpretation of A, B and R with the individuals a and b.
struct Named<'a> {
    base: &'a Finite,
    a: usize,
    b: usize,
}
fn individual_at(i: &Named, x: &Individual) -> usize {
    match x {
        Individual::Named(n) if n.iri.spelling == b"a" => i.a,
        Individual::Named(n) if n.iri.spelling == b"b" => i.b,
        _ => panic!("unknown test individual"),
    }
}
/// The Direct Semantics of a class expression with nominals.
fn denotes_named(i: &Named, e: &ClassExpression, x: usize) -> bool {
    match e {
        ClassExpression::ObjectIntersectionOf(xs) => {
            denotes_named(i, &xs.first, x)
                && denotes_named(i, &xs.second, x)
                && xs.rest.iter().all(|e| denotes_named(i, e, x))
        }
        ClassExpression::ObjectUnionOf(xs) => {
            denotes_named(i, &xs.first, x)
                || denotes_named(i, &xs.second, x)
                || xs.rest.iter().any(|e| denotes_named(i, e, x))
        }
        ClassExpression::ObjectComplementOf(e) => !denotes_named(i, e, x),
        ClassExpression::ObjectSomeValuesFrom(r, e) => {
            (0..i.base.size).any(|y| edge(i.base, r, x, y) && denotes_named(i, e, y))
        }
        ClassExpression::ObjectAllValuesFrom(r, e) => {
            (0..i.base.size).all(|y| !edge(i.base, r, x, y) || denotes_named(i, e, y))
        }
        ClassExpression::ObjectOneOf(xs) => {
            individual_at(i, &xs.first) == x || xs.rest.iter().any(|m| individual_at(i, m) == x)
        }
        ClassExpression::ObjectHasValue(r, m) => edge(i.base, r, x, individual_at(i, m)),
        _ => denotes(i.base, e, x),
    }
}
fn satisfied_named(i: &Named, item: &AnnotatedAxiom) -> bool {
    match &item.axiom {
        Axiom::SubClassOf(sub, sup) => {
            (0..i.base.size).all(|x| !denotes_named(i, sub, x) || denotes_named(i, sup, x))
        }
        Axiom::ClassAssertion(e, m) => denotes_named(i, e, individual_at(i, m)),
        Axiom::ObjectPropertyAssertion(r, s, t) => {
            edge(i.base, r, individual_at(i, s), individual_at(i, t))
        }
        Axiom::NegativeObjectPropertyAssertion(r, s, t) => {
            !edge(i.base, r, individual_at(i, s), individual_at(i, t))
        }
        Axiom::SameIndividual(xs) => individual_at(i, &xs.first) == individual_at(i, &xs.second),
        Axiom::DifferentIndividuals(xs) => {
            individual_at(i, &xs.first) != individual_at(i, &xs.second)
        }
        _ => panic!("outside the test axioms"),
    }
}
fn next(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *seed >> 33
}
fn random_member(seed: &mut u64) -> Individual {
    if next(seed).is_multiple_of(2) {
        named(b"a")
    } else {
        named(b"b")
    }
}
/// A random class expression over A, B, R and nominals of a and b.
fn random_nominal_expression(seed: &mut u64, depth: u32) -> ClassExpression {
    match next(seed) % if depth == 0 { 4 } else { 10 } {
        0 => class(b"A"),
        1 => class(b"B"),
        2 => one_of(vec![random_member(seed)]),
        3 => has_value(b"R", random_member(seed)),
        4 => and(
            random_nominal_expression(seed, depth - 1),
            random_nominal_expression(seed, depth - 1),
        ),
        5 => or(
            random_nominal_expression(seed, depth - 1),
            random_nominal_expression(seed, depth - 1),
        ),
        6 => not(random_nominal_expression(seed, depth - 1)),
        7 => some(b"R", random_nominal_expression(seed, depth - 1)),
        8 => all(b"R", random_nominal_expression(seed, depth - 1)),
        _ => one_of(vec![named(b"a"), named(b"b")]),
    }
}
fn random_nominal_axiom(seed: &mut u64) -> AnnotatedAxiom {
    match next(seed) % 7 {
        0 | 1 => sub(
            random_nominal_expression(seed, 1),
            random_nominal_expression(seed, 1),
        ),
        2 | 3 => asserted(random_nominal_expression(seed, 2), random_member(seed)),
        4 => related(property(b"R"), random_member(seed), random_member(seed)),
        5 => refused(b"R", random_member(seed), random_member(seed)),
        _ => {
            if next(seed).is_multiple_of(2) {
                same(vec![named(b"a"), named(b"b")])
            } else {
                different(vec![named(b"a"), named(b"b")])
            }
        }
    }
}

fn thing() -> ClassExpression {
    class(THING)
}
fn with_stack(body: fn()) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(body)
        .expect("a test thread")
        .join()
        .expect("the test body passes");
}

#[test]
fn nominal_closures_agree_with_small_models() {
    with_stack(nominal_closures_agree_with_small_models_body);
}
fn nominal_closures_agree_with_small_models_body() {
    let finite = interpretations();
    let mut seed = 101;
    let mut consistent_small = 0;
    let mut inconsistent = 0;
    let mut refuted = 0;
    for _ in 0..300 {
        let mut items: Vec<AnnotatedAxiom> =
            (0..3).map(|_| random_nominal_axiom(&mut seed)).collect();
        // Both individuals have nodes, so every question about them is asked.
        items.push(asserted(thing(), named(b"a")));
        items.push(asserted(thing(), named(b"b")));
        let query = random_nominal_expression(&mut seed, 2);
        let models: Vec<Named> = finite
            .iter()
            .flat_map(|base| {
                (0..base.size).flat_map(move |a| (0..base.size).map(move |b| Named { base, a, b }))
            })
            .filter(|i| items.iter().all(|item| satisfied_named(i, item)))
            .collect();
        let answer = consistent(&items);
        if !models.is_empty() {
            assert_ne!(
                answer,
                Some(false),
                "a model exists, so the closure is consistent"
            );
            consistent_small += 1;
        }
        if answer == Some(false) {
            inconsistent += 1;
        }
        // An instance answer must hold in every small model.
        if instance_of(&items, &individual(b"a"), &query) == Some(true) {
            assert!(
                models.iter().all(|i| denotes_named(i, &query, i.a)),
                "an entailed instance holds in every model"
            );
        }
        // A satisfiable class has an instance in some model, so a small model
        // with one refutes an unsatisfiability answer.
        if models
            .iter()
            .any(|i| (0..i.base.size).any(|x| denotes_named(i, &query, x)))
        {
            assert_ne!(class_satisfiable(&items, &query), Some(false));
            refuted += 1;
        }
    }
    assert!(
        consistent_small > 50,
        "the sample must exercise consistent closures"
    );
    assert!(
        inconsistent > 20,
        "the sample must exercise inconsistent closures"
    );
    assert!(refuted > 50, "the sample must exercise satisfiable classes");
}

fn has_self(r: ObjectPropertyExpression) -> ClassExpression {
    ClassExpression::ObjectHasSelf(r)
}

/// A deterministic pseudo-random class expression over A, B and R with self
/// restrictions along R or its inverse.
fn random_self_expression(seed: &mut u64, depth: u32) -> ClassExpression {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 4 } else { 9 };
    let role = if (*seed >> 45).is_multiple_of(2) {
        inverse(b"R")
    } else {
        property(b"R")
    };
    match choice {
        0 => class(b"A"),
        1 => class(b"B"),
        2 | 3 => has_self(role),
        4 => and(
            random_self_expression(seed, depth - 1),
            random_self_expression(seed, depth - 1),
        ),
        5 => or(
            random_self_expression(seed, depth - 1),
            random_self_expression(seed, depth - 1),
        ),
        6 => not(random_self_expression(seed, depth - 1)),
        7 => some_along(role, random_self_expression(seed, depth - 1)),
        _ => all_along(role, random_self_expression(seed, depth - 1)),
    }
}
fn random_self_axiom(seed: &mut u64) -> AnnotatedAxiom {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let role = if (*seed >> 45).is_multiple_of(2) {
        inverse(b"R")
    } else {
        property(b"R")
    };
    match (*seed >> 33) % 5 {
        0 => axiom(Axiom::ReflexiveObjectProperty(role)),
        1 => axiom(Axiom::IrreflexiveObjectProperty(role)),
        2 => axiom(Axiom::FunctionalObjectProperty(role)),
        _ => sub(
            random_self_expression(seed, 1),
            random_self_expression(seed, 1),
        ),
    }
}

/// Self restrictions are loops of the completion forest, and reflexive and
/// irreflexive properties require or forbid them everywhere.
#[test]
fn self_restrictions_and_reflexive_properties() {
    let r = || property(b"r");
    let reflexive = vec![axiom(Axiom::ReflexiveObjectProperty(r()))];
    assert_eq!(consistent(&reflexive), Some(true));
    assert_eq!(
        subsumed(&reflexive, &thing(), &has_self(inverse(b"r"))),
        Some(true)
    );
    // Universal restrictions pass along a loop.
    assert_eq!(
        subsumed(&reflexive, &all(b"r", class(b"A")), &class(b"A")),
        Some(true)
    );
    assert_eq!(
        subsumed(&Vec::new(), &all(b"r", class(b"A")), &class(b"A")),
        Some(false)
    );
    let both = vec![
        axiom(Axiom::ReflexiveObjectProperty(r())),
        axiom(Axiom::IrreflexiveObjectProperty(r())),
    ];
    assert_eq!(consistent(&both), Some(false));
    // An irreflexive property refutes the loops of the roles it includes, in
    // either direction, but not their other edges.
    let irreflexive = vec![
        axiom(Axiom::IrreflexiveObjectProperty(r())),
        included(property(b"s"), r()),
    ];
    assert_eq!(
        class_satisfiable(&irreflexive, &has_self(property(b"s"))),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&irreflexive, &has_self(inverse(b"s"))),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&irreflexive, &some(b"s", has_self(property(b"t")))),
        Some(true)
    );
    // A link from an individual to itself is a loop.
    let mut looped = irreflexive;
    looped.push(related(r(), named(b"a"), named(b"a")));
    assert_eq!(consistent(&looped), Some(false));
    // Along a functional property with a loop, every successor of an
    // individual is the individual itself.
    let functional = vec![
        axiom(Axiom::ReflexiveObjectProperty(r())),
        axiom(Axiom::FunctionalObjectProperty(r())),
        asserted(some(b"r", class(b"B")), named(b"a")),
    ];
    assert_eq!(
        instance_of(&functional, &individual(b"a"), &class(b"B")),
        Some(true)
    );
    // Below an anonymous element, the successor merges into its parent, whose
    // edge becomes a loop.
    let deep = vec![
        axiom(Axiom::ReflexiveObjectProperty(r())),
        axiom(Axiom::FunctionalObjectProperty(r())),
    ];
    assert_eq!(
        class_satisfiable(
            &deep,
            &some(b"s", and(some(b"r", class(b"B")), not(class(b"B"))))
        ),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&deep, &some(b"s", some(b"r", class(b"B")))),
        Some(true)
    );
    // The loop along a role included in the reflexive one comes from the merge.
    let mut included_loop = deep;
    included_loop.push(included(property(b"t"), r()));
    assert_eq!(
        class_satisfiable(
            &included_loop,
            &some(
                b"s",
                and(some(b"t", class(b"B")), not(has_self(property(b"t"))))
            )
        ),
        Some(false)
    );
    // The complement of a self restriction needs a simple role.
    let tangled = vec![
        axiom(Axiom::IrreflexiveObjectProperty(r())),
        transitive(r()),
    ];
    assert_eq!(consistent(&tangled), None);
    let reflexive_transitive = vec![axiom(Axiom::ReflexiveObjectProperty(r())), transitive(r())];
    assert_eq!(consistent(&reflexive_transitive), Some(true));
}

#[test]
fn every_class_with_a_small_model_of_self_restrictions_is_satisfiable() {
    let finite = interpretations();
    let mut seed = 31;
    let mut with_model = 0;
    let mut without = 0;
    let mut unanswered = 0;
    for _ in 0..300 {
        let items: Vec<AnnotatedAxiom> = (0..2).map(|_| random_self_axiom(&mut seed)).collect();
        let query = random_self_expression(&mut seed, 2);
        let small_model = finite.iter().any(|i| {
            items.iter().all(|item| satisfied(i, item))
                && (0..i.size).any(|x| denotes(i, &query, x))
        });
        match class_satisfiable(&items, &query) {
            Some(answer) => {
                if small_model {
                    assert!(answer, "a model exists, so the class must be satisfiable");
                    with_model += 1;
                } else if !answer {
                    without += 1;
                }
            }
            None => unanswered += 1,
        }
    }
    assert_eq!(unanswered, 0, "every sample is answered");
    assert!(
        with_model > 30,
        "the sample must exercise satisfiable inputs"
    );
    assert!(
        without > 10,
        "the sample must exercise unsatisfiable inputs"
    );
}

/// Asymmetric and disjoint object properties forbid pairs of edges, also
/// through loops and inclusions.
#[test]
fn asymmetric_and_disjoint_properties() {
    let r = || property(b"r");
    let s = || property(b"s");
    let asymmetric = vec![axiom(Axiom::AsymmetricObjectProperty(r()))];
    assert_eq!(consistent(&asymmetric), Some(true));
    assert_eq!(class_satisfiable(&asymmetric, &has_self(r())), Some(false));
    assert_eq!(
        class_satisfiable(&asymmetric, &some(b"r", thing())),
        Some(true)
    );
    assert_eq!(
        class_satisfiable(
            &asymmetric,
            &and(
                some(b"r", class(b"A")),
                all_along(inverse(b"r"), not(class(b"A")))
            )
        ),
        Some(true)
    );
    let mut both_ways = asymmetric;
    both_ways.push(related(r(), named(b"a"), named(b"b")));
    assert_eq!(consistent(&both_ways), Some(true));
    both_ways.push(related(r(), named(b"b"), named(b"a")));
    assert_eq!(consistent(&both_ways), Some(false));
    // A symmetric and asymmetric property relates nothing.
    let symmetric = vec![
        axiom(Axiom::AsymmetricObjectProperty(r())),
        axiom(Axiom::SymmetricObjectProperty(r())),
    ];
    assert_eq!(consistent(&symmetric), Some(true));
    assert_eq!(
        class_satisfiable(&symmetric, &some(b"r", thing())),
        Some(false)
    );
    // Disjoint properties relate no pair together, also through inclusions.
    let disjoint = vec![
        axiom(Axiom::DisjointObjectProperties(two(r(), s(), Vec::new()))),
        related(r(), named(b"a"), named(b"b")),
    ];
    assert_eq!(consistent(&disjoint), Some(true));
    let mut reversed = disjoint;
    reversed.push(related(s(), named(b"b"), named(b"a")));
    assert_eq!(consistent(&reversed), Some(true));
    reversed.push(related(s(), named(b"a"), named(b"b")));
    assert_eq!(consistent(&reversed), Some(false));
    let below_both = vec![
        axiom(Axiom::DisjointObjectProperties(two(r(), s(), Vec::new()))),
        included(property(b"t"), r()),
        included(property(b"t"), s()),
    ];
    assert_eq!(
        class_satisfiable(&below_both, &some(b"t", thing())),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&below_both, &and(some(b"r", thing()), some(b"s", thing()))),
        Some(true)
    );
    // Successors along both roles that a functional super-role merges.
    let mut merged = below_both;
    merged.push(included(r(), property(b"u")));
    merged.push(included(s(), property(b"u")));
    merged.push(axiom(Axiom::FunctionalObjectProperty(property(b"u"))));
    assert_eq!(
        class_satisfiable(&merged, &and(some(b"r", thing()), some(b"s", thing()))),
        Some(false)
    );
    // Three disjoint members, pairwise.
    let three = vec![axiom(Axiom::DisjointObjectProperties(two(
        r(),
        s(),
        vec![property(b"v")],
    )))];
    let mut v_and_s = three;
    v_and_s.push(related(property(b"v"), named(b"a"), named(b"b")));
    v_and_s.push(related(s(), named(b"a"), named(b"b")));
    assert_eq!(consistent(&v_and_s), Some(false));
    // Disjoint pairs need simple roles.
    let tangled = vec![axiom(Axiom::AsymmetricObjectProperty(r())), transitive(r())];
    assert_eq!(consistent(&tangled), None);
}

#[test]
fn every_class_with_a_small_model_of_asymmetric_properties_is_satisfiable() {
    let finite = interpretations();
    let mut seed = 47;
    let mut with_model = 0;
    let mut without = 0;
    for _ in 0..300 {
        let mut items: Vec<AnnotatedAxiom> = (0..2).map(|_| random_self_axiom(&mut seed)).collect();
        items.push(axiom(Axiom::AsymmetricObjectProperty(property(b"R"))));
        let query = random_self_expression(&mut seed, 2);
        let small_model = finite.iter().any(|i| {
            items.iter().all(|item| satisfied(i, item))
                && (0..i.size).any(|x| denotes(i, &query, x))
        });
        let answer = class_satisfiable(&items, &query).expect("every sample is answered");
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

fn chain_of(roles: Vec<ObjectPropertyExpression>, sup: ObjectPropertyExpression) -> AnnotatedAxiom {
    let mut rest = roles;
    let first = rest.remove(0);
    let second = rest.remove(0);
    axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(two(first, second, rest)),
        sup,
    ))
}
fn just(a: &[u8]) -> ClassExpression {
    ClassExpression::ObjectOneOf(NonEmpty {
        first: named(a),
        rest: Vec::new(),
    })
}
fn uncle_chain() -> AnnotatedAxiom {
    chain_of(
        vec![property(b"hasParent"), property(b"hasBrother")],
        property(b"hasUncle"),
    )
}

#[test]
fn role_chains_relate_individuals_along_their_roles() {
    let family = || {
        vec![
            related(property(b"hasParent"), named(b"ann"), named(b"bob")),
            related(property(b"hasBrother"), named(b"bob"), named(b"carl")),
        ]
    };
    let mut items = family();
    items.push(uncle_chain());
    assert_eq!(
        instance_of(
            &items,
            &individual(b"ann"),
            &some(b"hasUncle", just(b"carl"))
        ),
        Some(true)
    );
    // Without the chain nothing relates ann to carl.
    assert_eq!(
        instance_of(
            &family(),
            &individual(b"ann"),
            &some(b"hasUncle", just(b"carl"))
        ),
        Some(false)
    );
    // A negative assertion along the chain's role contradicts it.
    items.push(axiom(Axiom::NegativeObjectPropertyAssertion(
        property(b"hasUncle"),
        named(b"ann"),
        named(b"carl"),
    )));
    assert_eq!(consistent(&items), Some(false));
}

#[test]
fn role_chains_reach_class_inclusions() {
    let items = vec![
        uncle_chain(),
        sub(
            class(b"A"),
            some(b"hasParent", some(b"hasBrother", class(b"B"))),
        ),
    ];
    assert_eq!(
        subsumed(&items, &class(b"A"), &some(b"hasUncle", class(b"B"))),
        Some(true)
    );
    assert_eq!(
        class_satisfiable(
            &items,
            &and(class(b"A"), all(b"hasUncle", not(class(b"B"))))
        ),
        Some(false)
    );
    // The inverse chain: an uncle's nephews are the children of his siblings.
    assert_eq!(
        subsumed(
            &items,
            &some_along(
                inverse(b"hasBrother"),
                some_along(inverse(b"hasParent"), class(b"A"))
            ),
            &some_along(inverse(b"hasUncle"), class(b"A")),
        ),
        Some(true)
    );
}

#[test]
fn recursive_role_chains_relate_long_paths() {
    // locatedIn ∘ partOf ⊑ locatedIn: located in a room of a building.
    let items = vec![
        chain_of(
            vec![property(b"locatedIn"), property(b"partOf")],
            property(b"locatedIn"),
        ),
        related(property(b"locatedIn"), named(b"pump"), named(b"room")),
        related(property(b"partOf"), named(b"room"), named(b"floor")),
        related(property(b"partOf"), named(b"floor"), named(b"plant")),
    ];
    assert_eq!(
        instance_of(
            &items,
            &individual(b"pump"),
            &some(b"locatedIn", just(b"plant"))
        ),
        Some(true)
    );
    assert_eq!(
        instance_of(
            &items,
            &individual(b"room"),
            &some(b"locatedIn", just(b"plant"))
        ),
        Some(false)
    );
    // A chain whose roles include the chain's role in the middle is not regular.
    let tangled = vec![chain_of(
        vec![property(b"p"), property(b"r"), property(b"q")],
        property(b"r"),
    )];
    assert_eq!(class_satisfiable(&tangled, &all(b"r", class(b"B"))), None);
}

/// A finite interpretation of `A`, `B` and the properties `p`, `q`, `s` and
/// `r`, where `r` relates the pairs that `p ∘ q ⊑ r` and `r ∘ s ⊑ r` derive.
struct Chained {
    size: usize,
    a: Vec<bool>,
    b: Vec<bool>,
    relations: Vec<Vec<Vec<bool>>>,
}
const CHAIN_ROLES: [&[u8]; 4] = [b"p", b"q", b"s", b"r"];
fn next_random(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *seed >> 33
}
fn random_chained(seed: &mut u64) -> Chained {
    let size = 1 + (next_random(seed) % 3) as usize;
    let a = (0..size)
        .map(|_| next_random(seed).is_multiple_of(2))
        .collect();
    let b = (0..size)
        .map(|_| next_random(seed).is_multiple_of(2))
        .collect();
    let mut relations: Vec<Vec<Vec<bool>>> = (0..4)
        .map(|_| {
            (0..size)
                .map(|_| {
                    (0..size)
                        .map(|_| next_random(seed).is_multiple_of(3))
                        .collect()
                })
                .collect()
        })
        .collect();
    loop {
        let mut changed = false;
        for x in 0..size {
            for y in 0..size {
                for z in 0..size {
                    let pq = relations[0][x][y] && relations[1][y][z];
                    let rs = relations[3][x][y] && relations[2][y][z];
                    if (pq || rs) && !relations[3][x][z] {
                        relations[3][x][z] = true;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    Chained {
        size,
        a,
        b,
        relations,
    }
}
fn chained_edge(i: &Chained, role: &ObjectPropertyExpression, x: usize, y: usize) -> bool {
    let (p, flipped) = match role {
        ObjectPropertyExpression::Property(p) => (p, false),
        ObjectPropertyExpression::Inverse(p) => (p, true),
    };
    let index = CHAIN_ROLES
        .iter()
        .position(|name| *name == p.iri.spelling.as_slice())
        .expect("a known role");
    if flipped {
        i.relations[index][y][x]
    } else {
        i.relations[index][x][y]
    }
}
fn chained_denotes(i: &Chained, e: &ClassExpression, x: usize) -> bool {
    match e {
        ClassExpression::Class(c) => match c.iri.spelling.as_slice() {
            b"A" => i.a[x],
            b"B" => i.b[x],
            THING => true,
            NOTHING => false,
            _ => panic!("unknown test class"),
        },
        ClassExpression::ObjectIntersectionOf(xs) => {
            chained_denotes(i, &xs.first, x) && chained_denotes(i, &xs.second, x)
        }
        ClassExpression::ObjectUnionOf(xs) => {
            chained_denotes(i, &xs.first, x) || chained_denotes(i, &xs.second, x)
        }
        ClassExpression::ObjectComplementOf(e) => !chained_denotes(i, e, x),
        ClassExpression::ObjectSomeValuesFrom(r, e) => {
            (0..i.size).any(|y| chained_edge(i, r, x, y) && chained_denotes(i, e, y))
        }
        ClassExpression::ObjectAllValuesFrom(r, e) => {
            (0..i.size).all(|y| !chained_edge(i, r, x, y) || chained_denotes(i, e, y))
        }
        _ => panic!("outside the test fragment"),
    }
}
fn random_chained_expression(seed: &mut u64, depth: u32) -> ClassExpression {
    let choice = next_random(seed) % if depth == 0 { 3 } else { 8 };
    let role = |seed: &mut u64| {
        let name = CHAIN_ROLES[(next_random(seed) % 5).min(3) as usize];
        if next_random(seed).is_multiple_of(4) {
            inverse(name)
        } else {
            property(name)
        }
    };
    match choice {
        0 => class(b"A"),
        1 => class(b"B"),
        2 => not(class(b"B")),
        3 => and(
            random_chained_expression(seed, depth - 1),
            random_chained_expression(seed, depth - 1),
        ),
        4 => or(
            random_chained_expression(seed, depth - 1),
            random_chained_expression(seed, depth - 1),
        ),
        5 => not(random_chained_expression(seed, depth - 1)),
        6 => {
            let r = role(seed);
            some_along(r, random_chained_expression(seed, depth - 1))
        }
        _ => {
            let r = role(seed);
            all_along(r, random_chained_expression(seed, depth - 1))
        }
    }
}

#[test]
fn every_class_with_a_small_model_of_role_chains_is_satisfiable() {
    let mut seed = 23;
    let mut with_model = 0;
    let mut without = 0;
    for _ in 0..200 {
        // The same inclusion twice: one for the closure, one to evaluate.
        let mut copy = seed;
        let lhs = random_chained_expression(&mut seed, 1);
        let rhs = random_chained_expression(&mut seed, 2);
        let lhs_copy = random_chained_expression(&mut copy, 1);
        let rhs_copy = random_chained_expression(&mut copy, 2);
        let query = random_chained_expression(&mut seed, 2);
        let items = vec![
            chain_of(vec![property(b"p"), property(b"q")], property(b"r")),
            chain_of(vec![property(b"r"), property(b"s")], property(b"r")),
            sub(lhs, rhs),
        ];
        let small_model = (0..300).any(|_| {
            let i = random_chained(&mut seed);
            (0..i.size)
                .all(|x| !chained_denotes(&i, &lhs_copy, x) || chained_denotes(&i, &rhs_copy, x))
                && (0..i.size).any(|x| chained_denotes(&i, &query, x))
        });
        let answer = class_satisfiable(&items, &query).expect("every sample is answered");
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
    assert!(without > 5, "the sample must exercise unsatisfiable inputs");
}
