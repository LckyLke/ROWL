use rowl_kernel::alc_ontology::{
    class_satisfiable, consistent, instance_of, internalize, subsumed,
};
use rowl_kernel::model::*;
use rowl_kernel::nnf::NnfConcept;

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
fn some(r: &[u8], c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(property(r), Box::new(c))
}
fn all(r: &[u8], c: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectAllValuesFrom(property(r), Box::new(c))
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

#[test]
fn subclass_chains_and_disjointness() {
    let items = vec![
        sub(class(b"A"), class(b"B")),
        sub(class(b"B"), class(b"C")),
        axiom(Axiom::DisjointClasses(two(
            class(b"B"),
            class(b"D"),
            Vec::new(),
        ))),
    ];
    assert_eq!(subsumed(&items, &class(b"A"), &class(b"C")), Some(true));
    assert_eq!(subsumed(&items, &class(b"C"), &class(b"A")), Some(false));
    assert_eq!(class_satisfiable(&items, &class(b"A")), Some(true));
    assert_eq!(
        class_satisfiable(&items, &and(class(b"A"), class(b"D"))),
        Some(false)
    );
    assert_eq!(
        class_satisfiable(&items, &and(class(b"C"), class(b"D"))),
        Some(true)
    );
    // Every class is below owl:Thing, and owl:Nothing below every class.
    assert_eq!(subsumed(&items, &class(b"A"), &class(THING)), Some(true));
    assert_eq!(subsumed(&items, &class(NOTHING), &class(b"A")), Some(true));
}

#[test]
fn equivalence_and_disjoint_union() {
    let items = vec![
        axiom(Axiom::EquivalentClasses(two(
            class(b"A"),
            class(b"B"),
            vec![class(b"C")],
        ))),
        axiom(Axiom::DisjointUnion(
            Class {
                iri: iri(b"Animal"),
            },
            two(class(b"Cat"), class(b"Dog"), vec![class(b"Bird")]),
        )),
    ];
    assert_eq!(subsumed(&items, &class(b"C"), &class(b"A")), Some(true));
    assert_eq!(subsumed(&items, &class(b"A"), &class(b"C")), Some(true));
    assert_eq!(
        subsumed(&items, &class(b"Bird"), &class(b"Animal")),
        Some(true)
    );
    assert_eq!(
        class_satisfiable(&items, &and(class(b"Cat"), class(b"Bird"))),
        Some(false)
    );
    let neither = and(
        class(b"Animal"),
        and(
            not(class(b"Cat")),
            and(not(class(b"Dog")), not(class(b"Bird"))),
        ),
    );
    assert_eq!(class_satisfiable(&items, &neither), Some(false));
    assert_eq!(class_satisfiable(&items, &class(b"Animal")), Some(true));
    assert_eq!(consistent(&items), Some(true));
    // A duplicated member of a disjoint union must be empty.
    let items = vec![axiom(Axiom::DisjointClasses(two(
        class(b"A"),
        class(b"A"),
        Vec::new(),
    )))];
    assert_eq!(class_satisfiable(&items, &class(b"A")), Some(false));
    assert_eq!(consistent(&items), Some(true));
    // Something exists, so an axiom making everything empty is inconsistent.
    let items = vec![sub(class(THING), class(NOTHING))];
    assert_eq!(consistent(&items), Some(false));
    let items = vec![
        sub(class(THING), some(b"R", class(b"A"))),
        axiom(Axiom::ObjectPropertyRange(property(b"R"), not(class(b"A")))),
    ];
    assert_eq!(consistent(&items), Some(false));
}

#[test]
fn domain_and_range() {
    let items = vec![
        axiom(Axiom::ObjectPropertyDomain(
            property(b"hasPart"),
            class(b"Machine"),
        )),
        axiom(Axiom::ObjectPropertyRange(
            property(b"hasPart"),
            class(b"Part"),
        )),
        axiom(Axiom::DisjointClasses(two(
            class(b"Machine"),
            class(b"Part"),
            Vec::new(),
        ))),
    ];
    let anything = || class(THING);
    assert_eq!(
        subsumed(&items, &some(b"hasPart", anything()), &class(b"Machine")),
        Some(true)
    );
    assert_eq!(
        subsumed(
            &items,
            &some(b"hasPart", class(b"X")),
            &some(b"hasPart", and(class(b"X"), class(b"Part")))
        ),
        Some(true)
    );
    assert_eq!(
        subsumed(&items, &class(b"Machine"), &some(b"hasPart", anything())),
        Some(false)
    );
    // A part has no parts, since it would then be a machine.
    assert_eq!(
        subsumed(&items, &class(b"Part"), &all(b"hasPart", class(NOTHING))),
        Some(true)
    );
}

#[test]
fn unsupported_inputs_have_no_answer() {
    let declarations = vec![
        axiom(Axiom::Declaration(Entity::Class(Class { iri: iri(b"A") }))),
        axiom(Axiom::AnnotationAssertion(
            AnnotationProperty { iri: iri(b"label") },
            AnnotationSubject::Iri(iri(b"A")),
            AnnotationValue::Iri(iri(b"B")),
        )),
    ];
    assert_eq!(class_satisfiable(&declarations, &class(b"A")), Some(true));
    // Equality between individuals is not supported yet.
    let same = vec![axiom(Axiom::SameIndividual(two(
        Individual::Named(NamedIndividual { iri: iri(b"a") }),
        Individual::Named(NamedIndividual { iri: iri(b"b") }),
        Vec::new(),
    )))];
    assert_eq!(class_satisfiable(&same, &class(b"A")), None);
    assert_eq!(consistent(&same), None);
    let inverse = ClassExpression::ObjectSomeValuesFrom(
        ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(b"R") }),
        Box::new(class(b"A")),
    );
    assert_eq!(class_satisfiable(&declarations, &inverse), None);
    let inverse_domain = vec![axiom(Axiom::ObjectPropertyDomain(
        ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(b"R") }),
        class(b"A"),
    ))];
    assert_eq!(class_satisfiable(&inverse_domain, &class(b"A")), None);
    // The universal object property has a fixed meaning the tableau does not model.
    assert_eq!(
        class_satisfiable(&declarations, &some(TOP_OBJECT, class(b"A"))),
        None
    );
    let top_range = vec![axiom(Axiom::ObjectPropertyRange(
        property(TOP_OBJECT),
        class(b"A"),
    ))];
    assert_eq!(class_satisfiable(&top_range, &class(b"A")), None);
    let enumeration = ClassExpression::ObjectOneOf(NonEmpty {
        first: Individual::Named(NamedIndividual { iri: iri(b"a") }),
        rest: Vec::new(),
    });
    assert_eq!(class_satisfiable(&declarations, &enumeration), None);
    assert_eq!(subsumed(&declarations, &class(b"A"), &enumeration), None);
}

/// A deterministic pseudo-random ALC class expression over A, B, owl:Thing,
/// owl:Nothing and R.
fn random_expression(seed: &mut u64, depth: u32) -> ClassExpression {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 4 } else { 9 };
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
            random_expression(seed, depth - 1),
            random_expression(seed, depth - 1),
        ),
        5 => or(
            random_expression(seed, depth - 1),
            random_expression(seed, depth - 1),
        ),
        6 => not(random_expression(seed, depth - 1)),
        7 => some(b"R", random_expression(seed, depth - 1)),
        _ => all(b"R", random_expression(seed, depth - 1)),
    }
}
fn random_axiom(seed: &mut u64) -> AnnotatedAxiom {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    match (*seed >> 33) % 6 {
        0 => sub(random_expression(seed, 2), random_expression(seed, 2)),
        1 => axiom(Axiom::EquivalentClasses(two(
            random_expression(seed, 1),
            random_expression(seed, 1),
            vec![random_expression(seed, 1)],
        ))),
        2 => axiom(Axiom::DisjointClasses(two(
            random_expression(seed, 1),
            random_expression(seed, 1),
            vec![random_expression(seed, 1)],
        ))),
        3 => axiom(Axiom::DisjointUnion(
            Class { iri: iri(b"A") },
            two(
                random_expression(seed, 1),
                random_expression(seed, 1),
                Vec::new(),
            ),
        )),
        4 => axiom(Axiom::ObjectPropertyDomain(
            property(b"R"),
            random_expression(seed, 1),
        )),
        _ => axiom(Axiom::ObjectPropertyRange(
            property(b"R"),
            random_expression(seed, 1),
        )),
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
fn edge(i: &Finite, x: usize, y: usize) -> bool {
    i.r >> (x * i.size + y) & 1 == 1
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
        ClassExpression::ObjectSomeValuesFrom(_, e) => {
            (0..i.size).any(|y| edge(i, x, y) && denotes(i, e, y))
        }
        ClassExpression::ObjectAllValuesFrom(_, e) => {
            (0..i.size).all(|y| !edge(i, x, y) || denotes(i, e, y))
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
        Axiom::DisjointClasses(xs) => {
            let members = elements(xs);
            (0..members.len()).all(|p| {
                (p + 1..members.len()).all(|q| {
                    everywhere(&|x| !(denotes(i, members[p], x) && denotes(i, members[q], x)))
                })
            })
        }
        Axiom::DisjointUnion(c, xs) => {
            let members = elements(xs);
            let union = everywhere(&|x| {
                member(i, &c.iri.spelling, x) == members.iter().any(|e| denotes(i, e, x))
            });
            let disjoint = (0..members.len()).all(|p| {
                (p + 1..members.len()).all(|q| {
                    everywhere(&|x| !(denotes(i, members[p], x) && denotes(i, members[q], x)))
                })
            });
            union && disjoint
        }
        Axiom::ObjectPropertyDomain(_, e) => {
            everywhere(&|x| (0..i.size).all(|y| !edge(i, x, y) || denotes(i, e, x)))
        }
        Axiom::ObjectPropertyRange(_, e) => {
            everywhere(&|x| (0..i.size).all(|y| !edge(i, x, y) || denotes(i, e, y)))
        }
        _ => panic!("outside the test axioms"),
    }
}
/// The meaning of an NNF concept in the same interpretation.
fn holds(i: &Finite, c: &NnfConcept, x: usize) -> bool {
    match c {
        NnfConcept::Top => true,
        NnfConcept::Bottom => false,
        NnfConcept::Atom(a) => member(i, &a.iri.spelling, x),
        NnfConcept::NotAtom(a) => !member(i, &a.iri.spelling, x),
        NnfConcept::And(a, b) => holds(i, a, x) && holds(i, b, x),
        NnfConcept::Or(a, b) => holds(i, a, x) || holds(i, b, x),
        NnfConcept::Exists(_, c) => (0..i.size).any(|y| edge(i, x, y) && holds(i, c, y)),
        NnfConcept::Forall(_, c) => (0..i.size).all(|y| !edge(i, x, y) || holds(i, c, y)),
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
fn internalized_axioms_mean_the_axioms_in_small_interpretations() {
    let finite = interpretations();
    let mut seed = 5;
    for _ in 0..150 {
        let items: Vec<AnnotatedAxiom> = (0..2).map(|_| random_axiom(&mut seed)).collect();
        let tbox = internalize(&items).expect("supported axioms");
        for i in finite.iter().step_by(7) {
            let axioms_hold = items.iter().all(|item| satisfied(i, item));
            let tbox_holds = (0..i.size).all(|x| holds(i, &tbox, x));
            assert_eq!(axioms_hold, tbox_holds);
        }
    }
}

#[test]
fn every_class_with_a_small_model_of_the_axioms_is_satisfiable() {
    let finite = interpretations();
    let mut seed = 17;
    let mut with_model = 0;
    for _ in 0..150 {
        let items: Vec<AnnotatedAxiom> = (0..2).map(|_| random_axiom(&mut seed)).collect();
        let query = random_expression(&mut seed, 2);
        let answer = class_satisfiable(&items, &query).expect("supported input");
        let small_model = finite.iter().any(|i| {
            items.iter().all(|item| satisfied(i, item))
                && (0..i.size).any(|x| denotes(i, &query, x))
        });
        if small_model {
            assert!(answer, "a model exists, so the class must be satisfiable");
            with_model += 1;
        }
    }
    assert!(
        with_model > 30,
        "the sample must exercise satisfiable inputs"
    );
}

fn named(s: &[u8]) -> Individual {
    Individual::Named(NamedIndividual { iri: iri(s) })
}
fn asserted(c: ClassExpression, a: Individual) -> AnnotatedAxiom {
    axiom(Axiom::ClassAssertion(c, a))
}
fn related(r: &[u8], a: Individual, b: Individual) -> AnnotatedAxiom {
    axiom(Axiom::ObjectPropertyAssertion(property(r), a, b))
}

/// Machines with a faulty part need inspection; pump1 is a machine with the
/// faulty part motor1.
fn maintenance() -> Vec<AnnotatedAxiom> {
    vec![
        sub(
            and(class(b"Machine"), some(b"hasPart", class(b"FaultyPart"))),
            class(b"NeedsInspection"),
        ),
        asserted(class(b"Machine"), named(b"pump1")),
        related(b"hasPart", named(b"pump1"), named(b"motor1")),
        asserted(class(b"FaultyPart"), named(b"motor1")),
    ]
}
fn anon() -> Individual {
    Individual::Anonymous(AnonymousIndividual {
        scope: b"doc".to_vec(),
        label: b"x".to_vec(),
    })
}

#[test]
fn assertions_about_individuals() {
    let items = maintenance();
    let pump = NamedIndividual { iri: iri(b"pump1") };
    let motor = NamedIndividual {
        iri: iri(b"motor1"),
    };
    let other = NamedIndividual { iri: iri(b"other") };
    assert_eq!(consistent(&items), Some(true));
    assert_eq!(
        instance_of(&items, &pump, &class(b"NeedsInspection")),
        Some(true)
    );
    assert_eq!(
        instance_of(&items, &motor, &class(b"NeedsInspection")),
        Some(false)
    );
    // An individual without assertions is an instance only of what everything is.
    assert_eq!(instance_of(&items, &other, &class(b"Machine")), Some(false));
    assert_eq!(
        instance_of(&items, &other, &or(class(b"A"), not(class(b"A")))),
        Some(true)
    );
    // The assertions constrain classes too: some machine needs inspection.
    assert_eq!(
        class_satisfiable(&items, &and(class(b"Machine"), class(b"NeedsInspection"))),
        Some(true)
    );
    // A negative assertion of an asserted edge is inconsistent, also through
    // the inverse property.
    let mut denied = maintenance();
    denied.push(axiom(Axiom::NegativeObjectPropertyAssertion(
        property(b"hasPart"),
        named(b"pump1"),
        named(b"motor1"),
    )));
    assert_eq!(consistent(&denied), Some(false));
    let mut inverse = maintenance();
    inverse.push(axiom(Axiom::NegativeObjectPropertyAssertion(
        ObjectPropertyExpression::Inverse(ObjectProperty {
            iri: iri(b"hasPart"),
        }),
        named(b"motor1"),
        named(b"pump1"),
    )));
    assert_eq!(consistent(&inverse), Some(false));
    let mut unrelated = maintenance();
    unrelated.push(axiom(Axiom::NegativeObjectPropertyAssertion(
        property(b"hasPart"),
        named(b"motor1"),
        named(b"pump1"),
    )));
    assert_eq!(consistent(&unrelated), Some(true));
    // A class assertion that contradicts the TBox.
    let mut contradicted = maintenance();
    contradicted.push(asserted(not(class(b"NeedsInspection")), named(b"pump1")));
    assert_eq!(consistent(&contradicted), Some(false));
    // Anonymous individuals take part like named ones.
    let anonymous = vec![
        asserted(all(b"hasPart", class(b"FaultyPart")), anon()),
        related(b"hasPart", anon(), named(b"motor1")),
        asserted(not(class(b"FaultyPart")), named(b"motor1")),
    ];
    assert_eq!(consistent(&anonymous), Some(false));
    // A built-in object property in an assertion has no answer.
    let builtin = vec![related(TOP_OBJECT, named(b"a"), named(b"b"))];
    assert_eq!(consistent(&builtin), None);
}
