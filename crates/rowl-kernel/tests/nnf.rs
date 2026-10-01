use rowl_kernel::model::*;
use rowl_kernel::nnf::{nnf, NnfConcept};
use rowl_kernel::probes::Natural;

const THING: &[u8] = b"http://www.w3.org/2002/07/owl#Thing";
const NOTHING: &[u8] = b"http://www.w3.org/2002/07/owl#Nothing";

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn class(s: &[u8]) -> ClassExpression {
    ClassExpression::Class(Class { iri: iri(s) })
}
fn not(e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectComplementOf(Box::new(e))
}
fn members(mut all: Vec<ClassExpression>) -> Box<AtLeastTwo<ClassExpression>> {
    let rest = all.split_off(2);
    let second = all.pop().expect("two members");
    let first = all.pop().expect("two members");
    Box::new(AtLeastTwo {
        first,
        second,
        rest,
    })
}
fn and(all: Vec<ClassExpression>) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(members(all))
}
fn or(all: Vec<ClassExpression>) -> ClassExpression {
    ClassExpression::ObjectUnionOf(members(all))
}
fn role(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(s) })
}
fn some(p: &[u8], e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(role(p), Box::new(e))
}
fn all(p: &[u8], e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectAllValuesFrom(role(p), Box::new(e))
}
/// Render a concept with ¬ only on named classes, ⊓/⊔ fully parenthesized.
fn show(c: &NnfConcept) -> String {
    let name = |class: &Class| String::from_utf8_lossy(&class.iri.spelling).into_owned();
    match c {
        NnfConcept::Top => "⊤".into(),
        NnfConcept::Bottom => "⊥".into(),
        NnfConcept::Atom(class) => name(class),
        NnfConcept::NotAtom(class) => format!("¬{}", name(class)),
        NnfConcept::And(a, b) => format!("({} ⊓ {})", show(a), show(b)),
        NnfConcept::Or(a, b) => format!("({} ⊔ {})", show(a), show(b)),
        NnfConcept::Exists(p, c) => {
            format!("∃{}.{}", String::from_utf8_lossy(&p.iri.spelling), show(c))
        }
        NnfConcept::Forall(p, c) => {
            format!("∀{}.{}", String::from_utf8_lossy(&p.iri.spelling), show(c))
        }
    }
}
fn translated(e: &ClassExpression, positive: bool) -> String {
    show(&nnf(e, positive).expect("inside the ALC fragment"))
}

#[test]
fn negation_moves_inward_by_de_morgan_and_quantifier_duality() {
    let e = not(and(vec![
        class(b"Machine"),
        some(b"hasPart", class(b"Faulty")),
    ]));
    assert_eq!(translated(&e, true), "(¬Machine ⊔ ∀hasPart.¬Faulty)");
    assert_eq!(translated(&e, false), "(Machine ⊓ ∃hasPart.Faulty)");
    let e = not(all(b"hasPart", or(vec![class(b"A"), not(class(b"B"))])));
    assert_eq!(translated(&e, true), "∃hasPart.(¬A ⊓ B)");
    assert_eq!(translated(&not(not(class(b"A"))), true), "A");
    assert_eq!(translated(&not(not(class(b"A"))), false), "¬A");
}

#[test]
fn every_member_is_joined_left_nested_in_source_order() {
    let three = || vec![class(b"A"), class(b"B"), some(b"R", class(b"C"))];
    assert_eq!(translated(&and(three()), true), "((A ⊓ B) ⊓ ∃R.C)");
    assert_eq!(translated(&and(three()), false), "((¬A ⊔ ¬B) ⊔ ∀R.¬C)");
    assert_eq!(translated(&or(three()), true), "((A ⊔ B) ⊔ ∃R.C)");
    assert_eq!(translated(&or(three()), false), "((¬A ⊓ ¬B) ⊓ ∀R.¬C)");
    let four = or(vec![class(b"A"), class(b"B"), class(b"C"), class(b"D")]);
    assert_eq!(translated(&four, true), "(((A ⊔ B) ⊔ C) ⊔ D)");
}

#[test]
fn builtin_thing_and_nothing_become_top_and_bottom_exactly() {
    assert_eq!(translated(&class(THING), true), "⊤");
    assert_eq!(translated(&class(THING), false), "⊥");
    assert_eq!(translated(&class(NOTHING), true), "⊥");
    assert_eq!(translated(&class(NOTHING), false), "⊤");
    assert_eq!(translated(&some(b"R", not(class(NOTHING))), true), "∃R.⊤");
    // Only the exact built-in spellings qualify.
    assert_eq!(
        translated(&class(b"http://www.w3.org/2002/07/owl#thing"), false),
        "¬http://www.w3.org/2002/07/owl#thing"
    );
    assert_eq!(
        translated(&class(b"http://www.w3.org/2002/07/owl#Nothing "), true),
        "http://www.w3.org/2002/07/owl#Nothing "
    );
}

#[test]
fn class_and_property_spellings_are_copied_exactly() {
    let spelling = "urn:设备:Pump%20A".as_bytes();
    let e = some(spelling, class(spelling));
    match nnf(&e, true).expect("fragment") {
        NnfConcept::Exists(p, c) => {
            assert_eq!(p.iri.spelling, spelling);
            assert!(matches!(*c, NnfConcept::Atom(ref a) if a.iri.spelling == spelling));
        }
        _ => panic!("expected an existential restriction"),
    }
}

#[test]
fn expressions_outside_the_alc_fragment_have_no_translation() {
    let outside = || {
        vec![
            ClassExpression::ObjectSomeValuesFrom(
                ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(b"R") }),
                Box::new(class(b"A")),
            ),
            ClassExpression::ObjectOneOf(NonEmpty {
                first: Individual::Named(NamedIndividual { iri: iri(b"a") }),
                rest: Vec::new(),
            }),
            ClassExpression::ObjectHasSelf(ObjectPropertyExpression::Property(ObjectProperty {
                iri: iri(b"R"),
            })),
            ClassExpression::ObjectMinCardinality(
                Natural::Succ(Box::new(Natural::Zero)),
                ObjectPropertyExpression::Property(ObjectProperty { iri: iri(b"R") }),
                None,
            ),
            ClassExpression::DataSomeValuesFrom(
                DataProperty { iri: iri(b"d") },
                DataRange::Datatype(Datatype { iri: iri(b"t") }),
            ),
        ]
    };
    for positive in [true, false] {
        for e in outside() {
            assert!(nnf(&e, positive).is_none());
        }
        // One unsupported member anywhere rejects the whole expression.
        for e in outside() {
            let nested = not(and(vec![class(b"A"), all(b"S", or(vec![class(b"B"), e]))]));
            assert!(nnf(&nested, positive).is_none());
        }
    }
    assert!(nnf(&all(b"R", class(b"A")), true).is_some());
}

/// A finite interpretation over the domain {0, 1} with classes A and B and role R.
struct Finite {
    a: [bool; 2],
    b: [bool; 2],
    r: [[bool; 2]; 2],
}
fn class_holds(i: &Finite, spelling: &[u8], x: usize) -> bool {
    match spelling {
        b"A" => i.a[x],
        b"B" => i.b[x],
        THING => true,
        NOTHING => false,
        _ => panic!("unknown test class"),
    }
}
fn role_holds(i: &Finite, spelling: &[u8], x: usize, y: usize) -> bool {
    assert_eq!(spelling, b"R");
    i.r[x][y]
}
fn each(m: &AtLeastTwo<ClassExpression>) -> Vec<&ClassExpression> {
    let mut all = vec![&m.first, &m.second];
    all.extend(m.rest.iter());
    all
}
/// The OWL Direct Semantics for the ALC constructors, written independently.
fn denotes(i: &Finite, e: &ClassExpression, x: usize) -> bool {
    match e {
        ClassExpression::Class(c) => class_holds(i, &c.iri.spelling, x),
        ClassExpression::ObjectIntersectionOf(m) => each(m).into_iter().all(|e| denotes(i, e, x)),
        ClassExpression::ObjectUnionOf(m) => each(m).into_iter().any(|e| denotes(i, e, x)),
        ClassExpression::ObjectComplementOf(e) => !denotes(i, e, x),
        ClassExpression::ObjectSomeValuesFrom(ObjectPropertyExpression::Property(p), f) => {
            (0..2).any(|y| role_holds(i, &p.iri.spelling, x, y) && denotes(i, f, y))
        }
        ClassExpression::ObjectAllValuesFrom(ObjectPropertyExpression::Property(p), f) => {
            (0..2).all(|y| !role_holds(i, &p.iri.spelling, x, y) || denotes(i, f, y))
        }
        _ => panic!("outside the test fragment"),
    }
}
fn concept_holds(i: &Finite, c: &NnfConcept, x: usize) -> bool {
    match c {
        NnfConcept::Top => true,
        NnfConcept::Bottom => false,
        NnfConcept::Atom(a) => class_holds(i, &a.iri.spelling, x),
        NnfConcept::NotAtom(a) => !class_holds(i, &a.iri.spelling, x),
        NnfConcept::And(a, b) => concept_holds(i, a, x) && concept_holds(i, b, x),
        NnfConcept::Or(a, b) => concept_holds(i, a, x) || concept_holds(i, b, x),
        NnfConcept::Exists(p, c) => {
            (0..2).any(|y| role_holds(i, &p.iri.spelling, x, y) && concept_holds(i, c, y))
        }
        NnfConcept::Forall(p, c) => {
            (0..2).all(|y| !role_holds(i, &p.iri.spelling, x, y) || concept_holds(i, c, y))
        }
    }
}

#[test]
fn translation_agrees_with_owl_semantics_on_every_small_interpretation() {
    let expressions = || {
        vec![
            class(b"A"),
            class(THING),
            not(class(NOTHING)),
            and(vec![class(b"A"), not(class(b"B")), class(THING)]),
            or(vec![class(b"A"), class(NOTHING), some(b"R", class(b"B"))]),
            not(and(vec![class(b"A"), some(b"R", class(b"B"))])),
            not(all(
                b"R",
                or(vec![class(b"A"), some(b"R", not(class(b"B")))]),
            )),
            some(b"R", all(b"R", class(NOTHING))),
            not(not(some(b"R", and(vec![class(b"A"), class(b"B")])))),
            or(vec![
                all(b"R", class(b"A")),
                not(some(b"R", class(b"A"))),
                and(vec![class(b"B"), not(class(b"B"))]),
                not(or(vec![class(b"A"), all(b"R", not(class(THING)))])),
            ]),
        ]
    };
    let mut checked = 0;
    for code in 0..256u32 {
        let bit = |n: u32| code >> n & 1 == 1;
        let i = Finite {
            a: [bit(0), bit(1)],
            b: [bit(2), bit(3)],
            r: [[bit(4), bit(5)], [bit(6), bit(7)]],
        };
        for e in expressions() {
            for positive in [true, false] {
                let c = nnf(&e, positive).expect("inside the ALC fragment");
                for x in 0..2 {
                    assert_eq!(
                        concept_holds(&i, &c, x),
                        denotes(&i, &e, x) == positive,
                        "interpretation {code}, element {x}, polarity {positive}"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 256 * 10 * 2 * 2);
}
