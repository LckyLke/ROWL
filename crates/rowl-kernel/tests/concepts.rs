use rowl_kernel::concepts::{inverse, negate, same_role, translate, Concept};
use rowl_kernel::hierarchy::{below, is_transitive, Inclusion, RoleHierarchy};
use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;

const THING: &[u8] = b"http://www.w3.org/2002/07/owl#Thing";

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
fn property(s: &[u8]) -> ObjectProperty {
    ObjectProperty { iri: iri(s) }
}
fn named(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(property(s))
}
fn inverted(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Inverse(property(s))
}
fn some(r: ObjectPropertyExpression, e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectSomeValuesFrom(r, Box::new(e))
}
fn all(r: ObjectPropertyExpression, e: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectAllValuesFrom(r, Box::new(e))
}
fn and(first: ClassExpression, second: ClassExpression) -> ClassExpression {
    ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
        first,
        second,
        rest: Vec::new(),
    }))
}
fn role_name(r: &ObjectPropertyExpression) -> String {
    match r {
        ObjectPropertyExpression::Property(p) => String::from_utf8_lossy(&p.iri.spelling).into(),
        ObjectPropertyExpression::Inverse(p) => {
            format!("{}⁻", String::from_utf8_lossy(&p.iri.spelling))
        }
    }
}
fn individual_name(individual: &Individual) -> String {
    match individual {
        Individual::Named(named) => String::from_utf8_lossy(&named.iri.spelling).into(),
        Individual::Anonymous(node) => format!("_:{}", String::from_utf8_lossy(&node.label)),
    }
}
/// Render a concept with ¬ only on named classes and nominals and inverse roles
/// marked ⁻.
fn show(c: &Concept) -> String {
    let name = |class: &Class| String::from_utf8_lossy(&class.iri.spelling).into_owned();
    match c {
        Concept::Top => "⊤".into(),
        Concept::Bottom => "⊥".into(),
        Concept::Atom(class) => name(class),
        Concept::NotAtom(class) => format!("¬{}", name(class)),
        Concept::One(individual) => format!("{{{}}}", individual_name(individual)),
        Concept::NotOne(individual) => format!("¬{{{}}}", individual_name(individual)),
        Concept::HasSelf(r) => format!("∃{}.Self", role_name(r)),
        Concept::NotSelf(r) => format!("¬∃{}.Self", role_name(r)),
        Concept::And(a, b) => format!("({} ⊓ {})", show(a), show(b)),
        Concept::Or(a, b) => format!("({} ⊔ {})", show(a), show(b)),
        Concept::Exists(r, c) => format!("∃{}.{}", role_name(r), show(c)),
        Concept::Forall(r, c) => format!("∀{}.{}", role_name(r), show(c)),
        Concept::AtLeast(n, r, c) => format!("≥{n}{}.{}", role_name(r), show(c)),
        Concept::AtMost(n, r, c) => format!("≤{n}{}.{}", role_name(r), show(c)),
    }
}
fn natural(n: usize) -> Natural {
    (0..n).fold(Natural::Zero, |previous, _| {
        Natural::Succ(Box::new(previous))
    })
}
fn translated(e: &ClassExpression, positive: bool) -> String {
    show(&translate(e, positive).expect("inside the ALCI fragment"))
}

#[test]
fn inverse_restrictions_are_translated_with_their_orientation() {
    let partof = some(inverted(b"hasPart"), class(b"Pump"));
    assert_eq!(translated(&partof, true), "∃hasPart⁻.Pump");
    // De Morgan swaps the quantifier and keeps the inverse role.
    assert_eq!(translated(&partof, false), "∀hasPart⁻.¬Pump");
    let nested = not(and(
        all(named(b"hasPart"), class(b"Part")),
        some(inverted(b"contains"), class(THING)),
    ));
    assert_eq!(translated(&nested, true), "(∃hasPart.¬Part ⊔ ∀contains⁻.⊥)");
    // Expressions outside ALCI have no translation.
    let reflexive = ClassExpression::ObjectHasSelf(named(b"hasPart"));
    assert_eq!(translated(&reflexive, true), "∃hasPart.Self");
    // The complement of a self restriction excludes the loop.
    assert_eq!(
        translated(
            &not(ClassExpression::ObjectHasSelf(inverted(b"hasPart"))),
            true
        ),
        "¬∃hasPart⁻.Self"
    );
}

#[test]
fn enumerations_and_value_restrictions_become_nominals() {
    let individual = |s: &[u8]| Individual::Named(NamedIndividual { iri: iri(s) });
    let enumeration = ClassExpression::ObjectOneOf(NonEmpty {
        first: individual(b"red"),
        rest: vec![individual(b"green"), individual(b"blue")],
    });
    assert_eq!(
        translated(&enumeration, true),
        "(({red} ⊔ {green}) ⊔ {blue})"
    );
    // The complement of an enumeration excludes each of its individuals.
    assert_eq!(
        translated(&enumeration, false),
        "((¬{red} ⊓ ¬{green}) ⊓ ¬{blue})"
    );
    let single = ClassExpression::ObjectOneOf(NonEmpty {
        first: individual(b"red"),
        rest: Vec::new(),
    });
    assert_eq!(translated(&single, true), "{red}");
    let value = ClassExpression::ObjectHasValue(inverted(b"hasPart"), individual(b"pump1"));
    assert_eq!(translated(&value, true), "∃hasPart⁻.{pump1}");
    assert_eq!(translated(&value, false), "∀hasPart⁻.¬{pump1}");
    let complemented = negate(&translate(&value, true).expect("translated")).expect("negated");
    assert_eq!(show(&complemented), "∀hasPart⁻.¬{pump1}");
}

#[test]
fn roles_compare_by_orientation_and_spelling() {
    assert!(same_role(&named(b"hasPart"), &named(b"hasPart")));
    assert!(!same_role(&named(b"hasPart"), &inverted(b"hasPart")));
    assert!(same_role(
        &inverse(&named(b"hasPart")),
        &inverted(b"hasPart")
    ));
    assert!(same_role(&inverse(&inverted(b"partOf")), &named(b"partOf")));
}

#[test]
fn hierarchies_list_inclusions_and_transitive_roles() {
    let roles = RoleHierarchy {
        inclusions: vec![
            Inclusion {
                sub: named(b"hasComponent"),
                sup: named(b"hasPart"),
            },
            Inclusion {
                sub: inverted(b"hasComponent"),
                sup: inverted(b"hasPart"),
            },
        ],
        transitive: vec![named(b"hasPart"), inverted(b"hasPart")],
    };
    assert!(below(&roles, &named(b"hasComponent"), &named(b"hasPart")));
    assert!(below(
        &roles,
        &inverted(b"hasComponent"),
        &inverted(b"hasPart")
    ));
    assert!(below(&roles, &named(b"partOf"), &named(b"partOf")));
    assert!(!below(&roles, &named(b"hasPart"), &named(b"hasComponent")));
    assert!(!below(
        &roles,
        &named(b"hasComponent"),
        &inverted(b"hasPart")
    ));
    assert!(is_transitive(&roles, &inverted(b"hasPart")));
    assert!(!is_transitive(&roles, &named(b"hasComponent")));
}

#[test]
fn cardinality_restrictions_are_translated_with_their_bounds() {
    let at_least = |n, filler: Option<ClassExpression>| {
        ClassExpression::ObjectMinCardinality(natural(n), named(b"hasPart"), filler.map(Box::new))
    };
    let at_most = |n, filler: Option<ClassExpression>| {
        ClassExpression::ObjectMaxCardinality(natural(n), inverted(b"partOf"), filler.map(Box::new))
    };
    let exactly = |n| {
        ClassExpression::ObjectExactCardinality(
            natural(n),
            named(b"hasPart"),
            Some(Box::new(class(b"Valve"))),
        )
    };
    assert_eq!(
        translated(&at_least(2, Some(class(b"Valve"))), true),
        "≥2hasPart.Valve"
    );
    // The complement of ≥n is ≤(n-1), and of ≥0 nothing at all.
    assert_eq!(
        translated(&at_least(2, Some(class(b"Valve"))), false),
        "≤1hasPart.Valve"
    );
    assert_eq!(translated(&at_least(0, None), false), "⊥");
    // A missing filler is owl:Thing; the complement of ≤n is ≥(n+1).
    assert_eq!(translated(&at_most(1, None), true), "≤1partOf⁻.⊤");
    assert_eq!(translated(&at_most(1, None), false), "≥2partOf⁻.⊤");
    assert_eq!(
        translated(&exactly(1), true),
        "(≥1hasPart.Valve ⊓ ≤1hasPart.Valve)"
    );
    assert_eq!(
        translated(&exactly(1), false),
        "(≤0hasPart.Valve ⊔ ≥2hasPart.Valve)"
    );
    // The filler keeps its polarity under the complement of the restriction.
    let nested = not(at_most(0, Some(not(class(b"Pump")))));
    assert_eq!(translated(&nested, true), "≥1partOf⁻.¬Pump");
    // A filler outside the fragment has no translation.
    let unsupported = at_least(
        1,
        Some(ClassExpression::DataMinCardinality(
            natural(1),
            DataProperty {
                iri: iri(b"weight"),
            },
            None,
        )),
    );
    assert!(translate(&unsupported, true).is_none());
}

#[test]
fn complements_are_in_negation_normal_form() {
    let concept = translate(
        &and(
            some(named(b"hasPart"), class(b"Valve")),
            ClassExpression::ObjectMaxCardinality(natural(2), named(b"hasPart"), None),
        ),
        true,
    )
    .expect("inside the fragment");
    let complement = negate(&concept).expect("bounds below usize::MAX");
    assert_eq!(show(&complement), "(∀hasPart.¬Valve ⊔ ≥3hasPart.⊤)");
    assert_eq!(
        show(&negate(&complement).expect("bounds below usize::MAX")),
        "(∃hasPart.Valve ⊓ ≤2hasPart.⊤)"
    );
    let at_least = Concept::AtLeast(0, named(b"hasPart"), Box::new(Concept::Top));
    assert_eq!(show(&negate(&at_least).expect("no bound")), "⊥");
    let unbounded = Concept::AtMost(usize::MAX, named(b"hasPart"), Box::new(Concept::Top));
    assert!(negate(&unbounded).is_none());
}
