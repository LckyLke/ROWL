use rowl_kernel::concepts::{inverse, same_role, translate, Concept};
use rowl_kernel::hierarchy::{below, is_transitive, Inclusion, RoleHierarchy};
use rowl_kernel::model::*;

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
/// Render a concept with ¬ only on named classes and inverse roles marked ⁻.
fn show(c: &Concept) -> String {
    let name = |class: &Class| String::from_utf8_lossy(&class.iri.spelling).into_owned();
    match c {
        Concept::Top => "⊤".into(),
        Concept::Bottom => "⊥".into(),
        Concept::Atom(class) => name(class),
        Concept::NotAtom(class) => format!("¬{}", name(class)),
        Concept::And(a, b) => format!("({} ⊓ {})", show(a), show(b)),
        Concept::Or(a, b) => format!("({} ⊔ {})", show(a), show(b)),
        Concept::Exists(r, c) => format!("∃{}.{}", role_name(r), show(c)),
        Concept::Forall(r, c) => format!("∀{}.{}", role_name(r), show(c)),
    }
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
    let one_of = ClassExpression::ObjectHasSelf(named(b"hasPart"));
    assert!(translate(&one_of, true).is_none());
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
