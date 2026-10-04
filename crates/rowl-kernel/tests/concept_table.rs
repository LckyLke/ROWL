use rowl_kernel::concept_table::{close, intern, universal_from, Entry};
use rowl_kernel::concepts::Concept;
use rowl_kernel::hierarchy::{Inclusion, RoleHierarchy};
use rowl_kernel::model::*;

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn atom(s: &[u8]) -> Concept {
    Concept::Atom(Class { iri: iri(s) })
}
fn named(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(ObjectProperty { iri: iri(s) })
}
fn inverted(s: &[u8]) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Inverse(ObjectProperty { iri: iri(s) })
}
fn some(r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::Exists(r, Box::new(c))
}
fn only(r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::Forall(r, Box::new(c))
}
fn and(a: Concept, b: Concept) -> Concept {
    Concept::And(Box::new(a), Box::new(b))
}
/// Render entry `index` with its parts resolved, inverse roles marked ⁻.
fn show(entries: &[Entry], index: usize) -> String {
    let role = |r: &ObjectPropertyExpression| match r {
        ObjectPropertyExpression::Property(p) => {
            String::from_utf8_lossy(&p.iri.spelling).into_owned()
        }
        ObjectPropertyExpression::Inverse(p) => {
            format!("{}⁻", String::from_utf8_lossy(&p.iri.spelling))
        }
    };
    match &entries[index] {
        Entry::Top => "⊤".into(),
        Entry::Bottom => "⊥".into(),
        Entry::Atom(c) => String::from_utf8_lossy(&c.iri.spelling).into_owned(),
        Entry::NotAtom(c) => format!("¬{}", String::from_utf8_lossy(&c.iri.spelling)),
        Entry::One(_) => "{a}".into(),
        Entry::NotOne(_) => "¬{a}".into(),
        Entry::HasSelf(r) => format!("∃{}.Self", role(r)),
        Entry::NotSelf(r) => format!("¬∃{}.Self", role(r)),
        Entry::And(a, b) => format!("({} ⊓ {})", show(entries, *a), show(entries, *b)),
        Entry::Or(a, b) => format!("({} ⊔ {})", show(entries, *a), show(entries, *b)),
        Entry::Exists(r, c) => format!("∃{}.{}", role(r), show(entries, *c)),
        Entry::Forall(r, c) => format!("∀{}.{}", role(r), show(entries, *c)),
        Entry::AtLeast(n, r, c) => format!("≥{n}{}.{}", role(r), show(entries, *c)),
        Entry::AtMost(n, r, c, d) => format!(
            "≤{n}{}.{} (complement {})",
            role(r),
            show(entries, *c),
            show(entries, *d)
        ),
    }
}

#[test]
fn equal_subconcepts_share_one_entry() {
    let part = some(named(b"hasPart"), atom(b"Faulty"));
    let concept = and(part, some(named(b"hasPart"), atom(b"Faulty")));
    let (entries, index) = intern(Vec::new(), &concept).expect("room");
    assert_eq!(show(&entries, index), "(∃hasPart.Faulty ⊓ ∃hasPart.Faulty)");
    // Faulty, ∃hasPart.Faulty and the conjunction: three entries, parts first.
    assert_eq!(entries.len(), 3);
    match entries[index] {
        Entry::And(a, b) => assert_eq!(a, b),
        _ => panic!("the conjunction is the last entry"),
    }
    // Interning again changes nothing.
    let again = and(
        some(named(b"hasPart"), atom(b"Faulty")),
        some(named(b"hasPart"), atom(b"Faulty")),
    );
    let (entries, second) = intern(entries, &again).expect("room");
    assert_eq!((entries.len(), second), (3, index));
}

#[test]
fn closing_adds_the_restrictions_of_transitive_roles() {
    let roles = RoleHierarchy {
        inclusions: vec![
            Inclusion {
                sub: named(b"hasPart"),
                sup: named(b"contains"),
            },
            Inclusion {
                sub: inverted(b"hasPart"),
                sup: inverted(b"contains"),
            },
        ],
        transitive: vec![named(b"hasPart"), inverted(b"hasPart")],
        disjoint: Vec::new(),
    };
    let (entries, _) = intern(Vec::new(), &only(named(b"contains"), atom(b"Safe"))).expect("room");
    let (entries, _) = intern(entries, &only(inverted(b"contains"), atom(b"Used"))).expect("room");
    let before = entries.len();
    let entries = close(entries, &roles).expect("room");
    // ∀hasPart.Safe and ∀hasPart⁻.Used are added, nothing else.
    assert_eq!(entries.len(), before + 2);
    let safe = universal_from(&entries, &named(b"hasPart"), 0, 0);
    assert!(safe < entries.len());
    assert_eq!(show(&entries, safe), "∀hasPart.Safe");
    let used = universal_from(&entries, &inverted(b"hasPart"), 2, 0);
    assert_eq!(show(&entries, used), "∀hasPart⁻.Used");
    // A role that is not transitive adds nothing.
    let missing = universal_from(&entries, &named(b"contains"), 2, 0);
    assert_eq!(missing, entries.len());
}

#[test]
fn maximum_restrictions_record_the_complement_of_their_filler() {
    let filler = and(atom(b"Valve"), some(named(b"hasPart"), atom(b"Seal")));
    let concept = Concept::AtMost(1, inverted(b"partOf"), Box::new(filler));
    let (entries, index) = intern(Vec::new(), &concept).expect("room");
    assert_eq!(
        show(&entries, index),
        "≤1partOf⁻.(Valve ⊓ ∃hasPart.Seal) (complement (¬Valve ⊔ ∀hasPart.¬Seal))"
    );
    let at_least = Concept::AtLeast(2, named(b"hasPart"), Box::new(atom(b"Valve")));
    let (entries, other) = intern(entries, &at_least).expect("room");
    assert_eq!(show(&entries, other), "≥2hasPart.Valve");
    // Valve was interned with the maximum restriction and is shared.
    let (entries, valve) = intern(entries, &atom(b"Valve")).expect("room");
    let count = entries.len();
    let (entries, again) = intern(entries, &atom(b"Valve")).expect("room");
    assert_eq!((entries.len(), again), (count, valve));
}
