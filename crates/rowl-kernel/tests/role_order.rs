use rowl_kernel::model::Iri;
use rowl_kernel::role_order::{close_order, OrderClosure};
use rowl_kernel::roles::{Edges, Role, Roles};

fn iri(name: &str) -> Iri {
    Iri {
        spelling: name.as_bytes().to_vec(),
    }
}
fn r(iri: &Iri, inverse: bool) -> Role<'_> {
    Role { iri, inverse }
}
fn nodes<'a>(values: &[(&'a Iri, bool)]) -> Roles<'a> {
    values
        .iter()
        .rev()
        .fold(Roles::Empty, |next, (iri, inverse)| Roles::Entry {
            role: r(iri, *inverse),
            next: Box::new(next),
        })
}
type BorrowedPair<'a> = ((&'a Iri, bool), (&'a Iri, bool));
type KeyPair = ((Vec<u8>, bool), (Vec<u8>, bool));
fn edges<'a>(values: &[BorrowedPair<'a>]) -> Edges<'a> {
    values
        .iter()
        .rev()
        .fold(Edges::Empty, |next, ((a, x), (b, y))| Edges::Entry {
            sub: r(a, *x),
            sup: r(b, *y),
            next: Box::new(next),
        })
}
fn values(mut source: &Edges<'_>) -> Vec<KeyPair> {
    let mut output = vec![];
    while let Edges::Entry { sub, sup, next } = source {
        output.push((
            (sub.iri.spelling.clone(), sub.inverse),
            (sup.iri.spelling.clone(), sup.inverse),
        ));
        source = next;
    }
    output
}
fn key(a: &str, x: bool, b: &str, y: bool) -> KeyPair {
    ((a.as_bytes().to_vec(), x), (b.as_bytes().to_vec(), y))
}

#[test]
fn closure_inverts_sources_of_derived_normal_targets_but_not_inverse_targets() {
    let a = iri("urn:a");
    let b = iri("urn:b");
    let c = iri("urn:c");
    let ns = nodes(&[
        (&a, false),
        (&a, true),
        (&b, false),
        (&b, true),
        (&c, false),
        (&c, true),
    ]);
    let seeds = edges(&[((&a, false), (&b, true)), ((&b, true), (&c, false))]);
    let OrderClosure::Complete(output) = close_order(ns, seeds) else {
        panic!("complete universe lost a pair")
    };
    let out = values(&output);
    assert!(out.contains(&key("urn:a", false, "urn:c", false)));
    assert!(out.contains(&key("urn:a", true, "urn:c", false)));
    assert!(out.contains(&key("urn:b", false, "urn:c", false)));
    assert!(!out.contains(&key("urn:a", true, "urn:b", true)));
    assert!(!out.contains(&key("urn:a", false, "urn:c", true)));
    assert_eq!(out.len(), 5);
}

#[test]
fn closure_keeps_cycles_as_evidence_and_deduplicates_every_pair() {
    let a = iri("urn:a");
    let b = iri("urn:b");
    let ns = nodes(&[
        (&a, false),
        (&a, true),
        (&a, false),
        (&b, false),
        (&b, true),
    ]);
    let seeds = edges(&[
        ((&a, false), (&b, false)),
        ((&b, false), (&a, false)),
        ((&a, false), (&b, false)),
    ]);
    let OrderClosure::Complete(output) = close_order(ns, seeds) else {
        panic!("cycle failed to terminate")
    };
    let out = values(&output);
    assert!(out.contains(&key("urn:a", false, "urn:a", false)));
    assert!(out.contains(&key("urn:b", true, "urn:b", false)));
    let unique: std::collections::HashSet<_> = out.iter().collect();
    assert_eq!(unique.len(), out.len());
    assert_eq!(out.len(), 8);
}

#[test]
fn missing_inverse_source_pair_is_reported_and_empty_seeds_do_not_invent_constraints() {
    let a = iri("urn:a");
    let b = iri("urn:b");
    let ns = nodes(&[(&a, false), (&b, false)]);
    let seeds = edges(&[((&a, false), (&b, false))]);
    let OrderClosure::MissingPair { sub, sup } = close_order(ns, seeds) else {
        panic!("missing inverse source ignored")
    };
    assert_eq!(sub.iri.spelling, b"urn:a");
    assert!(sub.inverse);
    assert_eq!(sup.iri.spelling, b"urn:b");
    assert!(!sup.inverse);
    let OrderClosure::Complete(output) = close_order(Roles::Empty, Edges::Empty) else {
        panic!("empty relation failed")
    };
    assert!(values(&output).is_empty());
}

fn property(name: &str, inverse: bool) -> rowl_kernel::model::ObjectPropertyExpression {
    let p = rowl_kernel::model::ObjectProperty { iri: iri(name) };
    if inverse {
        rowl_kernel::model::ObjectPropertyExpression::Inverse(p)
    } else {
        rowl_kernel::model::ObjectPropertyExpression::Property(p)
    }
}
fn axiom(body: rowl_kernel::model::Axiom) -> rowl_kernel::model::AnnotatedAxiom {
    rowl_kernel::model::AnnotatedAxiom {
        annotations: vec![],
        axiom: body,
    }
}
fn chain(terms: &[(&str, bool)], sup: (&str, bool)) -> rowl_kernel::model::AnnotatedAxiom {
    use rowl_kernel::model::*;
    axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(AtLeastTwo {
            first: property(terms[0].0, terms[0].1),
            second: property(terms[1].0, terms[1].1),
            rest: terms[2..]
                .iter()
                .map(|(name, inv)| property(name, *inv))
                .collect(),
        }),
        property(sup.0, sup.1),
    ))
}
fn sub(a: (&str, bool), b: (&str, bool)) -> rowl_kernel::model::AnnotatedAxiom {
    use rowl_kernel::model::*;
    axiom(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Single(property(a.0, a.1)),
        property(b.0, b.1),
    ))
}

#[test]
fn regularity_accepts_endpoint_recursion_transitivity_and_top_exemption() {
    use rowl_kernel::role_order::{check_regularity, RegularityCheck};
    let examples = [
        chain(
            &[("urn:child", false), ("urn:sibling", false)],
            ("urn:child", false),
        ),
        chain(
            &[("urn:sibling", false), ("urn:child", false)],
            ("urn:child", false),
        ),
        chain(
            &[("urn:child", false), ("urn:child", false)],
            ("urn:child", false),
        ),
        chain(
            &[
                ("urn:a", false),
                ("http://www.w3.org/2002/07/owl#topObjectProperty", false),
                ("urn:b", false),
            ],
            ("http://www.w3.org/2002/07/owl#topObjectProperty", false),
        ),
    ];
    for example in examples {
        let axioms = vec![example];
        assert!(matches!(
            check_regularity(&axioms),
            RegularityCheck::Regular(_)
        ));
    }
    assert!(matches!(
        check_regularity(&vec![]),
        RegularityCheck::Regular(_)
    ));
}

#[test]
fn regularity_rejects_middle_recursion_and_two_recursive_ends_of_a_long_chain() {
    use rowl_kernel::role_order::{check_regularity, RegularityCheck};
    for terms in [
        vec![("urn:a", false), ("urn:r", false), ("urn:b", false)],
        vec![("urn:r", false), ("urn:a", false), ("urn:r", false)],
        vec![("urn:r", false), ("urn:r", false), ("urn:r", false)],
    ] {
        let axioms = vec![chain(&terms, ("urn:r", false))];
        let RegularityCheck::HierarchyConflict { sub, sup } = check_regularity(&axioms) else {
            panic!("invalid recursion accepted")
        };
        assert_eq!(sub.iri.spelling, sup.iri.spelling);
        assert_eq!(sub.inverse, sup.inverse);
    }
}

#[test]
fn regularity_checks_global_cycles_reverse_hierarchies_and_inverse_sources() {
    use rowl_kernel::role_order::{check_regularity, RegularityCheck};
    let cycle = vec![
        chain(
            &[("urn:father", false), ("urn:brother", false)],
            ("urn:uncle", false),
        ),
        chain(
            &[("urn:child", false), ("urn:uncle", false)],
            ("urn:brother", false),
        ),
    ];
    assert!(matches!(
        check_regularity(&cycle),
        RegularityCheck::HierarchyConflict { .. }
    ));
    for reverse in [("urn:a", false), ("urn:a", true)] {
        let conflict = vec![
            chain(&[("urn:a", false), ("urn:b", false)], ("urn:r", false)),
            sub(("urn:r", false), reverse),
        ];
        assert!(matches!(
            check_regularity(&conflict),
            RegularityCheck::HierarchyConflict { .. }
        ));
    }
    let ordinary_cycle = vec![
        sub(("urn:a", false), ("urn:b", false)),
        sub(("urn:b", false), ("urn:a", false)),
    ];
    let RegularityCheck::Regular(order) = check_regularity(&ordinary_cycle) else {
        panic!("ordinary hierarchy cycles were incorrectly forbidden")
    };
    assert!(values(&order).is_empty());
}

#[test]
fn regularity_preserves_a_concrete_order_for_the_w3c_family_example() {
    use rowl_kernel::role_order::{check_regularity, RegularityCheck};
    let axioms = vec![
        chain(
            &[("urn:father", false), ("urn:brother", false)],
            ("urn:uncle", false),
        ),
        chain(
            &[("urn:uncle", false), ("urn:wife", false)],
            ("urn:auntInLaw", false),
        ),
    ];
    let RegularityCheck::Regular(order) = check_regularity(&axioms) else {
        panic!("acyclic chains rejected")
    };
    let out = values(&order);
    assert!(out.contains(&key("urn:father", false, "urn:uncle", false)));
    assert!(out.contains(&key("urn:father", true, "urn:auntInLaw", false)));
    assert!(out.contains(&key("urn:uncle", false, "urn:auntInLaw", false)));
    assert!(!out.contains(&key("urn:auntInLaw", false, "urn:father", false)));
}
