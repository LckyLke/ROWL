use rowl_kernel::model::*;
use rowl_kernel::probes::Natural;
use rowl_kernel::roles::*;

type Key = (Vec<u8>, bool);
type Edge = (Key, Key);
fn iri(value: &str) -> Iri {
    Iri {
        spelling: value.as_bytes().to_vec(),
    }
}
fn role(value: &str, inverse: bool) -> ObjectPropertyExpression {
    let p = ObjectProperty { iri: iri(value) };
    if inverse {
        ObjectPropertyExpression::Inverse(p)
    } else {
        ObjectPropertyExpression::Property(p)
    }
}
fn k(value: &str, inverse: bool) -> Key {
    (value.as_bytes().to_vec(), inverse)
}
fn keys(mut roles: &Roles<'_>) -> Vec<Key> {
    let mut output = vec![];
    while let Roles::Entry { role, next } = roles {
        output.push((role.iri.spelling.clone(), role.inverse));
        roles = next;
    }
    output
}
fn edges(mut edges: &Edges<'_>) -> Vec<Edge> {
    let mut output = vec![];
    while let Edges::Entry { sub, sup, next } = edges {
        output.push((
            (sub.iri.spelling.clone(), sub.inverse),
            (sup.iri.spelling.clone(), sup.inverse),
        ));
        edges = next;
    }
    output
}
fn item(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: vec![],
        axiom,
    }
}
fn class() -> ClassExpression {
    ClassExpression::Class(Class {
        iri: iri("urn:Machine"),
    })
}

#[test]
fn chain_results_seed_both_orientations_without_becoming_hierarchy_edges() {
    let chain = item(Axiom::SubObjectPropertyOf(
        SubObjectPropertyExpression::Chain(AtLeastTwo {
            first: role("urn:father", false),
            second: role("urn:brother", true),
            rest: vec![role("urn:sibling", false)],
        }),
        role("urn:uncle", true),
    ));
    let facts = axiom_facts(&chain);
    assert!(edges(&facts.edges).is_empty());
    assert!(keys(&facts.simple_required).is_empty());
    assert_eq!(
        keys(&facts.composite),
        vec![k("urn:uncle", true), k("urn:uncle", false)]
    );
    let Chains::Entry {
        chain: retained,
        sup,
        next,
    } = &facts.chains
    else {
        panic!("chain missing")
    };
    let Axiom::SubObjectPropertyOf(SubObjectPropertyExpression::Chain(original), original_sup) =
        &chain.axiom
    else {
        unreachable!()
    };
    assert!(std::ptr::eq(*retained, original));
    assert!(std::ptr::eq(*sup, original_sup));
    assert!(matches!(next.as_ref(), Chains::Empty));
    assert_eq!(
        keys(&facts.nodes),
        vec![
            k("urn:father", false),
            k("urn:father", true),
            k("urn:brother", false),
            k("urn:brother", true),
            k("urn:sibling", false),
            k("urn:sibling", true),
            k("urn:uncle", false),
            k("urn:uncle", true)
        ]
    );
}

#[test]
fn equivalence_inverse_symmetry_and_subproperties_keep_all_oriented_edges() {
    let eq = item(Axiom::EquivalentObjectProperties(AtLeastTwo {
        first: role("urn:a", false),
        second: role("urn:b", true),
        rest: vec![role("urn:c", false)],
    }));
    let pairs = edges(&axiom_facts(&eq).edges);
    assert_eq!(pairs.len(), 12);
    for (left, right) in [
        (k("urn:a", false), k("urn:b", true)),
        (k("urn:a", false), k("urn:c", false)),
        (k("urn:b", true), k("urn:c", false)),
    ] {
        assert!(pairs.contains(&(left.clone(), right.clone())));
        assert!(pairs.contains(&(right.clone(), left.clone())));
        assert!(pairs.contains(&((left.0.clone(), !left.1), (right.0.clone(), !right.1))));
        assert!(pairs.contains(&((right.0, !right.1), (left.0, !left.1))));
    }
    let closure = vec![
        item(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Single(role("urn:a", true)),
            role("urn:b", false),
        )),
        item(Axiom::InverseObjectProperties(
            role("urn:b", false),
            role("urn:c", true),
        )),
        item(Axiom::SymmetricObjectProperty(role("urn:c", false))),
        item(Axiom::TransitiveObjectProperty(role("urn:b", true))),
    ];
    let facts = collect_facts(&closure);
    assert_eq!(
        edges(&facts.edges),
        vec![
            (k("urn:a", true), k("urn:b", false)),
            (k("urn:a", false), k("urn:b", true)),
            (k("urn:b", false), k("urn:c", false)),
            (k("urn:b", true), k("urn:c", true)),
            (k("urn:c", false), k("urn:b", false)),
            (k("urn:c", true), k("urn:b", true)),
            (k("urn:c", false), k("urn:c", true)),
            (k("urn:c", true), k("urn:c", false)),
        ]
    );
    assert_eq!(
        keys(&facts.composite),
        vec![k("urn:b", true), k("urn:b", false)]
    );
}

#[test]
fn simple_requirements_cover_nested_fillers_but_do_not_restrict_every_role_use() {
    let nested = ClassExpression::ObjectMaxCardinality(
        Natural::Zero,
        role("urn:part", true),
        Some(Box::new(ClassExpression::ObjectSomeValuesFrom(
            role("urn:transitive", false),
            Box::new(ClassExpression::ObjectHasSelf(role("urn:inspect", false))),
        ))),
    );
    assert_eq!(
        keys(&class_requirements(&nested)),
        vec![k("urn:part", true), k("urn:inspect", false)]
    );
    let closure = vec![
        item(Axiom::HasKey(nested, vec![role("urn:key", false)], vec![])),
        item(Axiom::ReflexiveObjectProperty(role("urn:reflexive", false))),
        item(Axiom::ObjectPropertyDomain(
            role("urn:domain", false),
            class(),
        )),
        item(Axiom::FunctionalObjectProperty(role(
            "urn:functional",
            false,
        ))),
        item(Axiom::InverseFunctionalObjectProperty(role(
            "urn:inverseFunctional",
            true,
        ))),
        item(Axiom::IrreflexiveObjectProperty(role(
            "urn:irreflexive",
            false,
        ))),
        item(Axiom::AsymmetricObjectProperty(role(
            "urn:asymmetric",
            true,
        ))),
        item(Axiom::DisjointObjectProperties(AtLeastTwo {
            first: role("urn:d1", false),
            second: role("urn:d2", true),
            rest: vec![role("urn:d3", false)],
        })),
    ];
    let facts = collect_facts(&closure);
    assert_eq!(
        keys(&facts.simple_required),
        vec![
            k("urn:part", true),
            k("urn:inspect", false),
            k("urn:functional", false),
            k("urn:inverseFunctional", true),
            k("urn:irreflexive", false),
            k("urn:asymmetric", true),
            k("urn:d1", false),
            k("urn:d2", true),
            k("urn:d3", false)
        ]
    );
}

#[test]
fn builtin_seeds_are_typed_exact_and_duplicate_closure_occurrences_are_retained() {
    const TOP: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
    const BOTTOM: &str = "http://www.w3.org/2002/07/owl#bottomObjectProperty";
    let closure = vec![
        item(Axiom::Declaration(Entity::Class(Class { iri: iri(TOP) }))),
        item(Axiom::Declaration(Entity::ObjectProperty(ObjectProperty {
            iri: iri(TOP),
        }))),
        item(Axiom::Declaration(Entity::ObjectProperty(ObjectProperty {
            iri: iri(BOTTOM),
        }))),
        item(Axiom::Declaration(Entity::ObjectProperty(ObjectProperty {
            iri: iri(TOP),
        }))),
        item(Axiom::Declaration(Entity::ObjectProperty(ObjectProperty {
            iri: iri("http://www.w3.org/2002/07/owl#TopObjectProperty"),
        }))),
    ];
    let facts = collect_facts(&closure);
    assert_eq!(
        keys(&facts.composite),
        vec![k(TOP, false), k(BOTTOM, false), k(TOP, false)]
    );
    assert_eq!(keys(&facts.nodes).len(), 8);
    assert!(keys(&facts.simple_required).is_empty());
    assert!(edges(&facts.edges).is_empty());
    for name in [TOP, BOTTOM, "urn:p"] {
        let p = role(name, true);
        let oriented = expression_role(&p);
        let original = oriented.iri;
        let twice = inverse_role(inverse_role(oriented));
        assert!(twice.inverse);
        assert!(std::ptr::eq(twice.iri, original));
    }
    let empty_closure = vec![];
    let empty = collect_facts(&empty_closure);
    assert!(keys(&empty.nodes).is_empty());
}

#[test]
fn composite_closure_follows_cycles_and_inverses_without_restricting_chain_operands() {
    let axioms = vec![
        item(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Chain(AtLeastTwo {
                first: role("urn:hasFather", false),
                second: role("urn:hasBrother", false),
                rest: vec![],
            }),
            role("urn:hasUncle", false),
        )),
        item(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Single(role("urn:hasUncle", false)),
            role("urn:hasRelative", false),
        )),
        item(Axiom::EquivalentObjectProperties(AtLeastTwo {
            first: role("urn:hasRelative", false),
            second: role("urn:relatedTo", false),
            rest: vec![role("urn:hasRelative", false)],
        })),
    ];
    let facts = collect_facts(&axioms);
    let RoleClosure::Complete(closure) =
        non_simple_closure(facts.nodes, facts.composite, facts.edges)
    else {
        panic!("complete collector lost a reached role")
    };
    let reached = keys(&closure);
    assert_eq!(reached.len(), 6);
    for name in ["urn:hasUncle", "urn:hasRelative", "urn:relatedTo"] {
        for orientation in [false, true] {
            assert_eq!(
                reached
                    .iter()
                    .filter(|r| **r == k(name, orientation))
                    .count(),
                1
            );
        }
    }
    assert!(!reached.contains(&k("urn:hasFather", false)));
    assert!(!reached.contains(&k("urn:hasBrother", false)));
}

#[test]
fn role_identity_is_exact_bytes_and_orientation_and_missing_reached_nodes_are_errors() {
    let first = iri("urn:p");
    let separately_allocated = iri("urn:p");
    let different_case = iri("urn:P");
    let a = Role {
        iri: &first,
        inverse: false,
    };
    let b = Role {
        iri: &separately_allocated,
        inverse: false,
    };
    assert!(same_role(&a, &b));
    assert!(!same_role(
        &a,
        &Role {
            iri: &first,
            inverse: true
        }
    ));
    assert!(!same_role(
        &a,
        &Role {
            iri: &different_case,
            inverse: false
        }
    ));
    let root = Roles::Entry {
        role: a,
        next: Box::new(Roles::Empty),
    };
    let RoleClosure::MissingNode(missing) = non_simple_closure(Roles::Empty, root, Edges::Empty)
    else {
        panic!("missing root ignored")
    };
    assert!(std::ptr::eq(missing.iri, &first));
    let q = iri("urn:q");
    let r = iri("urn:r");
    let nodes = Roles::Entry {
        role: b,
        next: Box::new(Roles::Empty),
    };
    let root = Roles::Entry {
        role: Role {
            iri: &first,
            inverse: false,
        },
        next: Box::new(Roles::Empty),
    };
    let edges = Edges::Entry {
        sub: Role {
            iri: &q,
            inverse: false,
        },
        sup: Role {
            iri: &r,
            inverse: false,
        },
        next: Box::new(Edges::Empty),
    };
    let RoleClosure::Complete(closure) = non_simple_closure(nodes, root, edges) else {
        panic!("unreachable missing endpoints affected closure")
    };
    assert_eq!(keys(&closure), vec![k("urn:p", false)]);
}

#[test]
fn composite_closure_handles_empty_and_repeated_roots_with_first_missing_successor() {
    let RoleClosure::Complete(empty) = non_simple_closure(Roles::Empty, Roles::Empty, Edges::Empty)
    else {
        panic!("empty graph failed")
    };
    assert!(keys(&empty).is_empty());
    let p = iri("urn:p");
    let q = iri("urn:q");
    let nodes = Roles::Entry {
        role: Role {
            iri: &p,
            inverse: false,
        },
        next: Box::new(Roles::Empty),
    };
    let roots = Roles::Entry {
        role: Role {
            iri: &p,
            inverse: false,
        },
        next: Box::new(Roles::Entry {
            role: Role {
                iri: &p,
                inverse: false,
            },
            next: Box::new(Roles::Empty),
        }),
    };
    let edges = Edges::Entry {
        sub: Role {
            iri: &p,
            inverse: false,
        },
        sup: Role {
            iri: &q,
            inverse: false,
        },
        next: Box::new(Edges::Empty),
    };
    let RoleClosure::MissingNode(missing) = non_simple_closure(nodes, roots, edges) else {
        panic!("missing reachable successor ignored")
    };
    assert!(std::ptr::eq(missing.iri, &q));
}

#[test]
fn simplicity_checker_rejects_the_first_nested_restriction_after_transitive_propagation() {
    let axioms = vec![
        item(Axiom::TransitiveObjectProperty(role(
            "urn:hasAncestor",
            false,
        ))),
        item(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Single(role("urn:hasAncestor", false)),
            role("urn:hasRelative", false),
        )),
        item(Axiom::SubClassOf(
            class(),
            ClassExpression::ObjectSomeValuesFrom(
                role("urn:hasPart", false),
                Box::new(ClassExpression::ObjectMaxCardinality(
                    Natural::Zero,
                    role("urn:hasRelative", true),
                    Some(Box::new(class())),
                )),
            ),
        )),
        item(Axiom::FunctionalObjectProperty(role(
            "urn:hasAncestor",
            false,
        ))),
    ];
    let SimplicityCheck::ForbiddenRole(forbidden) = check_simplicity(&axioms) else {
        panic!("nested inverse zero-cardinality conflict missed")
    };
    assert_eq!(
        (forbidden.iri.spelling.clone(), forbidden.inverse),
        k("urn:hasRelative", true)
    );
    let Axiom::SubClassOf(_, ClassExpression::ObjectSomeValuesFrom(_, nested)) = &axioms[2].axiom
    else {
        unreachable!()
    };
    let ClassExpression::ObjectMaxCardinality(_, original, _) = nested.as_ref() else {
        unreachable!()
    };
    assert!(std::ptr::eq(forbidden.iri, expression_role(original).iri));
    let RoleClosure::Complete(non_simple) = classify_non_simple(&axioms) else {
        panic!("complete raw graph lost a node")
    };
    assert!(keys(&non_simple).contains(&k("urn:hasRelative", true)));
    assert!(!keys(&non_simple).contains(&k("urn:hasPart", false)));
}

#[test]
fn simplicity_checker_accepts_chain_operands_and_unrestricted_composite_uses() {
    let axioms = vec![
        item(Axiom::SubObjectPropertyOf(
            SubObjectPropertyExpression::Chain(AtLeastTwo {
                first: role("urn:hasFather", false),
                second: role("urn:hasBrother", false),
                rest: vec![],
            }),
            role("urn:hasUncle", false),
        )),
        item(Axiom::SubClassOf(
            class(),
            ClassExpression::ObjectHasSelf(role("urn:hasFather", false)),
        )),
        item(Axiom::SubClassOf(
            class(),
            ClassExpression::ObjectSomeValuesFrom(role("urn:hasUncle", false), Box::new(class())),
        )),
        item(Axiom::ReflexiveObjectProperty(role("urn:hasUncle", false))),
        item(Axiom::HasKey(
            class(),
            vec![role("urn:hasUncle", false)],
            vec![],
        )),
    ];
    assert!(matches!(
        check_simplicity(&axioms),
        SimplicityCheck::Allowed
    ));
    assert!(matches!(
        check_simplicity(&vec![]),
        SimplicityCheck::Allowed
    ));
    let mut invalid = axioms;
    invalid.push(item(Axiom::AsymmetricObjectProperty(role(
        "urn:hasUncle",
        false,
    ))));
    let SimplicityCheck::ForbiddenRole(forbidden) = check_simplicity(&invalid) else {
        panic!("asymmetric composite role accepted")
    };
    assert_eq!(forbidden.iri.spelling, b"urn:hasUncle");
}
