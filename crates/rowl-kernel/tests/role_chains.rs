use rowl_kernel::completion::{Definition, Fact, Link};
use rowl_kernel::concepts::Concept;
use rowl_kernel::hierarchy::{Disjoint, Inclusion, RoleHierarchy};
use rowl_kernel::model::*;
use rowl_kernel::role_chains::{satisfiable, Chain};

fn iri(s: &[u8]) -> Iri {
    Iri {
        spelling: s.to_vec(),
    }
}
fn class(s: &[u8]) -> Class {
    Class { iri: iri(s) }
}
fn atom(s: &[u8]) -> Concept {
    Concept::Atom(class(s))
}
fn no(s: &[u8]) -> Concept {
    Concept::NotAtom(class(s))
}
fn and(a: Concept, b: Concept) -> Concept {
    Concept::And(Box::new(a), Box::new(b))
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
fn all(r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::Forall(r, Box::new(c))
}
fn at_most(n: usize, r: ObjectPropertyExpression, c: Concept) -> Concept {
    Concept::AtMost(n, r, Box::new(c))
}
fn chain(roles: Vec<ObjectPropertyExpression>, sup: ObjectPropertyExpression) -> Chain {
    Chain { roles, sup }
}
fn none() -> RoleHierarchy {
    RoleHierarchy {
        inclusions: Vec::new(),
        transitive: Vec::new(),
        disjoint: Vec::new(),
    }
}
/// A hierarchy with `sub ⊑ sup` and its inverse.
fn included(sub: &[u8], sup: &[u8]) -> RoleHierarchy {
    RoleHierarchy {
        inclusions: vec![
            Inclusion {
                sub: named(sub),
                sup: named(sup),
            },
            Inclusion {
                sub: inverted(sub),
                sup: inverted(sup),
            },
        ],
        transitive: Vec::new(),
        disjoint: Vec::new(),
    }
}
/// Satisfiability of one concept under role axioms and chains.
fn concept_sat(c: Concept, roles: &RoleHierarchy, chains: &Vec<Chain>) -> Option<bool> {
    satisfiable(
        1,
        &vec![Fact {
            node: 0,
            concept: c,
        }],
        &Vec::new(),
        &Vec::new(),
        &Concept::Top,
        &Vec::new(),
        roles,
        chains,
    )
}
fn with_stack(body: fn()) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(body)
        .expect("a test thread")
        .join()
        .expect("the test body passes");
}
fn uncle() -> Vec<Chain> {
    vec![chain(
        vec![named(b"parent"), named(b"brother")],
        named(b"uncle"),
    )]
}

#[test]
fn a_chain_relates_along_its_roles() {
    with_stack(|| {
        let chains = uncle();
        let path = some(named(b"parent"), some(named(b"brother"), atom(b"B")));
        assert_eq!(
            concept_sat(and(path, all(named(b"uncle"), no(b"B"))), &none(), &chains),
            Some(false)
        );
        let path = some(named(b"parent"), some(named(b"brother"), atom(b"B")));
        assert_eq!(concept_sat(path, &none(), &chains), Some(true));
        let short = some(named(b"parent"), atom(b"B"));
        assert_eq!(
            concept_sat(and(short, all(named(b"uncle"), no(b"B"))), &none(), &chains),
            Some(true)
        );
        // Without the chain the restriction says nothing about the path.
        let path = some(named(b"parent"), some(named(b"brother"), atom(b"B")));
        assert_eq!(
            concept_sat(
                and(path, all(named(b"uncle"), no(b"B"))),
                &none(),
                &Vec::new()
            ),
            Some(true)
        );
    });
}

#[test]
fn a_chain_relates_inverse_paths() {
    with_stack(|| {
        let chains = uncle();
        let back = some(inverted(b"brother"), some(inverted(b"parent"), atom(b"A")));
        assert_eq!(
            concept_sat(
                and(back, all(inverted(b"uncle"), no(b"A"))),
                &none(),
                &chains
            ),
            Some(false)
        );
    });
}

#[test]
fn recursive_chains_relate_long_paths() {
    with_stack(|| {
        // located ∘ part ⊑ located: the first role is the chain's role.
        let left = vec![chain(
            vec![named(b"located"), named(b"part")],
            named(b"located"),
        )];
        let path = some(
            named(b"located"),
            some(named(b"part"), some(named(b"part"), atom(b"B"))),
        );
        assert_eq!(
            concept_sat(and(path, all(named(b"located"), no(b"B"))), &none(), &left),
            Some(false)
        );
        // part ∘ located ⊑ located: the last role is the chain's role.
        let right = vec![chain(
            vec![named(b"part"), named(b"located")],
            named(b"located"),
        )];
        let path = some(
            named(b"part"),
            some(named(b"part"), some(named(b"located"), atom(b"B"))),
        );
        assert_eq!(
            concept_sat(and(path, all(named(b"located"), no(b"B"))), &none(), &right),
            Some(false)
        );
        // The paths must end along the chain's role.
        let path = some(
            named(b"part"),
            some(named(b"part"), some(named(b"part"), atom(b"B"))),
        );
        assert_eq!(
            concept_sat(and(path, all(named(b"located"), no(b"B"))), &none(), &right),
            Some(true)
        );
        // r ∘ r ⊑ r makes r transitive.
        let twin = vec![chain(vec![named(b"r"), named(b"r")], named(b"r"))];
        let path = some(
            named(b"r"),
            some(named(b"r"), some(named(b"r"), atom(b"B"))),
        );
        assert_eq!(
            concept_sat(and(path, all(named(b"r"), no(b"B"))), &none(), &twin),
            Some(false)
        );
    });
}

#[test]
fn chains_compose_with_inclusions() {
    with_stack(|| {
        // p ∘ q ⊑ s and s ⊑ r: a restriction on r reaches along the chain of s.
        let chains = vec![chain(vec![named(b"p"), named(b"q")], named(b"s"))];
        let roles = included(b"s", b"r");
        let path = some(named(b"p"), some(named(b"q"), atom(b"B")));
        assert_eq!(
            concept_sat(and(path, all(named(b"r"), no(b"B"))), &roles, &chains),
            Some(false)
        );
        // A chain whose roles are complex themselves: (p ∘ q) ∘ t ⊑ u via s.
        let chains = vec![
            chain(vec![named(b"p"), named(b"q")], named(b"s")),
            chain(vec![named(b"s"), named(b"t")], named(b"u")),
        ];
        let path = some(
            named(b"p"),
            some(named(b"q"), some(named(b"t"), atom(b"B"))),
        );
        assert_eq!(
            concept_sat(and(path, all(named(b"u"), no(b"B"))), &none(), &chains),
            Some(false)
        );
    });
}

#[test]
fn existentials_in_maximum_restrictions_count_chain_paths() {
    with_stack(|| {
        let chains = vec![chain(vec![named(b"p"), named(b"q")], named(b"r"))];
        // No t-neighbour may have an r-neighbour in B, but one has a p-q path.
        let path = some(named(b"p"), some(named(b"q"), atom(b"B")));
        let c = and(
            some(named(b"t"), path),
            at_most(0, named(b"t"), some(named(b"r"), atom(b"B"))),
        );
        assert_eq!(concept_sat(c, &none(), &chains), Some(false));
        let short = some(named(b"p"), atom(b"B"));
        let c = and(
            some(named(b"t"), short),
            at_most(0, named(b"t"), some(named(b"r"), atom(b"B"))),
        );
        assert_eq!(concept_sat(c, &none(), &chains), Some(true));
    });
}

#[test]
fn chains_reach_named_individuals() {
    with_stack(|| {
        // parent(a, b), brother(b, c), c : B and a : ∀uncle.¬B.
        let chains = uncle();
        let facts = vec![
            Fact {
                node: 0,
                concept: all(named(b"uncle"), no(b"B")),
            },
            Fact {
                node: 2,
                concept: atom(b"B"),
            },
        ];
        let links = vec![
            Link {
                role: named(b"parent"),
                from: 0,
                to: 1,
            },
            Link {
                role: named(b"brother"),
                from: 1,
                to: 2,
            },
        ];
        let answer = satisfiable(
            3,
            &Vec::new(),
            &facts,
            &links,
            &Concept::Top,
            &Vec::<Definition>::new(),
            &none(),
            &chains,
        );
        assert_eq!(answer, Some(false));
    });
}

#[test]
fn simple_positions_reject_complex_roles() {
    with_stack(|| {
        let chains = uncle();
        assert_eq!(
            concept_sat(at_most(1, named(b"uncle"), Concept::Top), &none(), &chains),
            None
        );
        assert_eq!(
            concept_sat(Concept::HasSelf(named(b"uncle")), &none(), &chains),
            None
        );
        let roles = RoleHierarchy {
            inclusions: Vec::new(),
            transitive: Vec::new(),
            disjoint: vec![Disjoint {
                left: named(b"uncle"),
                right: named(b"parent"),
            }],
        };
        assert_eq!(concept_sat(Concept::Top, &roles, &chains), None);
        // A number restriction on a role of a chain is fine.
        assert_eq!(
            concept_sat(at_most(1, named(b"parent"), Concept::Top), &none(), &chains),
            Some(true)
        );
        // Classes that start with a space are reserved for the encoding.
        assert_eq!(concept_sat(atom(b" x"), &none(), &chains), None);
        // A chain needs two roles.
        let short = vec![chain(vec![named(b"p")], named(b"r"))];
        assert_eq!(concept_sat(Concept::Top, &none(), &short), None);
    });
}

/// A finite interpretation of the classes `A`, `B` and the roles `p`, `q`,
/// `s` and `r`, where `r` relates every pair that the chains `p ∘ q ⊑ r` and
/// `r ∘ s ⊑ r` derive.
struct Finite {
    size: usize,
    a: Vec<bool>,
    b: Vec<bool>,
    relations: Vec<Vec<Vec<bool>>>,
}
fn next(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *seed >> 33
}
const ROLES: [&[u8]; 4] = [b"p", b"q", b"s", b"r"];
fn random_finite(seed: &mut u64) -> Finite {
    let size = 1 + (next(seed) % 3) as usize;
    let a = (0..size).map(|_| next(seed).is_multiple_of(2)).collect();
    let b = (0..size).map(|_| next(seed).is_multiple_of(2)).collect();
    let mut relations: Vec<Vec<Vec<bool>>> = (0..4)
        .map(|_| {
            (0..size)
                .map(|_| (0..size).map(|_| next(seed).is_multiple_of(3)).collect())
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
    Finite {
        size,
        a,
        b,
        relations,
    }
}
fn related(i: &Finite, role: &ObjectPropertyExpression, x: usize, y: usize) -> bool {
    let (property, inverse) = match role {
        ObjectPropertyExpression::Property(p) => (p, false),
        ObjectPropertyExpression::Inverse(p) => (p, true),
    };
    let index = ROLES
        .iter()
        .position(|name| *name == property.iri.spelling.as_slice())
        .expect("a known role");
    if inverse {
        i.relations[index][y][x]
    } else {
        i.relations[index][x][y]
    }
}
fn holds(i: &Finite, concept: &Concept, x: usize) -> bool {
    let count = |role: &ObjectPropertyExpression, filler: &Concept| {
        (0..i.size)
            .filter(|&y| related(i, role, x, y) && holds(i, filler, y))
            .count()
    };
    match concept {
        Concept::Top => true,
        Concept::Bottom => false,
        Concept::Atom(c) => {
            if c.iri.spelling == b"A" {
                i.a[x]
            } else {
                i.b[x]
            }
        }
        Concept::NotAtom(c) => {
            if c.iri.spelling == b"A" {
                !i.a[x]
            } else {
                !i.b[x]
            }
        }
        Concept::And(l, r) => holds(i, l, x) && holds(i, r, x),
        Concept::Or(l, r) => holds(i, l, x) || holds(i, r, x),
        Concept::Exists(role, f) => count(role, f) > 0,
        Concept::Forall(role, f) => (0..i.size).all(|y| !related(i, role, x, y) || holds(i, f, y)),
        Concept::AtLeast(n, role, f) => count(role, f) >= *n,
        Concept::AtMost(n, role, f) => count(role, f) <= *n,
        _ => panic!("not generated"),
    }
}
fn random_role(seed: &mut u64, simple: bool) -> ObjectPropertyExpression {
    let choices: &[&[u8]] = if simple {
        &[b"p", b"q", b"s"]
    } else {
        &[b"p", b"q", b"s", b"r", b"r"]
    };
    let name = choices[(next(seed) % choices.len() as u64) as usize];
    if next(seed).is_multiple_of(4) {
        inverted(name)
    } else {
        named(name)
    }
}
fn random_concept(seed: &mut u64, depth: usize) -> Concept {
    let pick = if depth == 0 {
        next(seed) % 4
    } else {
        next(seed) % 10
    };
    match pick {
        0 => atom(b"A"),
        1 => no(b"A"),
        2 => atom(b"B"),
        3 => no(b"B"),
        4 => and(
            random_concept(seed, depth - 1),
            random_concept(seed, depth - 1),
        ),
        5 => Concept::Or(
            Box::new(random_concept(seed, depth - 1)),
            Box::new(random_concept(seed, depth - 1)),
        ),
        6 => some(random_role(seed, false), random_concept(seed, depth - 1)),
        7 | 8 => all(random_role(seed, false), random_concept(seed, depth - 1)),
        _ => {
            let role = random_role(seed, true);
            let filler = random_concept(seed, depth - 1);
            if next(seed).is_multiple_of(2) {
                at_most((next(seed) % 2) as usize, role, filler)
            } else {
                Concept::AtLeast(2, role, Box::new(filler))
            }
        }
    }
}

#[test]
fn every_concept_with_a_small_model_of_the_chains_is_satisfiable() {
    with_stack(|| {
        let chains = vec![
            chain(vec![named(b"p"), named(b"q")], named(b"r")),
            chain(vec![named(b"r"), named(b"s")], named(b"r")),
        ];
        let mut seed = 11;
        let mut with_model = 0;
        let mut without = 0;
        for _ in 0..300 {
            // A path of two or three steps next to restrictions on the
            // chains' roles, so that many samples are unsatisfiable.
            let end = next(&mut seed) % 4;
            let literal = |pick: u64| match pick {
                0 => atom(b"A"),
                1 => no(b"A"),
                2 => atom(b"B"),
                _ => no(b"B"),
            };
            let mut path = literal(end);
            for _ in 0..2 + next(&mut seed) % 2 {
                path = some(random_role(&mut seed, false), path);
            }
            let restriction = if next(&mut seed).is_multiple_of(2) {
                all(random_role(&mut seed, false), literal(end ^ 1))
            } else {
                all(random_role(&mut seed, false), random_concept(&mut seed, 1))
            };
            let concept = and(random_concept(&mut seed, 2), and(path, restriction));
            let small_model = (0..400).any(|_| {
                let i = random_finite(&mut seed);
                (0..i.size).any(|x| holds(&i, &concept, x))
            });
            let answer = concept_sat(concept, &none(), &chains).expect("every sample is answered");
            if small_model {
                assert!(answer, "a model exists, so the concept must be satisfiable");
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
    });
}
