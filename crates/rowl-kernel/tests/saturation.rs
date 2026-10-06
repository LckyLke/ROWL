use rowl_kernel::classification::classify as tableau_classify;
use rowl_kernel::data_ontology::{prepare, prepared_consistent};
use rowl_kernel::model::*;
use rowl_kernel::saturation::{classify, consistent, taxonomy};

/// A small deterministic generator.
struct Random(u64);
impl Random {
    fn next(&mut self, bound: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % bound
    }
}

fn iri(text: String) -> Iri {
    Iri {
        spelling: text.into_bytes(),
    }
}
fn class(name: usize) -> Class {
    match name {
        0 => Class {
            iri: iri("http://www.w3.org/2002/07/owl#Thing".into()),
        },
        1 => Class {
            iri: iri("http://www.w3.org/2002/07/owl#Nothing".into()),
        },
        n => Class {
            iri: iri(format!("https://example.org/C{n}")),
        },
    }
}
fn role(name: usize) -> ObjectProperty {
    ObjectProperty {
        iri: iri(format!("https://example.org/r{name}")),
    }
}
fn property(name: usize) -> ObjectPropertyExpression {
    ObjectPropertyExpression::Property(role(name))
}

/// A random EL class expression over `classes` named classes (and, rarely,
/// owl:Thing and owl:Nothing) and `roles` roles.
fn expression(random: &mut Random, classes: usize, roles: usize, depth: usize) -> ClassExpression {
    let choice = if depth == 0 { 0 } else { random.next(6) };
    match choice {
        0..=2 => {
            let pick = random.next(classes + 2);
            // owl:Thing and owl:Nothing (0 and 1) only now and then.
            let name = if pick < 2 && random.next(4) != 0 {
                2 + random.next(classes)
            } else {
                pick
            };
            ClassExpression::Class(class(name))
        }
        3..=4 => ClassExpression::ObjectSomeValuesFrom(
            property(random.next(roles)),
            Box::new(expression(random, classes, roles, depth - 1)),
        ),
        _ => {
            let extra = random.next(2);
            let mut rest = Vec::new();
            for _ in 0..extra {
                rest.push(expression(random, classes, roles, depth - 1));
            }
            ClassExpression::ObjectIntersectionOf(Box::new(AtLeastTwo {
                first: expression(random, classes, roles, depth - 1),
                second: expression(random, classes, roles, depth - 1),
                rest,
            }))
        }
    }
}

fn annotated(axiom: Axiom) -> AnnotatedAxiom {
    AnnotatedAxiom {
        annotations: Vec::new(),
        axiom,
    }
}

fn ontology(
    random: &mut Random,
    classes: usize,
    roles: usize,
    axioms: usize,
) -> Vec<AnnotatedAxiom> {
    let mut out = Vec::new();
    for _ in 0..axioms {
        let axiom = match random.next(12) {
            0..=5 => Axiom::SubClassOf(
                expression(random, classes, roles, 2),
                expression(random, classes, roles, 2),
            ),
            6 => Axiom::EquivalentClasses(AtLeastTwo {
                first: expression(random, classes, roles, 1),
                second: expression(random, classes, roles, 1),
                rest: Vec::new(),
            }),
            7 => Axiom::DisjointClasses(AtLeastTwo {
                first: ClassExpression::Class(class(2 + random.next(classes))),
                second: ClassExpression::Class(class(2 + random.next(classes))),
                rest: Vec::new(),
            }),
            8 => Axiom::ObjectPropertyDomain(
                property(random.next(roles)),
                expression(random, classes, roles, 1),
            ),
            9 => Axiom::SubObjectPropertyOf(
                SubObjectPropertyExpression::Single(property(random.next(roles))),
                property(random.next(roles)),
            ),
            10 => Axiom::TransitiveObjectProperty(property(random.next(roles))),
            _ => Axiom::SubObjectPropertyOf(
                SubObjectPropertyExpression::Chain(AtLeastTwo {
                    first: property(random.next(roles)),
                    second: property(random.next(roles)),
                    rest: Vec::new(),
                }),
                property(random.next(roles)),
            ),
        };
        out.push(annotated(axiom));
    }
    out
}

/// Run `work` on a thread with a large stack: the verified functions recurse
/// over the length of their input.
fn on_large_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(work)
        .expect("a thread")
        .join()
        .expect("the work does not panic");
}

#[test]
fn saturation_agrees_with_the_tableau_on_random_el_ontologies() {
    on_large_stack(agreement);
}

fn agreement() {
    let mut random = Random(42);
    let mut compared = 0;
    let mut declined = 0;
    let mut unsatisfiable = 0;
    let mut nontrivial = 0;
    for round in 0..400 {
        let classes = 3 + round % 5;
        let roles = 1 + round % 3;
        let items = ontology(&mut random, classes, roles, 2 + round % 7);
        let names: Vec<Class> = (0..classes + 2).map(class).collect();
        let saturated = classify(&items, &names).expect("the ontology is EL");
        let Some(prepared) = prepare(&items) else {
            declined += 1;
            continue;
        };
        let Some(expected) = tableau_classify(&prepared, &items, &names) else {
            declined += 1;
            continue;
        };
        assert_eq!(saturated.satisfiable, expected.satisfiable, "round {round}");
        assert_eq!(saturated.subsumed, expected.subsumed, "round {round}");
        let listed = taxonomy(&items, &names).expect("the ontology is EL");
        assert_eq!(listed.satisfiable, expected.satisfiable, "round {round}");
        for (i, row) in expected.subsumed.iter().enumerate() {
            if expected.satisfiable[i] {
                let mut supers = listed.supers[i].clone();
                supers.sort();
                let wanted: Vec<usize> = (0..row.len()).filter(|j| row[*j]).collect();
                assert_eq!(supers, wanted, "round {round}, class {i}");
            } else {
                assert!(listed.supers[i].is_empty(), "round {round}, class {i}");
            }
        }
        assert_eq!(
            consistent(&items),
            prepared_consistent(&prepared),
            "round {round}"
        );
        compared += 1;
        unsatisfiable += saturated.satisfiable.iter().filter(|s| !**s).count();
        for (i, row) in saturated.subsumed.iter().enumerate() {
            if saturated.satisfiable[i] {
                for (j, s) in row.iter().enumerate() {
                    if *s && i != j && j != 0 {
                        nontrivial += 1;
                    }
                }
            }
        }
    }
    eprintln!("compared {compared}, declined {declined}, unsatisfiable {unsatisfiable}, subsumptions {nontrivial}");
    assert!(compared > 250, "compared {compared}, declined {declined}");
    assert!(unsatisfiable > 50 && nontrivial > 200);
}

#[test]
fn saturation_declines_outside_el() {
    let items = vec![annotated(Axiom::SubClassOf(
        ClassExpression::Class(class(2)),
        ClassExpression::ObjectUnionOf(Box::new(AtLeastTwo {
            first: ClassExpression::Class(class(3)),
            second: ClassExpression::Class(class(4)),
            rest: Vec::new(),
        })),
    ))];
    assert!(classify(&items, &vec![class(2)]).is_none());
    assert!(taxonomy(&items, &vec![class(2)]).is_none());
    assert!(consistent(&items).is_none());
    let assertion = vec![annotated(Axiom::ClassAssertion(
        ClassExpression::Class(class(2)),
        Individual::Named(NamedIndividual {
            iri: iri("https://example.org/a".into()),
        }),
    ))];
    assert!(classify(&assertion, &vec![class(2)]).is_none());
}
