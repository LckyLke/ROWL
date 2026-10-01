use rowl_kernel::prototype::{
    decide, evaluate, next_valuation, Atom, Decision, Formula, Valuation,
};

#[test]
fn mutation_visits_each_valuation_once_and_stops() {
    let mut valuation = Valuation { a: false, b: false };
    for expected in [(false, true), (true, false), (true, true)] {
        assert!(next_valuation(&mut valuation));
        assert_eq!((valuation.a, valuation.b), expected);
    }
    assert!(!next_valuation(&mut valuation));
    assert_eq!((valuation.a, valuation.b), (true, true));
}

fn atom_a() -> Formula {
    Formula::Atom(Atom::A)
}

fn atom_b() -> Formula {
    Formula::Atom(Atom::B)
}

fn not(inner: Formula) -> Formula {
    Formula::Not(Box::new(inner))
}

fn and(left: Formula, right: Formula) -> Formula {
    Formula::And(Box::new(left), Box::new(right))
}

fn or(left: Formula, right: Formula) -> Formula {
    Formula::Or(Box::new(left), Box::new(right))
}

#[test]
fn contradiction_is_unsatisfiable_but_empty_classes_are_allowed() {
    assert!(matches!(
        decide(&and(atom_a(), not(atom_a()))),
        Decision::Unsatisfiable
    ));
    let formula = and(not(atom_a()), not(atom_b()));
    let Decision::Satisfiable(witness) = decide(&formula) else {
        panic!("two empty classes admit a domain element");
    };
    assert!(!witness.a && !witness.b);
}

#[test]
fn union_does_not_entail_either_disjunct() {
    // Countermodels to A ∨ B ⊑ A and A ∨ B ⊑ B both exist.
    for query in [atom_a(), atom_b()] {
        let counterexample = and(or(atom_a(), atom_b()), not(query));
        let Decision::Satisfiable(witness) = decide(&counterexample) else {
            panic!("one satisfying branch cannot justify an entailment");
        };
        assert!(evaluate(&counterexample, &witness));
    }
}

#[test]
fn tautology_and_bottom_respect_nonempty_domain() {
    assert!(matches!(
        decide(&or(atom_a(), not(atom_a()))),
        Decision::Satisfiable(_)
    ));
    assert!(matches!(decide(&Formula::Top), Decision::Satisfiable(_)));
    assert!(matches!(decide(&Formula::Bottom), Decision::Unsatisfiable));
}

#[test]
fn search_covers_all_four_valuations() {
    for a in [false, true] {
        for b in [false, true] {
            let left = if a { atom_a() } else { not(atom_a()) };
            let right = if b { atom_b() } else { not(atom_b()) };
            let formula = and(left, right);
            let Decision::Satisfiable(witness) = decide(&formula) else {
                panic!("a reachable interpretation was skipped");
            };
            assert_eq!((witness.a, witness.b), (a, b));
        }
    }
}

#[test]
fn de_morgan_equivalence_under_every_interpretation() {
    let left = not(and(atom_a(), atom_b()));
    let right = or(not(atom_a()), not(atom_b()));
    for a in [false, true] {
        for b in [false, true] {
            let valuation = Valuation { a, b };
            assert_eq!(evaluate(&left, &valuation), evaluate(&right, &valuation));
        }
    }
}
