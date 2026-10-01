//! M1 translation probe: Boolean class expressions over two atomic classes.
//!
//! A valuation describes class membership of a single domain element. Boolean
//! class satisfiability has a one-element model exactly when a valuation exists.
//! This module has no properties, individuals, axioms, datatypes, or imports.
//! Neither atom being absent nor an unchosen search branch implies negation.
//!
//! Keep this module in the safe Rust subset translated by Charon/Aeneas.

/// Two independent atomic classes in the internal feasibility experiment.
pub enum Atom {
    A,
    B,
}

/// Arbitrarily nested Boolean class expressions; boxes give finite owned trees.
pub enum Formula {
    Top,
    Bottom,
    Atom(Atom),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
}

/// Membership of one element in the two atomic classes.
pub struct Valuation {
    pub a: bool,
    pub b: bool,
}

/// An exhaustive answer for this prototype's language only.
pub enum Decision {
    Satisfiable(Valuation),
    Unsatisfiable,
}

/// Advance deterministically through FF, FT, TF, TT; leave TT unchanged.
///
/// This mutable state transition is an Aeneas feasibility probe. A false return
/// means every valuation has been visited, rather than a clash or negated fact.
pub fn next_valuation(valuation: &mut Valuation) -> bool {
    if !valuation.b {
        valuation.b = true;
        return true;
    }
    if !valuation.a {
        valuation.a = true;
        valuation.b = false;
        return true;
    }
    false
}

/// Evaluate the expression at an element with the given class membership.
pub fn evaluate(formula: &Formula, valuation: &Valuation) -> bool {
    match formula {
        Formula::Top => true,
        Formula::Bottom => false,
        Formula::Atom(Atom::A) => valuation.a,
        Formula::Atom(Atom::B) => valuation.b,
        Formula::Not(inner) => !evaluate(inner, valuation),
        Formula::And(left, right) => evaluate(left, valuation) && evaluate(right, valuation),
        Formula::Or(left, right) => evaluate(left, valuation) || evaluate(right, valuation),
    }
}

/// Explore every interpretation, returning the first satisfying witness.
///
/// The search terminates because there are four valuations and evaluation
/// recurses over strict subtrees. The Lean proof checks the actual translation.
pub fn decide(formula: &Formula) -> Decision {
    let mut valuation = Valuation { a: false, b: false };
    loop {
        if evaluate(formula, &valuation) {
            return Decision::Satisfiable(valuation);
        }
        if !next_valuation(&mut valuation) {
            return Decision::Unsatisfiable;
        }
    }
}
