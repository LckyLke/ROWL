//! The universal role for the completion forest, through a case split.
//!
//! `owl:topObjectProperty`, the universal role `U`, relates every pair of
//! elements, which no model of the forest has to. A restriction along it,
//! `∃U.C` or `∀U.C` in either orientation, holds at every element or at none,
//! so its truth is one global choice: whether some element is in `C`, or
//! whether every element is. `satisfiable` collects these restrictions, the
//! atoms, and tries the guesses of their truths in turn. Under a guess, every
//! atom becomes `⊤` or `⊥`, `∃U.Self` becomes `⊤` and its complement `⊥`, and
//! the guess is made good by what it requires: a further element in the filler
//! of a true `∃U.C` or outside the filler of a false `∀U.C`, each at a further
//! node of its own, and the filler of a true `∀U.C` or the complement of the
//! filler of a false `∃U.C` everywhere, in the TBox concept. The completion
//! forest, with the role chains in front of it, decides each guess. In a model
//! of a guess, with `U` then relating every pair, every guess is right, the
//! atoms of a filler before the atom itself, so it is a model of the question;
//! and a model of the question in which `U` relates every pair is a model of the
//! guess of its own truths. No name has to be fresh. Number restrictions must
//! not count along the universal role, which the caller checks.
//!
//! The answer is `None` when there are more than 16 atoms, when a list or a
//! node would exceed the `usize` range, when a complement cannot be formed, or
//! when the forest gives no answer for a guess.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::manual_map,
    clippy::len_zero,
    clippy::needless_return,
    clippy::if_same_then_else,
    clippy::too_many_arguments,
    clippy::match_like_matches_macro,
    clippy::collapsible_match
)] // Indexed operations, explicit branches and pushes without macros for the pinned extraction subset.
use crate::alc_ontology::{named_property, same_pattern};
use crate::assertion_equality::same_individual_value;
use crate::completion::{Definition, Fact, Link};
use crate::concepts::{copy_concept, copy_individual, copy_role, negate, same_role, Concept};
use crate::hierarchy::RoleHierarchy;
use crate::model::{Class, ObjectPropertyExpression};
use crate::nnf::copy_iri;
use crate::role_chains::{self, Chain};
use crate::symbols::same_spelling;

/// The most atoms whose truths are guessed.
const GUESSES: usize = 16;

/// Whether the role is not `owl:topObjectProperty`, in either orientation.
pub fn not_top(role: &ObjectPropertyExpression) -> bool {
    !same_pattern(
        &named_property(role).iri.spelling,
        b"http://www.w3.org/2002/07/owl#topObjectProperty",
    )
}
/// Whether the universal role is a role of the concept.
pub fn universal(concept: &Concept) -> bool {
    match concept {
        Concept::HasSelf(role) => !not_top(role),
        Concept::NotSelf(role) => !not_top(role),
        Concept::And(left, right) => universal(left) || universal(right),
        Concept::Or(left, right) => universal(left) || universal(right),
        Concept::Exists(role, filler) => !not_top(role) || universal(filler),
        Concept::Forall(role, filler) => !not_top(role) || universal(filler),
        Concept::AtLeast(_, role, filler) => !not_top(role) || universal(filler),
        Concept::AtMost(_, role, filler) => !not_top(role) || universal(filler),
        _ => false,
    }
}
/// Whether the universal role is a role of a fact in `facts[index..]`.
pub fn facts_universal(facts: &Vec<Fact>, index: usize) -> bool {
    if index < facts.len() {
        universal(&facts[index].concept) || facts_universal(facts, index + 1)
    } else {
        false
    }
}
/// Whether the universal role is a role of a definition in
/// `definitions[index..]`.
pub fn definitions_universal(definitions: &Vec<Definition>, index: usize) -> bool {
    if index < definitions.len() {
        universal(&definitions[index].concept) || definitions_universal(definitions, index + 1)
    } else {
        false
    }
}
/// Whether two concepts are the same: classes and individuals by exact
/// spelling, roles in the same orientation.
fn same_concept(left: &Concept, right: &Concept) -> bool {
    match (left, right) {
        (Concept::Top, Concept::Top) => true,
        (Concept::Bottom, Concept::Bottom) => true,
        (Concept::Atom(a), Concept::Atom(b)) => same_spelling(&a.iri.spelling, &b.iri.spelling),
        (Concept::NotAtom(a), Concept::NotAtom(b)) => {
            same_spelling(&a.iri.spelling, &b.iri.spelling)
        }
        (Concept::One(a), Concept::One(b)) => same_individual_value(a, b),
        (Concept::NotOne(a), Concept::NotOne(b)) => same_individual_value(a, b),
        (Concept::HasSelf(a), Concept::HasSelf(b)) => same_role(a, b),
        (Concept::NotSelf(a), Concept::NotSelf(b)) => same_role(a, b),
        (Concept::And(l1, r1), Concept::And(l2, r2)) => {
            if same_concept(l1, l2) {
                same_concept(r1, r2)
            } else {
                false
            }
        }
        (Concept::Or(l1, r1), Concept::Or(l2, r2)) => {
            if same_concept(l1, l2) {
                same_concept(r1, r2)
            } else {
                false
            }
        }
        (Concept::Exists(r1, c1), Concept::Exists(r2, c2)) => {
            if same_role(r1, r2) {
                same_concept(c1, c2)
            } else {
                false
            }
        }
        (Concept::Forall(r1, c1), Concept::Forall(r2, c2)) => {
            if same_role(r1, r2) {
                same_concept(c1, c2)
            } else {
                false
            }
        }
        (Concept::AtLeast(n1, r1, c1), Concept::AtLeast(n2, r2, c2)) => {
            if *n1 == *n2 && same_role(r1, r2) {
                same_concept(c1, c2)
            } else {
                false
            }
        }
        (Concept::AtMost(n1, r1, c1), Concept::AtMost(n2, r2, c2)) => {
            if *n1 == *n2 && same_role(r1, r2) {
                same_concept(c1, c2)
            } else {
                false
            }
        }
        _ => false,
    }
}
/// The index of the first atom of `atoms[index..]` that is the concept, or the
/// number of atoms when none is.
fn atom_index(atoms: &Vec<Concept>, concept: &Concept, index: usize) -> usize {
    if index < atoms.len() {
        if same_concept(&atoms[index], concept) {
            index
        } else {
            atom_index(atoms, concept, index + 1)
        }
    } else {
        atoms.len()
    }
}
/// `atoms` with the concept, a restriction along the universal role, unless it
/// is one of them already; `None` when there is no room.
fn add_atom(mut atoms: Vec<Concept>, concept: &Concept) -> Option<Vec<Concept>> {
    if atom_index(&atoms, concept, 0) < atoms.len() {
        Some(atoms)
    } else if atoms.len() < usize::MAX {
        atoms.push(copy_concept(concept));
        Some(atoms)
    } else {
        None
    }
}
/// `atoms` with every restriction along the universal role in the concept,
/// each once; `None` when there is no room.
fn collect(concept: &Concept, atoms: Vec<Concept>) -> Option<Vec<Concept>> {
    match concept {
        Concept::And(left, right) => match collect(left, atoms) {
            Some(atoms) => collect(right, atoms),
            None => None,
        },
        Concept::Or(left, right) => match collect(left, atoms) {
            Some(atoms) => collect(right, atoms),
            None => None,
        },
        Concept::Exists(role, filler) => match collect(filler, atoms) {
            Some(atoms) => {
                if not_top(role) {
                    Some(atoms)
                } else {
                    add_atom(atoms, concept)
                }
            }
            None => None,
        },
        Concept::Forall(role, filler) => match collect(filler, atoms) {
            Some(atoms) => {
                if not_top(role) {
                    Some(atoms)
                } else {
                    add_atom(atoms, concept)
                }
            }
            None => None,
        },
        Concept::AtLeast(_, _, filler) => collect(filler, atoms),
        Concept::AtMost(_, _, filler) => collect(filler, atoms),
        _ => Some(atoms),
    }
}
/// `atoms` with the atoms of the facts of `facts[index..]`.
fn collect_facts(facts: &Vec<Fact>, index: usize, atoms: Vec<Concept>) -> Option<Vec<Concept>> {
    if index < facts.len() {
        match collect(&facts[index].concept, atoms) {
            Some(atoms) => collect_facts(facts, index + 1, atoms),
            None => None,
        }
    } else {
        Some(atoms)
    }
}
/// `atoms` with the atoms of the definitions of `definitions[index..]`.
fn collect_definitions(
    definitions: &Vec<Definition>,
    index: usize,
    atoms: Vec<Concept>,
) -> Option<Vec<Concept>> {
    if index < definitions.len() {
        match collect(&definitions[index].concept, atoms) {
            Some(atoms) => collect_definitions(definitions, index + 1, atoms),
            None => None,
        }
    } else {
        Some(atoms)
    }
}
/// `⊤` when the guess for the atom of the concept is true, else `⊥`.
fn truth(atoms: &Vec<Concept>, guess: &Vec<bool>, concept: &Concept) -> Concept {
    let index = atom_index(atoms, concept, 0);
    if index < guess.len() {
        if guess[index] {
            Concept::Top
        } else {
            Concept::Bottom
        }
    } else {
        Concept::Bottom
    }
}
/// The concept with every restriction along the universal role replaced by the
/// guess for it, `∃U.Self` by `⊤` and its complement by `⊥`.
fn fixed(concept: &Concept, atoms: &Vec<Concept>, guess: &Vec<bool>) -> Concept {
    match concept {
        Concept::HasSelf(role) => {
            if not_top(role) {
                Concept::HasSelf(copy_role(role))
            } else {
                Concept::Top
            }
        }
        Concept::NotSelf(role) => {
            if not_top(role) {
                Concept::NotSelf(copy_role(role))
            } else {
                Concept::Bottom
            }
        }
        Concept::And(left, right) => Concept::And(
            Box::new(fixed(left, atoms, guess)),
            Box::new(fixed(right, atoms, guess)),
        ),
        Concept::Or(left, right) => Concept::Or(
            Box::new(fixed(left, atoms, guess)),
            Box::new(fixed(right, atoms, guess)),
        ),
        Concept::Exists(role, filler) => {
            if not_top(role) {
                Concept::Exists(copy_role(role), Box::new(fixed(filler, atoms, guess)))
            } else {
                truth(atoms, guess, concept)
            }
        }
        Concept::Forall(role, filler) => {
            if not_top(role) {
                Concept::Forall(copy_role(role), Box::new(fixed(filler, atoms, guess)))
            } else {
                truth(atoms, guess, concept)
            }
        }
        Concept::AtLeast(n, role, filler) => {
            Concept::AtLeast(*n, copy_role(role), Box::new(fixed(filler, atoms, guess)))
        }
        Concept::AtMost(n, role, filler) => {
            Concept::AtMost(*n, copy_role(role), Box::new(fixed(filler, atoms, guess)))
        }
        Concept::Top => Concept::Top,
        Concept::Bottom => Concept::Bottom,
        Concept::Atom(class) => Concept::Atom(Class {
            iri: copy_iri(&class.iri),
        }),
        Concept::NotAtom(class) => Concept::NotAtom(Class {
            iri: copy_iri(&class.iri),
        }),
        Concept::One(individual) => Concept::One(copy_individual(individual)),
        Concept::NotOne(individual) => Concept::NotOne(copy_individual(individual)),
    }
}
/// `out` with the facts of `facts[index..]` under the guess; `None` when there
/// is no room.
fn fixed_facts(
    facts: &Vec<Fact>,
    atoms: &Vec<Concept>,
    guess: &Vec<bool>,
    index: usize,
    mut out: Vec<Fact>,
) -> Option<Vec<Fact>> {
    if index < facts.len() {
        if out.len() < usize::MAX {
            out.push(Fact {
                node: facts[index].node,
                concept: fixed(&facts[index].concept, atoms, guess),
            });
            fixed_facts(facts, atoms, guess, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// `out` with the definitions of `definitions[index..]` under the guess;
/// `None` when there is no room.
fn fixed_definitions(
    definitions: &Vec<Definition>,
    atoms: &Vec<Concept>,
    guess: &Vec<bool>,
    index: usize,
    mut out: Vec<Definition>,
) -> Option<Vec<Definition>> {
    if index < definitions.len() {
        if out.len() < usize::MAX {
            out.push(Definition {
                class: Class {
                    iri: copy_iri(&definitions[index].class.iri),
                },
                concept: fixed(&definitions[index].concept, atoms, guess),
            });
            fixed_definitions(definitions, atoms, guess, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// `query` with a further element at `node` in the concept; `None` when there
/// is no room.
fn witness(mut query: Vec<Fact>, node: usize, concept: Concept) -> Option<Vec<Fact>> {
    if query.len() < usize::MAX {
        query.push(Fact { node, concept });
        Some(query)
    } else {
        None
    }
}
/// The TBox concept and the query facts with what the guess requires of the
/// atoms of `atoms[index..]`: for atom `i` with the filler `C` under the guess,
/// a further element at the node `base + i` in `C` for a true `∃U.C` and
/// outside `C` for a false `∀U.C`, and `C` everywhere for a true `∀U.C` and its
/// complement for a false `∃U.C`; `None` when a complement cannot be formed or
/// there is no room.
fn require(
    atoms: &Vec<Concept>,
    guess: &Vec<bool>,
    base: usize,
    index: usize,
    axioms: Concept,
    query: Vec<Fact>,
) -> Option<(Concept, Vec<Fact>)> {
    if index < atoms.len() && index < guess.len() && index < usize::MAX - base {
        match &atoms[index] {
            Concept::Exists(_, filler) => {
                let inside = fixed(filler, atoms, guess);
                if guess[index] {
                    match witness(query, base + index, inside) {
                        Some(query) => require(atoms, guess, base, index + 1, axioms, query),
                        None => None,
                    }
                } else {
                    match negate(&inside) {
                        Some(outside) => {
                            let axioms = Concept::And(Box::new(axioms), Box::new(outside));
                            require(atoms, guess, base, index + 1, axioms, query)
                        }
                        None => None,
                    }
                }
            }
            Concept::Forall(_, filler) => {
                let inside = fixed(filler, atoms, guess);
                if guess[index] {
                    let axioms = Concept::And(Box::new(axioms), Box::new(inside));
                    require(atoms, guess, base, index + 1, axioms, query)
                } else {
                    match negate(&inside) {
                        Some(outside) => match witness(query, base + index, outside) {
                            Some(query) => require(atoms, guess, base, index + 1, axioms, query),
                            None => None,
                        },
                        None => None,
                    }
                }
            }
            _ => None,
        }
    } else if index < atoms.len() {
        None
    } else {
        Some((axioms, query))
    }
}
/// The completion forest's answer under one guess for every atom, with the
/// further nodes from `count` on.
fn guessed(
    count: usize,
    query: &Vec<Fact>,
    facts: &Vec<Fact>,
    links: &Vec<Link>,
    axioms: &Concept,
    definitions: &Vec<Definition>,
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    atoms: &Vec<Concept>,
    guess: &Vec<bool>,
) -> Option<bool> {
    if atoms.len() < usize::MAX - count {
        let fixed_query = match fixed_facts(query, atoms, guess, 0, Vec::new()) {
            Some(fixed_query) => fixed_query,
            None => return None,
        };
        let fixed_axioms = fixed(axioms, atoms, guess);
        let (fixed_axioms, fixed_query) =
            match require(atoms, guess, count, 0, fixed_axioms, fixed_query) {
                Some(required) => required,
                None => return None,
            };
        let fixed_facts = match fixed_facts(facts, atoms, guess, 0, Vec::new()) {
            Some(fixed_facts) => fixed_facts,
            None => return None,
        };
        let fixed_definitions = match fixed_definitions(definitions, atoms, guess, 0, Vec::new()) {
            Some(fixed_definitions) => fixed_definitions,
            None => return None,
        };
        role_chains::satisfiable(
            count + atoms.len(),
            &fixed_query,
            &fixed_facts,
            links,
            &fixed_axioms,
            &fixed_definitions,
            roles,
            chains,
        )
    } else {
        None
    }
}
/// `out` with the guesses of `guess[index..]`.
fn copy_guess(guess: &Vec<bool>, index: usize, mut out: Vec<bool>) -> Vec<bool> {
    if index < guess.len() {
        if out.len() < usize::MAX {
            out.push(guess[index]);
        }
        copy_guess(guess, index + 1, out)
    } else {
        out
    }
}
/// The answer over every guess for all atoms that starts with `guess`: `true`
/// as soon as one has a model, `false` when none has.
fn guesses(
    count: usize,
    query: &Vec<Fact>,
    facts: &Vec<Fact>,
    links: &Vec<Link>,
    axioms: &Concept,
    definitions: &Vec<Definition>,
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    atoms: &Vec<Concept>,
    guess: Vec<bool>,
) -> Option<bool> {
    if guess.len() < atoms.len() {
        let mut no = copy_guess(&guess, 0, Vec::new());
        no.push(false);
        match guesses(
            count,
            query,
            facts,
            links,
            axioms,
            definitions,
            roles,
            chains,
            atoms,
            no,
        ) {
            Some(true) => Some(true),
            Some(false) => {
                let mut yes = guess;
                yes.push(true);
                guesses(
                    count,
                    query,
                    facts,
                    links,
                    axioms,
                    definitions,
                    roles,
                    chains,
                    atoms,
                    yes,
                )
            }
            None => None,
        }
    } else {
        guessed(
            count,
            query,
            facts,
            links,
            axioms,
            definitions,
            roles,
            chains,
            atoms,
            &guess,
        )
    }
}
/// Whether there is a model of the role hierarchy, the role chains and the
/// disjoint pairs, in which the universal role relates every pair, with
/// elements for the `count` nodes, in which the TBox concept holds everywhere,
/// every definition `A ⊑ C` holds wherever `A` does, the query facts and facts
/// hold at their nodes and the links relate their nodes: the answer of the
/// completion forest over the guesses for the atoms.
pub fn satisfiable(
    count: usize,
    query: &Vec<Fact>,
    facts: &Vec<Fact>,
    links: &Vec<Link>,
    axioms: &Concept,
    definitions: &Vec<Definition>,
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
) -> Option<bool> {
    let atoms = match collect(axioms, Vec::new()) {
        Some(atoms) => atoms,
        None => return None,
    };
    let atoms = match collect_definitions(definitions, 0, atoms) {
        Some(atoms) => atoms,
        None => return None,
    };
    let atoms = match collect_facts(facts, 0, atoms) {
        Some(atoms) => atoms,
        None => return None,
    };
    let atoms = match collect_facts(query, 0, atoms) {
        Some(atoms) => atoms,
        None => return None,
    };
    if atoms.len() <= GUESSES {
        guesses(
            count,
            query,
            facts,
            links,
            axioms,
            definitions,
            roles,
            chains,
            &atoms,
            Vec::new(),
        )
    } else {
        None
    }
}
