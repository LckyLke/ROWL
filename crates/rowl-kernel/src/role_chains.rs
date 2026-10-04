//! Role chains, the complex role inclusions `r1 ∘ … ∘ rn ⊑ r` of SROIQ, for
//! the completion forest, by an encoding with fresh classes.
//!
//! A role is complex when the role of a chain is included in it. Every complex
//! role `c` has an automaton that reads the paths along which the role axioms
//! relate a pair by `c`:
//!
//! 1. from its initial state an edge along `c`, or along a role included in
//!    it, leads to its final state, and so does every complex role included in
//!    `c` that does not include `c`;
//! 2. a transitive role equivalent to `c`, or a chain of two roles equivalent
//!    to `c` whose role is equivalent to `c`, returns from the final to the
//!    initial state;
//! 3. every other chain whose role is equivalent to `c` adds a segment of new
//!    states along its roles: back to the final state from the final state when
//!    its first role is equivalent to `c` (and the segment leaves that role
//!    out), back to the initial state from the initial state when its last
//!    role is (leaving it out), and from the initial to the final state
//!    otherwise.
//!
//! A universal restriction `∀c.C` on a complex role becomes a fresh class, the
//! atom of the initial state of `c` with the filler `C`, and the forest unfolds
//! every atom lazily. The atom of a state includes, for every transition to a
//! state `q`, with `Y` the atom of `q` with the same filler: `∀c.Y` for an edge
//! along `c`, `∀s.Y` along a role `s` that is not complex, the atom of the
//! initial state of `s` with the filler `Y` along a complex role `s`, and `Y`
//! itself for a return; the atom of the final state also includes its filler.
//! In the model of a forest every role relates the pairs that the role axioms
//! derive from the edges, and the atoms carry their fillers along every such
//! pair. Conversely, a model of the role axioms becomes a model of the encoding
//! when every atom holds where every path that its automaton accepts leads into
//! its filler. In the filler of a maximum restriction, where a restriction
//! counts the elements that do not satisfy it, an existential restriction
//! `∃c.C` on a complex role becomes the complement of the atom of the
//! complement of `C`.
//!
//! Number restrictions, self restrictions and their complements, and disjoint
//! pairs must be on roles that are not complex, as OWL 2 requires simple roles
//! there. An atom's class is a space followed by the eight bytes of its index,
//! and no class of the problem may start with a space. `None` means that a
//! chain has fewer than two roles, that a role that must be simple is complex,
//! that a class of the problem starts with a space, that an automaton would be
//! nested in itself or the encoding needs more than `LIMIT` atoms (which only
//! a hierarchy that is not regular calls for), that a structure would exceed
//! the `usize` range, or that the forest gives no answer.
#![allow(
    clippy::ptr_arg,
    clippy::question_mark,
    clippy::collapsible_match,
    clippy::collapsible_if,
    clippy::collapsible_else_if,
    clippy::needless_return,
    clippy::single_match,
    clippy::manual_map,
    clippy::too_many_arguments,
    clippy::vec_init_then_push,
    clippy::len_zero,
    clippy::match_like_matches_macro,
    clippy::if_same_then_else
)] // Indexed operations, explicit branches and pushes without macros for the pinned extraction subset.
use crate::completion::{Definition, Fact, Link};
use crate::concepts::{copy_concept, copy_role, inverse, negate, same_role, Concept};
use crate::forest;
use crate::hierarchy::{below, RoleHierarchy};
use crate::model::{Class, Iri, ObjectPropertyExpression};
use crate::nnf::copy_iri;

/// A role chain: every pair related along `roles`, one after the other, is
/// related by `sup`.
pub struct Chain {
    pub roles: Vec<ObjectPropertyExpression>,
    pub sup: ObjectPropertyExpression,
}
/// A state of the automaton of a complex role.
pub enum State {
    Initial,
    Final,
    /// The state of the segment of the chain at the first index after as many
    /// of its roles as the second.
    Inside(usize, usize),
}
/// What a transition reads.
pub enum Label {
    /// An edge along the role of the automaton.
    Direct,
    /// A pair related by the role.
    Role(ObjectPropertyExpression),
    /// Nothing.
    Empty,
}
/// A transition of an automaton.
pub struct Transition {
    pub label: Label,
    pub target: State,
}
/// The filler of an atom: a base concept, or the class of another atom.
pub enum Filler {
    Base(usize),
    Atom(usize),
}
/// An atom: the state of the automaton of a complex role, with a filler.
pub struct Atom {
    pub role: ObjectPropertyExpression,
    pub state: State,
    pub filler: Filler,
}
/// Where the segment of a chain starts and ends, and which of its roles it
/// reads: `length` roles from `offset`.
pub struct Segment {
    pub start: State,
    pub end: State,
    pub offset: usize,
    pub length: usize,
}

/// The most atoms an encoding may have.
const LIMIT: usize = 1_048_576;

/// Each role includes the other.
fn equivalent(
    roles: &RoleHierarchy,
    left: &ObjectPropertyExpression,
    right: &ObjectPropertyExpression,
) -> bool {
    if below(roles, left, right) {
        below(roles, right, left)
    } else {
        false
    }
}
/// Whether the role of a chain of `chains[index..]` is included in `role`.
fn complex_from(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    role: &ObjectPropertyExpression,
    index: usize,
) -> bool {
    if index < chains.len() {
        if below(roles, &chains[index].sup, role) {
            true
        } else {
            complex_from(roles, chains, role, index + 1)
        }
    } else {
        false
    }
}
/// Whether the role is complex: the role of a chain is included in it.
pub fn complex(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    role: &ObjectPropertyExpression,
) -> bool {
    complex_from(roles, chains, role, 0)
}
/// A copy of a state.
fn copy_state(state: &State) -> State {
    match state {
        State::Initial => State::Initial,
        State::Final => State::Final,
        State::Inside(chain, position) => State::Inside(*chain, *position),
    }
}
/// The same state.
fn same_state(left: &State, right: &State) -> bool {
    match left {
        State::Initial => match right {
            State::Initial => true,
            _ => false,
        },
        State::Final => match right {
            State::Final => true,
            _ => false,
        },
        State::Inside(chain, position) => match right {
            State::Inside(other, place) => {
                if *chain == *other {
                    *position == *place
                } else {
                    false
                }
            }
            _ => false,
        },
    }
}
/// A copy of a filler.
fn copy_filler(filler: &Filler) -> Filler {
    match filler {
        Filler::Base(index) => Filler::Base(*index),
        Filler::Atom(index) => Filler::Atom(*index),
    }
}
/// The same filler.
fn same_filler(left: &Filler, right: &Filler) -> bool {
    match left {
        Filler::Base(index) => match right {
            Filler::Base(other) => *index == *other,
            _ => false,
        },
        Filler::Atom(index) => match right {
            Filler::Atom(other) => *index == *other,
            _ => false,
        },
    }
}
/// Whether the chain has two roles equivalent to `role` and its role is too.
fn twin(roles: &RoleHierarchy, chain: &Chain, role: &ObjectPropertyExpression) -> bool {
    if chain.roles.len() == 2 {
        if equivalent(roles, &chain.sup, role) {
            if equivalent(roles, &chain.roles[0], role) {
                equivalent(roles, &chain.roles[1], role)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}
/// The segment that a chain of at least two roles adds to the automaton of
/// `role`: none when its role is not equivalent to `role` or for a twin.
fn segment(
    roles: &RoleHierarchy,
    chain: &Chain,
    role: &ObjectPropertyExpression,
) -> Option<Segment> {
    let length = chain.roles.len();
    if length < 2 {
        return None;
    }
    if !equivalent(roles, &chain.sup, role) {
        return None;
    }
    if equivalent(roles, &chain.roles[0], role) {
        if length == 2 {
            if equivalent(roles, &chain.roles[1], role) {
                return None;
            }
        }
        return Some(Segment {
            start: State::Final,
            end: State::Final,
            offset: 1,
            length: length - 1,
        });
    }
    if equivalent(roles, &chain.roles[length - 1], role) {
        return Some(Segment {
            start: State::Initial,
            end: State::Initial,
            offset: 0,
            length: length - 1,
        });
    }
    Some(Segment {
        start: State::Initial,
        end: State::Final,
        offset: 0,
        length,
    })
}
/// The transition of the segment of the chain at `index` after `position` of
/// its roles, with `position < segment.length`.
fn step(chain: &Chain, index: usize, segment: &Segment, position: usize) -> Transition {
    let label = if segment.offset + position < chain.roles.len() {
        Label::Role(copy_role(&chain.roles[segment.offset + position]))
    } else {
        Label::Empty
    };
    let target = if position + 1 == segment.length {
        copy_state(&segment.end)
    } else {
        State::Inside(index, position + 1)
    };
    Transition { label, target }
}
/// The transitions of the complex roles strictly below `role`, from the
/// inclusions of `roles.inclusions[index..]`, appended to `out`.
fn sub_transitions(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    role: &ObjectPropertyExpression,
    index: usize,
    mut out: Vec<Transition>,
) -> Option<Vec<Transition>> {
    if index < roles.inclusions.len() {
        let inclusion = &roles.inclusions[index];
        if same_role(&inclusion.sup, role) {
            if complex(roles, chains, &inclusion.sub) {
                if !below(roles, role, &inclusion.sub) {
                    if out.len() < usize::MAX {
                        out.push(Transition {
                            label: Label::Role(copy_role(&inclusion.sub)),
                            target: State::Final,
                        });
                    } else {
                        return None;
                    }
                }
            }
        }
        sub_transitions(roles, chains, role, index + 1, out)
    } else {
        Some(out)
    }
}
/// Whether a transitive role of `roles.transitive[index..]` is equivalent to
/// `role`.
fn transitive_from(roles: &RoleHierarchy, role: &ObjectPropertyExpression, index: usize) -> bool {
    if index < roles.transitive.len() {
        if equivalent(roles, &roles.transitive[index], role) {
            true
        } else {
            transitive_from(roles, role, index + 1)
        }
    } else {
        false
    }
}
/// The transitions from `state`, the initial or the final state, that the
/// chains of `chains[index..]` add, appended to `out`.
fn chain_transitions(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    role: &ObjectPropertyExpression,
    state: &State,
    index: usize,
    mut out: Vec<Transition>,
) -> Option<Vec<Transition>> {
    if index < chains.len() {
        let chain = &chains[index];
        if twin(roles, chain, role) {
            match state {
                State::Final => {
                    if out.len() < usize::MAX {
                        out.push(Transition {
                            label: Label::Empty,
                            target: State::Initial,
                        });
                    } else {
                        return None;
                    }
                }
                _ => {}
            }
        } else {
            match segment(roles, chain, role) {
                Some(segment) => {
                    if same_state(&segment.start, state) {
                        if out.len() < usize::MAX {
                            out.push(step(chain, index, &segment, 0));
                        } else {
                            return None;
                        }
                    }
                }
                None => {}
            }
        }
        chain_transitions(roles, chains, role, state, index + 1, out)
    } else {
        Some(out)
    }
}
/// The transitions from a state of the automaton of the complex role `role`.
pub fn transitions(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    role: &ObjectPropertyExpression,
    state: &State,
) -> Option<Vec<Transition>> {
    match state {
        State::Initial => {
            let mut out = Vec::new();
            out.push(Transition {
                label: Label::Direct,
                target: State::Final,
            });
            match sub_transitions(roles, chains, role, 0, out) {
                Some(out) => chain_transitions(roles, chains, role, state, 0, out),
                None => None,
            }
        }
        State::Final => {
            let mut out = Vec::new();
            if transitive_from(roles, role, 0) {
                out.push(Transition {
                    label: Label::Empty,
                    target: State::Initial,
                });
            }
            chain_transitions(roles, chains, role, state, 0, out)
        }
        State::Inside(index, position) => {
            let mut out = Vec::new();
            if *index < chains.len() {
                match segment(roles, &chains[*index], role) {
                    Some(segment) => {
                        if 0 < *position {
                            if *position < segment.length {
                                out.push(step(&chains[*index], *index, &segment, *position));
                            }
                        }
                    }
                    None => {}
                }
            }
            Some(out)
        }
    }
}
/// The eight bytes of `value % 256^(8 - count)`, least significant first, from
/// the `count`th on, appended to `out`, which has `count + 1` bytes.
fn bytes(value: usize, count: usize, mut out: Vec<u8>) -> Vec<u8> {
    if count < 8 {
        if out.len() < usize::MAX {
            out.push((value % 256) as u8);
        }
        bytes(value / 256, count + 1, out)
    } else {
        out
    }
}
/// The class of the atom at `index`: a space and the eight bytes of the index.
pub fn name(index: usize) -> Class {
    let mut spelling = Vec::new();
    spelling.push(b' ');
    Class {
        iri: Iri {
            spelling: bytes(index, 0, spelling),
        },
    }
}
/// Whether the spelling of the class starts with a space.
fn spaced(class: &Class) -> bool {
    if 0 < class.iri.spelling.len() {
        class.iri.spelling[0] == b' '
    } else {
        false
    }
}
/// Whether no class of the concept starts with a space and its number
/// restrictions, self restrictions and their complements are on roles that
/// are not complex.
fn fits(roles: &RoleHierarchy, chains: &Vec<Chain>, concept: &Concept) -> bool {
    match concept {
        Concept::Atom(class) => !spaced(class),
        Concept::NotAtom(class) => !spaced(class),
        Concept::HasSelf(role) => !complex(roles, chains, role),
        Concept::NotSelf(role) => !complex(roles, chains, role),
        Concept::And(left, right) => {
            if fits(roles, chains, left) {
                fits(roles, chains, right)
            } else {
                false
            }
        }
        Concept::Or(left, right) => {
            if fits(roles, chains, left) {
                fits(roles, chains, right)
            } else {
                false
            }
        }
        Concept::Exists(_, filler) => fits(roles, chains, filler),
        Concept::Forall(_, filler) => fits(roles, chains, filler),
        Concept::AtLeast(_, role, filler) => {
            if complex(roles, chains, role) {
                false
            } else {
                fits(roles, chains, filler)
            }
        }
        Concept::AtMost(_, role, filler) => {
            if complex(roles, chains, role) {
                false
            } else {
                fits(roles, chains, filler)
            }
        }
        _ => true,
    }
}
/// The index of the first atom of `atoms[index..]` with the role, state and
/// filler, or the number of atoms.
fn find_from(
    atoms: &Vec<Atom>,
    role: &ObjectPropertyExpression,
    state: &State,
    filler: &Filler,
    index: usize,
) -> usize {
    if index < atoms.len() {
        let atom = &atoms[index];
        if same_role(&atom.role, role) {
            if same_state(&atom.state, state) {
                if same_filler(&atom.filler, filler) {
                    return index;
                }
            }
        }
        find_from(atoms, role, state, filler, index + 1)
    } else {
        atoms.len()
    }
}
/// The index of the atom with the role, state and filler, added at the end
/// when there is none yet; `None` when there is no room.
fn atom_for(
    mut atoms: Vec<Atom>,
    role: &ObjectPropertyExpression,
    state: &State,
    filler: &Filler,
) -> Option<(Vec<Atom>, usize)> {
    let found = find_from(&atoms, role, state, filler, 0);
    if found < atoms.len() {
        return Some((atoms, found));
    }
    if atoms.len() < usize::MAX {
        atoms.push(Atom {
            role: copy_role(role),
            state: copy_state(state),
            filler: copy_filler(filler),
        });
        Some((atoms, found))
    } else {
        None
    }
}
/// The atom of the initial state of `role` with a new base filler.
fn universal(
    atoms: Vec<Atom>,
    mut bases: Vec<Concept>,
    role: &ObjectPropertyExpression,
    filler: Concept,
) -> Option<(Vec<Atom>, Vec<Concept>, usize)> {
    if bases.len() < usize::MAX {
        let base = bases.len();
        bases.push(filler);
        match atom_for(atoms, role, &State::Initial, &Filler::Base(base)) {
            Some((atoms, index)) => Some((atoms, bases, index)),
            None => None,
        }
    } else {
        None
    }
}
/// The encoding of a concept in a positive position, or in a negative one,
/// the filler of a maximum restriction, with the atoms and base fillers it
/// adds.
fn encode(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    concept: &Concept,
    positive: bool,
    atoms: Vec<Atom>,
    bases: Vec<Concept>,
) -> Option<(Vec<Atom>, Vec<Concept>, Concept)> {
    match concept {
        Concept::And(left, right) => match encode(roles, chains, left, positive, atoms, bases) {
            Some((atoms, bases, first)) => {
                match encode(roles, chains, right, positive, atoms, bases) {
                    Some((atoms, bases, second)) => Some((
                        atoms,
                        bases,
                        Concept::And(Box::new(first), Box::new(second)),
                    )),
                    None => None,
                }
            }
            None => None,
        },
        Concept::Or(left, right) => match encode(roles, chains, left, positive, atoms, bases) {
            Some((atoms, bases, first)) => {
                match encode(roles, chains, right, positive, atoms, bases) {
                    Some((atoms, bases, second)) => {
                        Some((atoms, bases, Concept::Or(Box::new(first), Box::new(second))))
                    }
                    None => None,
                }
            }
            None => None,
        },
        Concept::Exists(role, filler) => {
            match encode(roles, chains, filler, positive, atoms, bases) {
                Some((atoms, bases, inner)) => {
                    if positive {
                        Some((
                            atoms,
                            bases,
                            Concept::Exists(copy_role(role), Box::new(inner)),
                        ))
                    } else if complex(roles, chains, role) {
                        match negate(&inner) {
                            Some(complement) => match universal(atoms, bases, role, complement) {
                                Some((atoms, bases, index)) => {
                                    Some((atoms, bases, Concept::NotAtom(name(index))))
                                }
                                None => None,
                            },
                            None => None,
                        }
                    } else {
                        Some((
                            atoms,
                            bases,
                            Concept::Exists(copy_role(role), Box::new(inner)),
                        ))
                    }
                }
                None => None,
            }
        }
        Concept::Forall(role, filler) => {
            match encode(roles, chains, filler, positive, atoms, bases) {
                Some((atoms, bases, inner)) => {
                    if positive {
                        if complex(roles, chains, role) {
                            match universal(atoms, bases, role, inner) {
                                Some((atoms, bases, index)) => {
                                    Some((atoms, bases, Concept::Atom(name(index))))
                                }
                                None => None,
                            }
                        } else {
                            Some((
                                atoms,
                                bases,
                                Concept::Forall(copy_role(role), Box::new(inner)),
                            ))
                        }
                    } else {
                        Some((
                            atoms,
                            bases,
                            Concept::Forall(copy_role(role), Box::new(inner)),
                        ))
                    }
                }
                None => None,
            }
        }
        Concept::AtLeast(n, role, filler) => {
            match encode(roles, chains, filler, positive, atoms, bases) {
                Some((atoms, bases, inner)) => Some((
                    atoms,
                    bases,
                    Concept::AtLeast(*n, copy_role(role), Box::new(inner)),
                )),
                None => None,
            }
        }
        Concept::AtMost(n, role, filler) => {
            match encode(roles, chains, filler, !positive, atoms, bases) {
                Some((atoms, bases, inner)) => Some((
                    atoms,
                    bases,
                    Concept::AtMost(*n, copy_role(role), Box::new(inner)),
                )),
                None => None,
            }
        }
        _ => Some((atoms, bases, copy_concept(concept))),
    }
}
/// The concept of a filler.
fn filler_concept(bases: &Vec<Concept>, filler: &Filler) -> Concept {
    match filler {
        Filler::Base(index) => {
            if *index < bases.len() {
                copy_concept(&bases[*index])
            } else {
                Concept::Top
            }
        }
        Filler::Atom(index) => Concept::Atom(name(*index)),
    }
}
/// Whether the atom at `index`, or an atom that its filler leads to within
/// `fuel` steps, is of `role`: nesting the automaton of `role` there would
/// repeat it without end, which only a hierarchy that is not regular calls
/// for. Running out of steps counts as a repetition.
fn nests(atoms: &Vec<Atom>, role: &ObjectPropertyExpression, index: usize, fuel: usize) -> bool {
    if fuel == 0 {
        return true;
    }
    if index < atoms.len() {
        if same_role(&atoms[index].role, role) {
            true
        } else {
            match &atoms[index].filler {
                Filler::Atom(next) => nests(atoms, role, *next, fuel - 1),
                Filler::Base(_) => false,
            }
        }
    } else {
        false
    }
}
/// What the transitions of `transitions[index..]` from an atom of `role` with
/// the filler require, conjoined onto `acc`, with the atoms they add.
fn unfold_from(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    transitions: &Vec<Transition>,
    role: &ObjectPropertyExpression,
    filler: &Filler,
    index: usize,
    atoms: Vec<Atom>,
    acc: Concept,
) -> Option<(Vec<Atom>, Concept)> {
    if index < transitions.len() {
        let transition = &transitions[index];
        match atom_for(atoms, role, &transition.target, filler) {
            Some((atoms, target)) => {
                let (atoms, part) = match &transition.label {
                    Label::Direct => (
                        atoms,
                        Concept::Forall(copy_role(role), Box::new(Concept::Atom(name(target)))),
                    ),
                    Label::Role(along) => {
                        if complex(roles, chains, along) {
                            if nests(&atoms, along, target, atoms.len()) {
                                return None;
                            }
                            match atom_for(atoms, along, &State::Initial, &Filler::Atom(target)) {
                                Some((atoms, nested)) => (atoms, Concept::Atom(name(nested))),
                                None => return None,
                            }
                        } else {
                            (
                                atoms,
                                Concept::Forall(
                                    copy_role(along),
                                    Box::new(Concept::Atom(name(target))),
                                ),
                            )
                        }
                    }
                    Label::Empty => (atoms, Concept::Atom(name(target))),
                };
                unfold_from(
                    roles,
                    chains,
                    transitions,
                    role,
                    filler,
                    index + 1,
                    atoms,
                    Concept::And(Box::new(acc), Box::new(part)),
                )
            }
            None => None,
        }
    } else {
        Some((atoms, acc))
    }
}
/// What the atom at `index` requires, with the atoms that requires.
fn unfold(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    bases: &Vec<Concept>,
    atoms: Vec<Atom>,
    index: usize,
) -> Option<(Vec<Atom>, Concept)> {
    if index < atoms.len() {
        let role = copy_role(&atoms[index].role);
        let state = copy_state(&atoms[index].state);
        let filler = copy_filler(&atoms[index].filler);
        let start = match &state {
            State::Final => filler_concept(bases, &filler),
            _ => Concept::Top,
        };
        match transitions(roles, chains, &role, &state) {
            Some(transitions) => {
                unfold_from(roles, chains, &transitions, &role, &filler, 0, atoms, start)
            }
            None => None,
        }
    } else {
        None
    }
}
/// The definitions of the atoms of `atoms[index..]` and of the atoms that they
/// add, appended to `out`; `None` beyond `LIMIT` atoms.
fn generate(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    bases: &Vec<Concept>,
    atoms: Vec<Atom>,
    index: usize,
    mut out: Vec<Definition>,
) -> Option<(Vec<Atom>, Vec<Definition>)> {
    if index < atoms.len() {
        if LIMIT < atoms.len() {
            return None;
        }
        match unfold(roles, chains, bases, atoms, index) {
            Some((atoms, concept)) => {
                if out.len() < usize::MAX {
                    out.push(Definition {
                        class: name(index),
                        concept,
                    });
                    generate(roles, chains, bases, atoms, index + 1, out)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some((atoms, out))
    }
}
/// The chains of `chains[index..]` copied onto `out`, with their roles
/// reversed and inverted when `mirror` holds.
fn copy_chains(
    chains: &Vec<Chain>,
    mirror: bool,
    index: usize,
    mut out: Vec<Chain>,
) -> Option<Vec<Chain>> {
    if index < chains.len() {
        let chain = &chains[index];
        let roles = if mirror {
            reversed(&chain.roles, chain.roles.len(), Vec::new())
        } else {
            copied(&chain.roles, 0, Vec::new())
        };
        let sup = if mirror {
            inverse(&chain.sup)
        } else {
            copy_role(&chain.sup)
        };
        if out.len() < usize::MAX {
            out.push(Chain { roles, sup });
            copy_chains(chains, mirror, index + 1, out)
        } else {
            None
        }
    } else {
        Some(out)
    }
}
/// The roles of `roles[index..]` copied onto `out`.
fn copied(
    roles: &Vec<ObjectPropertyExpression>,
    index: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Vec<ObjectPropertyExpression> {
    if index < roles.len() {
        if out.len() < usize::MAX {
            out.push(copy_role(&roles[index]));
        }
        copied(roles, index + 1, out)
    } else {
        out
    }
}
/// The inverses of the roles of `roles[..count]`, last first, copied onto
/// `out`.
fn reversed(
    roles: &Vec<ObjectPropertyExpression>,
    count: usize,
    mut out: Vec<ObjectPropertyExpression>,
) -> Vec<ObjectPropertyExpression> {
    if 0 < count {
        if count - 1 < roles.len() {
            if out.len() < usize::MAX {
                out.push(inverse(&roles[count - 1]));
            }
        }
        reversed(roles, count - 1, out)
    } else {
        out
    }
}
/// Whether every chain of `chains[index..]` has at least two roles.
fn long_from(chains: &Vec<Chain>, index: usize) -> bool {
    if index < chains.len() {
        if chains[index].roles.len() < 2 {
            false
        } else {
            long_from(chains, index + 1)
        }
    } else {
        true
    }
}
/// Whether no disjoint pair of `roles.disjoint[index..]` has a complex role.
fn pairs_fit(roles: &RoleHierarchy, chains: &Vec<Chain>, index: usize) -> bool {
    if index < roles.disjoint.len() {
        let pair = &roles.disjoint[index];
        if complex(roles, chains, &pair.left) {
            false
        } else if complex(roles, chains, &pair.right) {
            false
        } else {
            pairs_fit(roles, chains, index + 1)
        }
    } else {
        true
    }
}
/// Whether the concepts of `facts[index..]` fit.
fn facts_fit(roles: &RoleHierarchy, chains: &Vec<Chain>, facts: &Vec<Fact>, index: usize) -> bool {
    if index < facts.len() {
        if fits(roles, chains, &facts[index].concept) {
            facts_fit(roles, chains, facts, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// Whether the classes and concepts of `definitions[index..]` fit.
fn definitions_fit(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    definitions: &Vec<Definition>,
    index: usize,
) -> bool {
    if index < definitions.len() {
        if spaced(&definitions[index].class) {
            false
        } else if fits(roles, chains, &definitions[index].concept) {
            definitions_fit(roles, chains, definitions, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}
/// The encodings of the facts of `facts[index..]`, appended to `out`.
fn encode_facts(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    facts: &Vec<Fact>,
    index: usize,
    atoms: Vec<Atom>,
    bases: Vec<Concept>,
    mut out: Vec<Fact>,
) -> Option<(Vec<Atom>, Vec<Concept>, Vec<Fact>)> {
    if index < facts.len() {
        match encode(roles, chains, &facts[index].concept, true, atoms, bases) {
            Some((atoms, bases, concept)) => {
                if out.len() < usize::MAX {
                    out.push(Fact {
                        node: facts[index].node,
                        concept,
                    });
                    encode_facts(roles, chains, facts, index + 1, atoms, bases, out)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some((atoms, bases, out))
    }
}
/// The encodings of the definitions of `definitions[index..]`, appended to
/// `out`.
fn encode_definitions(
    roles: &RoleHierarchy,
    chains: &Vec<Chain>,
    definitions: &Vec<Definition>,
    index: usize,
    atoms: Vec<Atom>,
    bases: Vec<Concept>,
    mut out: Vec<Definition>,
) -> Option<(Vec<Atom>, Vec<Concept>, Vec<Definition>)> {
    if index < definitions.len() {
        match encode(
            roles,
            chains,
            &definitions[index].concept,
            true,
            atoms,
            bases,
        ) {
            Some((atoms, bases, concept)) => {
                if out.len() < usize::MAX {
                    out.push(Definition {
                        class: Class {
                            iri: copy_iri(&definitions[index].class.iri),
                        },
                        concept,
                    });
                    encode_definitions(roles, chains, definitions, index + 1, atoms, bases, out)
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        Some((atoms, bases, out))
    }
}
/// Satisfiability as `forest::satisfiable` decides it, with the chains as
/// further role axioms: whether some model of the role hierarchy, its disjoint
/// pairs and the chains satisfies the TBox concept everywhere, the definitions,
/// and the facts and links at the elements of their nodes.
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
    if chains.len() == 0 {
        return forest::satisfiable(count, query, facts, links, axioms, definitions, roles);
    }
    if !long_from(chains, 0) {
        return None;
    }
    let chains = match copy_chains(chains, false, 0, Vec::new()) {
        Some(copies) => match copy_chains(chains, true, 0, copies) {
            Some(all) => all,
            None => return None,
        },
        None => return None,
    };
    if !pairs_fit(roles, &chains, 0) {
        return None;
    }
    if !fits(roles, &chains, axioms) {
        return None;
    }
    if !facts_fit(roles, &chains, query, 0) {
        return None;
    }
    if !facts_fit(roles, &chains, facts, 0) {
        return None;
    }
    if !definitions_fit(roles, &chains, definitions, 0) {
        return None;
    }
    let (atoms, bases, axioms) = match encode(roles, &chains, axioms, true, Vec::new(), Vec::new())
    {
        Some(triple) => triple,
        None => return None,
    };
    let (atoms, bases, query) =
        match encode_facts(roles, &chains, query, 0, atoms, bases, Vec::new()) {
            Some(triple) => triple,
            None => return None,
        };
    let (atoms, bases, facts) =
        match encode_facts(roles, &chains, facts, 0, atoms, bases, Vec::new()) {
            Some(triple) => triple,
            None => return None,
        };
    let (atoms, bases, definitions) =
        match encode_definitions(roles, &chains, definitions, 0, atoms, bases, Vec::new()) {
            Some(triple) => triple,
            None => return None,
        };
    let (_, definitions) = match generate(roles, &chains, &bases, atoms, 0, definitions) {
        Some(pair) => pair,
        None => return None,
    };
    forest::satisfiable(count, &query, &facts, links, &axioms, &definitions, roles)
}
