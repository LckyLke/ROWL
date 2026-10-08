//! The length facets `xsd:length`, `xsd:minLength` and `xsd:maxLength` (OWL 2
//! Structural Specification §4.3-§4.6, `rdf:PlainLiteral` §4, XML Schema 1.1
//! Part 2 §4.3.1-§4.3.3): the length of a string, of the string of a plain
//! literal with a language tag and of an IRI is its number of characters, and
//! that of the octets of `xsd:hexBinary` and `xsd:base64Binary` their number.
//!
//! The values of each length are counted by finite automata whose letters fall
//! into atoms, finite sets of known sizes. The XML characters fall into nine
//! atoms: tab, line feed and carriage return; the space; `:`; the ASCII
//! letters; the ASCII digits; `-`; the other characters that may start an XML
//! name; the other characters that may continue one; and the other XML
//! characters. The automaton of the strings is the product of five small ones
//! (`next_text`) that follow whether a string so far has a tab, a line feed
//! or a carriage return; where its spaces are; whether its characters are
//! name characters and its first a name start character; whether it has a
//! `:`; and how far it is a language tag `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*`.
//! A string's state tells the rank of the deepest subtype of `xsd:string` that
//! the string is in (`rank`): `xsd:string` 0, `xsd:normalizedString` 1,
//! `xsd:token` 2, `xsd:NMTOKEN` 3, `xsd:Name` 4, `xsd:NCName` 5 and
//! `xsd:language` 6. The octet sequences have an automaton of one state and one
//! atom of the 256 octets.
//!
//! `slot_size` counts the words with lengths from `low` on and before `high`
//! that the automaton takes from its first state to a state of a rank from
//! `first` on and before `last` (every state for the octets), capped at `cap`:
//! the capped numbers of the words of each length from each state follow
//! from those one letter shorter, and once they repeat they stay. `None` when
//! they do not repeat within `SETTLE` lengths.
#![allow(
    clippy::ptr_arg,
    clippy::manual_range_contains,
    clippy::len_zero,
    clippy::needless_return,
    clippy::if_same_then_else,
    clippy::too_many_arguments,
    clippy::implicit_saturating_sub
)] // Indexed operations and explicit branches for the pinned extraction subset.

use crate::datatypes::DataValue;

/// The lengths that facets may bound: below a sixteenth of the `usize` range.
pub const LENGTHS: usize = usize::MAX / 16;

/// The number `value` followed by the ASCII digits `digits[index..]`, if it
/// stays below `LENGTHS`.
fn digits_value(digits: &Vec<u8>, index: usize, value: usize) -> Option<usize> {
    if index < digits.len() {
        if (48 <= digits[index]) & (digits[index] <= 57) & (value < LENGTHS / 10) {
            digits_value(
                digits,
                index + 1,
                value * 10 + (digits[index] - 48) as usize,
            )
        } else {
            None
        }
    } else if value < LENGTHS {
        Some(value)
    } else {
        None
    }
}

/// The bound of a length facet whose constraining value is a natural number
/// below `LENGTHS`.
pub fn length_bound(value: &DataValue) -> Option<usize> {
    match value {
        DataValue::Number(negative, digits, fraction) => {
            if !*negative & (fraction.len() == 0) {
                digits_value(digits, 0, 0)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `count` plus the number of the bytes of `bytes[index..]` that start a
/// character of UTF-8 text: those that are no continuation byte.
fn characters_from(bytes: &Vec<u8>, index: usize, count: usize) -> usize {
    if index < bytes.len() {
        if (bytes[index] < 128) | (192 <= bytes[index]) {
            characters_from(bytes, index + 1, count + 1)
        } else {
            characters_from(bytes, index + 1, count)
        }
    } else {
        count
    }
}

/// The length of a value of the string datatypes, of `rdf:PlainLiteral`, of
/// `xsd:anyURI` or of the binary datatypes: its characters or its octets.
pub fn value_length(value: &DataValue) -> Option<usize> {
    match value {
        DataValue::Text(bytes) => Some(characters_from(bytes, 0, 0)),
        DataValue::Tagged(bytes, _) => Some(characters_from(bytes, 0, 0)),
        DataValue::Uri(bytes) => Some(characters_from(bytes, 0, 0)),
        DataValue::Hex(octets) => Some(octets.len()),
        DataValue::Base64(octets) => Some(octets.len()),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The automaton of the strings
// ---------------------------------------------------------------------------

/// The state of the breaks after an atom: 0 without a tab, line feed or
/// carriage return, 1 with one.
fn next_breaks(state: usize, atom: usize) -> usize {
    if atom == 0 {
        1
    } else {
        state
    }
}
/// The state of the spaces after an atom: 0 for the empty string, 1 after a
/// character other than a space, 2 after a space, and 3 once a space came
/// first or two spaces in a row.
fn next_spaces(state: usize, atom: usize) -> usize {
    if state == 3 {
        3
    } else if atom == 1 {
        if state == 1 {
            2
        } else {
            3
        }
    } else {
        1
    }
}
/// Whether the atom holds name characters.
fn name_atom(atom: usize) -> bool {
    (2 <= atom) & (atom <= 7)
}
/// Whether the atom holds name start characters.
fn start_atom(atom: usize) -> bool {
    (atom == 2) | (atom == 3) | (atom == 6)
}
/// The state of the names after an atom: 0 for the empty string, 1 for name
/// characters after a first one that does not start a name, 2 for name
/// characters after a first one that does, and 3 once another character came.
fn next_names(state: usize, atom: usize) -> usize {
    if !name_atom(atom) {
        3
    } else if state == 0 {
        if start_atom(atom) {
            2
        } else {
            1
        }
    } else {
        state
    }
}
/// The state of the colons after an atom: 0 without `:`, 1 with one.
fn next_colons(state: usize, atom: usize) -> usize {
    if atom == 2 {
        1
    } else {
        state
    }
}
/// The state of the language tag after an atom: from 0 to 8 the characters of
/// its first subtag so far, from 9 to 17 nine more than those of a later
/// subtag after its `-`, and 18 once it is no language tag.
fn next_tag(state: usize, atom: usize) -> usize {
    if 18 <= state {
        18
    } else if atom == 5 {
        if (state == 0) | (state == 9) {
            18
        } else {
            9
        }
    } else if (atom == 3) | ((atom == 4) & (9 <= state)) {
        if (state == 8) | (state == 17) {
            18
        } else {
            state + 1
        }
    } else {
        18
    }
}

/// The number of states of the automaton of the strings.
pub const TEXT_STATES: usize = 1216;

/// The state of the automaton of the strings after an atom: the five states
/// of breaks, spaces, names, colons and the language tag, written
/// `(((breaks · 4 + spaces) · 4 + names) · 2 + colons) · 19 + tag`.
fn next_text(state: usize, atom: usize) -> usize {
    let tag = state % 19;
    let rest = state / 19;
    let colons = rest % 2;
    let rest = rest / 2;
    let names = rest % 4;
    let rest = rest / 4;
    let spaces = rest % 4;
    let breaks = rest / 4;
    (((next_breaks(breaks, atom) * 4 + next_spaces(spaces, atom)) * 4 + next_names(names, atom))
        * 2
        + next_colons(colons, atom))
        * 19
        + next_tag(tag, atom)
}

/// The rank of the deepest subtype of `xsd:string` that the strings of a state
/// of the automaton are in.
pub fn rank(state: usize) -> u8 {
    let tag = state % 19;
    let rest = state / 19;
    let colons = rest % 2;
    let rest = rest / 2;
    let names = rest % 4;
    let rest = rest / 4;
    let spaces = rest % 4;
    let breaks = rest / 4;
    if breaks != 0 {
        0
    } else if 1 < spaces {
        1
    } else if (names == 0) | (names == 3) {
        2
    } else if names == 1 {
        3
    } else if colons != 0 {
        4
    } else if (tag == 0) | (tag == 9) | (tag == 18) {
        5
    } else {
        6
    }
}

// ---------------------------------------------------------------------------
// Counting
// ---------------------------------------------------------------------------

/// The number of states: of the octets (`octets`), or of the strings.
fn states(octets: bool) -> usize {
    if octets {
        1
    } else {
        TEXT_STATES
    }
}
/// The number of atoms.
fn atoms(octets: bool) -> usize {
    if octets {
        1
    } else {
        9
    }
}
/// The number of letters of an atom.
fn atom_size(octets: bool, atom: usize) -> usize {
    if octets {
        256
    } else if atom == 0 {
        3
    } else if atom == 1 {
        1
    } else if atom == 2 {
        1
    } else if atom == 3 {
        52
    } else if atom == 4 {
        10
    } else if atom == 5 {
        1
    } else if atom == 6 {
        971453
    } else if atom == 7 {
        116
    } else {
        140396
    }
}
/// The state after an atom.
fn next_state(octets: bool, state: usize, atom: usize) -> usize {
    if octets {
        0
    } else {
        next_text(state, atom)
    }
}
/// Whether a state ends the counted words: every state of the octets, and the
/// states of the strings of a rank from `first` on and before `last`.
fn accepts(octets: bool, first: u8, last: u8, state: usize) -> bool {
    if octets {
        true
    } else {
        let rank = rank(state);
        (first <= rank) & (rank < last)
    }
}

/// `left + right`, or `cap` when that is not less.
pub fn capped_sum(left: usize, right: usize, cap: usize) -> usize {
    if left < cap {
        if right < cap - left {
            left + right
        } else {
            cap
        }
    } else {
        cap
    }
}
/// `left · right`, or `cap` when that is not less.
pub fn capped_product(left: usize, right: usize, cap: usize) -> usize {
    if (left == 0) | (right == 0) | (cap == 0) {
        0
    } else if right <= (cap - 1) / left {
        left * right
    } else {
        cap
    }
}

/// `total` plus the capped numbers of the words one letter longer than those
/// counted by `counts` that start with a letter of the atoms from `atom` on
/// from `state`, capped.
fn state_step(
    octets: bool,
    counts: &Vec<usize>,
    cap: usize,
    state: usize,
    atom: usize,
    total: usize,
) -> usize {
    if atom < atoms(octets) {
        let target = next_state(octets, state, atom);
        let words = if target < counts.len() {
            counts[target]
        } else {
            0
        };
        state_step(
            octets,
            counts,
            cap,
            state,
            atom + 1,
            capped_sum(
                total,
                capped_product(atom_size(octets, atom), words, cap),
                cap,
            ),
        )
    } else {
        total
    }
}
/// `out` with the capped numbers of the words one letter longer than those
/// counted by `counts` from the states from `state` on.
fn step_from(
    octets: bool,
    counts: &Vec<usize>,
    cap: usize,
    state: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if state < states(octets) {
        let value = state_step(octets, counts, cap, state, 0, 0);
        if out.len() < usize::MAX {
            out.push(value);
        }
        step_from(octets, counts, cap, state + 1, out)
    } else {
        out
    }
}
/// `out` with the capped numbers of the empty words from the states from
/// `state` on: one at a state that ends the counted words.
fn initial_from(
    octets: bool,
    first: u8,
    last: u8,
    cap: usize,
    state: usize,
    mut out: Vec<usize>,
) -> Vec<usize> {
    if state < states(octets) {
        let value = if accepts(octets, first, last, state) {
            capped_sum(0, 1, cap)
        } else {
            0
        };
        if out.len() < usize::MAX {
            out.push(value);
        }
        initial_from(octets, first, last, cap, state + 1, out)
    } else {
        out
    }
}
/// Whether `left[index..]` and `right[index..]` are the same.
fn same_counts(left: &Vec<usize>, right: &Vec<usize>, index: usize) -> bool {
    if index < left.len() {
        if index < right.len() {
            (left[index] == right[index]) && same_counts(left, right, index + 1)
        } else {
            false
        }
    } else {
        right.len() <= index
    }
}

/// How many lengths the capped numbers may take to repeat.
pub const SETTLE: usize = 64;

/// `total` plus the capped number of the counted words with lengths from
/// `low` on and before `high`, from `length` on, that start in the first
/// state, where `counts` are the capped numbers of the counted words of length
/// `length` from each state; `None` when the numbers do not repeat within
/// `fuel` more lengths.
fn words_from(
    octets: bool,
    cap: usize,
    counts: Vec<usize>,
    length: usize,
    low: usize,
    high: usize,
    total: usize,
    fuel: usize,
) -> Option<usize> {
    if high <= length {
        Some(total)
    } else {
        let here = if 0 < counts.len() { counts[0] } else { 0 };
        let next = step_from(octets, &counts, cap, 0, Vec::new());
        if same_counts(&next, &counts, 0) {
            let from = if low < length { length } else { low };
            let rest = if from < high { high - from } else { 0 };
            Some(capped_sum(total, capped_product(rest, here, cap), cap))
        } else if fuel == 0 {
            None
        } else {
            let total = if low <= length {
                capped_sum(total, here, cap)
            } else {
                total
            };
            words_from(octets, cap, next, length + 1, low, high, total, fuel - 1)
        }
    }
}

/// The number of the words with lengths from `low` on and before `high` that
/// the automaton of the octets (`octets`), or of the strings, takes from its
/// first state to a state that ends the counted words (of the ranks from
/// `first` on and before `last` for the strings), or `cap` when that is not
/// less; `None` when the capped numbers of the lengths do not repeat within
/// `SETTLE` lengths.
pub fn slot_size(
    octets: bool,
    first: u8,
    last: u8,
    low: usize,
    high: usize,
    cap: usize,
) -> Option<usize> {
    let counts = initial_from(octets, first, last, cap, 0, Vec::new());
    words_from(octets, cap, counts, 0, low, high, 0, SETTLE)
}
