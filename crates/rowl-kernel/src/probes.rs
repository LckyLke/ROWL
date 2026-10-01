//! Remaining M1 feasibility probes. These are primitives, not an OWL frontend
//! or a datatype solver. Their precise contracts are checked after extraction.

/// A mathematically unbounded natural number used in correctness experiments.
/// This unary representation prioritizes simple proofs, not efficient storage.
pub enum Natural {
    Zero,
    Succ(Box<Natural>),
}

/// An exact sum: no machine-integer arithmetic or overflow is involved.
pub fn add(left: &Natural, right: Natural) -> Natural {
    match left {
        Natural::Zero => right,
        Natural::Succ(predecessor) => Natural::Succ(Box::new(add(predecessor, right))),
    }
}

/// Replace one arena slot through a mutable borrow. A stale index returns false
/// and preserves the complete vector instead of panicking.
#[allow(clippy::ptr_arg)] // This feasibility probe specifically checks the Vec borrow model.
pub fn replace_slot(slots: &mut Vec<u32>, index: usize, value: u32) -> bool {
    if index < slots.len() {
        slots[index] = value;
        true
    } else {
        false
    }
}

/// Recognize an ASCII decimal digit. This is a lexical primitive only;
/// an arbitrary byte sequence is never treated as a parsed OWL document.
#[allow(clippy::manual_range_contains)] // Keep comparisons explicit for extraction.
pub fn decimal_digit(byte: u8) -> Option<u8> {
    if byte >= b'0' && byte <= b'9' {
        Some(byte - b'0')
    } else {
        None
    }
}

/// A prototype catalog indexed by opaque document identifiers. The actual
/// IRI catalog, duplicate-document policy and import closure belong to M3.
pub enum Catalog {
    Empty,
    Entry {
        key: u32,
        bytes: Vec<u8>,
        next: Box<Catalog>,
    },
}

/// Return the first matching document's exact bytes without modifying catalog.
pub fn lookup(catalog: &Catalog, key: u32) -> Option<&Vec<u8>> {
    match catalog {
        Catalog::Empty => None,
        Catalog::Entry {
            key: entry_key,
            bytes,
            next,
        } => {
            if key == *entry_key {
                Some(bytes)
            } else {
                lookup(next, key)
            }
        }
    }
}
