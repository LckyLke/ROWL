use rowl_kernel::probes::{add, decimal_digit, lookup, replace_slot, Catalog, Natural};

fn natural(value: usize) -> Natural {
    let mut result = Natural::Zero;
    for _ in 0..value {
        result = Natural::Succ(Box::new(result));
    }
    result
}

fn value(natural: &Natural) -> usize {
    match natural {
        Natural::Zero => 0,
        Natural::Succ(predecessor) => 1 + value(predecessor),
    }
}

#[test]
fn exact_sum_crosses_byte_integer_boundary() {
    assert_eq!(value(&add(&natural(255), natural(2))), 257);
    assert_eq!(value(&add(&natural(0), natural(12))), 12);
}

#[test]
fn arena_update_preserves_other_slots_and_rejects_stale_indices() {
    let mut slots = vec![4, 9, 7];
    assert!(replace_slot(&mut slots, 1, 42));
    assert_eq!(slots, vec![4, 42, 7]);
    assert!(!replace_slot(&mut slots, 3, 99));
    assert_eq!(slots, vec![4, 42, 7]);
    assert!(!replace_slot(&mut Vec::new(), 0, 99));
}

#[test]
fn digit_recognition_rejects_adjacent_bytes_and_unicode_bytes() {
    for (byte, expected) in [
        (b'/', None),
        (b'0', Some(0)),
        (b'9', Some(9)),
        (b':', None),
        (0xff, None),
    ] {
        assert_eq!(decimal_digit(byte), expected);
    }
}

#[test]
fn catalog_lookup_returns_bytes_without_mutation_and_reports_absence() {
    let catalog = Catalog::Entry {
        key: 3,
        bytes: vec![0, 0xff, b'x'],
        next: Box::new(Catalog::Entry {
            key: 7,
            bytes: vec![b'y'],
            next: Box::new(Catalog::Empty),
        }),
    };
    assert_eq!(lookup(&catalog, 7), Some(&vec![b'y']));
    assert_eq!(lookup(&catalog, 3), Some(&vec![0, 0xff, b'x']));
    assert_eq!(lookup(&catalog, 42), None);
    assert_eq!(lookup(&catalog, 3), Some(&vec![0, 0xff, b'x']));
}
