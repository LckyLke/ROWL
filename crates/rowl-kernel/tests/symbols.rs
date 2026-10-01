use rowl_kernel::symbols::{empty, intern, key_of, lookup, same_spelling, InternResult};
use std::collections::BTreeMap;

#[test]
fn byte_equality_preserves_all_bytes_and_exact_length() {
    assert!(same_spelling(&vec![], &vec![]));
    let all: Vec<u8> = (0..=255).collect();
    assert!(same_spelling(&all, &all.clone()));
    for i in 0..all.len() {
        let mut changed = all.clone();
        changed[i] ^= 1;
        assert!(!same_spelling(&all, &changed));
    }
    for i in 0..all.len() {
        assert!(!same_spelling(&all, &all[..i].to_vec()));
        assert!(!same_spelling(&all[..i].to_vec(), &all));
    }
}

#[test]
fn repeated_spelling_reuses_first_symbol_and_original_borrow() {
    let first = b"urn:maintenance:FaultyPart".to_vec();
    let same = first.clone();
    let other = b"urn:maintenance:Machine".to_vec();
    let (result, table) = intern(empty(2), &first);
    assert!(matches!(result, InternResult::Inserted(0)));
    let (result, table) = intern(table, &other);
    assert!(matches!(result, InternResult::Inserted(1)));
    let (result, table) = intern(table, &same);
    assert!(matches!(result, InternResult::Existing(0)));
    assert_eq!(lookup(&table, &same), Some(0));
    assert!(std::ptr::eq(key_of(&table, 0).unwrap(), &first));
    assert!(std::ptr::eq(key_of(&table, 1).unwrap(), &other));
    assert_eq!(key_of(&table, 2), None);
    assert_eq!(key_of(&table, u32::MAX), None);
}

#[test]
fn capacity_errors_preserve_table_and_existing_keys_still_work() {
    let a = b"urn:a".to_vec();
    let b = b"urn:b".to_vec();
    let (result, table) = intern(empty(0), &a);
    assert!(matches!(result, InternResult::CapacityExceeded));
    assert_eq!(lookup(&table, &a), None);
    assert_eq!(key_of(&table, 0), None);
    let (result, table) = intern(empty(1), &a);
    assert!(matches!(result, InternResult::Inserted(0)));
    let (result, table) = intern(table, &b);
    assert!(matches!(result, InternResult::CapacityExceeded));
    assert_eq!(lookup(&table, &b), None);
    assert_eq!(key_of(&table, 0), Some(&a));
    let (result, table) = intern(table, &a);
    assert!(matches!(result, InternResult::Existing(0)));
    assert_eq!(key_of(&table, 0), Some(&a));
}

#[test]
fn lexical_variants_are_distinct_without_normalization() {
    let keys: Vec<Vec<u8>> = [
        "http://example.org/A",
        "http://example.org/a",
        "http://example.org/%41",
        "http://example.org/é",
        "http://example.org/e\u{301}",
        "urn:x\0",
        "urn:x",
        "",
    ]
    .iter()
    .map(|s| s.as_bytes().to_vec())
    .chain([vec![255]])
    .collect();
    let mut table = empty(keys.len() as u32);
    for (i, key) in keys.iter().enumerate() {
        let (result, after) = intern(table, key);
        assert!(matches!(result, InternResult::Inserted(symbol) if symbol == i as u32));
        table = after;
    }
    for (i, key) in keys.iter().enumerate() {
        assert_eq!(lookup(&table, key), Some(i as u32));
        assert_eq!(key_of(&table, i as u32), Some(key));
    }
    // This is a raw byte-key table. UTF-8/IRI validity is a separate stage.
}

#[test]
fn insertion_history_matches_an_independent_ordered_map_oracle() {
    let keys: Vec<Vec<u8>> = (0u32..500)
        .map(|i| (i.wrapping_mul(73) % 127).to_le_bytes().to_vec())
        .collect();
    let mut expected: BTreeMap<Vec<u8>, u32> = BTreeMap::new();
    let mut table = empty(127);
    for key in &keys {
        let next = expected.len() as u32;
        let existed = expected.get(key).copied();
        let symbol = *expected.entry(key.clone()).or_insert(next);
        let (result, after) = intern(table, key);
        assert!(match result {
            InternResult::Existing(actual) => existed == Some(actual),
            InternResult::Inserted(actual) => existed.is_none() && actual == symbol,
            InternResult::CapacityExceeded => false,
        });
        table = after;
        for (old_key, old_symbol) in &expected {
            assert_eq!(lookup(&table, old_key), Some(*old_symbol));
            assert_eq!(key_of(&table, *old_symbol), Some(old_key));
        }
    }
}
