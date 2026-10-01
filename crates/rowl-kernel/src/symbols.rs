//! Exact byte-key interning for future verified lexical stages.
//!
//! Keys are borrowed unchanged; equality uses our own checked byte traversal.
//! This primitive does not validate UTF-8/IRIs, resolve prefixes or normalize
//! spellings. Raw IRI spellings use the same byte representation; lexical validity is
//! a separate obligation. Tables are created only by `empty`, then consumed by `intern`.
#![allow(clippy::ptr_arg)] // Use the Vec primitives covered by the pinned extraction.

pub struct SymbolTable<'a> {
    keys: Vec<&'a Vec<u8>>,
    limit: u32,
}

pub enum InternResult {
    Existing(u32),
    Inserted(u32),
    CapacityExceeded,
}

/// The caller selects a symbol-count budget. Zero is a valid empty budget.
pub fn empty<'a>(limit: u32) -> SymbolTable<'a> {
    SymbolTable {
        keys: Vec::new(),
        limit,
    }
}

fn compare_from(left: &Vec<u8>, right: &Vec<u8>, index: usize) -> bool {
    if index < left.len() {
        if left[index] == right[index] {
            compare_from(left, right, index + 1)
        } else {
            false
        }
    } else {
        true
    }
}

/// Exact equality of two arbitrary byte sequences; no hashing or normalization.
pub fn same_spelling(left: &Vec<u8>, right: &Vec<u8>) -> bool {
    if left.len() == right.len() {
        compare_from(left, right, 0)
    } else {
        false
    }
}

fn find_from(keys: &Vec<&Vec<u8>>, key: &Vec<u8>, index: usize) -> Option<u32> {
    if index < keys.len() {
        if same_spelling(keys[index], key) {
            Some(index as u32)
        } else {
            find_from(keys, key, index + 1)
        }
    } else {
        None
    }
}

/// Look up an exact spelling without modifying the table.
pub fn lookup(table: &SymbolTable<'_>, key: &Vec<u8>) -> Option<u32> {
    find_from(&table.keys, key, 0)
}

/// Recover the originally stored byte vector, or None for an unknown symbol.
pub fn key_of<'a>(table: &SymbolTable<'a>, symbol: u32) -> Option<&'a Vec<u8>> {
    let index = symbol as usize;
    if index < table.keys.len() {
        Some(table.keys[index])
    } else {
        None
    }
}

/// Existing keys work even at capacity. Insertion appends a fresh zero-based
/// symbol; a rejected insertion preserves the complete table.
pub fn intern<'a>(mut table: SymbolTable<'a>, key: &'a Vec<u8>) -> (InternResult, SymbolTable<'a>) {
    match lookup(&table, key) {
        Some(symbol) => (InternResult::Existing(symbol), table),
        None => {
            let count = table.keys.len() as u32;
            if count < table.limit {
                table.keys.push(key);
                (InternResult::Inserted(count), table)
            } else {
                (InternResult::CapacityExceeded, table)
            }
        }
    }
}
