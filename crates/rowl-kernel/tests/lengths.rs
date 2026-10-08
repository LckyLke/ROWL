use rowl_kernel::datatypes::DataValue;
use rowl_kernel::lengths::{length_bound, slot_size, value_length};

const BIG: usize = 1 << 40;

#[test]
fn octet_sequences_are_counted_by_length() {
    assert_eq!(slot_size(true, 0, 0, 0, 1, BIG), Some(1));
    assert_eq!(slot_size(true, 0, 0, 1, 2, BIG), Some(256));
    assert_eq!(slot_size(true, 0, 0, 0, 3, BIG), Some(1 + 256 + 65536));
    // Counts are capped.
    assert_eq!(slot_size(true, 0, 0, 2, 3, 1000), Some(1000));
}

#[test]
fn strings_are_counted_by_rank() {
    // The empty string is a token, but no NMTOKEN.
    assert_eq!(slot_size(false, 0, 7, 0, 1, BIG), Some(1));
    assert_eq!(slot_size(false, 2, 3, 0, 1, BIG), Some(1));
    // Tab, line feed and carriage return are the strings of one character
    // that are no normalized strings.
    assert_eq!(slot_size(false, 0, 1, 1, 2, BIG), Some(3));
    // 52 language tags of one letter.
    assert_eq!(slot_size(false, 6, 7, 1, 2, BIG), Some(52));
    // `:` is the only name of one character that is no NCName.
    assert_eq!(slot_size(false, 4, 5, 1, 2, BIG), Some(1));
}

#[test]
fn values_have_lengths() {
    // A string's length is its number of characters, that of binary data its
    // number of octets.
    assert_eq!(
        value_length(&DataValue::Text("äöü".as_bytes().to_vec())),
        Some(3)
    );
    assert_eq!(value_length(&DataValue::Hex(vec![10, 11])), Some(2));
    assert_eq!(value_length(&DataValue::Truth(true)), None);
    // Bounds are natural numbers.
    assert_eq!(
        length_bound(&DataValue::Number(false, b"12".to_vec(), Vec::new())),
        Some(12)
    );
    assert_eq!(
        length_bound(&DataValue::Number(true, b"12".to_vec(), Vec::new())),
        None
    );
    assert_eq!(
        length_bound(&DataValue::Number(false, b"1".to_vec(), b"5".to_vec())),
        None
    );
}
