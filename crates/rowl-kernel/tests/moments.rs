use rowl_kernel::datatypes::{DataValue, Moment};
use rowl_kernel::moments::{instant, instant_order, moment_value, zoned};

/// The kernel value of an `xsd:dateTime` lexical form.
fn moment(text: &str) -> Moment {
    match moment_value(&text.as_bytes().to_vec(), false) {
        Some(DataValue::Moment(m)) => m,
        _ => panic!("not a time instant: {text}"),
    }
}

/// The order of the places of two time instants on the time line: 0 before,
/// 1 at the same place, 2 after.
fn order(a: &str, b: &str) -> u8 {
    instant_order(&instant(&moment(a)), &instant(&moment(b)))
}

#[test]
fn instants_follow_the_time_line() {
    // One place at two offsets.
    assert_eq!(
        order("2024-01-01T10:00:00+02:00", "2024-01-01T08:00:00Z"),
        1
    );
    assert_eq!(
        order("2024-12-31T23:30:00-01:00", "2025-01-01T00:30:00Z"),
        1
    );
    assert_eq!(
        order("2024-03-01T00:10:00+14:00", "2024-02-29T10:10:00Z"),
        1
    );
    // Across midnight and the end of a year.
    assert_eq!(order("2024-01-01T00:00:00Z", "2023-12-31T23:59:59.999Z"), 2);
    // Leap days, long years and years before the common era.
    assert_eq!(order("2024-02-29T00:00:00", "2024-03-01T00:00:00"), 0);
    assert_eq!(order("2100-02-28T00:00:00", "2100-03-01T00:00:00"), 0);
    assert_eq!(order("12345-01-01T00:00:00", "9999-12-31T23:59:59"), 2);
    assert_eq!(order("-0001-12-31T00:00:00", "0000-01-01T00:00:00"), 0);
    // Fractions of a second.
    assert_eq!(order("2024-01-01T00:00:00.5", "2024-01-01T00:00:00.50"), 1);
    assert_eq!(order("2024-01-01T00:00:00.05", "2024-01-01T00:00:00.5"), 0);
    // 24:00:00 is the start of the next day.
    assert_eq!(order("2024-01-01T24:00:00", "2024-01-02T00:00:00"), 1);
}

#[test]
fn instants_keep_their_time_zones_apart() {
    assert!(zoned(&moment("2024-01-01T00:00:00Z")));
    assert!(zoned(&moment("2024-01-01T00:00:00-00:00")));
    assert!(!zoned(&moment("2024-01-01T00:00:00")));
    // The instant of a time stamp has no time zone.
    assert!(!zoned(&instant(&moment("2024-01-01T00:00:00+05:30"))));
    let moved = instant(&moment("2024-01-01T00:00:00+05:30"));
    assert_eq!(moved.year, b"2023".to_vec());
    assert_eq!(
        (
            moved.month,
            moved.day,
            moved.hour,
            moved.minute,
            moved.second
        ),
        (12, 31, 18, 30, 0)
    );
}
