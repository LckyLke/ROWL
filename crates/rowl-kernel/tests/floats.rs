use rowl_kernel::datatypes::Binary;
use rowl_kernel::floats::{binary_value, high_position, low_position, places, position, BIAS};

/// The canonical form of a finite floating-point value: its sign, odd
/// significand (zero for the zeros) and exponent of 2.
fn canonical(negative: bool, mut m: u64, mut e: i64) -> (bool, u64, i64) {
    if m == 0 {
        return (negative, 0, 0);
    }
    while m.is_multiple_of(2) {
        m /= 2;
        e += 1;
    }
    (negative, m, e)
}

/// The value of a `Binary` in that form, `None` for the infinities and NaN.
fn finite_of(value: &Binary) -> Option<(bool, u64, i64)> {
    match value {
        Binary::Finite(negative, m, scale) => {
            let e = if *m == 0 {
                0
            } else {
                *scale as i64 - BIAS as i64
            };
            Some((*negative, *m, e))
        }
        _ => None,
    }
}

fn double_form(x: f64) -> Option<(bool, u64, i64)> {
    if !x.is_finite() {
        return None;
    }
    let bits = x.to_bits();
    let negative = bits >> 63 == 1;
    let exponent = ((bits >> 52) & 0x7ff) as i64;
    let fraction = bits & ((1u64 << 52) - 1);
    if exponent == 0 {
        Some(canonical(negative, fraction, -1074))
    } else {
        Some(canonical(
            negative,
            fraction | (1u64 << 52),
            exponent - 1075,
        ))
    }
}

fn float_form(x: f32) -> Option<(bool, u64, i64)> {
    if !x.is_finite() {
        return None;
    }
    let bits = x.to_bits();
    let negative = bits >> 31 == 1;
    let exponent = ((bits >> 23) & 0xff) as i64;
    let fraction = (bits & ((1u32 << 23) - 1)) as u64;
    if exponent == 0 {
        Some(canonical(negative, fraction, -149))
    } else {
        Some(canonical(negative, fraction | (1u64 << 23), exponent - 150))
    }
}

/// Our value of a numeral agrees with Rust's correctly rounded parsing.
fn agrees(text: &str) {
    let double = binary_value(&text.as_bytes().to_vec(), true).unwrap_or_else(|| panic!("{text}"));
    let expected: f64 = text.parse().unwrap();
    match double_form(expected) {
        Some(form) => assert_eq!(finite_of(&double), Some(form), "double {text}"),
        None => assert!(
            matches!(double, Binary::Infinite(n) if n == expected.is_sign_negative()),
            "double {text}"
        ),
    }
    let float = binary_value(&text.as_bytes().to_vec(), false).unwrap_or_else(|| panic!("{text}"));
    let expected: f32 = text.parse().unwrap();
    match float_form(expected) {
        Some(form) => assert_eq!(finite_of(&float), Some(form), "float {text}"),
        None => assert!(
            matches!(float, Binary::Infinite(n) if n == expected.is_sign_negative()),
            "float {text}"
        ),
    }
}

#[test]
fn numerals_round_to_the_nearest_value_ties_to_even() {
    for text in [
        "0",
        "1",
        "-1",
        "+1",
        "1.5",
        "3.14",
        "0.1",
        "-0.1",
        ".5",
        "5.",
        "-.25e3",
        "1e10",
        "1E10",
        "1e+10",
        "1e-10",
        "123456789012345678901234567890",
        "9007199254740992",
        "9007199254740993",
        "9007199254740995",
        "9007199254740994",
        "16777216",
        "16777217",
        "16777219",
        "2.2250738585072011e-308",
        "2.2250738585072014e-308",
        "4.9406564584124654e-324",
        "2.4703282292062327e-324",
        "2.4703282292062328e-324",
        "1.7976931348623157e308",
        "1.7976931348623158e308",
        "1.7976931348623159e308",
        "1e308",
        "1e309",
        "1e-400",
        "-1e-400",
        "3.4028234663852886e38",
        "3.4028235677973366e38",
        "3.4028236e38",
        "1.401298464324817e-45",
        "7.006492321624085e-46",
        "7.006492321624086e-46",
        "1.1754943508222875e-38",
        "0.000000000000000000000000000000000000000000000000001",
        "1e00000000000000000000000000000000005",
        "1e-0000000000000000000000000000000000002",
        "0.30000000000000004",
        "123.456e-7",
        "99999999999999999999999999999999999999999999999999e-30",
    ] {
        agrees(text);
    }
}

#[test]
fn pseudo_random_numerals_agree() {
    // A linear congruential generator, so that the cases are the same in every run.
    let mut state: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = |bound: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % bound
    };
    for _ in 0..3000 {
        let digits = 1 + next(30) as usize;
        let mut text = String::new();
        if next(2) == 1 {
            text.push('-');
        }
        let point = next(digits as u64 + 1) as usize;
        for i in 0..digits {
            if i == point && i > 0 {
                text.push('.');
            }
            text.push(char::from(b'0' + next(10) as u8));
        }
        if next(3) > 0 {
            let exponent = next(700) as i64 - 360;
            text.push('e');
            text.push_str(&exponent.to_string());
        }
        agrees(&text);
    }
}

#[test]
fn the_special_values_and_the_signed_zeros() {
    let read = |text: &str, double: bool| binary_value(&text.as_bytes().to_vec(), double);
    assert!(matches!(read("INF", true), Some(Binary::Infinite(false))));
    assert!(matches!(read("+INF", true), Some(Binary::Infinite(false))));
    assert!(matches!(read("-INF", false), Some(Binary::Infinite(true))));
    assert!(matches!(read("NaN", true), Some(Binary::NotANumber)));
    for bad in [
        "-NaN", "+NaN", "inf", "nan", "Infinity", "", ".", "+", "-", "e5", "1e", "1e+", "1.5.2",
        "--1", "+-1", " 1", "1 ", "1,5", "0x10", "1e5.5", "1d5",
    ] {
        assert!(read(bad, true).is_none(), "{bad}");
        assert!(read(bad, false).is_none(), "{bad}");
    }
    // The two zeros are two values, and an underflow keeps the sign.
    assert_eq!(
        read("0", true).as_ref().and_then(finite_of),
        Some((false, 0, 0))
    );
    assert_eq!(
        read("-0", true).as_ref().and_then(finite_of),
        Some((true, 0, 0))
    );
    assert_eq!(
        read("-0.0e10", false).as_ref().and_then(finite_of),
        Some((true, 0, 0))
    );
    assert_eq!(
        read("-1e-999", true).as_ref().and_then(finite_of),
        Some((true, 0, 0))
    );
    // A lexical form of a thousand bytes or more gets no value.
    let long = "1".repeat(1024);
    assert!(read(&long, true).is_none());
}

/// The place of a value of a format in the order of XML Schema 1.1 Part 2,
/// section 3.3.5: NaN first, then the IEEE bit pattern of the magnitude
/// counted down from `-0` for the negative values and up from `+0` for the
/// others, so that the infinities are at the ends and the two zeros side by
/// side.
fn expected_place(top: u128, negative: bool, magnitude: u128) -> u128 {
    if negative {
        top + 1 - magnitude
    } else {
        top + 2 + magnitude
    }
}

fn double_text(x: f64) -> String {
    if x.is_infinite() {
        if x < 0.0 { "-INF" } else { "INF" }.to_string()
    } else {
        format!("{x:e}")
    }
}

fn float_text(x: f32) -> String {
    if x.is_infinite() {
        if x < 0.0 { "-INF" } else { "INF" }.to_string()
    } else {
        format!("{x:e}")
    }
}

#[test]
fn places_follow_the_bit_patterns() {
    let read = |text: String, double: bool| binary_value(&text.into_bytes(), double).unwrap();
    let top_double: u128 = 0x7ff0_0000_0000_0000;
    let top_float: u128 = 0x7f80_0000;
    assert_eq!(places(true), 2 * top_double + 3);
    assert_eq!(places(false), 2 * top_float + 3);
    let mut doubles = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.1,
        -0.1,
        f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE,
        5e-324,
        -5e-324,
        2.225_073_858_507_201e-308,
        f64::MAX,
        f64::MIN,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ];
    let mut floats = vec![
        0.0f32,
        -0.0,
        1.0,
        -1.0,
        0.1,
        f32::MIN_POSITIVE,
        1e-45,
        -1e-45,
        f32::MAX,
        f32::MIN,
        f32::INFINITY,
        f32::NEG_INFINITY,
    ];
    // Pseudo-random bit patterns, the same in every run.
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    for _ in 0..2000 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let x = f64::from_bits(state);
        if !x.is_nan() {
            doubles.push(x);
        }
        let y = f32::from_bits((state >> 32) as u32);
        if !y.is_nan() {
            floats.push(y);
        }
    }
    for x in doubles {
        let place = expected_place(top_double, x.is_sign_negative(), x.abs().to_bits() as u128);
        assert_eq!(
            position(&read(double_text(x), true), true),
            place,
            "double {x:e}"
        );
    }
    for x in floats {
        let place = expected_place(top_float, x.is_sign_negative(), x.abs().to_bits() as u128);
        assert_eq!(
            position(&read(float_text(x), false), false),
            place,
            "float {x:e}"
        );
    }
    // NaN comes first, and the infinities are at the ends.
    assert_eq!(position(&read("NaN".to_string(), true), true), 0);
    assert_eq!(position(&read("-INF".to_string(), false), false), 1);
    assert_eq!(
        position(&read("INF".to_string(), false), false),
        places(false) - 1
    );
    // The places of the values equal to a value: both zeros for a zero, the
    // value's own place otherwise.
    for double in [true, false] {
        let top = if double { top_double } else { top_float };
        for zero in ["0", "-0"] {
            let value = read(zero.to_string(), double);
            assert_eq!(low_position(&value, double), top + 1);
            assert_eq!(high_position(&value, double), top + 2);
        }
        let one = read("1.5".to_string(), double);
        assert_eq!(low_position(&one, double), position(&one, double));
        assert_eq!(high_position(&one, double), position(&one, double));
    }
}
