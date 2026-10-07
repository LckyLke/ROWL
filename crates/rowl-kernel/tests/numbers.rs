use rowl_kernel::numbers::{
    add_naturals, canonical, compare_naturals, divide_naturals, gcd_naturals, multiply_naturals,
    subtract_naturals, ten_power, times_power,
};

fn digits(value: u128) -> Vec<u8> {
    if value == 0 {
        Vec::new()
    } else {
        value.to_string().into_bytes()
    }
}
fn value(digits: &[u8]) -> u128 {
    if digits.is_empty() {
        0
    } else {
        std::str::from_utf8(digits).unwrap().parse().unwrap()
    }
}
fn gcd(a: u128, b: u128) -> u128 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// A small deterministic generator of numbers of varied lengths.
fn samples() -> Vec<u128> {
    let mut out = vec![
        0, 1, 2, 5, 9, 10, 11, 99, 100, 101, 999, 1000, 1024, 4096, 99999,
    ];
    let mut state: u64 = 0x2545F4914F6CDD1D;
    for round in 0..60 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let modulus = 10u128.pow((round % 18) as u32 + 1);
        out.push(u128::from(state) % modulus);
    }
    out
}

#[test]
fn canonical_spellings_drop_leading_zeros() {
    assert_eq!(canonical(&b"000120".to_vec()), b"120".to_vec());
    assert_eq!(canonical(&b"000".to_vec()), Vec::<u8>::new());
    assert_eq!(canonical(&Vec::new()), Vec::<u8>::new());
}

#[test]
fn arithmetic_agrees_with_machine_integers() {
    let numbers = samples();
    for &a in &numbers {
        for &b in &numbers {
            let (da, db) = (digits(a), digits(b));
            let order = compare_naturals(&da, &db);
            assert_eq!(order, (a.cmp(&b) as i8 + 1) as u8, "{a} vs {b}");
            assert_eq!(add_naturals(&da, &db), digits(a + b), "{a} + {b}");
            if a >= b {
                assert_eq!(subtract_naturals(&da, &db), digits(a - b), "{a} - {b}");
            }
            if a < 1 << 60 && b < 1 << 60 {
                assert_eq!(multiply_naturals(&da, &db), digits(a * b), "{a} * {b}");
            }
            if let (Some(quotient), Some(rest)) = (a.checked_div(b), a.checked_rem(b)) {
                let (q, r) = divide_naturals(&da, &db);
                assert_eq!((value(&q), value(&r)), (quotient, rest), "{a} / {b}");
                assert_eq!(q, digits(quotient));
                assert_eq!(r, digits(rest));
            }
            assert_eq!(gcd_naturals(&da, &db), digits(gcd(a, b)), "gcd {a} {b}");
        }
    }
}

#[test]
fn powers_of_ten() {
    assert_eq!(ten_power(0), b"1".to_vec());
    assert_eq!(ten_power(3), b"1000".to_vec());
    assert_eq!(times_power(b"12".to_vec(), 2), b"1200".to_vec());
    assert_eq!(times_power(Vec::new(), 4), Vec::<u8>::new());
}

#[test]
fn numbers_beyond_machine_integers() {
    let big = b"123456789012345678901234567890123456789".to_vec();
    let square = multiply_naturals(&big, &big);
    let (q, r) = divide_naturals(&square, &big);
    assert_eq!(q, big);
    assert!(r.is_empty());
    let one_more = add_naturals(&square, &b"1".to_vec());
    let (q, r) = divide_naturals(&one_more, &big);
    assert_eq!(q, big);
    assert_eq!(r, b"1".to_vec());
    assert_eq!(subtract_naturals(&one_more, &square), b"1".to_vec());
    assert_eq!(compare_naturals(&square, &one_more), 0);
    assert_eq!(gcd_naturals(&square, &big), big);
}
