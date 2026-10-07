use rowl_kernel::datatypes::{
    compare_values, facet_applies, facet_holds, facet_of, in_kind, kind_of, literal_value,
    same_value, DataValue, Facet, Kind, Moment,
};
use rowl_kernel::model::{Datatype, Iri, Literal};

const INTEGER: &[u8] = b"http://www.w3.org/2001/XMLSchema#integer";
const DECIMAL: &[u8] = b"http://www.w3.org/2001/XMLSchema#decimal";
const STRING: &[u8] = b"http://www.w3.org/2001/XMLSchema#string";
const PLAIN: &[u8] = b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const BOOLEAN: &[u8] = b"http://www.w3.org/2001/XMLSchema#boolean";
const XML_LITERAL: &[u8] = b"http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral";
const REAL: &[u8] = b"http://www.w3.org/2002/07/owl#real";
const RATIONAL: &[u8] = b"http://www.w3.org/2002/07/owl#rational";
const BYTE: &[u8] = b"http://www.w3.org/2001/XMLSchema#byte";
const UNSIGNED_LONG: &[u8] = b"http://www.w3.org/2001/XMLSchema#unsignedLong";
const LONG: &[u8] = b"http://www.w3.org/2001/XMLSchema#long";
const NON_NEGATIVE: &[u8] = b"http://www.w3.org/2001/XMLSchema#nonNegativeInteger";
const POSITIVE: &[u8] = b"http://www.w3.org/2001/XMLSchema#positiveInteger";
const NEGATIVE: &[u8] = b"http://www.w3.org/2001/XMLSchema#negativeInteger";

fn datatype(iri: &[u8]) -> Datatype {
    Datatype {
        iri: Iri {
            spelling: iri.to_vec(),
        },
    }
}
fn value(lexical: &[u8], iri: &[u8]) -> Option<DataValue> {
    literal_value(&Literal {
        lexical: lexical.to_vec(),
        datatype: datatype(iri),
    })
}
fn number(negative: bool, integer: &[u8], fraction: &[u8]) -> DataValue {
    DataValue::Number(negative, integer.to_vec(), fraction.to_vec())
}
fn same(left: &Option<DataValue>, right: &DataValue) -> bool {
    match left {
        Some(left) => same_value(left, right),
        None => false,
    }
}

#[test]
fn the_five_datatypes_are_recognized_by_their_iris() {
    assert!(matches!(kind_of(&datatype(INTEGER)), Some(Kind::Integer)));
    assert!(matches!(kind_of(&datatype(DECIMAL)), Some(Kind::Decimal)));
    assert!(matches!(kind_of(&datatype(STRING)), Some(Kind::String)));
    assert!(matches!(kind_of(&datatype(PLAIN)), Some(Kind::Plain)));
    assert!(matches!(kind_of(&datatype(BOOLEAN)), Some(Kind::Boolean)));
    assert!(kind_of(&datatype(XML_LITERAL)).is_none());
    assert!(value(b"<a/>", XML_LITERAL).is_none());
}

#[test]
fn integer_lexical_forms_and_their_canonical_numbers() {
    assert!(same(&value(b"42", INTEGER), &number(false, b"42", b"")));
    assert!(same(&value(b"+0042", INTEGER), &number(false, b"42", b"")));
    assert!(same(&value(b"-17", INTEGER), &number(true, b"17", b"")));
    assert!(same(&value(b"-0", INTEGER), &number(false, b"", b"")));
    assert!(same(&value(b"000", INTEGER), &number(false, b"", b"")));
    for ill in [
        &b""[..],
        b"+",
        b"-",
        b"1.0",
        b" 1",
        b"1 ",
        b"1e3",
        b"--1",
        b"0x1",
        b"\xd9\xa1",
    ] {
        assert!(value(ill, INTEGER).is_none(), "{ill:?}");
    }
}

#[test]
fn decimal_lexical_forms_and_their_canonical_numbers() {
    assert!(same(&value(b"1.50", DECIMAL), &number(false, b"1", b"5")));
    assert!(same(&value(b"-.250", DECIMAL), &number(true, b"", b"25")));
    assert!(same(&value(b"5.", DECIMAL), &number(false, b"5", b"")));
    assert!(same(&value(b"007.000", DECIMAL), &number(false, b"7", b"")));
    assert!(same(&value(b"-0.000", DECIMAL), &number(false, b"", b"")));
    assert!(same(&value(b"12", DECIMAL), &number(false, b"12", b"")));
    for ill in [&b"."[..], b"-.", b"1.2.3", b"1,5", b"", b"+.e1"] {
        assert!(value(ill, DECIMAL).is_none(), "{ill:?}");
    }
}

#[test]
fn numbers_compare_by_value() {
    let one = value(b"1", INTEGER).expect("an integer");
    assert!(same(&value(b"1.0", DECIMAL), &one));
    assert!(same(&value(b"+01.000", DECIMAL), &one));
    assert!(!same(&value(b"1.01", DECIMAL), &one));
    assert!(!same(&value(b"-1", INTEGER), &one));
    assert!(in_kind(&one, Kind::Integer));
    assert!(in_kind(&one, Kind::Decimal));
    let half = value(b"0.5", DECIMAL).expect("a decimal");
    assert!(!in_kind(&half, Kind::Integer));
    assert!(in_kind(&half, Kind::Decimal));
    assert!(!in_kind(&half, Kind::String));
}

#[test]
fn strings_and_plain_literals() {
    let text = value(b"Ann", STRING).expect("a string");
    assert!(same(&value(b"Ann@", PLAIN), &text));
    assert!(in_kind(&text, Kind::String));
    assert!(in_kind(&text, Kind::Plain));
    let tagged = value(b"Ann@EN-gb", PLAIN).expect("a tagged string");
    assert!(same_value(
        &tagged,
        &DataValue::Tagged(b"Ann".to_vec(), b"en-gb".to_vec())
    ));
    assert!(same(&value(b"Ann@en-GB", PLAIN), &tagged));
    assert!(!same(&value(b"Ann@en", PLAIN), &tagged));
    assert!(!in_kind(&tagged, Kind::String));
    assert!(in_kind(&tagged, Kind::Plain));
    assert!(same(
        &value(b"a@b@de", PLAIN),
        &DataValue::Tagged(b"a@b".to_vec(), b"de".to_vec())
    ));
    assert!(value(b"no tag", PLAIN).is_none());
    assert!(value(b"x@not a tag", PLAIN).is_none());
    assert!(value(b"\x00", STRING).is_none());
    assert!(value(b"\xff", STRING).is_none());
    assert!(same(&value(b"", STRING), &DataValue::Text(Vec::new())));
}

#[test]
fn truth_values() {
    assert!(same(&value(b"true", BOOLEAN), &DataValue::Truth(true)));
    assert!(same(&value(b"1", BOOLEAN), &DataValue::Truth(true)));
    assert!(same(&value(b"false", BOOLEAN), &DataValue::Truth(false)));
    assert!(same(&value(b"0", BOOLEAN), &DataValue::Truth(false)));
    assert!(value(b"True", BOOLEAN).is_none());
    assert!(value(b"yes", BOOLEAN).is_none());
    let truth = DataValue::Truth(true);
    assert!(in_kind(&truth, Kind::Boolean));
    assert!(!in_kind(&truth, Kind::Integer));
    assert!(!same(&value(b"1", INTEGER), &truth));
}

fn fraction(negative: bool, numerator: &[u8], denominator: &[u8]) -> DataValue {
    DataValue::Fraction(negative, numerator.to_vec(), denominator.to_vec())
}
fn iri(spelling: &[u8]) -> Iri {
    Iri {
        spelling: spelling.to_vec(),
    }
}

#[test]
fn the_numeric_datatypes_are_recognized_by_their_iris() {
    assert!(matches!(kind_of(&datatype(REAL)), Some(Kind::Real)));
    assert!(matches!(kind_of(&datatype(RATIONAL)), Some(Kind::Rational)));
    assert!(matches!(kind_of(&datatype(BYTE)), Some(Kind::Byte)));
    assert!(matches!(
        kind_of(&datatype(UNSIGNED_LONG)),
        Some(Kind::UnsignedLong)
    ));
    assert!(matches!(
        kind_of(&datatype(NON_NEGATIVE)),
        Some(Kind::NonNegativeInteger)
    ));
    assert!(kind_of(&datatype(b"http://www.w3.org/2001/XMLSchema#Byte")).is_none());
}

#[test]
fn owl_real_has_no_lexical_forms() {
    assert!(value(b"1", REAL).is_none());
    assert!(value(b"1/2", REAL).is_none());
}

#[test]
fn rationals_in_lowest_terms_or_as_decimals() {
    assert!(same(&value(b"1/3", RATIONAL), &fraction(false, b"1", b"3")));
    assert!(same(&value(b"-4/6", RATIONAL), &fraction(true, b"2", b"3")));
    assert!(same(
        &value(b"+10/0030", RATIONAL),
        &fraction(false, b"1", b"3")
    ));
    assert!(same(&value(b"1/2", RATIONAL), &number(false, b"", b"5")));
    assert!(same(&value(b"-6/4", RATIONAL), &number(true, b"1", b"5")));
    assert!(same(&value(b"12/4", RATIONAL), &number(false, b"3", b"")));
    assert!(same(&value(b"-0/7", RATIONAL), &number(false, b"", b"")));
    assert!(same(
        &value(b"7/1", RATIONAL),
        &value(b"7", INTEGER).unwrap()
    ));
    assert!(same(
        &value(b"1/80", RATIONAL),
        &number(false, b"", b"0125")
    ));
    assert!(same(
        &value(b"123456789012345678901234567891/7", RATIONAL),
        &fraction(false, b"123456789012345678901234567891", b"7")
    ));
    assert!(same(
        &value(b"123456789012345678901234567890/7", RATIONAL),
        &number(false, b"17636684144620811271604938270", b"")
    ));
    assert!(same(
        &value(
            b"10000000000000000000000000000000001/50000000000000000000000000000000005",
            RATIONAL
        ),
        &number(false, b"", b"2")
    ));
    for ill in [
        &b"1"[..],
        b"1/0",
        b"1/00",
        b"1/-2",
        b"1/+2",
        b"1/",
        b"/2",
        b"1.5/2",
        b"1/2/3",
        b" 1/2",
        b"1/ 2",
    ] {
        assert!(value(ill, RATIONAL).is_none(), "{ill:?}");
    }
}

#[test]
fn integer_subtypes_bound_their_values() {
    assert!(same(&value(b"127", BYTE), &number(false, b"127", b"")));
    assert!(same(&value(b"-128", BYTE), &number(true, b"128", b"")));
    assert!(value(b"128", BYTE).is_none());
    assert!(value(b"-129", BYTE).is_none());
    assert!(value(b"1.0", BYTE).is_none());
    assert!(same(
        &value(b"18446744073709551615", UNSIGNED_LONG),
        &number(false, b"18446744073709551615", b"")
    ));
    assert!(value(b"18446744073709551616", UNSIGNED_LONG).is_none());
    assert!(same(&value(b"-0", UNSIGNED_LONG), &number(false, b"", b"")));
    assert!(value(b"-1", UNSIGNED_LONG).is_none());
    assert!(value(b"9223372036854775808", LONG).is_none());
    assert!(value(b"-9223372036854775808", LONG).is_some());
    assert!(same(&value(b"-0", NON_NEGATIVE), &number(false, b"", b"")));
    assert!(value(b"0", POSITIVE).is_none());
    assert!(value(b"+1", POSITIVE).is_some());
    assert!(value(b"-1", NEGATIVE).is_some());
    assert!(value(b"0", NEGATIVE).is_none());
    let five = value(b"5", BYTE).expect("a byte");
    assert!(same(&value(b"5.000", DECIMAL), &five));
    assert!(in_kind(&five, Kind::Byte));
    assert!(in_kind(&five, Kind::Real));
    assert!(in_kind(&five, Kind::Rational));
    assert!(!in_kind(&five, Kind::NegativeInteger));
    let third = value(b"1/3", RATIONAL).expect("a rational");
    assert!(in_kind(&third, Kind::Real));
    assert!(in_kind(&third, Kind::Rational));
    assert!(!in_kind(&third, Kind::Decimal));
    assert!(!in_kind(&third, Kind::Byte));
}

#[test]
fn numbers_are_ordered_exactly() {
    let order = |a: &[u8], ta: &[u8], b: &[u8], tb: &[u8]| {
        compare_values(&value(a, ta).unwrap(), &value(b, tb).unwrap())
    };
    assert_eq!(order(b"1", INTEGER, b"2", INTEGER), Some(0));
    assert_eq!(order(b"2", INTEGER, b"1.999", DECIMAL), Some(2));
    assert_eq!(order(b"-2", INTEGER, b"-1.5", DECIMAL), Some(0));
    assert_eq!(order(b"-0.5", DECIMAL, b"0", INTEGER), Some(0));
    assert_eq!(order(b"1/3", RATIONAL, b"0.333333333333", DECIMAL), Some(2));
    assert_eq!(
        order(b"1/3", RATIONAL, b"0.3333333333334", DECIMAL),
        Some(0)
    );
    assert_eq!(order(b"-1/3", RATIONAL, b"-1/4", RATIONAL), Some(0));
    assert_eq!(order(b"2/6", RATIONAL, b"1/3", RATIONAL), Some(1));
    assert_eq!(order(b"0.75", DECIMAL, b"3/4", RATIONAL), Some(1));
    assert_eq!(order(b"10", INTEGER, b"9.99", DECIMAL), Some(2));
    assert_eq!(order(b"0.1", DECIMAL, b"0.09", DECIMAL), Some(2));
    assert_eq!(order(b"-10", INTEGER, b"-9.99", DECIMAL), Some(0));
    assert!(compare_values(&DataValue::Truth(true), &number(false, b"1", b"")).is_none());
}

#[test]
fn range_facets_on_single_values() {
    let min_inclusive = facet_of(&iri(b"http://www.w3.org/2001/XMLSchema#minInclusive"));
    let max_exclusive = facet_of(&iri(b"http://www.w3.org/2001/XMLSchema#maxExclusive"));
    assert!(matches!(min_inclusive, Some(Facet::MinInclusive)));
    assert!(matches!(max_exclusive, Some(Facet::MaxExclusive)));
    assert!(facet_of(&iri(b"http://www.w3.org/2001/XMLSchema#minLength")).is_none());
    let dose = value(b"4000", DECIMAL).unwrap();
    let prescribed = value(b"4500.5", DECIMAL).unwrap();
    assert_eq!(
        facet_holds(Facet::MaxInclusive, &dose, &prescribed),
        Some(false)
    );
    assert_eq!(facet_holds(Facet::MaxInclusive, &dose, &dose), Some(true));
    assert_eq!(facet_holds(Facet::MaxExclusive, &dose, &dose), Some(false));
    assert_eq!(
        facet_holds(Facet::MinExclusive, &dose, &prescribed),
        Some(true)
    );
    let third = value(b"1/3", RATIONAL).unwrap();
    assert_eq!(
        facet_holds(
            Facet::MinInclusive,
            &third,
            &value(b"0.34", DECIMAL).unwrap()
        ),
        Some(true)
    );
    assert_eq!(
        facet_holds(Facet::MinInclusive, &third, &DataValue::Truth(true)),
        None
    );
    assert!(facet_applies(Kind::Real, &third));
    assert!(facet_applies(Kind::Rational, &third));
    assert!(!facet_applies(Kind::Decimal, &third));
    assert!(facet_applies(Kind::Decimal, &dose));
    assert!(!facet_applies(Kind::Byte, &dose));
    assert!(!facet_applies(Kind::String, &dose));
}

const ANY_URI: &[u8] = b"http://www.w3.org/2001/XMLSchema#anyURI";
const HEX: &[u8] = b"http://www.w3.org/2001/XMLSchema#hexBinary";
const BASE64: &[u8] = b"http://www.w3.org/2001/XMLSchema#base64Binary";

#[test]
fn iris_and_octets_are_values_of_their_own() {
    assert!(matches!(kind_of(&datatype(ANY_URI)), Some(Kind::AnyUri)));
    assert!(matches!(kind_of(&datatype(HEX)), Some(Kind::HexBinary)));
    assert!(matches!(
        kind_of(&datatype(BASE64)),
        Some(Kind::Base64Binary)
    ));
    // anyURI: the lexical mapping is the identity, relative IRIs and spaces included.
    let uri = value(b"http://example.org/a b", ANY_URI).expect("an IRI");
    assert!(same_value(
        &uri,
        &DataValue::Uri(b"http://example.org/a b".to_vec())
    ));
    assert!(same(
        &value(b"../relative", ANY_URI),
        &DataValue::Uri(b"../relative".to_vec())
    ));
    assert!(value(b"\x01", ANY_URI).is_none());
    assert!(in_kind(&uri, Kind::AnyUri));
    assert!(!in_kind(&uri, Kind::String));
    assert!(!same_value(
        &uri,
        &DataValue::Text(b"http://example.org/a b".to_vec())
    ));
    // hexBinary: two digits per octet, in either case.
    let octets = DataValue::Hex(vec![0x0f, 0xb7]);
    assert!(same(&value(b"0FB7", HEX), &octets));
    assert!(same(&value(b"0fb7", HEX), &octets));
    assert!(same(&value(b"", HEX), &DataValue::Hex(Vec::new())));
    assert!(value(b"0FB", HEX).is_none());
    assert!(value(b"0G", HEX).is_none());
    assert!(value(b" 0F", HEX).is_none());
    // base64Binary: groups of four, padding at the end, one space after a character.
    let three = DataValue::Base64(vec![1, 2, 3]);
    assert!(same(&value(b"AQID", BASE64), &three));
    assert!(same(&value(b"A Q I D", BASE64), &three));
    assert!(same(
        &value(b"AQI=", BASE64),
        &DataValue::Base64(vec![1, 2])
    ));
    assert!(same(&value(b"AQ==", BASE64), &DataValue::Base64(vec![1])));
    assert!(same(&value(b"AQ= =", BASE64), &DataValue::Base64(vec![1])));
    assert!(same(
        &value(b"AQIDBA==", BASE64),
        &DataValue::Base64(vec![1, 2, 3, 4])
    ));
    assert!(same(&value(b"", BASE64), &DataValue::Base64(Vec::new())));
    for bad in [
        &b"AQI"[..],
        b"AR==",
        b"AQJ=",
        b" AQID",
        b"AQID ",
        b"AQ  ID",
        b"AQ=I",
        b"A=QI",
        b"AQ==AQID",
        b"AQ*D",
    ] {
        assert!(
            value(bad, BASE64).is_none(),
            "{}",
            String::from_utf8_lossy(bad)
        );
    }
    // The two binary datatypes have disjoint copies of the octet sequences.
    let hex = value(b"0203", HEX).expect("octets");
    let base64 = value(b"AgM=", BASE64).expect("octets");
    assert!(!same_value(&hex, &base64));
    assert!(in_kind(&hex, Kind::HexBinary) && !in_kind(&hex, Kind::Base64Binary));
    assert!(in_kind(&base64, Kind::Base64Binary) && !in_kind(&base64, Kind::HexBinary));
    assert!(!facet_applies(Kind::HexBinary, &number(false, b"1", b"")));
}

const NORMALIZED: &[u8] = b"http://www.w3.org/2001/XMLSchema#normalizedString";
const TOKEN: &[u8] = b"http://www.w3.org/2001/XMLSchema#token";
const LANGUAGE: &[u8] = b"http://www.w3.org/2001/XMLSchema#language";
const NMTOKEN: &[u8] = b"http://www.w3.org/2001/XMLSchema#NMTOKEN";
const NAME: &[u8] = b"http://www.w3.org/2001/XMLSchema#Name";
const NCNAME: &[u8] = b"http://www.w3.org/2001/XMLSchema#NCName";

/// The subtypes of `xsd:string` whose lexical space holds `lexical`.
fn string_kinds(lexical: &[u8]) -> Vec<&'static str> {
    [
        (NORMALIZED, "normalizedString"),
        (TOKEN, "token"),
        (LANGUAGE, "language"),
        (NMTOKEN, "NMTOKEN"),
        (NAME, "Name"),
        (NCNAME, "NCName"),
    ]
    .into_iter()
    .filter(|(iri, _)| value(lexical, iri).is_some())
    .map(|(_, name)| name)
    .collect()
}

#[test]
fn the_subtypes_of_strings_hold_the_strings_of_their_lexical_forms() {
    assert!(matches!(
        kind_of(&datatype(NORMALIZED)),
        Some(Kind::NormalizedString)
    ));
    assert!(matches!(kind_of(&datatype(TOKEN)), Some(Kind::Token)));
    assert!(matches!(kind_of(&datatype(LANGUAGE)), Some(Kind::Language)));
    assert!(matches!(kind_of(&datatype(NMTOKEN)), Some(Kind::NmToken)));
    assert!(matches!(kind_of(&datatype(NAME)), Some(Kind::Name)));
    assert!(matches!(kind_of(&datatype(NCNAME)), Some(Kind::NcName)));
    // The value is the string itself: equal to the xsd:string literal.
    let token = value(b"en-GB", TOKEN).expect("a token");
    assert!(same(&value(b"en-GB", STRING), &token));
    assert!(same(&value(b"en-GB", LANGUAGE), &token));
    assert!(same(&value(b"en-GB@", PLAIN), &token));
    // Language codes keep their case: "MN" and "mn" are distinct values.
    assert!(!same(
        &value(b"MN", LANGUAGE),
        &value(b"mn", LANGUAGE).expect("a language")
    ));
    // Each lexical form lies in exactly the subtypes it matches, from the
    // narrowest on: language, NCName, Name, NMTOKEN, token, normalizedString.
    let all = vec![
        "normalizedString",
        "token",
        "language",
        "NMTOKEN",
        "Name",
        "NCName",
    ];
    assert_eq!(string_kinds(b"en-GB"), all);
    assert_eq!(
        string_kinds(b"x-a1b2c3d4"),
        all,
        "a private-use subtag is a language subtag"
    );
    let names = vec!["normalizedString", "token", "NMTOKEN", "Name", "NCName"];
    assert_eq!(string_kinds(b"_id"), names);
    assert_eq!(
        string_kinds(b"abcdefghi"),
        names,
        "nine letters are no subtag"
    );
    assert_eq!(string_kinds(b"en--GB"), names);
    assert_eq!(
        string_kinds(b"1en"),
        vec!["normalizedString", "token", "NMTOKEN"],
        "a digit is no name start character"
    );
    assert_eq!(
        string_kinds(b"\xc3\xa9t\xc3\xa9"),
        names,
        "letters beyond ASCII"
    );
    assert_eq!(
        string_kinds(b"xml:lang"),
        vec!["normalizedString", "token", "NMTOKEN", "Name"]
    );
    assert_eq!(
        string_kinds(b"-1.5"),
        vec!["normalizedString", "token", "NMTOKEN"]
    );
    assert_eq!(
        string_kinds(b"\xcc\x80a"),
        vec!["normalizedString", "token", "NMTOKEN"],
        "a combining mark is no name start character"
    );
    assert_eq!(string_kinds(b"a b"), vec!["normalizedString", "token"]);
    assert_eq!(string_kinds(b""), vec!["normalizedString", "token"]);
    assert_eq!(string_kinds(b" a"), vec!["normalizedString"]);
    assert_eq!(string_kinds(b"a "), vec!["normalizedString"]);
    assert_eq!(string_kinds(b"a  b"), vec!["normalizedString"]);
    assert_eq!(string_kinds(b"a\tb"), Vec::<&str>::new());
    assert_eq!(string_kinds(b"a\nb"), Vec::<&str>::new());
    assert_eq!(string_kinds(b"a\rb"), Vec::<&str>::new());
    assert_eq!(
        string_kinds(b"\x01"),
        Vec::<&str>::new(),
        "no XML character"
    );
    // Membership of values follows the same tests.
    let tab = value(b"a\tb", STRING).expect("a string");
    assert!(in_kind(&tab, Kind::String) && in_kind(&tab, Kind::Plain));
    assert!(!in_kind(&tab, Kind::NormalizedString));
    assert!(in_kind(&token, Kind::Language) && in_kind(&token, Kind::NcName));
    let colon = value(b"xml:lang", STRING).expect("a string");
    assert!(in_kind(&colon, Kind::Name) && !in_kind(&colon, Kind::NcName));
    assert!(!in_kind(&number(false, b"1", b""), Kind::Token));
    assert!(!facet_applies(Kind::Token, &number(false, b"1", b"")));
}

const DATE_TIME: &[u8] = b"http://www.w3.org/2001/XMLSchema#dateTime";
const STAMP: &[u8] = b"http://www.w3.org/2001/XMLSchema#dateTimeStamp";

/// The moment with these parts, the year given with its sign.
fn moment(
    year: &str,
    date: (u8, u8),
    time: (u8, u8, u8),
    fraction: &[u8],
    zone: Option<(bool, u8, u8)>,
) -> DataValue {
    let (negative, digits) = match year.strip_prefix('-') {
        Some(digits) => (true, digits),
        None => (false, year),
    };
    DataValue::Moment(Moment {
        negative,
        year: digits.as_bytes().to_vec(),
        month: date.0,
        day: date.1,
        hour: time.0,
        minute: time.1,
        second: time.2,
        fraction: fraction.to_vec(),
        zone,
    })
}

#[test]
fn time_instants_keep_their_time_zones() {
    assert!(matches!(
        kind_of(&datatype(DATE_TIME)),
        Some(Kind::DateTime)
    ));
    assert!(matches!(
        kind_of(&datatype(STAMP)),
        Some(Kind::DateTimeStamp)
    ));
    let local = moment("2001", (10, 26), (21, 32, 52), b"", None);
    assert!(same(&value(b"2001-10-26T21:32:52", DATE_TIME), &local));
    let east = moment("2001", (10, 26), (21, 32, 52), b"", Some((false, 2, 0)));
    assert!(same(&value(b"2001-10-26T21:32:52+02:00", DATE_TIME), &east));
    let utc = moment("2001", (10, 26), (19, 32, 52), b"", Some((false, 0, 0)));
    assert!(same(&value(b"2001-10-26T19:32:52Z", DATE_TIME), &utc));
    assert!(same(&value(b"2001-10-26T19:32:52+00:00", DATE_TIME), &utc));
    assert!(same(&value(b"2001-10-26T19:32:52-00:00", DATE_TIME), &utc));
    // One instant at two offsets: equal in time, but two values.
    assert!(!same_value(&east, &utc));
    assert!(!same_value(&local, &east));
    let west = moment("2001", (10, 26), (9, 2, 5), b"", Some((true, 13, 30)));
    assert!(same(&value(b"2001-10-26T09:02:05-13:30", DATE_TIME), &west));
    assert!(same(
        &value(b"2001-10-26T09:02:05+14:00", DATE_TIME),
        &moment("2001", (10, 26), (9, 2, 5), b"", Some((false, 14, 0)))
    ));
    // Fractions of a second are decimals.
    let fine = moment("2001", (10, 26), (21, 32, 52), b"12", None);
    assert!(same(&value(b"2001-10-26T21:32:52.12", DATE_TIME), &fine));
    assert!(same(&value(b"2001-10-26T21:32:52.1200", DATE_TIME), &fine));
    assert!(same(&value(b"2001-10-26T21:32:52.000", DATE_TIME), &local));
    // Years: four digits or more, negative ones and year zero.
    assert!(same(
        &value(b"12345-01-01T00:00:00", DATE_TIME),
        &moment("12345", (1, 1), (0, 0, 0), b"", None)
    ));
    assert!(same(
        &value(b"-0044-03-15T12:00:00", DATE_TIME),
        &moment("-44", (3, 15), (12, 0, 0), b"", None)
    ));
    let zero = moment("", (1, 1), (0, 0, 0), b"", None);
    assert!(same(&value(b"0000-01-01T00:00:00", DATE_TIME), &zero));
    assert!(same(&value(b"-0000-01-01T00:00:00", DATE_TIME), &zero));
    // Leap years of the proleptic Gregorian calendar.
    for leap in [
        &b"2000-02-29T00:00:00"[..],
        b"2004-02-29T00:00:00",
        b"0000-02-29T00:00:00",
        b"-0004-02-29T00:00:00",
        b"-0400-02-29T00:00:00",
        b"2400-02-29T00:00:00",
    ] {
        assert!(
            value(leap, DATE_TIME).is_some(),
            "{}",
            String::from_utf8_lossy(leap)
        );
    }
    // The end of a day is the start of the next.
    assert!(same(
        &value(b"2001-12-31T24:00:00Z", DATE_TIME),
        &moment("2002", (1, 1), (0, 0, 0), b"", Some((false, 0, 0)))
    ));
    assert!(same(
        &value(b"2001-02-28T24:00:00.000", DATE_TIME),
        &moment("2001", (3, 1), (0, 0, 0), b"", None)
    ));
    assert!(same(
        &value(b"2000-02-28T24:00:00", DATE_TIME),
        &moment("2000", (2, 29), (0, 0, 0), b"", None)
    ));
    assert!(same(
        &value(b"-0001-12-31T24:00:00", DATE_TIME),
        &moment("", (1, 1), (0, 0, 0), b"", None)
    ));
    assert!(same(
        &value(b"9999-12-31T24:00:00", DATE_TIME),
        &moment("10000", (1, 1), (0, 0, 0), b"", None)
    ));
    for bad in [
        &b"2001-02-29T00:00:00"[..],
        b"1900-02-29T00:00:00",
        b"-0100-02-29T00:00:00",
        b"2001-04-31T00:00:00",
        b"2001-00-10T00:00:00",
        b"2001-13-10T00:00:00",
        b"2001-10-00T00:00:00",
        b"2001-10-26T24:00:01",
        b"2001-10-26T24:00:00.1",
        b"2001-10-26T25:00:00",
        b"2001-10-26T21:60:00",
        b"2001-10-26T21:32:60",
        b"2001-10-26T21:32:52+14:01",
        b"2001-10-26T21:32:52+15:00",
        b"2001-10-26T21:32:52+1:00",
        b"2001-10-26T21:32:52+01:60",
        b"2001-10-26T21:32:52z",
        b"2001-10-26T21:32:52Z ",
        b"2001-10-26T21:32:52.",
        b"2001-10-26T21:32",
        b"2001-10-26",
        b"201-10-26T21:32:52",
        b"02001-10-26T21:32:52",
        b"+2001-10-26T21:32:52",
        b"2001-1-26T21:32:52",
        b"2001-10-26 21:32:52",
        b"",
    ] {
        assert!(
            value(bad, DATE_TIME).is_none(),
            "{}",
            String::from_utf8_lossy(bad)
        );
    }
    // A time stamp needs its time zone.
    assert!(value(b"2001-10-26T21:32:52", STAMP).is_none());
    assert!(same(&value(b"2001-10-26T19:32:52Z", STAMP), &utc));
    assert!(in_kind(&utc, Kind::DateTime) && in_kind(&utc, Kind::DateTimeStamp));
    assert!(in_kind(&local, Kind::DateTime) && !in_kind(&local, Kind::DateTimeStamp));
    assert!(!in_kind(&local, Kind::String) && !in_kind(&local, Kind::Real));
    let text = value(b"2001-10-26T21:32:52", STRING).expect("a string");
    assert!(!same_value(&text, &local));
    assert!(!facet_applies(Kind::DateTime, &number(false, b"1", b"")));
}
