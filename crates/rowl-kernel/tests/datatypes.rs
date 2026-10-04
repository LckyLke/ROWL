use rowl_kernel::datatypes::{in_kind, kind_of, literal_value, same_value, DataValue, Kind};
use rowl_kernel::model::{Datatype, Iri, Literal};

const INTEGER: &[u8] = b"http://www.w3.org/2001/XMLSchema#integer";
const DECIMAL: &[u8] = b"http://www.w3.org/2001/XMLSchema#decimal";
const STRING: &[u8] = b"http://www.w3.org/2001/XMLSchema#string";
const PLAIN: &[u8] = b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral";
const BOOLEAN: &[u8] = b"http://www.w3.org/2001/XMLSchema#boolean";
const DOUBLE: &[u8] = b"http://www.w3.org/2001/XMLSchema#double";

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
    assert!(kind_of(&datatype(DOUBLE)).is_none());
    assert!(value(b"1", DOUBLE).is_none());
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
