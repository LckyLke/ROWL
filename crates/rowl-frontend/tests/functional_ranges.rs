use rowl_frontend::functional_annotations::{read_annotations, AnnotationLimits};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_literals::SourceLiteralError;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::functional_ranges::{
    read_data_range, read_optional_range, RangeError, RangeExpected, SourceDataRange,
};
use rowl_frontend::prefixes::{check, Check};

const EX: &str = "https://example.org/lab/";
const XSD: &str = "http://www.w3.org/2001/XMLSchema#";

/// Read one data range at the first axiom position of a source document.
fn read(
    body: &str,
    depth: usize,
    count: usize,
) -> (Vec<u8>, Result<(SourceDataRange, Tokens), RangeError>) {
    let source = format!(
        "Prefix(:=<{EX}>)\nOntology(<https://example.org/lab> <https://example.org/lab/1>\n{body}"
    );
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 400, 10, 100)
        .unwrap_or_else(|_| panic!("fixture prefix syntax must be complete"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("fixture declarations must form a normative prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("fixture header must be accepted"));
    let limits = AnnotationLimits {
        depth: 2,
        count: 10,
        iri: 100,
        lexical: 100,
    };
    let ontology = read_annotations(&table, &bytes, header.remaining, &limits)
        .unwrap_or_else(|_| panic!("fixture ontology annotations must be accepted"));
    let result = read_data_range(&table, &bytes, ontology.remaining, depth, count, 100);
    (bytes, result)
}
fn offset(bytes: &[u8], needle: &str, occurrence: usize) -> usize {
    let mut found = 0;
    for start in 0..bytes.len() {
        if bytes[start..].starts_with(needle.as_bytes()) {
            if found == occurrence {
                return start;
            }
            found += 1;
        }
    }
    panic!("fixture text must occur")
}
fn name(iri: &[u8]) -> String {
    let text = String::from_utf8(iri.to_vec()).expect("IRIs are UTF-8");
    if let Some(local) = text.strip_prefix(XSD) {
        return format!("xsd:{local}");
    }
    text.strip_prefix(EX).unwrap_or(&text).to_string()
}
fn text(range: &SourceDataRange) -> String {
    match range {
        SourceDataRange::Datatype(iri) => name(&iri.value),
        SourceDataRange::IntersectionOf { members, .. } => {
            format!(
                "and({})",
                members.iter().map(text).collect::<Vec<_>>().join(",")
            )
        }
        SourceDataRange::UnionOf { members, .. } => {
            format!(
                "or({})",
                members.iter().map(text).collect::<Vec<_>>().join(",")
            )
        }
        SourceDataRange::ComplementOf { operand, .. } => format!("not({})", text(operand)),
        SourceDataRange::OneOf { members, .. } => format!(
            "one({})",
            members
                .iter()
                .map(|literal| format!(
                    "{}^{}",
                    String::from_utf8(literal.lexical.clone()).expect("UTF-8"),
                    name(&literal.datatype)
                ))
                .collect::<Vec<_>>()
                .join(",")
        ),
        SourceDataRange::Restriction {
            datatype, facets, ..
        } => format!(
            "restrict({},{})",
            name(&datatype.value),
            facets
                .iter()
                .map(|facet| format!(
                    "{}={}",
                    name(&facet.facet.value),
                    String::from_utf8(facet.value.lexical.clone()).expect("UTF-8")
                ))
                .collect::<Vec<_>>()
                .join(",")
        ),
    }
}
fn expected(result: Result<(SourceDataRange, Tokens), RangeError>) -> (&'static str, usize) {
    match result {
        Err(RangeError::Expected { expected, offset }) => {
            let kind = match expected {
                RangeExpected::Range => "range",
                RangeExpected::Open => "open",
                RangeExpected::Iri => "iri",
                RangeExpected::Literal => "literal",
                RangeExpected::Close => "close",
            };
            (kind, offset)
        }
        _ => panic!("expected a source syntax failure"),
    }
}

#[test]
fn nested_ranges_keep_their_shape() {
    let (bytes, result) = read(
        "DataIntersectionOf(xsd:integer DataComplementOf(DataOneOf(\"0\"^^xsd:integer \"7\"^^xsd:integer)) DataUnionOf(xsd:decimal :Code) DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer xsd:maxExclusive \"10\"^^xsd:integer))\n)",
        5,
        10,
    );
    let (range, remaining) = result.unwrap_or_else(|_| panic!("fixture must be accepted"));
    assert_eq!(
        text(&range),
        "and(xsd:integer,not(one(0^xsd:integer,7^xsd:integer)),or(xsd:decimal,Code),restrict(xsd:integer,xsd:minInclusive=1,xsd:maxExclusive=10))"
    );
    match &range {
        SourceDataRange::IntersectionOf { keyword, .. } => {
            assert_eq!(keyword.start, offset(&bytes, "DataIntersectionOf", 0))
        }
        _ => panic!("the outer range is an intersection"),
    }
    assert!(matches!(remaining, Tokens::Cons { .. }));
}

#[test]
fn plain_literals_in_enumerations_expand() {
    let (_, result) = read("DataOneOf(\"a\" \"b\"@en)", 5, 10);
    let (range, _) = result.unwrap_or_else(|_| panic!("fixture must be accepted"));
    assert_eq!(
        text(&range),
        "one(a@^http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral,b@en^http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral)"
    );
}

#[test]
fn errors_follow_source_order() {
    let (bytes, result) = read("DataUnionOf(xsd:integer)", 5, 10);
    assert_eq!(expected(result), ("range", offset(&bytes, ")", 1)));
    let (bytes, result) = read("DataOneOf()", 5, 10);
    assert_eq!(expected(result), ("literal", offset(&bytes, ")", 1)));
    let (bytes, result) = read("DatatypeRestriction(xsd:integer)", 5, 10);
    assert_eq!(expected(result), ("iri", offset(&bytes, ")", 1)));
    let (bytes, result) = read("DatatypeRestriction(\"1\" xsd:minInclusive \"1\")", 5, 10);
    assert_eq!(expected(result), ("iri", offset(&bytes, "\"1\"", 0)));
    let (_, result) = read(
        "DatatypeRestriction(xsd:integer xsd:minInclusive xsd:maxInclusive)",
        5,
        10,
    );
    assert!(matches!(
        result,
        Err(RangeError::Literal(SourceLiteralError::Expected { .. }))
    ));
    let (bytes, result) = read("DataComplementOf(xsd:integer xsd:string)", 5, 10);
    assert_eq!(expected(result), ("close", offset(&bytes, "xsd:string", 0)));
    let (bytes, result) = read("DataComplementOf xsd:integer)", 5, 10);
    assert_eq!(expected(result), ("open", offset(&bytes, "xsd:integer", 0)));
    let (bytes, result) = read("\"1\"", 5, 10);
    assert_eq!(expected(result), ("range", offset(&bytes, "\"1\"", 0)));
    let (bytes, result) = read("", 5, 10);
    assert_eq!(expected(result), ("range", bytes.len()));
}

#[test]
fn depth_and_count_limits_are_checked() {
    let body = "DataComplementOf(DataComplementOf(xsd:integer))";
    let (_, result) = read(body, 2, 10);
    assert!(result.is_ok());
    let (bytes, result) = read(body, 1, 10);
    match result {
        Err(RangeError::DepthLimit { offset: at }) => {
            assert_eq!(at, offset(&bytes, "DataComplementOf", 1))
        }
        _ => panic!("nesting beyond the allowance is reported"),
    }
    let (_, result) = read("xsd:integer", 0, 10);
    assert!(result.is_ok(), "datatypes need no nesting allowance");
    let (bytes, result) = read("DataOneOf(\"1\" \"2\" \"3\")", 5, 2);
    match result {
        Err(RangeError::CountLimit { offset: at }) => assert_eq!(at, offset(&bytes, "\"3\"", 0)),
        _ => panic!("literals beyond the count are reported"),
    }
    let (bytes, result) = read(
        "DatatypeRestriction(xsd:integer xsd:minInclusive \"1\" xsd:maxInclusive \"2\")",
        5,
        1,
    );
    match result {
        Err(RangeError::CountLimit { offset: at }) => {
            assert_eq!(at, offset(&bytes, "xsd:maxInclusive", 0))
        }
        _ => panic!("facets beyond the count are reported"),
    }
}

#[test]
fn optional_ranges_stop_before_the_closing_parenthesis() {
    let source = format!("Prefix(:=<{EX}>)\nOntology(<https://example.org/lab>\n) xsd:integer");
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 400, 10, 100).unwrap_or_else(|_| panic!("prefixes"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    let (none, rest) = read_optional_range(&table, &bytes, header.remaining, 5, 10, 100)
        .unwrap_or_else(|_| panic!("an absent range"));
    assert!(none.is_none());
    let rest = match rest {
        Tokens::Cons { next, .. } => *next,
        Tokens::Empty => panic!("the closing parenthesis remains"),
    };
    let (some, _) = read_optional_range(&table, &bytes, rest, 5, 10, 100)
        .unwrap_or_else(|_| panic!("a present range"));
    assert_eq!(
        some.map(|range| text(&range)),
        Some("xsd:integer".to_string())
    );
}
