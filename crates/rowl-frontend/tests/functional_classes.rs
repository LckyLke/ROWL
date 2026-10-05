use rowl_frontend::functional::{Keyword, Terminal};
use rowl_frontend::functional_annotations::{read_annotations, AnnotationLimits};
use rowl_frontend::functional_classes::{
    read_class_expression, read_object_property, Bound, ClassError, ClassExpected, ClassLimits,
    SourceClass, SourceObjectProperty,
};
use rowl_frontend::functional_header::read_header_tail;
use rowl_frontend::functional_individuals::{IndividualError, SourceIndividual};
use rowl_frontend::functional_iris::SourceIriError;
use rowl_frontend::functional_lexer::Tokens;
use rowl_frontend::functional_prefixes::read_prefix_header;
use rowl_frontend::functional_ranges::{RangeError, RangeExpected, SourceDataRange};
use rowl_frontend::prefixes::{check, Check};

const EX: &str = "https://example.org/maintenance/";

fn limits(depth: usize, count: usize) -> ClassLimits {
    ClassLimits {
        depth,
        count,
        iri: 100,
    }
}
/// Read one class expression at the first axiom position of a source document
/// (after the header and its ontology annotations), returning the source bytes.
fn read(body: &str, limits: &ClassLimits) -> (Vec<u8>, Result<(SourceClass, Tokens), ClassError>) {
    let source = format!("Prefix(:=<{EX}>)\nOntology(<https://example.org/maintenance> <https://example.org/maintenance/1>\n{body}");
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 400, 10, 100)
        .unwrap_or_else(|_| panic!("fixture prefix syntax must be complete"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("fixture declarations must form a normative prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("fixture header must be accepted"));
    let annotation_limits = AnnotationLimits {
        depth: 2,
        count: 10,
        iri: 100,
        lexical: 100,
    };
    let ontology = read_annotations(&table, &bytes, header.remaining, &annotation_limits)
        .unwrap_or_else(|_| panic!("fixture ontology annotations must be accepted"));
    let result = read_class_expression(&table, &bytes, ontology.remaining, limits);
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
    text.strip_prefix(EX).unwrap_or(&text).to_string()
}
fn property_text(property: &SourceObjectProperty) -> String {
    match property {
        SourceObjectProperty::Named(iri) => name(&iri.value),
        SourceObjectProperty::Inverse { property, .. } => format!("inv({})", name(&property.value)),
    }
}
fn individual_text(individual: &SourceIndividual) -> String {
    match individual {
        SourceIndividual::Named(iri) => name(&iri.value),
        SourceIndividual::Anonymous { label, .. } => {
            format!(
                "_:{}",
                String::from_utf8(label.clone()).expect("labels are UTF-8")
            )
        }
    }
}
/// A compact rendering of the parsed tree, for comparing shapes.
fn text(class: &SourceClass) -> String {
    match class {
        SourceClass::Named(iri) => name(&iri.value),
        SourceClass::IntersectionOf { members, .. } => {
            format!(
                "and({})",
                members.iter().map(text).collect::<Vec<_>>().join(",")
            )
        }
        SourceClass::UnionOf { members, .. } => {
            format!(
                "or({})",
                members.iter().map(text).collect::<Vec<_>>().join(",")
            )
        }
        SourceClass::ComplementOf { operand, .. } => format!("not({})", text(operand)),
        SourceClass::SomeValuesFrom {
            property, filler, ..
        } => format!("some({},{})", property_text(property), text(filler)),
        SourceClass::AllValuesFrom {
            property, filler, ..
        } => format!("all({},{})", property_text(property), text(filler)),
        SourceClass::OneOf { members, .. } => format!(
            "one({})",
            members
                .iter()
                .map(individual_text)
                .collect::<Vec<_>>()
                .join(",")
        ),
        SourceClass::HasValue {
            property,
            individual,
            ..
        } => format!(
            "value({},{})",
            property_text(property),
            individual_text(individual)
        ),
        SourceClass::HasSelf { property, .. } => format!("self({})", property_text(property)),
        SourceClass::Cardinality {
            bound,
            value,
            property,
            filler,
            ..
        } => {
            let bound = match bound {
                Bound::Min => "min",
                Bound::Max => "max",
                Bound::Exact => "exact",
            };
            match filler {
                Some(filler) => format!(
                    "{bound}({value},{},{})",
                    property_text(property),
                    text(filler)
                ),
                None => format!("{bound}({value},{})", property_text(property)),
            }
        }
        SourceClass::DataSomeValuesFrom {
            property, range, ..
        } => format!("dsome({},{})", name(&property.value), range_text(range)),
        SourceClass::DataAllValuesFrom {
            property, range, ..
        } => format!("dall({},{})", name(&property.value), range_text(range)),
        SourceClass::DataHasValue {
            property, value, ..
        } => format!(
            "dvalue({},{})",
            name(&property.value),
            String::from_utf8(value.lexical.clone()).expect("UTF-8")
        ),
        SourceClass::DataCardinality {
            bound,
            value,
            property,
            range,
            ..
        } => {
            let bound = match bound {
                Bound::Min => "dmin",
                Bound::Max => "dmax",
                Bound::Exact => "dexact",
            };
            match range {
                Some(range) => format!(
                    "{bound}({value},{},{})",
                    name(&property.value),
                    range_text(range)
                ),
                None => format!("{bound}({value},{})", name(&property.value)),
            }
        }
    }
}
fn range_text(range: &SourceDataRange) -> String {
    match range {
        SourceDataRange::Datatype(iri) => name(&iri.value),
        SourceDataRange::IntersectionOf { members, .. } => format!(
            "dand({})",
            members.iter().map(range_text).collect::<Vec<_>>().join(",")
        ),
        SourceDataRange::UnionOf { members, .. } => format!(
            "dor({})",
            members.iter().map(range_text).collect::<Vec<_>>().join(",")
        ),
        SourceDataRange::ComplementOf { operand, .. } => format!("dnot({})", range_text(operand)),
        SourceDataRange::OneOf { members, .. } => format!("done[{}]", members.len()),
        SourceDataRange::Restriction {
            datatype, facets, ..
        } => format!("facets({},{})", name(&datatype.value), facets.len()),
    }
}
fn expected(result: Result<(SourceClass, Tokens), ClassError>) -> (&'static str, usize) {
    match result {
        Err(ClassError::Expected { expected, offset }) => {
            let kind = match expected {
                ClassExpected::Class => "class",
                ClassExpected::Open => "open",
                ClassExpected::Property => "property",
                ClassExpected::Iri => "iri",
                ClassExpected::Close => "close",
                ClassExpected::Number => "number",
            };
            (kind, offset)
        }
        _ => panic!("expected a source syntax failure"),
    }
}

#[test]
fn nested_expressions_keep_their_shape_tokens_and_iris() {
    let body = "ObjectIntersectionOf(:Machine ObjectSomeValuesFrom(:hasPart ObjectComplementOf(:FaultyPart)) ObjectUnionOf(:Pump <https://example.org/other#Valve>))\n)";
    let (bytes, result) = read(body, &limits(5, 10));
    let (class, remaining) = result.unwrap_or_else(|_| panic!("fixture must be accepted"));
    assert_eq!(
        text(&class),
        "and(Machine,some(hasPart,not(FaultyPart)),or(Pump,https://example.org/other#Valve))"
    );
    match &class {
        SourceClass::IntersectionOf { keyword, members } => {
            assert!(matches!(
                keyword.terminal,
                Terminal::Keyword(Keyword::ObjectIntersectionOf)
            ));
            assert_eq!(keyword.start, offset(&bytes, "ObjectIntersectionOf", 0));
            match &members[0] {
                SourceClass::Named(iri) => {
                    assert_eq!(iri.token.start, offset(&bytes, ":Machine", 0));
                    assert_eq!(iri.value, format!("{EX}Machine").into_bytes());
                }
                _ => panic!("the first member is named"),
            }
        }
        _ => panic!("the outer expression is an intersection"),
    }
    // The suffix starts at the ontology's closing parenthesis.
    match remaining {
        Tokens::Cons { token, next } => {
            assert!(matches!(token.terminal, Terminal::Close));
            assert!(matches!(*next, Tokens::Empty));
        }
        Tokens::Empty => panic!("the closing parenthesis remains"),
    }
}

#[test]
fn inverse_properties_and_universal_restrictions() {
    let (_, result) = read(
        "ObjectAllValuesFrom(ObjectInverseOf(:partOf) ObjectAllValuesFrom(:hasPart :Part))",
        &limits(5, 10),
    );
    let (class, _) = result.unwrap_or_else(|_| panic!("fixture must be accepted"));
    assert_eq!(text(&class), "all(inv(partOf),all(hasPart,Part))");
}

#[test]
fn enumerations_and_individual_values_keep_their_individuals() {
    let (bytes, result) = read(
        "ObjectUnionOf(ObjectOneOf(:pump1 _:spare <https://example.org/other#p>) ObjectHasValue(ObjectInverseOf(:hasPart) :motor1))",
        &limits(5, 10),
    );
    let (class, _) = result.unwrap_or_else(|_| panic!("fixture must be accepted"));
    assert_eq!(
        text(&class),
        "or(one(pump1,_:spare,https://example.org/other#p),value(inv(hasPart),motor1))"
    );
    match &class {
        SourceClass::UnionOf { members, .. } => match &members[0] {
            SourceClass::OneOf { keyword, members } => {
                assert!(matches!(
                    keyword.terminal,
                    Terminal::Keyword(Keyword::ObjectOneOf)
                ));
                assert_eq!(keyword.start, offset(&bytes, "ObjectOneOf", 0));
                assert_eq!(members.len(), 3);
            }
            _ => panic!("the first member is an enumeration"),
        },
        _ => panic!("the outer expression is a union"),
    }
    let (_, result) = read("ObjectOneOf(:pump1)", &limits(1, 10));
    let (class, _) = result.unwrap_or_else(|_| panic!("one individual suffices"));
    assert_eq!(text(&class), "one(pump1)");
    // An empty enumeration expects an individual where it stops.
    let (bytes, result) = read("ObjectOneOf()", &limits(5, 10));
    match result {
        Err(ClassError::Individual(IndividualError::Expected { offset: at })) => {
            assert_eq!(at, offset(&bytes, ")", 1))
        }
        _ => panic!("an enumeration needs an individual"),
    }
    // A class where the individual value belongs.
    let (bytes, result) = read("ObjectHasValue(:hasPart :Motor :extra)", &limits(5, 10));
    match result {
        Err(ClassError::Expected {
            expected: ClassExpected::Close,
            offset: at,
        }) => assert_eq!(at, offset(&bytes, ":extra", 0)),
        _ => panic!("one individual value is followed by `)`"),
    }
    let (bytes, result) = read("ObjectHasValue(:hasPart \"motor\")", &limits(5, 10));
    match result {
        Err(ClassError::Individual(IndividualError::Expected { offset: at })) => {
            assert_eq!(at, offset(&bytes, "\"motor\"", 0))
        }
        _ => panic!("a literal is not an individual"),
    }
    let (bytes, result) = read("ObjectOneOf(:a undeclared:b)", &limits(5, 10));
    match result {
        Err(ClassError::Individual(IndividualError::Iri(SourceIriError::UndeclaredPrefix {
            offset: at,
        }))) => assert_eq!(at, offset(&bytes, "undeclared:b", 0)),
        _ => panic!("undeclared prefixes in individuals are reported with their offset"),
    }
    // Enumerations share the member count and the nesting allowance.
    let (bytes, result) = read("ObjectOneOf(:a :b :c)", &limits(5, 2));
    match result {
        Err(ClassError::Individual(IndividualError::CountLimit { offset: at })) => {
            assert_eq!(at, offset(&bytes, ":c", 0))
        }
        _ => panic!("individuals beyond the count are reported"),
    }
    let (bytes, result) = read("ObjectHasValue(:p :a)", &limits(0, 10));
    match result {
        Err(ClassError::DepthLimit { offset: at }) => {
            assert_eq!(at, offset(&bytes, "ObjectHasValue", 0))
        }
        _ => panic!("value restrictions use one nesting level"),
    }
}

#[test]
fn self_and_number_restrictions_keep_their_numbers_and_fillers() {
    let (bytes, result) = read(
        "ObjectIntersectionOf(ObjectHasSelf(ObjectInverseOf(:monitors)) ObjectMinCardinality(002 :hasPart :Pump) ObjectMaxCardinality(0 :hasPart) ObjectExactCardinality(10 ObjectInverseOf(:partOf) ObjectComplementOf(:Valve)))",
        &limits(5, 10),
    );
    let (class, _) = result.unwrap_or_else(|_| panic!("fixture must be accepted"));
    assert_eq!(
        text(&class),
        "and(self(inv(monitors)),min(2,hasPart,Pump),max(0,hasPart),exact(10,inv(partOf),not(Valve)))"
    );
    match &class {
        SourceClass::IntersectionOf { members, .. } => match &members[1] {
            SourceClass::Cardinality {
                keyword, number, ..
            } => {
                assert!(matches!(
                    keyword.terminal,
                    Terminal::Keyword(Keyword::ObjectMinCardinality)
                ));
                assert!(matches!(number.terminal, Terminal::Integer));
                assert_eq!(number.start, offset(&bytes, "002", 0));
                assert_eq!(number.end, offset(&bytes, "002", 0) + 3);
            }
            _ => panic!("the second member is a number restriction"),
        },
        _ => panic!("the outer expression is an intersection"),
    }
}

#[test]
fn numbers_are_checked_against_the_count_limit_before_the_property() {
    let (_, result) = read("ObjectMaxCardinality(10 :hasPart)", &limits(5, 10));
    assert!(result.is_ok(), "a number at the count limit is accepted");
    let (bytes, result) = read("ObjectMaxCardinality(0011 undeclared:p)", &limits(5, 10));
    match result {
        Err(ClassError::CountLimit { offset: at }) => assert_eq!(at, offset(&bytes, "0011", 0)),
        _ => panic!("numbers above the count limit are reported at the number"),
    }
    // A number far beyond any machine integer is rejected without its value.
    let huge = "9".repeat(5000);
    let (bytes, result) = read(&format!("ObjectMinCardinality({huge} :p)"), &limits(5, 10));
    match result {
        Err(ClassError::CountLimit { offset: at }) => assert_eq!(at, offset(&bytes, &huge, 0)),
        _ => panic!("huge numbers are reported at the number"),
    }
    let (bytes, result) = read("ObjectMinCardinality(:p 1)", &limits(5, 10));
    assert_eq!(expected(result), ("number", offset(&bytes, ":p", 0)));
    let (bytes, result) = read("ObjectMinCardinality(", &limits(5, 10));
    assert_eq!(expected(result), ("number", bytes.len()));
    let (bytes, result) = read("ObjectExactCardinality(1 :p :A :B)", &limits(5, 10));
    assert_eq!(expected(result), ("close", offset(&bytes, ":B", 0)));
    let (bytes, result) = read("ObjectExactCardinality(1 :p", &limits(5, 10));
    assert_eq!(expected(result), ("close", bytes.len()));
    let (bytes, result) = read("ObjectHasSelf(:p :q)", &limits(5, 10));
    assert_eq!(expected(result), ("close", offset(&bytes, ":q", 0)));
    let (bytes, result) = read(
        "ObjectMinCardinality(1 :p ObjectComplementOf(:A))",
        &limits(1, 10),
    );
    match result {
        Err(ClassError::DepthLimit { offset: at }) => {
            assert_eq!(at, offset(&bytes, "ObjectComplementOf", 0))
        }
        _ => panic!("fillers are one level deeper"),
    }
}

#[test]
fn data_restrictions_read_one_property_and_their_ranges() {
    let (bytes, result) = read(
        "ObjectIntersectionOf(DataSomeValuesFrom(:dose <http://www.w3.org/2001/XMLSchema#integer>) DataAllValuesFrom(:code DataOneOf(\"a\" \"b\")) DataHasValue(:dose \"5\"^^<http://www.w3.org/2001/XMLSchema#integer>) DataMinCardinality(2 :dose) DataExactCardinality(01 :dose DatatypeRestriction(:Dose :minimum \"1\")))",
        &limits(5, 10),
    );
    let (class, _) = result.unwrap_or_else(|_| panic!("fixture must be accepted"));
    assert_eq!(
        text(&class),
        "and(dsome(dose,http://www.w3.org/2001/XMLSchema#integer),dall(code,done[2]),dvalue(dose,5),dmin(2,dose),dexact(1,dose,facets(Dose,1)))"
    );
    match &class {
        SourceClass::IntersectionOf { members, .. } => match &members[2] {
            SourceClass::DataHasValue { keyword, value, .. } => {
                assert!(matches!(
                    keyword.terminal,
                    Terminal::Keyword(Keyword::DataHasValue)
                ));
                assert_eq!(
                    value.datatype,
                    b"http://www.w3.org/2001/XMLSchema#integer".to_vec()
                );
                assert_eq!(value.quoted.start, offset(&bytes, "\"5\"", 0));
            }
            _ => panic!("the third member is a data value restriction"),
        },
        _ => panic!("the outer expression is an intersection"),
    }
    // Every OWL 2 data range is unary, so a second data property is read as
    // the data range and the real range is where `)` is expected.
    let (bytes, result) = read("DataSomeValuesFrom(:d :e :Range)", &limits(5, 10));
    assert_eq!(expected(result), ("close", offset(&bytes, ":Range", 0)));
    let (bytes, result) = read(
        "DataSomeValuesFrom(ObjectInverseOf(:p) :Range)",
        &limits(5, 10),
    );
    assert_eq!(
        expected(result),
        ("iri", offset(&bytes, "ObjectInverseOf", 0))
    );
    let (_, result) = read("DataHasValue(:d :e)", &limits(5, 10));
    assert!(matches!(result, Err(ClassError::Literal(_))));
    let (bytes, result) = read("DataMaxCardinality(11 :d)", &limits(5, 10));
    match result {
        Err(ClassError::CountLimit { offset: at }) => assert_eq!(at, offset(&bytes, "11", 0)),
        _ => panic!("data numbers share the count limit"),
    }
    // Data ranges nest within the same depth.
    let (bytes, result) = read(
        "DataSomeValuesFrom(:d DataComplementOf(:Range))",
        &limits(1, 10),
    );
    match result {
        Err(ClassError::Range(RangeError::DepthLimit { offset: at })) => {
            assert_eq!(at, offset(&bytes, "DataComplementOf", 0))
        }
        _ => panic!("data ranges are one level deeper"),
    }
    let (_, result) = read(
        "DataSomeValuesFrom(:d DataComplementOf(:Range))",
        &limits(2, 10),
    );
    assert!(result.is_ok());
}

#[test]
fn errors_follow_source_order() {
    let (bytes, result) = read("ObjectIntersectionOf(:A)", &limits(5, 10));
    assert_eq!(expected(result), ("class", offset(&bytes, ")", 1)));
    let (bytes, result) = read("ObjectComplementOf(", &limits(5, 10));
    assert_eq!(expected(result), ("class", bytes.len()));
    let (bytes, result) = read("ObjectSomeValuesFrom(:p)", &limits(5, 10));
    assert_eq!(expected(result), ("class", offset(&bytes, ")", 1)));
    let (bytes, result) = read("ObjectComplementOf :A)", &limits(5, 10));
    assert_eq!(expected(result), ("open", offset(&bytes, ":A", 0)));
    let (bytes, result) = read(
        "ObjectSomeValuesFrom(ObjectComplementOf(:A) :B)",
        &limits(5, 10),
    );
    assert_eq!(
        expected(result),
        ("property", offset(&bytes, "ObjectComplementOf", 0))
    );
    let (bytes, result) = read(
        "ObjectSomeValuesFrom(ObjectInverseOf(:p :A)",
        &limits(5, 10),
    );
    assert_eq!(expected(result), ("close", offset(&bytes, ":A", 0)));
    let (bytes, result) = read("ObjectComplementOf(:A :B)", &limits(5, 10));
    assert_eq!(expected(result), ("close", offset(&bytes, ":B", 0)));
    let (bytes, result) = read("ObjectUnionOf(:A DataSomeValuesFrom(:d))", &limits(5, 10));
    match result {
        Err(ClassError::Range(RangeError::Expected {
            expected: RangeExpected::Range,
            offset: at,
        })) => assert_eq!(at, offset(&bytes, ")", 1)),
        _ => panic!("a data restriction needs its data range"),
    }
    let (bytes, result) = read("ObjectUnionOf(:A undeclared:B)", &limits(5, 10));
    match result {
        Err(ClassError::Iri(SourceIriError::UndeclaredPrefix { offset: at })) => {
            assert_eq!(at, offset(&bytes, "undeclared:B", 0))
        }
        _ => panic!("undeclared prefixes are reported with their offset"),
    }
}

#[test]
fn depth_and_count_limits_are_checked_at_their_keyword_and_member() {
    let body = "ObjectComplementOf(ObjectComplementOf(:A))";
    let (_, result) = read(body, &limits(2, 10));
    assert!(result.is_ok());
    let (bytes, result) = read(body, &limits(1, 10));
    match result {
        Err(ClassError::DepthLimit { offset: at }) => {
            assert_eq!(at, offset(&bytes, "ObjectComplementOf", 1))
        }
        _ => panic!("nesting beyond the allowance is reported"),
    }
    let (_, result) = read(":A", &limits(0, 10));
    assert!(result.is_ok(), "named classes need no nesting allowance");
    let body = "ObjectUnionOf(:A :B :C)";
    let (_, result) = read(body, &limits(5, 3));
    assert!(result.is_ok());
    let (bytes, result) = read(body, &limits(5, 2));
    match result {
        Err(ClassError::CountLimit { offset: at }) => assert_eq!(at, offset(&bytes, ":C", 0)),
        _ => panic!("members beyond the count are reported"),
    }
}

#[test]
fn object_properties_read_alone() {
    let source = format!("Prefix(:=<{EX}>)\nOntology(<https://example.org/maintenance>\nObjectInverseOf(:partOf) :hasPart\n)");
    let bytes = source.as_bytes().to_vec();
    let prefix = read_prefix_header(&bytes, 400, 10, 100).unwrap_or_else(|_| panic!("prefixes"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    let (first, rest) = read_object_property(&table, &bytes, header.remaining, 100)
        .unwrap_or_else(|_| panic!("inverse property"));
    let (second, _) =
        read_object_property(&table, &bytes, rest, 100).unwrap_or_else(|_| panic!("property"));
    assert_eq!(property_text(&first), "inv(partOf)");
    assert_eq!(property_text(&second), "hasPart");
}

/// A deterministic pseudo-random expression in Functional Syntax, together
/// with its expected rendering.
fn random_expression(seed: &mut u64, depth: u32) -> (String, String) {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let choice = (*seed >> 33) % if depth == 0 { 2 } else { 9 };
    match choice {
        0 => (":A".to_string(), "A".to_string()),
        1 => (format!("<{EX}B>"), "B".to_string()),
        2 | 3 => {
            let keyword = if choice == 2 {
                "ObjectIntersectionOf"
            } else {
                "ObjectUnionOf"
            };
            let count = 2 + (*seed >> 40) as usize % 2;
            let parts: Vec<(String, String)> = (0..count)
                .map(|_| random_expression(seed, depth - 1))
                .collect();
            let source = parts
                .iter()
                .map(|p| p.0.clone())
                .collect::<Vec<_>>()
                .join(" ");
            let shape = parts
                .iter()
                .map(|p| p.1.clone())
                .collect::<Vec<_>>()
                .join(",");
            let name = if choice == 2 { "and" } else { "or" };
            (format!("{keyword}( {source} )"), format!("{name}({shape})"))
        }
        4 => {
            let (source, shape) = random_expression(seed, depth - 1);
            (
                format!("ObjectComplementOf({source})"),
                format!("not({shape})"),
            )
        }
        7 => {
            let inverse = (*seed >> 41) % 2 == 1;
            let (property, property_shape) = if inverse {
                ("ObjectInverseOf(:R)", "inv(R)")
            } else {
                (":R", "R")
            };
            (
                format!("ObjectHasSelf({property})"),
                format!("self({property_shape})"),
            )
        }
        8 => {
            let (keyword, bound) = match (*seed >> 42) % 3 {
                0 => ("ObjectMinCardinality", "min"),
                1 => ("ObjectMaxCardinality", "max"),
                _ => ("ObjectExactCardinality", "exact"),
            };
            let value = (*seed >> 44) % 11;
            let zeros = "0".repeat(((*seed >> 48) % 3) as usize);
            if (*seed >> 50) % 2 == 1 {
                let (source, shape) = random_expression(seed, depth - 1);
                (
                    format!("{keyword}({zeros}{value} :R {source})"),
                    format!("{bound}({value},R,{shape})"),
                )
            } else {
                (
                    format!("{keyword}({zeros}{value} :R)"),
                    format!("{bound}({value},R)"),
                )
            }
        }
        _ => {
            let inverse = (*seed >> 41) % 2 == 1;
            let (property, property_shape) = if inverse {
                ("ObjectInverseOf(:R)", "inv(R)")
            } else {
                (":R", "R")
            };
            let (source, shape) = random_expression(seed, depth - 1);
            if choice == 5 {
                (
                    format!("ObjectSomeValuesFrom({property} {source})"),
                    format!("some({property_shape},{shape})"),
                )
            } else {
                (
                    format!("ObjectAllValuesFrom({property} {source})"),
                    format!("all({property_shape},{shape})"),
                )
            }
        }
    }
}

#[test]
fn printed_expressions_read_back_to_their_shape() {
    let mut seed = 7;
    for _ in 0..120 {
        let (source, shape) = random_expression(&mut seed, 4);
        let (_, result) = read(&format!("{source}\n)"), &limits(10, 10));
        let (class, _) = result.unwrap_or_else(|_| panic!("printed expression must read back"));
        assert_eq!(text(&class), shape);
    }
}
