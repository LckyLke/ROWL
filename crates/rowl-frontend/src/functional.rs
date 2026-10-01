//! Complete OWL 2 Functional Syntax terminal grammars (2012 edition).
//! Whole-byte matching and greedy matching share these same compiled grammars.
//! This module does not decode token payloads or assemble an OWL ontology.
use crate::longest::{longest_prefix, PrefixResult};
use crate::regular::{matches_utf8, Expression, MatchResult};
use crate::{iri, langtag, names};

#[derive(Clone, Copy)]
pub enum Keyword {
    Prefix,
    Ontology,
    Import,
    Declaration,
    Class,
    Datatype,
    ObjectProperty,
    DataProperty,
    AnnotationProperty,
    NamedIndividual,
    Annotation,
    AnnotationAssertion,
    SubAnnotationPropertyOf,
    AnnotationPropertyDomain,
    AnnotationPropertyRange,
    ObjectInverseOf,
    DataIntersectionOf,
    DataUnionOf,
    DataComplementOf,
    DataOneOf,
    DatatypeRestriction,
    ObjectIntersectionOf,
    ObjectUnionOf,
    ObjectComplementOf,
    ObjectOneOf,
    ObjectSomeValuesFrom,
    ObjectAllValuesFrom,
    ObjectHasValue,
    ObjectHasSelf,
    ObjectMinCardinality,
    ObjectMaxCardinality,
    ObjectExactCardinality,
    DataSomeValuesFrom,
    DataAllValuesFrom,
    DataHasValue,
    DataMinCardinality,
    DataMaxCardinality,
    DataExactCardinality,
    SubClassOf,
    EquivalentClasses,
    DisjointClasses,
    DisjointUnion,
    SubObjectPropertyOf,
    ObjectPropertyChain,
    EquivalentObjectProperties,
    DisjointObjectProperties,
    ObjectPropertyDomain,
    ObjectPropertyRange,
    InverseObjectProperties,
    FunctionalObjectProperty,
    InverseFunctionalObjectProperty,
    ReflexiveObjectProperty,
    IrreflexiveObjectProperty,
    SymmetricObjectProperty,
    AsymmetricObjectProperty,
    TransitiveObjectProperty,
    SubDataPropertyOf,
    EquivalentDataProperties,
    DisjointDataProperties,
    DataPropertyDomain,
    DataPropertyRange,
    FunctionalDataProperty,
    DatatypeDefinition,
    HasKey,
    SameIndividual,
    DifferentIndividuals,
    ClassAssertion,
    ObjectPropertyAssertion,
    NegativeObjectPropertyAssertion,
    DataPropertyAssertion,
    NegativeDataPropertyAssertion,
}
#[derive(Clone, Copy)]
pub enum Terminal {
    Keyword(Keyword),
    Open,
    Close,
    Equals,
    DatatypeIndicator,
    Integer,
    QuotedString,
    LanguageTag,
    NodeId,
    FullIri,
    PrefixName,
    AbbreviatedIri,
    Whitespace,
    Comment,
}
fn range(lower: u32, upper: u32) -> Expression {
    Expression::Interval { lower, upper }
}
fn ch(cp: u32) -> Expression {
    range(cp, cp)
}
fn alt(a: Expression, b: Expression) -> Expression {
    Expression::Alternative(Box::new(a), Box::new(b))
}
fn cat(a: Expression, b: Expression) -> Expression {
    Expression::Sequence(Box::new(a), Box::new(b))
}
fn star(a: Expression) -> Expression {
    Expression::Repeat(Box::new(a))
}
fn literal_from(bytes: &[u8], position: usize) -> Expression {
    if position < bytes.len() {
        cat(
            ch(u32::from(bytes[position])),
            literal_from(bytes, position + 1),
        )
    } else {
        Expression::Epsilon
    }
}
fn literal(bytes: &[u8]) -> Expression {
    literal_from(bytes, 0)
}
/// Exact case-sensitive ASCII keyword; every normative keyword is represented.
pub fn keyword_grammar(keyword: Keyword) -> Expression {
    match keyword {
        Keyword::Prefix => literal(b"Prefix"),
        Keyword::Ontology => literal(b"Ontology"),
        Keyword::Import => literal(b"Import"),
        Keyword::Declaration => literal(b"Declaration"),
        Keyword::Class => literal(b"Class"),
        Keyword::Datatype => literal(b"Datatype"),
        Keyword::ObjectProperty => literal(b"ObjectProperty"),
        Keyword::DataProperty => literal(b"DataProperty"),
        Keyword::AnnotationProperty => literal(b"AnnotationProperty"),
        Keyword::NamedIndividual => literal(b"NamedIndividual"),
        Keyword::Annotation => literal(b"Annotation"),
        Keyword::AnnotationAssertion => literal(b"AnnotationAssertion"),
        Keyword::SubAnnotationPropertyOf => literal(b"SubAnnotationPropertyOf"),
        Keyword::AnnotationPropertyDomain => literal(b"AnnotationPropertyDomain"),
        Keyword::AnnotationPropertyRange => literal(b"AnnotationPropertyRange"),
        Keyword::ObjectInverseOf => literal(b"ObjectInverseOf"),
        Keyword::DataIntersectionOf => literal(b"DataIntersectionOf"),
        Keyword::DataUnionOf => literal(b"DataUnionOf"),
        Keyword::DataComplementOf => literal(b"DataComplementOf"),
        Keyword::DataOneOf => literal(b"DataOneOf"),
        Keyword::DatatypeRestriction => literal(b"DatatypeRestriction"),
        Keyword::ObjectIntersectionOf => literal(b"ObjectIntersectionOf"),
        Keyword::ObjectUnionOf => literal(b"ObjectUnionOf"),
        Keyword::ObjectComplementOf => literal(b"ObjectComplementOf"),
        Keyword::ObjectOneOf => literal(b"ObjectOneOf"),
        Keyword::ObjectSomeValuesFrom => literal(b"ObjectSomeValuesFrom"),
        Keyword::ObjectAllValuesFrom => literal(b"ObjectAllValuesFrom"),
        Keyword::ObjectHasValue => literal(b"ObjectHasValue"),
        Keyword::ObjectHasSelf => literal(b"ObjectHasSelf"),
        Keyword::ObjectMinCardinality => literal(b"ObjectMinCardinality"),
        Keyword::ObjectMaxCardinality => literal(b"ObjectMaxCardinality"),
        Keyword::ObjectExactCardinality => literal(b"ObjectExactCardinality"),
        Keyword::DataSomeValuesFrom => literal(b"DataSomeValuesFrom"),
        Keyword::DataAllValuesFrom => literal(b"DataAllValuesFrom"),
        Keyword::DataHasValue => literal(b"DataHasValue"),
        Keyword::DataMinCardinality => literal(b"DataMinCardinality"),
        Keyword::DataMaxCardinality => literal(b"DataMaxCardinality"),
        Keyword::DataExactCardinality => literal(b"DataExactCardinality"),
        Keyword::SubClassOf => literal(b"SubClassOf"),
        Keyword::EquivalentClasses => literal(b"EquivalentClasses"),
        Keyword::DisjointClasses => literal(b"DisjointClasses"),
        Keyword::DisjointUnion => literal(b"DisjointUnion"),
        Keyword::SubObjectPropertyOf => literal(b"SubObjectPropertyOf"),
        Keyword::ObjectPropertyChain => literal(b"ObjectPropertyChain"),
        Keyword::EquivalentObjectProperties => literal(b"EquivalentObjectProperties"),
        Keyword::DisjointObjectProperties => literal(b"DisjointObjectProperties"),
        Keyword::ObjectPropertyDomain => literal(b"ObjectPropertyDomain"),
        Keyword::ObjectPropertyRange => literal(b"ObjectPropertyRange"),
        Keyword::InverseObjectProperties => literal(b"InverseObjectProperties"),
        Keyword::FunctionalObjectProperty => literal(b"FunctionalObjectProperty"),
        Keyword::InverseFunctionalObjectProperty => literal(b"InverseFunctionalObjectProperty"),
        Keyword::ReflexiveObjectProperty => literal(b"ReflexiveObjectProperty"),
        Keyword::IrreflexiveObjectProperty => literal(b"IrreflexiveObjectProperty"),
        Keyword::SymmetricObjectProperty => literal(b"SymmetricObjectProperty"),
        Keyword::AsymmetricObjectProperty => literal(b"AsymmetricObjectProperty"),
        Keyword::TransitiveObjectProperty => literal(b"TransitiveObjectProperty"),
        Keyword::SubDataPropertyOf => literal(b"SubDataPropertyOf"),
        Keyword::EquivalentDataProperties => literal(b"EquivalentDataProperties"),
        Keyword::DisjointDataProperties => literal(b"DisjointDataProperties"),
        Keyword::DataPropertyDomain => literal(b"DataPropertyDomain"),
        Keyword::DataPropertyRange => literal(b"DataPropertyRange"),
        Keyword::FunctionalDataProperty => literal(b"FunctionalDataProperty"),
        Keyword::DatatypeDefinition => literal(b"DatatypeDefinition"),
        Keyword::HasKey => literal(b"HasKey"),
        Keyword::SameIndividual => literal(b"SameIndividual"),
        Keyword::DifferentIndividuals => literal(b"DifferentIndividuals"),
        Keyword::ClassAssertion => literal(b"ClassAssertion"),
        Keyword::ObjectPropertyAssertion => literal(b"ObjectPropertyAssertion"),
        Keyword::NegativeObjectPropertyAssertion => literal(b"NegativeObjectPropertyAssertion"),
        Keyword::DataPropertyAssertion => literal(b"DataPropertyAssertion"),
        Keyword::NegativeDataPropertyAssertion => literal(b"NegativeDataPropertyAssertion"),
    }
}
fn digits() -> Expression {
    cat(range(48, 57), star(range(48, 57)))
}
fn quoted_raw() -> Expression {
    alt(
        ch(9),
        alt(
            ch(10),
            alt(
                ch(13),
                alt(
                    range(32, 33),
                    alt(
                        range(35, 91),
                        alt(
                            range(93, 0xd7ff),
                            alt(range(0xe000, 0xfffd), range(0x10000, 0x10ffff)),
                        ),
                    ),
                ),
            ),
        ),
    )
}
fn quoted() -> Expression {
    cat(
        ch(34),
        cat(
            star(alt(quoted_raw(), cat(ch(92), alt(ch(34), ch(92))))),
            ch(34),
        ),
    )
}
fn space() -> Expression {
    alt(ch(32), alt(ch(9), alt(ch(10), ch(13))))
}
fn whitespace() -> Expression {
    cat(space(), star(space()))
}
fn comment_raw() -> Expression {
    alt(
        ch(9),
        alt(
            range(32, 0xd7ff),
            alt(range(0xe000, 0xfffd), range(0x10000, 0x10ffff)),
        ),
    )
}
fn comment() -> Expression {
    cat(ch(35), star(comment_raw()))
}
/// Compile any standard terminal grammar, including whitespace and comments.
pub fn grammar(terminal: Terminal) -> Expression {
    match terminal {
        Terminal::Keyword(keyword) => keyword_grammar(keyword),
        Terminal::Open => ch(40),
        Terminal::Close => ch(41),
        Terminal::Equals => ch(61),
        Terminal::DatatypeIndicator => cat(ch(94), ch(94)),
        Terminal::Integer => digits(),
        Terminal::QuotedString => quoted(),
        Terminal::LanguageTag => cat(ch(64), langtag::normal_grammar()),
        Terminal::NodeId => names::node_grammar(),
        Terminal::FullIri => cat(ch(60), cat(iri::iri(), ch(62))),
        Terminal::PrefixName => names::prefix_grammar(),
        Terminal::AbbreviatedIri => names::abbreviated_grammar(),
        Terminal::Whitespace => whitespace(),
        Terminal::Comment => comment(),
    }
}
/// Whole-byte token recognition, with exact malformed UTF-8 diagnostics.
#[allow(clippy::ptr_arg)]
pub fn recognize(terminal: Terminal, bytes: &Vec<u8>) -> MatchResult {
    matches_utf8(grammar(terminal), bytes)
}
/// Greedy byte-prefix matching for any standard terminal. Empty matches are
/// excluded by every terminal grammar. Token identification and separator policy
/// are supplied by the document lexer separately.
#[allow(clippy::ptr_arg)]
pub fn longest(terminal: Terminal, bytes: &Vec<u8>, position: usize) -> PrefixResult {
    longest_prefix(grammar(terminal), bytes, position)
}

/// A selected source span; payload decoding remains the parser's responsibility.
pub struct Token {
    pub terminal: Terminal,
    pub start: usize,
    pub end: usize,
}
pub enum Selection {
    NoMatch,
    Token(Token),
    MalformedUtf8(crate::unicode::TextError),
}
fn seed(terminal: Terminal, bytes: &Vec<u8>, position: usize) -> Selection {
    match longest(terminal, bytes, position) {
        PrefixResult::Matched(None) => Selection::NoMatch,
        PrefixResult::Matched(Some(end)) => Selection::Token(Token {
            terminal,
            start: position,
            end,
        }),
        PrefixResult::MalformedUtf8(error) => Selection::MalformedUtf8(error),
    }
}
fn extend(terminal: Terminal, bytes: &Vec<u8>, position: usize, previous: Selection) -> Selection {
    match previous {
        Selection::MalformedUtf8(error) => Selection::MalformedUtf8(error),
        Selection::NoMatch => seed(terminal, bytes, position),
        Selection::Token(prior) => match longest(terminal, bytes, position) {
            PrefixResult::MalformedUtf8(error) => Selection::MalformedUtf8(error),
            PrefixResult::Matched(None) => Selection::Token(prior),
            PrefixResult::Matched(Some(end)) => {
                if end > prior.end {
                    Selection::Token(Token {
                        terminal,
                        start: position,
                        end,
                    })
                } else {
                    Selection::Token(prior)
                }
            }
        },
    }
}
/// Select the greatest byte endpoint across the entire standard terminal set.
/// Ties retain the earlier inventory entry deterministically. This is one lexical
/// selection step; separators, discarded tokens and document parsing are separate.
#[allow(clippy::ptr_arg)]
pub fn next_terminal(bytes: &Vec<u8>, position: usize) -> Selection {
    let choice = seed(Terminal::Keyword(Keyword::Prefix), bytes, position);
    let choice = extend(
        Terminal::Keyword(Keyword::Ontology),
        bytes,
        position,
        choice,
    );
    let choice = extend(Terminal::Keyword(Keyword::Import), bytes, position, choice);
    let choice = extend(
        Terminal::Keyword(Keyword::Declaration),
        bytes,
        position,
        choice,
    );
    let choice = extend(Terminal::Keyword(Keyword::Class), bytes, position, choice);
    let choice = extend(
        Terminal::Keyword(Keyword::Datatype),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::AnnotationProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::NamedIndividual),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::Annotation),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::AnnotationAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::SubAnnotationPropertyOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::AnnotationPropertyDomain),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::AnnotationPropertyRange),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectInverseOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataIntersectionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataUnionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataComplementOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataOneOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DatatypeRestriction),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectIntersectionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectUnionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectComplementOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectOneOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectSomeValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectAllValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectHasValue),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectHasSelf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectMinCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectMaxCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectExactCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataSomeValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataAllValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataHasValue),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataMinCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataMaxCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataExactCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::SubClassOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::EquivalentClasses),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DisjointClasses),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DisjointUnion),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::SubObjectPropertyOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectPropertyChain),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::EquivalentObjectProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DisjointObjectProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectPropertyDomain),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectPropertyRange),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::InverseObjectProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::FunctionalObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::InverseFunctionalObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ReflexiveObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::IrreflexiveObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::SymmetricObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::AsymmetricObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::TransitiveObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::SubDataPropertyOf),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::EquivalentDataProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DisjointDataProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataPropertyDomain),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataPropertyRange),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::FunctionalDataProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DatatypeDefinition),
        bytes,
        position,
        choice,
    );
    let choice = extend(Terminal::Keyword(Keyword::HasKey), bytes, position, choice);
    let choice = extend(
        Terminal::Keyword(Keyword::SameIndividual),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DifferentIndividuals),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ClassAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::ObjectPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::NegativeObjectPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::DataPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend(
        Terminal::Keyword(Keyword::NegativeDataPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend(Terminal::Open, bytes, position, choice);
    let choice = extend(Terminal::Close, bytes, position, choice);
    let choice = extend(Terminal::Equals, bytes, position, choice);
    let choice = extend(Terminal::DatatypeIndicator, bytes, position, choice);
    let choice = extend(Terminal::Integer, bytes, position, choice);
    let choice = extend(Terminal::QuotedString, bytes, position, choice);
    let choice = extend(Terminal::LanguageTag, bytes, position, choice);
    let choice = extend(Terminal::NodeId, bytes, position, choice);
    let choice = extend(Terminal::FullIri, bytes, position, choice);
    let choice = extend(Terminal::PrefixName, bytes, position, choice);
    let choice = extend(Terminal::AbbreviatedIri, bytes, position, choice);
    let choice = extend(Terminal::Whitespace, bytes, position, choice);
    extend(Terminal::Comment, bytes, position, choice)
}
