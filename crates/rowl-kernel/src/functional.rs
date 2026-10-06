//! Complete OWL 2 Functional Syntax terminal grammars (2012 edition).
//! Whole-byte matching and greedy matching share these same compiled grammars.
//! This module does not decode token payloads or assemble an OWL ontology.
use crate::longest::{longest_prefix, longest_valid_prefix, PrefixResult};
use crate::regular::{matches_utf8, Expression, MatchResult};
use crate::unicode::{decode_next, Decoded};
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
/// `longest` for text already validated as UTF-8 from `position`; the same
/// result there, without rescanning the rest of the text.
pub fn longest_valid(terminal: Terminal, bytes: &Vec<u8>, position: usize) -> PrefixResult {
    longest_valid_prefix(grammar(terminal), bytes, position)
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
/// `next_terminal` for text already validated as UTF-8 from `position`: the
/// same selection there, with each terminal's scan stopping as soon as it can
/// match no longer prefix.
pub fn next_terminal_valid(bytes: &Vec<u8>, position: usize) -> Selection {
    let choice = seed_valid(Terminal::Keyword(Keyword::Prefix), bytes, position);
    let choice = extend_valid(
        Terminal::Keyword(Keyword::Ontology),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(Terminal::Keyword(Keyword::Import), bytes, position, choice);
    let choice = extend_valid(
        Terminal::Keyword(Keyword::Declaration),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(Terminal::Keyword(Keyword::Class), bytes, position, choice);
    let choice = extend_valid(
        Terminal::Keyword(Keyword::Datatype),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::AnnotationProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::NamedIndividual),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::Annotation),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::AnnotationAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::SubAnnotationPropertyOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::AnnotationPropertyDomain),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::AnnotationPropertyRange),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectInverseOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataIntersectionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataUnionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataComplementOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataOneOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DatatypeRestriction),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectIntersectionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectUnionOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectComplementOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectOneOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectSomeValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectAllValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectHasValue),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectHasSelf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectMinCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectMaxCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectExactCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataSomeValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataAllValuesFrom),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataHasValue),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataMinCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataMaxCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataExactCardinality),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::SubClassOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::EquivalentClasses),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DisjointClasses),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DisjointUnion),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::SubObjectPropertyOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectPropertyChain),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::EquivalentObjectProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DisjointObjectProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectPropertyDomain),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectPropertyRange),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::InverseObjectProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::FunctionalObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::InverseFunctionalObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ReflexiveObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::IrreflexiveObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::SymmetricObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::AsymmetricObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::TransitiveObjectProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::SubDataPropertyOf),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::EquivalentDataProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DisjointDataProperties),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataPropertyDomain),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataPropertyRange),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::FunctionalDataProperty),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DatatypeDefinition),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(Terminal::Keyword(Keyword::HasKey), bytes, position, choice);
    let choice = extend_valid(
        Terminal::Keyword(Keyword::SameIndividual),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DifferentIndividuals),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ClassAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::ObjectPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::NegativeObjectPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::DataPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(
        Terminal::Keyword(Keyword::NegativeDataPropertyAssertion),
        bytes,
        position,
        choice,
    );
    let choice = extend_valid(Terminal::Open, bytes, position, choice);
    let choice = extend_valid(Terminal::Close, bytes, position, choice);
    let choice = extend_valid(Terminal::Equals, bytes, position, choice);
    let choice = extend_valid(Terminal::DatatypeIndicator, bytes, position, choice);
    let choice = extend_valid(Terminal::Integer, bytes, position, choice);
    let choice = extend_valid(Terminal::QuotedString, bytes, position, choice);
    let choice = extend_valid(Terminal::LanguageTag, bytes, position, choice);
    let choice = extend_valid(Terminal::NodeId, bytes, position, choice);
    let choice = extend_valid(Terminal::FullIri, bytes, position, choice);
    let choice = extend_valid(Terminal::PrefixName, bytes, position, choice);
    let choice = extend_valid(Terminal::AbbreviatedIri, bytes, position, choice);
    let choice = extend_valid(Terminal::Whitespace, bytes, position, choice);
    extend_valid(Terminal::Comment, bytes, position, choice)
}

/// The first code point of each keyword's spelling.
fn keyword_first(keyword: Keyword) -> u32 {
    match keyword {
        Keyword::Prefix => 80,
        Keyword::Ontology => 79,
        Keyword::Import => 73,
        Keyword::Declaration => 68,
        Keyword::Class => 67,
        Keyword::Datatype => 68,
        Keyword::ObjectProperty => 79,
        Keyword::DataProperty => 68,
        Keyword::AnnotationProperty => 65,
        Keyword::NamedIndividual => 78,
        Keyword::Annotation => 65,
        Keyword::AnnotationAssertion => 65,
        Keyword::SubAnnotationPropertyOf => 83,
        Keyword::AnnotationPropertyDomain => 65,
        Keyword::AnnotationPropertyRange => 65,
        Keyword::ObjectInverseOf => 79,
        Keyword::DataIntersectionOf => 68,
        Keyword::DataUnionOf => 68,
        Keyword::DataComplementOf => 68,
        Keyword::DataOneOf => 68,
        Keyword::DatatypeRestriction => 68,
        Keyword::ObjectIntersectionOf => 79,
        Keyword::ObjectUnionOf => 79,
        Keyword::ObjectComplementOf => 79,
        Keyword::ObjectOneOf => 79,
        Keyword::ObjectSomeValuesFrom => 79,
        Keyword::ObjectAllValuesFrom => 79,
        Keyword::ObjectHasValue => 79,
        Keyword::ObjectHasSelf => 79,
        Keyword::ObjectMinCardinality => 79,
        Keyword::ObjectMaxCardinality => 79,
        Keyword::ObjectExactCardinality => 79,
        Keyword::DataSomeValuesFrom => 68,
        Keyword::DataAllValuesFrom => 68,
        Keyword::DataHasValue => 68,
        Keyword::DataMinCardinality => 68,
        Keyword::DataMaxCardinality => 68,
        Keyword::DataExactCardinality => 68,
        Keyword::SubClassOf => 83,
        Keyword::EquivalentClasses => 69,
        Keyword::DisjointClasses => 68,
        Keyword::DisjointUnion => 68,
        Keyword::SubObjectPropertyOf => 83,
        Keyword::ObjectPropertyChain => 79,
        Keyword::EquivalentObjectProperties => 69,
        Keyword::DisjointObjectProperties => 68,
        Keyword::ObjectPropertyDomain => 79,
        Keyword::ObjectPropertyRange => 79,
        Keyword::InverseObjectProperties => 73,
        Keyword::FunctionalObjectProperty => 70,
        Keyword::InverseFunctionalObjectProperty => 73,
        Keyword::ReflexiveObjectProperty => 82,
        Keyword::IrreflexiveObjectProperty => 73,
        Keyword::SymmetricObjectProperty => 83,
        Keyword::AsymmetricObjectProperty => 65,
        Keyword::TransitiveObjectProperty => 84,
        Keyword::SubDataPropertyOf => 83,
        Keyword::EquivalentDataProperties => 69,
        Keyword::DisjointDataProperties => 68,
        Keyword::DataPropertyDomain => 68,
        Keyword::DataPropertyRange => 68,
        Keyword::FunctionalDataProperty => 70,
        Keyword::DatatypeDefinition => 68,
        Keyword::HasKey => 72,
        Keyword::SameIndividual => 83,
        Keyword::DifferentIndividuals => 68,
        Keyword::ClassAssertion => 67,
        Keyword::ObjectPropertyAssertion => 79,
        Keyword::NegativeObjectPropertyAssertion => 78,
        Keyword::DataPropertyAssertion => 68,
        Keyword::NegativeDataPropertyAssertion => 78,
    }
}
/// Whether a prefixed name can start with the code point: every PNAME_NS and
/// PNAME_LN begins with `:` or a PN_CHARS_BASE code point, whose ASCII members
/// are the letters.
#[allow(clippy::manual_range_contains)] // Keep comparisons explicit for extraction.
fn name_start(codepoint: u32) -> bool {
    codepoint == 58
        || (65 <= codepoint && codepoint <= 90)
        || (97 <= codepoint && codepoint <= 122)
        || 128 <= codepoint
}
/// Whether a token of the terminal can start with the code point: every token
/// of each terminal begins with its one code point or set.
#[allow(clippy::manual_range_contains)] // Keep comparisons explicit for extraction.
fn may_start(terminal: Terminal, codepoint: u32) -> bool {
    match terminal {
        Terminal::Keyword(keyword) => codepoint == keyword_first(keyword),
        Terminal::Open => codepoint == 40,
        Terminal::Close => codepoint == 41,
        Terminal::Equals => codepoint == 61,
        Terminal::DatatypeIndicator => codepoint == 94,
        Terminal::Integer => 48 <= codepoint && codepoint <= 57,
        Terminal::QuotedString => codepoint == 34,
        Terminal::LanguageTag => codepoint == 64,
        Terminal::NodeId => codepoint == 95,
        Terminal::FullIri => codepoint == 60,
        Terminal::PrefixName => name_start(codepoint),
        Terminal::AbbreviatedIri => name_start(codepoint),
        Terminal::Whitespace => {
            codepoint == 32 || codepoint == 9 || codepoint == 10 || codepoint == 13
        }
        Terminal::Comment => codepoint == 35,
    }
}
fn seed_from(terminal: Terminal, bytes: &Vec<u8>, position: usize, first: u32) -> Selection {
    if may_start(terminal, first) {
        seed_valid(terminal, bytes, position)
    } else {
        Selection::NoMatch
    }
}
fn extend_from(
    terminal: Terminal,
    bytes: &Vec<u8>,
    position: usize,
    first: u32,
    previous: Selection,
) -> Selection {
    if may_start(terminal, first) {
        extend_valid(terminal, bytes, position, previous)
    } else {
        previous
    }
}
fn next_terminal_from(bytes: &Vec<u8>, position: usize, first: u32) -> Selection {
    let choice = seed_from(Terminal::Keyword(Keyword::Prefix), bytes, position, first);
    let choice = extend_from(
        Terminal::Keyword(Keyword::Ontology),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::Import),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::Declaration),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::Class),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::Datatype),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::AnnotationProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::NamedIndividual),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::Annotation),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::AnnotationAssertion),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::SubAnnotationPropertyOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::AnnotationPropertyDomain),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::AnnotationPropertyRange),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectInverseOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataIntersectionOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataUnionOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataComplementOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataOneOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DatatypeRestriction),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectIntersectionOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectUnionOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectComplementOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectOneOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectSomeValuesFrom),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectAllValuesFrom),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectHasValue),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectHasSelf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectMinCardinality),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectMaxCardinality),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectExactCardinality),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataSomeValuesFrom),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataAllValuesFrom),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataHasValue),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataMinCardinality),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataMaxCardinality),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataExactCardinality),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::SubClassOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::EquivalentClasses),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DisjointClasses),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DisjointUnion),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::SubObjectPropertyOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectPropertyChain),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::EquivalentObjectProperties),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DisjointObjectProperties),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectPropertyDomain),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectPropertyRange),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::InverseObjectProperties),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::FunctionalObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::InverseFunctionalObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ReflexiveObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::IrreflexiveObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::SymmetricObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::AsymmetricObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::TransitiveObjectProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::SubDataPropertyOf),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::EquivalentDataProperties),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DisjointDataProperties),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataPropertyDomain),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataPropertyRange),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::FunctionalDataProperty),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DatatypeDefinition),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::HasKey),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::SameIndividual),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DifferentIndividuals),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ClassAssertion),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::ObjectPropertyAssertion),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::NegativeObjectPropertyAssertion),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::DataPropertyAssertion),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(
        Terminal::Keyword(Keyword::NegativeDataPropertyAssertion),
        bytes,
        position,
        first,
        choice,
    );
    let choice = extend_from(Terminal::Open, bytes, position, first, choice);
    let choice = extend_from(Terminal::Close, bytes, position, first, choice);
    let choice = extend_from(Terminal::Equals, bytes, position, first, choice);
    let choice = extend_from(Terminal::DatatypeIndicator, bytes, position, first, choice);
    let choice = extend_from(Terminal::Integer, bytes, position, first, choice);
    let choice = extend_from(Terminal::QuotedString, bytes, position, first, choice);
    let choice = extend_from(Terminal::LanguageTag, bytes, position, first, choice);
    let choice = extend_from(Terminal::NodeId, bytes, position, first, choice);
    let choice = extend_from(Terminal::FullIri, bytes, position, first, choice);
    let choice = extend_from(Terminal::PrefixName, bytes, position, first, choice);
    let choice = extend_from(Terminal::AbbreviatedIri, bytes, position, first, choice);
    let choice = extend_from(Terminal::Whitespace, bytes, position, first, choice);
    extend_from(Terminal::Comment, bytes, position, first, choice)
}
/// `next_terminal` for text already validated as UTF-8 from `position`, trying
/// only the terminals whose tokens can start with the code point there: the
/// same selection, without building the grammars that cannot match.
pub fn next_terminal_fast(bytes: &Vec<u8>, position: usize) -> Selection {
    match decode_next(bytes, position) {
        Decoded::Scalar { codepoint, .. } => next_terminal_from(bytes, position, codepoint),
        _ => next_terminal_valid(bytes, position),
    }
}
fn seed_valid(terminal: Terminal, bytes: &Vec<u8>, position: usize) -> Selection {
    match longest_valid(terminal, bytes, position) {
        PrefixResult::Matched(None) => Selection::NoMatch,
        PrefixResult::Matched(Some(end)) => Selection::Token(Token {
            terminal,
            start: position,
            end,
        }),
        PrefixResult::MalformedUtf8(error) => Selection::MalformedUtf8(error),
    }
}
fn extend_valid(
    terminal: Terminal,
    bytes: &Vec<u8>,
    position: usize,
    previous: Selection,
) -> Selection {
    match previous {
        Selection::MalformedUtf8(error) => Selection::MalformedUtf8(error),
        Selection::NoMatch => seed_valid(terminal, bytes, position),
        Selection::Token(prior) => match longest_valid(terminal, bytes, position) {
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
