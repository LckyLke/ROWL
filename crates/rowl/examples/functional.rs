//! Run with `cargo run -p rowl --example functional`.
//! Inspect real source spans using the complete standard terminal selector.
//! Quoted-string payload decoding is also demonstrated.
//! Integer payloads have exact mathematical values at their original spans.
//! Whole-source tokenization is demonstrated; OWL document parsing is pending.
use rowl::experimental::functional::{next_terminal, Selection, Terminal};
use rowl::experimental::functional_lexer::{lex, LexResult, Tokens};
use rowl::experimental::functional_names::{read_span as read_name, NameKind};
use rowl::experimental::functional_payload::read_quoted;
use rowl::experimental::ntriples::ErrorKind;
use rowl::experimental::{decimal, Natural};

fn label(terminal: Terminal) -> &'static str {
    match terminal {
        Terminal::Keyword(_) => "keyword",
        Terminal::Open => "opening parenthesis",
        Terminal::Close => "closing parenthesis",
        Terminal::Equals => "equals",
        Terminal::DatatypeIndicator => "datatype marker",
        Terminal::Integer => "nonnegative integer",
        Terminal::QuotedString => "quoted string",
        Terminal::LanguageTag => "language tag",
        Terminal::NodeId => "anonymous node ID",
        Terminal::FullIri => "full IRI",
        Terminal::PrefixName => "prefix name",
        Terminal::AbbreviatedIri => "abbreviated IRI",
        Terminal::Whitespace => "whitespace",
        Terminal::Comment => "comment",
    }
}

fn main() {
    for (source, position) in [
        ("SubClassOf(:Pump :Machine)", 0),
        ("SubClassOf:NeedsInspection)", 0),
        ("\"faulty #motor\"@en", 0),
        ("\"faulty #motor\"@en", 15),
    ] {
        match next_terminal(&source.as_bytes().to_vec(), position) {
            Selection::Token(token) => println!(
                "{} [{}..{}]: {}",
                label(token.terminal),
                token.start,
                token.end,
                &source[token.start..token.end]
            ),
            _ => panic!("example source must contain an eligible standard terminal"),
        }
    }
    let quoted = r#""faulty \"motor\"\\sensor"@en"#.as_bytes().to_vec();
    let (payload, end) = read_quoted(&quoted, 0, 100)
        .unwrap_or_else(|error| panic!("unexpected quote failure at {}", error.offset));
    println!(
        "decoded payload [0..{end}]: {}",
        String::from_utf8(payload).expect("the example payload is UTF-8")
    );
    match read_quoted(&quoted, 0, 3) {
        Err(error) if matches!(error.kind, ErrorKind::ResourceLimit) => println!(
            "three-byte payload budget exceeded at original source byte {}",
            error.offset
        ),
        _ => panic!("the short budget must be rejected"),
    }
    let source = "# maintenance rule\nSubClassOf(ObjectSomeValuesFrom(:hasPart :FaultyPart) :NeedsInspection)";
    let mut stream = match lex(&source.as_bytes().to_vec(), 20) {
        LexResult::Tokens(stream) => stream,
        _ => panic!("the complete maintenance token stream must be accepted"),
    };
    println!("Complete maintenance source, with comments discarded:");
    while let Tokens::Cons { token, next } = stream {
        println!(
            "  {} [{}..{}]: {}",
            label(token.terminal),
            token.start,
            token.end,
            &source[token.start..token.end]
        );
        stream = *next;
    }
    match lex(&b"Ontology() 10abc".to_vec(), 20) {
        LexResult::MissingSeparator { offset: 13 } => {
            println!("Later separator failure at byte 13 rejects the entire token stream.")
        }
        _ => panic!("the malformed suffix must reject the entire token stream"),
    }
    let source = b"ObjectMinCardinality(003 :hasPart :Part)".to_vec();
    let mut tokens = match lex(&source, 10) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("the complete cardinality source must be lexed"),
    };
    while let Tokens::Cons { token, next } = tokens {
        if matches!(token.terminal, Terminal::Integer) {
            let number = decimal::read_span(&source, token.start, token.end)
                .unwrap_or_else(|_| panic!("a lexed integer must have its exact value"));
            let mut remaining = &number;
            let mut value = 0;
            while let Natural::Succ(previous) = remaining {
                value += 1;
                remaining = previous;
            }
            println!(
                "Integer payload [{}..{}]: {} has exact value {value}",
                token.start,
                token.end,
                String::from_utf8_lossy(&source[token.start..token.end])
            );
        }
        tokens = *next;
    }
    let source = b"Declaration(Class(<https://example.org/maintenance#Pump>))".to_vec();
    let mut tokens = match lex(&source, 10) {
        LexResult::Tokens(tokens) => tokens,
        _ => panic!("the complete class-declaration token source must be accepted"),
    };
    while let Tokens::Cons { token, next } = tokens {
        if matches!(token.terminal, Terminal::FullIri) {
            let iri = read_name(NameKind::FullIri, &source, token.start, token.end, 100)
                .unwrap_or_else(|_| panic!("a complete lexed IRI must have its exact value"));
            println!(
                "Full IRI payload [{}..{}]: {}",
                token.start,
                token.end,
                String::from_utf8(iri).expect("the original IRI is canonical UTF-8")
            );
        }
        tokens = *next;
    }
    println!("These are verified lexical/value stages; full OWL document parsing and inference remain pending.");
}
