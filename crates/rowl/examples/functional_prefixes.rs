//! Actual source prefix/header parsing and checked source-name resolution.
//! Complete ontology contents are returned as tokens and remain unparsed.
use rowl::experimental::functional::Terminal;
use rowl::experimental::functional_iris::{resolve_span, SourceIriKind};
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};

fn main() {
    let source = b"Prefix(ex:=<https://example.org/maintenance#>) Ontology(<urn:maintenance> Declaration(Class(ex:Pump)) ClassAssertion(ex:Pump ex:pump7))".to_vec();
    let header = read_prefix_header(&source, 100, 10, 100)
        .unwrap_or_else(|_| panic!("complete prefix/header source syntax"));
    println!("Prefix declarations read from original bytes:");
    for declaration in &header.declarations {
        println!(
            "  {} = {}",
            String::from_utf8_lossy(&declaration.name),
            String::from_utf8_lossy(&declaration.namespace)
        );
    }
    let table = match check(&header.declarations) {
        Check::Ready(table) => table,
        _ => panic!("the parsed declaration table must satisfy all normative rules"),
    };
    println!(
        "Exact original ontology opening at bytes {}..{}",
        header.ontology.start, header.opening.end
    );
    let mut tokens = header.remaining;
    while let Tokens::Cons { token, next } = tokens {
        let kind = match token.terminal {
            Terminal::FullIri => Some(SourceIriKind::Full),
            Terminal::AbbreviatedIri => Some(SourceIriKind::Abbreviated),
            _ => None,
        };
        if let Some(kind) = kind {
            let value = resolve_span(&table, kind, &source, token.start, token.end, 100)
                .unwrap_or_else(|_| panic!("each example source IRI must resolve exactly"));
            println!(
                "  {} → {}",
                String::from_utf8_lossy(&source[token.start..token.end]),
                String::from_utf8_lossy(&value)
            );
        }
        tokens = *next;
    }
    println!("The prefix table now comes from source bytes. Ontology contents, imports and inference remain separate pending stages.");
}
