//! Exact literal values from a maintenance ontology's original source bytes.
use rowl::experimental::functional::Terminal;
use rowl::experimental::functional_header::read_header_tail;
use rowl::experimental::functional_lexer::Tokens;
use rowl::experimental::functional_literals::read_literal;
use rowl::experimental::functional_prefixes::read_prefix_header;
use rowl::experimental::prefixes::{check, Check};
fn main() {
    let bytes = include_bytes!("../../../examples/maintenance-literals.ofn").to_vec();
    let prefix =
        read_prefix_header(&bytes, 100, 10, 100).unwrap_or_else(|_| panic!("source prefixes"));
    let table = match check(&prefix.declarations) {
        Check::Ready(table) => table,
        _ => panic!("prefix table"),
    };
    let header = read_header_tail(&table, &bytes, prefix.remaining, 10, 100)
        .unwrap_or_else(|_| panic!("header"));
    let mut stream = header.remaining;
    loop {
        match stream {
            Tokens::Empty => break,
            Tokens::Cons { token, next } => {
                if matches!(token.terminal, Terminal::QuotedString) {
                    let original = &bytes[token.start..token.end];
                    let (literal, remaining) =
                        read_literal(&table, &bytes, Tokens::Cons { token, next }, 100, 100)
                            .unwrap_or_else(|_| panic!("literal source"));
                    println!(
                        "Source {} -> lexical {}, datatype {}",
                        String::from_utf8_lossy(original),
                        String::from_utf8_lossy(&literal.lexical),
                        String::from_utf8_lossy(&literal.datatype)
                    );
                    stream = remaining;
                } else {
                    stream = *next;
                }
            }
        }
    }
    println!("The demo selects literal tokens; full annotation/axiom parsing, datatype value validation and OWL reasoning remain pending.");
}
