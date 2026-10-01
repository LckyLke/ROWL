//! Run with `cargo run -p rowl --example prefixes`.
//! Expand maintenance vocabulary names using the verified lexical operations.
//! This supplies prefix/local parts directly; it does not parse an OWL document.
use rowl::experimental::prefixes::{check, expand_parts, Check, Declaration, Expansion};

fn main() {
    let declarations = vec![Declaration {
        name: b":".to_vec(),
        namespace: b"https://example.org/maintenance#".to_vec(),
    }];
    let table = match check(&declarations) {
        Check::Ready(table) => table,
        _ => panic!("example declarations must be valid"),
    };
    for (prefix, local) in [(":", "pump17"), (":", "NeedsInspection"), ("owl:", "Class")] {
        match expand_parts(
            &table,
            &prefix.as_bytes().to_vec(),
            &local.as_bytes().to_vec(),
            256,
        ) {
            Expansion::Expanded(bytes) => println!(
                "{prefix}{local} → {}",
                String::from_utf8(bytes).expect("verified expansion has valid UTF-8")
            ),
            _ => panic!("example name must expand"),
        }
    }
    assert!(matches!(
        expand_parts(&table, &b"unknown:".to_vec(), &b"Pump".to_vec(), 256),
        Expansion::UndeclaredPrefix
    ));
    println!("unknown:Pump → UndeclaredPrefix");
    assert!(matches!(
        expand_parts(&table, &b":".to_vec(), &b"pump17".to_vec(), 4),
        Expansion::ResourceLimit
    ));
    println!(":pump17 with a 4-byte output limit → ResourceLimit");
    println!("These are exact name expansions. OWL document parsing and inference remain pending.");
}
