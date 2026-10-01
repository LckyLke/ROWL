//! Exercise the verified byte-key table; IRI parsing is a later stage.
use rowl::experimental::symbols::{empty, intern, key_of, InternResult};

fn main() {
    let spellings = [
        b"urn:maintenance:FaultyPart".to_vec(),
        b"urn:maintenance:Machine".to_vec(),
        b"urn:maintenance:FaultyPart".to_vec(),
        b"urn:maintenance:NeedsInspection".to_vec(),
    ];
    let mut table = empty(2);
    for spelling in &spellings {
        let (outcome, after) = intern(table, spelling);
        let text = String::from_utf8_lossy(spelling);
        match outcome {
            InternResult::Inserted(symbol) => println!("{text}: inserted symbol {symbol}"),
            InternResult::Existing(symbol) => println!("{text}: reused symbol {symbol}"),
            InternResult::CapacityExceeded => {
                println!("{text}: capacity exceeded; table preserved")
            }
        }
        table = after;
    }
    println!(
        "Symbol 0 still names {}",
        String::from_utf8_lossy(key_of(&table, 0).unwrap())
    );
    println!("This demonstrates exact byte identity, not IRI validation or OWL reasoning.");
}
