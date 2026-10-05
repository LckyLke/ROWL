//! Times each stage of the verified pipeline on a Functional Syntax file:
//! reading, preparing and one consistency check.
use rowl::experimental::data_ontology::{prepare, prepared_consistent};
use rowl::experimental::functional_document::read_document;
use rowl::experimental::functional_lexer::{lex, LexResult};
use rowl::experimental::functional_model::document_ontology;
use rowl::reasoner::default_limits;
use std::time::Instant;

fn main() {
    let path = std::env::args().nth(1).expect("a Functional Syntax file");
    let bytes = std::fs::read(&path).expect("readable file");
    let limits = default_limits();
    let start = Instant::now();
    let tokens = match lex(&bytes, limits.tokens) {
        LexResult::Tokens(_) => "tokens",
        _ => "error",
    };
    println!("lex: {:?} {}", start.elapsed(), tokens);
    let start = Instant::now();
    let document = match read_document(&bytes, &limits) {
        Ok(document) => document,
        Err(_) => panic!("the document is read"),
    };
    println!("read: {:?}", start.elapsed());
    let start = Instant::now();
    let ontology = document_ontology(&document, &b"timing".to_vec()).expect("maps");
    println!(
        "map: {:?} ({} axioms)",
        start.elapsed(),
        ontology.axioms.len()
    );
    let start = Instant::now();
    let prepared = prepare(&ontology.axioms).expect("prepared");
    println!("prepare: {:?}", start.elapsed());
    let start = Instant::now();
    let answer = prepared_consistent(&prepared);
    println!("consistent: {:?} {:?}", start.elapsed(), answer);
}
