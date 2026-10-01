use rowl::experimental::iri::{validate_iri, validate_reference};
use rowl::experimental::regular::MatchResult;
use rowl::experimental::unicode::TextError;

fn main() {
    for spelling in [
        "https://factory.example/pump#motor",
        "https://例え.テスト/機械",
        "https://factory.example/pump%2G",
        "../motor",
    ] {
        let bytes = spelling.as_bytes().to_vec();
        let absolute = matches!(validate_iri(&bytes), MatchResult::Matched(true));
        let reference = matches!(validate_reference(&bytes), MatchResult::Matched(true));
        println!("{spelling}: IRI={absolute}, IRI-reference={reference}");
    }
    let malformed = vec![b'x', b':', 0xc0, 0x80];
    match validate_iri(&malformed) {
        MatchResult::MalformedUtf8(TextError::InvalidUtf8 { offset }) => {
            println!("Malformed UTF-8 unit starts at byte {offset}");
        }
        MatchResult::MalformedUtf8(_) => panic!("unexpected decoder diagnostic"),
        MatchResult::Matched(_) => panic!("malformed UTF-8 was not diagnosed"),
    }
}
