use rowl_frontend::imports::{DocumentCatalog, DocumentIds};
use rowl_frontend::snapshot::{resolve_texts, TextResolution};
use rowl_frontend::unicode::TextError;

fn source(
    key: u32,
    bytes: Vec<u8>,
    dependencies: DocumentIds,
    next: DocumentCatalog,
) -> DocumentCatalog {
    DocumentCatalog::Document {
        key,
        bytes,
        dependencies,
        next: Box::new(next),
    }
}

#[test]
fn closure_keeps_verbatim_bytes_and_ignores_unreachable_invalid_text() {
    let bytes = "\u{feff}Ontology(é)\r\n".as_bytes().to_vec();
    let catalog = source(
        1,
        bytes.clone(),
        DocumentIds::Cons(1, Box::new(DocumentIds::Empty)),
        source(2, vec![255], DocumentIds::Empty, DocumentCatalog::Empty),
    );
    match resolve_texts(1, catalog) {
        TextResolution::Complete(DocumentCatalog::Document {
            key,
            bytes: actual,
            dependencies,
            next,
        }) => {
            assert_eq!(key, 1);
            assert_eq!(actual, bytes);
            assert!(matches!(dependencies, DocumentIds::Cons(1, _)));
            assert!(matches!(*next, DocumentCatalog::Empty));
        }
        _ => panic!("valid reachable source rejected"),
    }
}

#[test]
fn a_reachable_text_error_carries_its_document_and_byte_offset() {
    let catalog = source(
        1,
        b"root".to_vec(),
        DocumentIds::Cons(2, Box::new(DocumentIds::Empty)),
        source(
            2,
            vec![0x41, 0xc0, 0x80],
            DocumentIds::Empty,
            DocumentCatalog::Empty,
        ),
    );
    assert!(matches!(
        resolve_texts(1, catalog),
        TextResolution::InvalidText {
            document: 2,
            error: TextError::InvalidUtf8 { offset: 1 }
        }
    ));
    let catalog = source(3, vec![65, 0], DocumentIds::Empty, DocumentCatalog::Empty);
    assert!(matches!(
        resolve_texts(3, catalog),
        TextResolution::InvalidText {
            document: 3,
            error: TextError::NonXmlCharacter {
                offset: 1,
                codepoint: 0
            }
        }
    ));
}

#[test]
fn topology_errors_precede_text_checks() {
    let catalog = source(
        1,
        vec![255],
        DocumentIds::Cons(9, Box::new(DocumentIds::Empty)),
        DocumentCatalog::Empty,
    );
    assert!(matches!(
        resolve_texts(1, catalog),
        TextResolution::MissingDocument(9)
    ));
    let catalog = source(
        1,
        vec![255],
        DocumentIds::Empty,
        source(
            1,
            b"duplicate".to_vec(),
            DocumentIds::Empty,
            DocumentCatalog::Empty,
        ),
    );
    assert!(matches!(
        resolve_texts(1, catalog),
        TextResolution::DuplicateDocument(1)
    ));
}
