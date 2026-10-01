//! Deterministic closure discovery over an immutable, symbol-indexed catalog.
//!
//! A document symbol is a structural lookup identity, never an OWL individual.
//! Symbols must eventually come from verified IRI interning. Bytes are retained
//! verbatim. Import edges here are supplied metadata, not extracted from bytes.
//! No network access, fuel cutoff, or silently skipped missing documents.

pub enum DocumentIds {
    Empty,
    Cons(u32, Box<DocumentIds>),
}

pub enum DocumentCatalog {
    Empty,
    Document {
        key: u32,
        bytes: Vec<u8>,
        dependencies: DocumentIds,
        next: Box<DocumentCatalog>,
    },
}

enum Taken {
    Missing,
    Found {
        bytes: Vec<u8>,
        dependencies: DocumentIds,
        remaining: DocumentCatalog,
    },
}

pub enum Resolution {
    Complete(DocumentCatalog),
    MissingDocument(u32),
    DuplicateDocument(u32),
}

fn copy_ids(ids: &DocumentIds) -> DocumentIds {
    match ids {
        DocumentIds::Empty => DocumentIds::Empty,
        DocumentIds::Cons(key, tail) => DocumentIds::Cons(*key, Box::new(copy_ids(tail))),
    }
}

fn append_ids(left: DocumentIds, right: DocumentIds) -> DocumentIds {
    match left {
        DocumentIds::Empty => right,
        DocumentIds::Cons(key, tail) => DocumentIds::Cons(key, Box::new(append_ids(*tail, right))),
    }
}

fn contains(catalog: &DocumentCatalog, sought: u32) -> bool {
    match catalog {
        DocumentCatalog::Empty => false,
        DocumentCatalog::Document { key, next, .. } => *key == sought || contains(next, sought),
    }
}

fn duplicate(catalog: &DocumentCatalog) -> Option<u32> {
    match catalog {
        DocumentCatalog::Empty => None,
        DocumentCatalog::Document { key, next, .. } => {
            if contains(next, *key) {
                Some(*key)
            } else {
                duplicate(next)
            }
        }
    }
}

/// Remove exactly the first matching document, preserving all other payloads.
fn take(catalog: DocumentCatalog, sought: u32) -> Taken {
    match catalog {
        DocumentCatalog::Empty => Taken::Missing,
        DocumentCatalog::Document {
            key,
            bytes,
            dependencies,
            next,
        } => {
            if key == sought {
                Taken::Found {
                    bytes,
                    dependencies,
                    remaining: *next,
                }
            } else {
                match take(*next, sought) {
                    Taken::Missing => Taken::Missing,
                    Taken::Found {
                        bytes: found_bytes,
                        dependencies: found_dependencies,
                        remaining,
                    } => Taken::Found {
                        bytes: found_bytes,
                        dependencies: found_dependencies,
                        remaining: DocumentCatalog::Document {
                            key,
                            bytes,
                            dependencies,
                            next: Box::new(remaining),
                        },
                    },
                }
            }
        }
    }
}

fn discover(
    pending: DocumentIds,
    available: DocumentCatalog,
    resolved: DocumentCatalog,
) -> Resolution {
    match pending {
        DocumentIds::Empty => Resolution::Complete(resolved),
        DocumentIds::Cons(key, tail) => {
            if contains(&resolved, key) {
                discover(*tail, available, resolved)
            } else {
                match take(available, key) {
                    Taken::Missing => Resolution::MissingDocument(key),
                    Taken::Found {
                        bytes,
                        dependencies,
                        remaining,
                    } => {
                        let pending = append_ids(copy_ids(&dependencies), *tail);
                        let resolved = DocumentCatalog::Document {
                            key,
                            bytes,
                            dependencies,
                            next: Box::new(resolved),
                        };
                        discover(pending, remaining, resolved)
                    }
                }
            }
        }
    }
}

/// The catalog must be a function: duplicates are errors even if unreachable.
/// Cycles are handled by recording a document before exploring its imports.
pub fn resolve(root: u32, catalog: DocumentCatalog) -> Resolution {
    match duplicate(&catalog) {
        Some(key) => Resolution::DuplicateDocument(key),
        None => discover(
            DocumentIds::Cons(root, Box::new(DocumentIds::Empty)),
            catalog,
            DocumentCatalog::Empty,
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(keys: &[u32]) -> DocumentIds {
        if keys.is_empty() {
            DocumentIds::Empty
        } else {
            DocumentIds::Cons(keys[0], Box::new(ids(&keys[1..])))
        }
    }

    fn document(key: u32, dependencies: &[u32], tail: DocumentCatalog) -> DocumentCatalog {
        DocumentCatalog::Document {
            key,
            bytes: vec![0, 255, key as u8],
            dependencies: ids(dependencies),
            next: Box::new(tail),
        }
    }

    fn keys(catalog: &DocumentCatalog) -> Vec<u32> {
        match catalog {
            DocumentCatalog::Empty => vec![],
            DocumentCatalog::Document {
                key, bytes, next, ..
            } => {
                assert_eq!(bytes, &[0, 255, *key as u8]);
                let mut result = vec![*key];
                result.extend(keys(next));
                result
            }
        }
    }

    #[test]
    fn cyclic_diamond_imports_resolve_once_with_verbatim_bytes() {
        let catalog = document(
            1,
            &[2, 3, 2],
            document(
                2,
                &[4],
                document(
                    3,
                    &[4],
                    document(4, &[1], document(9, &[], DocumentCatalog::Empty)),
                ),
            ),
        );
        let Resolution::Complete(closure) = resolve(1, catalog) else {
            panic!("expected closure")
        };
        assert_eq!(keys(&closure), vec![3, 4, 2, 1]);
    }

    #[test]
    fn missing_root_and_transitive_import_are_errors() {
        assert!(matches!(
            resolve(7, DocumentCatalog::Empty),
            Resolution::MissingDocument(7)
        ));
        let catalog = document(1, &[2], document(2, &[3], DocumentCatalog::Empty));
        assert!(matches!(
            resolve(1, catalog),
            Resolution::MissingDocument(3)
        ));
    }

    #[test]
    fn duplicate_catalog_keys_are_rejected_before_discovery() {
        let catalog = document(
            1,
            &[],
            document(9, &[], document(9, &[], DocumentCatalog::Empty)),
        );
        assert!(matches!(
            resolve(1, catalog),
            Resolution::DuplicateDocument(9)
        ));
    }

    #[test]
    fn unreachable_missing_import_does_not_affect_root_closure() {
        let catalog = document(1, &[], document(9, &[99], DocumentCatalog::Empty));
        let Resolution::Complete(closure) = resolve(1, catalog) else {
            panic!("expected closure")
        };
        assert_eq!(keys(&closure), vec![1]);
    }
}
