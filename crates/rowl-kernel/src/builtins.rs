//! OWL 2 implicit declaration roles (2012 Structural Specification, Table 5).
//! This finite vocabulary does not implement datatype value or lexical spaces.
#![allow(clippy::ptr_arg)] // Restrict operations to the checked extraction subset.
#![allow(clippy::if_same_then_else)] // One branch per normative entry keeps proof correspondence explicit.
use crate::typing::EntityKind;
fn equal_from(key: &Vec<u8>, pattern: &[u8], index: usize) -> bool {
    if index < key.len() {
        key[index] == pattern[index] && equal_from(key, pattern, index + 1)
    } else {
        true
    }
}
fn same_pattern(key: &Vec<u8>, pattern: &[u8]) -> bool {
    key.len() == pattern.len() && equal_from(key, pattern, 0)
}
fn group_0(key: &Vec<u8>) -> Option<EntityKind> {
    if same_pattern(key, b"http://www.w3.org/2002/07/owl#Thing") {
        Some(EntityKind::Class)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#Nothing") {
        Some(EntityKind::Class)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#topObjectProperty") {
        Some(EntityKind::ObjectProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#bottomObjectProperty") {
        Some(EntityKind::ObjectProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#topDataProperty") {
        Some(EntityKind::DataProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#bottomDataProperty") {
        Some(EntityKind::DataProperty)
    } else if same_pattern(key, b"http://www.w3.org/2000/01/rdf-schema#Literal") {
        Some(EntityKind::Datatype)
    } else {
        None
    }
}
fn group_1(key: &Vec<u8>) -> Option<EntityKind> {
    if same_pattern(key, b"http://www.w3.org/2002/07/owl#real") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#rational") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#decimal") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#integer") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#nonNegativeInteger") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#nonPositiveInteger") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#positiveInteger") {
        Some(EntityKind::Datatype)
    } else {
        None
    }
}
fn group_2(key: &Vec<u8>) -> Option<EntityKind> {
    if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#negativeInteger") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#long") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#int") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#short") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#byte") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#unsignedLong") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#unsignedInt") {
        Some(EntityKind::Datatype)
    } else {
        None
    }
}
fn group_3(key: &Vec<u8>) -> Option<EntityKind> {
    if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#unsignedShort") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#unsignedByte") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#double") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#float") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#string") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#normalizedString") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#token") {
        Some(EntityKind::Datatype)
    } else {
        None
    }
}
fn group_4(key: &Vec<u8>) -> Option<EntityKind> {
    if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#language") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#Name") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#NCName") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#NMTOKEN") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#boolean") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#hexBinary") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#base64Binary") {
        Some(EntityKind::Datatype)
    } else {
        None
    }
}
fn group_5(key: &Vec<u8>) -> Option<EntityKind> {
    if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#anyURI") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#dateTime") {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2001/XMLSchema#dateTimeStamp") {
        Some(EntityKind::Datatype)
    } else if same_pattern(
        key,
        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
    ) {
        Some(EntityKind::Datatype)
    } else if same_pattern(
        key,
        b"http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral",
    ) {
        Some(EntityKind::Datatype)
    } else if same_pattern(key, b"http://www.w3.org/2000/01/rdf-schema#label") {
        Some(EntityKind::AnnotationProperty)
    } else if same_pattern(key, b"http://www.w3.org/2000/01/rdf-schema#comment") {
        Some(EntityKind::AnnotationProperty)
    } else {
        None
    }
}
fn group_6(key: &Vec<u8>) -> Option<EntityKind> {
    if same_pattern(key, b"http://www.w3.org/2000/01/rdf-schema#seeAlso") {
        Some(EntityKind::AnnotationProperty)
    } else if same_pattern(key, b"http://www.w3.org/2000/01/rdf-schema#isDefinedBy") {
        Some(EntityKind::AnnotationProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#deprecated") {
        Some(EntityKind::AnnotationProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#versionInfo") {
        Some(EntityKind::AnnotationProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#priorVersion") {
        Some(EntityKind::AnnotationProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#backwardCompatibleWith") {
        Some(EntityKind::AnnotationProperty)
    } else if same_pattern(key, b"http://www.w3.org/2002/07/owl#incompatibleWith") {
        Some(EntityKind::AnnotationProperty)
    } else {
        None
    }
}
/// Exact finite built-in spelling recognition; no prefix or case normalization.
pub fn builtin_kind(key: &Vec<u8>) -> Option<EntityKind> {
    match group_0(key) {
        Some(kind) => Some(kind),
        None => match group_1(key) {
            Some(kind) => Some(kind),
            None => match group_2(key) {
                Some(kind) => Some(kind),
                None => match group_3(key) {
                    Some(kind) => Some(kind),
                    None => match group_4(key) {
                        Some(kind) => Some(kind),
                        None => match group_5(key) {
                            Some(kind) => Some(kind),
                            None => group_6(key),
                        },
                    },
                },
            },
        },
    }
}
