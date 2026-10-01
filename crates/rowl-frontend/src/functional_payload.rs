//! OWL Functional Syntax quoted-string payloads, with exact source diagnostics.
//! The reader stops at the closing quote; a separate lexer validates the suffix.
#![allow(clippy::ptr_arg)]
use crate::encoding::encode;
use crate::ntriples::{append_encoded, expect, required, ErrorKind, ReadError};
use crate::unicode::xml_character;

type Step<T> = Result<(T, usize), ReadError>;
fn error(kind: ErrorKind, offset: usize) -> ReadError {
    ReadError { kind, offset }
}
fn escape(bytes: &Vec<u8>, slash: usize, position: usize) -> Step<u32> {
    let (cp, next) = required(bytes, position)?;
    if cp == 34 || cp == 92 {
        Ok((cp, next))
    } else {
        Err(error(ErrorKind::InvalidEscape, slash))
    }
}
fn quoted_item(bytes: &Vec<u8>, position: usize, cp: u32, next: usize) -> Step<u32> {
    if cp == 92 {
        escape(bytes, position, next)
    } else if cp == 34 || !xml_character(cp) {
        Err(error(ErrorKind::InvalidCharacter, position))
    } else {
        Ok((cp, next))
    }
}
/// Read exactly one quoted string and return its unescaped UTF-8 bytes and the
/// first byte after the closing quote. Only quote/backslash escapes are allowed.
/// The output byte budget excludes source quotes and escape backslashes.
/// Multiline XML text is preserved verbatim. Errors refer to original bytes.
pub fn read_quoted(bytes: &Vec<u8>, start: usize, limit: usize) -> Step<Vec<u8>> {
    let mut position = expect(bytes, start, 34, ErrorKind::InvalidCharacter)?;
    let mut output = Vec::new();
    loop {
        let (cp, next) = required(bytes, position)?;
        if cp == 34 {
            return Ok((output, next));
        }
        let (value, end) = quoted_item(bytes, position, cp, next)?;
        let encoded = match encode(value) {
            Some(value) => value,
            None => return Err(error(ErrorKind::InvalidCharacter, position)),
        };
        if !append_encoded(&mut output, encoded, limit) {
            return Err(error(ErrorKind::ResourceLimit, position));
        }
        position = end;
    }
}
