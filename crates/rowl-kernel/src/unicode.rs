//! Byte-level UTF-8 decoding and the XML 1.0 `Char` production used by OWL.
//!
//! No encoding detection, BOM removal, XML normalization or OWL parsing occurs
//! here. Offsets are byte offsets into the unchanged caller-supplied buffer.

pub enum TextError {
    InvalidPosition { offset: usize },
    InvalidUtf8 { offset: usize },
    NonXmlCharacter { offset: usize, codepoint: u32 },
}

pub enum Decoded {
    End,
    Scalar { codepoint: u32, next: usize },
    Error(TextError),
}

pub enum Scalars {
    Empty,
    Cons {
        codepoint: u32,
        offset: usize,
        next: Box<Scalars>,
    },
}

pub enum TextScan {
    Valid(Scalars),
    Invalid(TextError),
}

// Direct comparisons keep these operations inside the extracted Rust subset.
#[allow(clippy::manual_range_contains)]
fn continuation(byte: u8) -> bool {
    (byte >= 128) & (byte <= 191)
}

#[allow(clippy::manual_range_contains)]
fn two(first: u8, second: u8) -> Option<u32> {
    if (first >= 194) & (first <= 223) & continuation(second) {
        Some((u32::from(first) - 192) * 64 + (u32::from(second) - 128))
    } else {
        None
    }
}

#[allow(clippy::manual_range_contains)]
fn three(first: u8, second: u8, third: u8) -> Option<u32> {
    let tail = continuation(second);
    let head = ((first == 224) & (second >= 160) & (second <= 191))
        | ((first >= 225) & (first <= 236) & tail)
        | ((first == 237) & (second >= 128) & (second <= 159))
        | ((first >= 238) & (first <= 239) & tail);
    if head & continuation(third) {
        Some(
            (u32::from(first) - 224) * 4096
                + (u32::from(second) - 128) * 64
                + (u32::from(third) - 128),
        )
    } else {
        None
    }
}

#[allow(clippy::manual_range_contains)]
fn four(first: u8, second: u8, third: u8, fourth: u8) -> Option<u32> {
    let head = ((first == 240) & (second >= 144) & (second <= 191))
        | ((first >= 241) & (first <= 243) & continuation(second))
        | ((first == 244) & (second >= 128) & (second <= 143));
    if head & continuation(third) & continuation(fourth) {
        Some(
            (u32::from(first) - 240) * 262144
                + (u32::from(second) - 128) * 4096
                + (u32::from(third) - 128) * 64
                + (u32::from(fourth) - 128),
        )
    } else {
        None
    }
}

/// Decode exactly one Unicode scalar, or report the start of the invalid unit.
// Keep the current verified Vec contract; a slice API needs its own extraction/proof.
#[allow(clippy::ptr_arg)]
pub fn decode_next(bytes: &Vec<u8>, offset: usize) -> Decoded {
    let length = bytes.len();
    if offset > length {
        return Decoded::Error(TextError::InvalidPosition { offset });
    }
    if offset == length {
        return Decoded::End;
    }
    let first = bytes[offset];
    if first < 128 {
        return Decoded::Scalar {
            codepoint: u32::from(first),
            next: offset + 1,
        };
    }
    let remaining = length - offset;
    if first < 224 {
        if remaining >= 2 {
            if let Some(codepoint) = two(first, bytes[offset + 1]) {
                return Decoded::Scalar {
                    codepoint,
                    next: offset + 2,
                };
            }
        }
    } else if first < 240 {
        if remaining >= 3 {
            if let Some(codepoint) = three(first, bytes[offset + 1], bytes[offset + 2]) {
                return Decoded::Scalar {
                    codepoint,
                    next: offset + 3,
                };
            }
        }
    } else if remaining >= 4 {
        if let Some(codepoint) = four(
            first,
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ) {
            return Decoded::Scalar {
                codepoint,
                next: offset + 4,
            };
        }
    }
    Decoded::Error(TextError::InvalidUtf8 { offset })
}

/// XML 1.0 (third edition) `Char`; discouraged characters are still legal.
#[allow(clippy::manual_range_contains)]
pub fn xml_character(codepoint: u32) -> bool {
    (codepoint == 9)
        | (codepoint == 10)
        | (codepoint == 13)
        | ((codepoint >= 32) & (codepoint <= 55295))
        | ((codepoint >= 57344) & (codepoint <= 65533))
        | ((codepoint >= 65536) & (codepoint <= 1114111))
}

fn read_from(bytes: &Vec<u8>, offset: usize) -> TextScan {
    match decode_next(bytes, offset) {
        Decoded::End => TextScan::Valid(Scalars::Empty),
        Decoded::Error(error) => TextScan::Invalid(error),
        Decoded::Scalar { codepoint, next } => {
            if !xml_character(codepoint) {
                return TextScan::Invalid(TextError::NonXmlCharacter { offset, codepoint });
            }
            match read_from(bytes, next) {
                TextScan::Valid(tail) => TextScan::Valid(Scalars::Cons {
                    codepoint,
                    offset,
                    next: Box::new(tail),
                }),
                TextScan::Invalid(error) => TextScan::Invalid(error),
            }
        }
    }
}

/// Decode all bytes as UTF-8 and require every scalar to satisfy XML `Char`.
pub fn read_text(bytes: &Vec<u8>) -> TextScan {
    read_from(bytes, 0)
}
