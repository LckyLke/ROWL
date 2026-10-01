//! Scalar-to-UTF-8 encoding shared by verified serialization work.
//!
//! Invalid scalar values are explicit; a fixed-size enum avoids allocation and
//! length overflow. No replacement character or truncation policy is applied.

pub enum Encoded {
    One(u8),
    Two(u8, u8),
    Three(u8, u8, u8),
    Four(u8, u8, u8, u8),
}

#[allow(clippy::manual_range_contains)]
pub fn scalar(codepoint: u32) -> bool {
    (codepoint <= 0x10ffff) && !((codepoint >= 0xd800) && (codepoint <= 0xdfff))
}

pub fn encode(codepoint: u32) -> Option<Encoded> {
    if !scalar(codepoint) {
        None
    } else if codepoint < 128 {
        Some(Encoded::One(codepoint as u8))
    } else if codepoint < 2048 {
        Some(Encoded::Two(
            (192 + codepoint / 64) as u8,
            (128 + codepoint % 64) as u8,
        ))
    } else if codepoint < 65536 {
        Some(Encoded::Three(
            (224 + codepoint / 4096) as u8,
            (128 + (codepoint / 64) % 64) as u8,
            (128 + codepoint % 64) as u8,
        ))
    } else {
        Some(Encoded::Four(
            (240 + codepoint / 262144) as u8,
            (128 + (codepoint / 4096) % 64) as u8,
            (128 + (codepoint / 64) % 64) as u8,
            (128 + codepoint % 64) as u8,
        ))
    }
}
