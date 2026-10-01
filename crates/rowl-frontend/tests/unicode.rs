use rowl_frontend::unicode::{
    decode_next, read_text, xml_character, Decoded, Scalars, TextError, TextScan,
};

#[test]
fn every_unicode_scalar_decodes_like_the_standard_encoder() {
    for codepoint in 0..=0x10ffff {
        if let Some(character) = char::from_u32(codepoint) {
            let mut storage = [0; 4];
            let bytes = character.encode_utf8(&mut storage).as_bytes().to_vec();
            assert!(
                matches!(decode_next(&bytes, 0), Decoded::Scalar { codepoint: actual, next } if actual == codepoint && next == bytes.len())
            );
            assert!(matches!(decode_next(&bytes, bytes.len()), Decoded::End));
        }
    }
}

#[test]
fn malformed_units_are_rejected_at_their_start() {
    let cases: &[&[u8]] = &[
        &[0x80],
        &[0xbf],
        &[0xc0, 0x80],
        &[0xc1, 0xbf],
        &[0xc2],
        &[0xc2, 0x7f],
        &[0xe0, 0x9f, 0xbf],
        &[0xe1, 0x80],
        &[0xed, 0xa0, 0x80],
        &[0xf0, 0x8f, 0xbf, 0xbf],
        &[0xf1, 0x80, 0x80],
        &[0xf4, 0x90, 0x80, 0x80],
        &[0xf5, 0x80, 0x80, 0x80],
        &[0xff],
    ];
    for case in cases {
        let mut bytes = b"ok".to_vec();
        bytes.extend_from_slice(case);
        assert!(matches!(
            decode_next(&bytes, 2),
            Decoded::Error(TextError::InvalidUtf8 { offset: 2 })
        ));
        assert!(matches!(
            read_text(&bytes),
            TextScan::Invalid(TextError::InvalidUtf8 { offset: 2 })
        ));
    }
    assert!(matches!(
        decode_next(&vec![], 1),
        Decoded::Error(TextError::InvalidPosition { offset: 1 })
    ));
}

#[test]
fn text_offsets_and_xml_character_boundaries_are_exact() {
    let bytes = "Aé🦉\r\n".as_bytes().to_vec();
    let mut scalars = match read_text(&bytes) {
        TextScan::Valid(s) => s,
        _ => panic!("valid text rejected"),
    };
    let mut actual = vec![];
    while let Scalars::Cons {
        codepoint,
        offset,
        next,
    } = scalars
    {
        actual.push((codepoint, offset));
        scalars = *next;
    }
    assert_eq!(
        actual,
        vec![(65, 0), (233, 1), (0x1f989, 3), (13, 7), (10, 8)]
    );
    for allowed in [
        9, 10, 13, 32, 0xd7ff, 0xe000, 0xfffd, 0x10000, 0x10ffff, 0x7f, 0xfdd0,
    ] {
        assert!(xml_character(allowed));
    }
    for forbidden in [
        0,
        8,
        11,
        12,
        14,
        31,
        0xd800,
        0xdfff,
        0xfffe,
        0xffff,
        0x110000,
        u32::MAX,
    ] {
        assert!(!xml_character(forbidden));
    }
    assert!(matches!(
        read_text(&"é\0later".as_bytes().to_vec()),
        TextScan::Invalid(TextError::NonXmlCharacter {
            offset: 2,
            codepoint: 0
        })
    ));
    // Preserve a BOM as a character; encoding detection and normalization belong elsewhere.
    assert!(matches!(
        read_text(&"\u{feff}".as_bytes().to_vec()),
        TextScan::Valid(_)
    ));
    assert!(matches!(
        read_text(&vec![]),
        TextScan::Valid(Scalars::Empty)
    ));
}
