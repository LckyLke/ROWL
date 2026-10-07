import Rowl.RdfWrite

/-!
The round trips of the N-Triples and Turtle writers through the verified
readers, and the exactness of the N-Triples writer's errors.

`ntriples_write_read`: the bytes `ntriples::write` returns are read back by
`ntriples::read`, in any blank node scope, as the graph's triples in order,
each blank node becoming the blank node of the reader's scope whose label is
`WrittenLabel` of its own scope and label (`renameTerm`); the renaming is one
to one (`written_label_injective`). `turtle_write_read` proves the same through
`turtle::read`, against every base IRI shorter than `usize::MAX / 8` bytes.
`ntriples_write_error_exact`: when the N-Triples writer reports a term error,
no N-Triples document denotes the graph, even with other blank nodes, since
every graph an N-Triples document denotes has no fault (`document_writable`).

The proofs derive the reader relations of `NTriples`, `TurtleTokens` and
`Turtle` for the written bytes, position by position (`Occurs`).
-/
namespace Rowl.RdfWriteRead
open Rowl.RdfWrite
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open scoped Computability
open Rowl.NTriples (UnitAt AbsoluteIri LanguageTag LangStringBytes IriCharacter XsdStringBytes QuotedBody QuotedItem
  EscapeValue HexDigits HexValue EcharValue Closing RawAllowed EndLine)
open Rowl.Unicode (Prefix)
open Rowl.TurtleTokens (Span Resolves usize_of)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Bytes at a position -/

/-- The bytes `x` occur in `d` at `p`. -/
def Occurs (d : List U8) (p : Nat) (x : List U8) : Prop := ∃ pre post, d = pre ++ x ++ post ∧ pre.length = p

theorem drop_add (d : List U8) (p k : Nat) : d.drop (p + k) = (d.drop p).drop k := by
  rw [List.drop_drop]

theorem occurs_append {d : List U8} {p : Nat} {x y : List U8} :
    Occurs d p (x ++ y) ↔ Occurs d p x ∧ Occurs d (p + x.length) y := by
  constructor
  · rintro ⟨pre, post, rfl, rfl⟩
    exact ⟨⟨pre, y ++ post, by simp, rfl⟩, ⟨pre ++ x, post, by simp, by simp⟩⟩
  · rintro ⟨⟨pre1, post1, h1, l1⟩, ⟨pre2, post2, h2, l2⟩⟩
    have left : pre2 = pre1 ++ x := by
      have a := congrArg (List.take pre2.length) h2
      have b := congrArg (List.take pre2.length) h1
      rw [List.append_assoc, List.take_left] at a
      rw [List.append_assoc, ← List.append_assoc pre1, List.take_left' (by simp; omega)] at b
      rw [← a, b]
    subst left
    have right : post1 = y ++ post2 := by
      rw [h1] at h2
      simpa [List.append_assoc] using h2
    exact ⟨pre1, post2, by rw [h1, right]; simp, l1⟩

theorem occurs_cons {d : List U8} {p : Nat} {b : U8} {x : List U8} :
    Occurs d p (b :: x) ↔ Occurs d p [b] ∧ Occurs d (p + 1) x := by
  have := occurs_append (d := d) (p := p) (x := [b]) (y := x)
  simpa using this

theorem occurs_bound {d : List U8} {p : Nat} {x : List U8} (h : Occurs d p x) : p + x.length ≤ d.length := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  simp

theorem occurs_byte {d : List U8} {p : Nat} {b : U8} (h : Occurs d p [b]) : d[p]? = some b := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  simp

theorem occurs_byte_is {d : List U8} {p : Nat} {b : U8} (h : Occurs d p [b]) :
    Rowl.TurtleTokens.ByteIs d p b.val := by
  unfold Rowl.TurtleTokens.ByteIs
  rw [occurs_byte h]
  rfl

theorem occurs_span {d : List U8} {p : Nat} {x : List U8} (h : Occurs d p x) : Span d p (p + x.length) = x := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  unfold Span
  simp

/-- The character at `i` of written bytes is decoded where they occur. -/
theorem occurs_prefix {d : List U8} {p : Nat} {x : List U8} {i cp w : Nat} (h : Occurs d p x)
    (decoded : Prefix x i = some (cp, w)) : Prefix d (p + i) = some (cp, w) := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact prefix_written decoded

theorem occurs_unit {d : List U8} {p : Nat} {x : List U8} {i cp w : Nat} (h : Occurs d p x)
    (decoded : Prefix x i = some (cp, w)) {c : U32} {next : Usize} (hc : c.val = cp) (hn : next.val = p + i + w) :
    UnitAt d (p + i) c next := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact unit_written decoded hc hn

theorem occurs_unit_ascii {d : List U8} {p : Nat} {b : U8} (h : Occurs d p [b]) (small : b.val < 128)
    {c : U32} {next : Usize} (hc : c.val = b.val) (hn : next.val = p + 1) : UnitAt d p c next := by
  have := occurs_unit (i := 0) h (prefix_ascii b [] small) hc (by simpa using hn)
  simpa using this

theorem occurs_turtle_unit {d : List U8} {p : Nat} {x : List U8} {i cp w : Nat} (h : Occurs d p x)
    (decoded : Prefix x i = some (cp, w)) : Rowl.TurtleTokens.Unit d (p + i) cp (p + i + w) := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact turtle_unit_written decoded

theorem occurs_turtle_ascii {d : List U8} {p : Nat} {b : U8} (h : Occurs d p [b]) (small : b.val < 128) :
    Rowl.TurtleTokens.Unit d p b.val (p + 1) := by
  have := occurs_turtle_unit (i := 0) h (prefix_ascii b [] small)
  simpa using this

/-- A number that fits in 32 bits. -/
theorem u32_of {n : Nat} (h : n < 2 ^ 32) : ∃ c : U32, c.val = n :=
  ⟨⟨BitVec.ofNat 32 n⟩, by
    show (BitVec.ofNat 32 n).toNat = n
    rw [BitVec.toNat_ofNat]
    omega⟩


/-! ## Reading written characters -/

theorem encoded_scalar {cp : Nat} {e : encoding.Encoded} (h : Rowl.Encoding.EncodeCorrect cp (some e)) :
    Rowl.Encoding.Scalar cp := by
  cases e with
  | One a =>
    simp only [Rowl.Encoding.EncodeCorrect] at h
    unfold Rowl.Encoding.Scalar
    omega
  | Two a b =>
    simp only [Rowl.Encoding.EncodeCorrect] at h
    have := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val 0 0).1 h.1
    unfold Rowl.Encoding.Scalar
    omega
  | Three a b c =>
    simp only [Rowl.Encoding.EncodeCorrect] at h
    have := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val c.val 0).2.1 h.1
    unfold Rowl.Encoding.Scalar
    omega
  | Four a b c d =>
    simp only [Rowl.Encoding.EncodeCorrect] at h
    have := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val c.val d.val).2.2 h.1
    unfold Rowl.Encoding.Scalar
    omega

/-- The character decoded at `i` is a scalar value whose UTF-8 encoding is
    the bytes it occupies. -/
theorem prefix_character {s : List U8} {i cp w : Nat} (h : Prefix s i = some (cp, w)) :
    Rowl.Encoding.Scalar cp ∧
      ∃ e, Rowl.Encoding.EncodeCorrect cp (some e) ∧ Rowl.Encoding.Bytes e = Span s i (i + w) := by
  rw [prefix_drop] at h
  obtain ⟨e, correct, bytes⟩ := prefix_encoded h
  refine ⟨encoded_scalar correct, e, correct, ?_⟩
  rw [bytes]
  unfold Span
  congr 1
  omega

theorem span_length {s : List U8} {i cp w : Nat} (h : Prefix s i = some (cp, w)) : (Span s i (i + w)).length = w := by
  have := prefix_bounds h
  unfold Span
  simp
  omega

theorem drop_span (s : List U8) (i w : Nat) : s.drop i = Span s i (i + w) ++ s.drop (i + w) := by
  unfold Span
  rw [show i + w - i = w by omega, drop_add, List.take_append_drop]

theorem u32_ne {c d : U32} (h : c.val ≠ d.val) : c ≠ d := fun e => h (by rw [e])

theorem scalar_small {cp : Nat} (h : Rowl.Encoding.Scalar cp) : cp < 2 ^ 32 := by
  unfold Rowl.Encoding.Scalar at h
  omega

/-! ## Hexadecimal digits -/

theorem hex_length : ∀ (count v : Nat), (Hex count v).length = count
  | 0, _ => rfl
  | count + 1, v => by simp [Hex, hex_length count]

theorem uchar_length (cp : Nat) : (Uchar cp).length = 10 := by
  simp [Uchar, hex_length]

theorem hex_upper_val {n : Nat} (h : n < 16) : (hexUpper n).val = if n < 10 then 48 + n else 55 + n := by
  unfold hexUpper
  split_ifs <;> exact byte_val (by omega)

theorem hex_upper_ascii {n : Nat} (h : n < 16) : (hexUpper n).val < 128 := by
  rw [hex_upper_val h]
  split_ifs <;> omega

theorem hex_upper_value {n : Nat} (h : n < 16) : HexValue (hexUpper n).val = some n := by
  rw [hex_upper_val h]
  unfold HexValue
  by_cases small : n < 10
  · rw [if_pos small, if_pos (by omega)]
    congr 1
    omega
  · rw [if_neg small, if_neg (by omega), if_pos (by omega)]
    congr 1
    omega

/-- One more digit after hexadecimal digits. -/
theorem hex_digits_snoc {bs : List U8} {start count value result stop : Nat}
    (digits : HexDigits bs start count value result stop) {cp : U32} {next : Usize} {d : Nat}
    (unit : UnitAt bs stop cp next) (hd : HexValue cp.val = some d) :
    HexDigits bs start (count + 1) value (result * 16 + d) next.val := by
  induction digits with
  | empty => exact .digit unit hd .empty
  | digit u h _ ih => exact .digit u h (ih unit)

/-- Written hexadecimal digits are read as the number they denote. -/
theorem hex_read {d : List U8} (fits : d.length ≤ Usize.max) :
    ∀ (count v p : Nat), Occurs d p (Hex count v) → HexDigits d p count 0 (v % 16 ^ count) (p + count)
  | 0, v, p, _ => by
    rw [pow_zero, Nat.mod_one, Nat.add_zero]
    exact .empty
  | count + 1, v, p, occ => by
    rw [Hex] at occ
    obtain ⟨first, last⟩ := occurs_append.mp occ
    rw [hex_length] at last
    have digits := hex_read fits count (v / 16) p first
    have bound := occurs_bound last
    simp only [List.length_singleton] at bound
    have small : v % 16 < 16 := Nat.mod_lt _ (by omega)
    obtain ⟨c, hc⟩ := u32_of (n := (hexUpper (v % 16)).val) (by have := hex_upper_ascii small; omega)
    obtain ⟨next, hn⟩ := usize_of (n := p + count + 1) (by omega)
    have unit : UnitAt d (p + count) c next := occurs_unit_ascii last (hex_upper_ascii small) hc hn
    have step := hex_digits_snoc digits unit (by rw [hc]; exact hex_upper_value small)
    have key : v % 16 ^ (count + 1) = v / 16 % 16 ^ count * 16 + v % 16 := by
      rw [pow_succ', Nat.mod_mul]
      ring
    rw [key, show p + (count + 1) = next.val by omega]
    exact step

/-! ## IRI and string bodies -/

/-- The characters of an IRI written from `i`, then `>`, are the body of an
    IRIREF that denotes the bytes from `i`. -/
theorem iri_body_read {d : List U8} (fits : d.length ≤ Usize.max) {s : List U8} {i : Nat} {word : List Nat}
    (valid : Rowl.Regular.Utf8From s i word) :
    ∀ {p : Nat}, Occurs d p (IriText s i ++ [62#u8]) → ∀ (start stop : Usize), start.val = p →
      stop.val = p + (IriText s i).length + 1 → QuotedBody d true start (s.drop i) stop := by
  induction valid with
  | endOfInput =>
    intro p occ start stop hs hq
    rw [iri_text_nil (prefix_end s)] at occ hq
    simp only [List.nil_append, List.length_nil] at occ hq
    rw [List.drop_length]
    have unit : UnitAt d start.val 62#u32 stop := by
      rw [hs]
      exact occurs_unit_ascii occ (by decide) rfl (by omega)
    exact .close unit
  | @character offset cp w tail found positive bounded rest ih =>
    intro p occ start stop hs hq
    rw [iri_text_cons found] at occ hq
    obtain ⟨scalar, e, encodes, bytes⟩ := prefix_character found
    generalize hchunk : (if IriCharacter cp then Span s offset (offset + w) else Uchar cp) = chunk at occ hq
    rw [List.append_assoc] at occ
    obtain ⟨chunkOcc, restOcc⟩ := occurs_append.mp occ
    have restBound := occurs_bound restOcc
    simp only [List.length_append, List.length_singleton] at restBound hq
    obtain ⟨c, hc⟩ := u32_of (scalar_small scalar)
    obtain ⟨mid, hm⟩ := usize_of (n := p + chunk.length) (by omega)
    have tailBody := ih restOcc mid stop hm (by omega)
    rw [drop_span s offset w, ← bytes]
    have encodes' : Rowl.Encoding.EncodeCorrect c.val (some e) := by rw [hc]; exact encodes
    by_cases raw : IriCharacter cp
    · rw [if_pos raw] at hchunk
      subst hchunk
      rw [span_length found] at hm
      have unit : UnitAt d start.val c mid := by
        have := occurs_unit (i := 0) chunkOcc (prefix_span found) hc (by omega)
        simpa [hs] using this
      have notSlash : c ≠ 92#u32 := u32_ne (by rw [hc]; exact raw.2.2.2.2.2.2.2.2.2)
      have notClosing : c ≠ Closing true := u32_ne (by rw [hc]; exact raw.2.2.1)
      exact .item unit notClosing (.raw unit notSlash (by simpa [RawAllowed, hc] using raw)) encodes' tailBody
    · rw [if_neg raw] at hchunk
      subst hchunk
      rw [uchar_length] at restBound hq hm
      unfold Uchar at chunkOcc
      obtain ⟨slashOcc, afterSlash⟩ := occurs_cons.mp chunkOcc
      obtain ⟨letterOcc, hexOcc⟩ := occurs_cons.mp afterSlash
      obtain ⟨n1, h1⟩ := usize_of (n := p + 1) (by omega)
      obtain ⟨n2, h2⟩ := usize_of (n := p + 1 + 1) (by omega)
      have slash : UnitAt d start.val 92#u32 n1 := by
        rw [hs]
        exact occurs_unit_ascii slashOcc (by decide) rfl h1
      have letter : UnitAt d n1.val 85#u32 n2 := by
        rw [h1]
        exact occurs_unit_ascii letterOcc (by decide) rfl h2
      have digits := hex_read fits 8 cp (p + 1 + 1) hexOcc
      have whole : cp % 16 ^ 8 = cp := Nat.mod_eq_of_lt (by unfold Rowl.Encoding.Scalar at scalar; omega)
      rw [whole] at digits
      have escape : EscapeValue d true n1.val c mid :=
        .eight letter (by rw [hc]; exact scalar) (by rw [hc, h2, hm]; exact digits)
      have notClosing : (92#u32 : U32) ≠ Closing true := u32_ne (by decide)
      exact .item slash notClosing (.escaped slash escape) encodes' tailBody

theorem escape_letter_echar {cp m : Nat} (h : EscapeLetter cp = some m) :
    m < 128 ∧ EcharValue m = some cp ∧ m ≠ 117 ∧ m ≠ 85 := by
  unfold EscapeLetter at h
  by_cases a : cp = 34
  · rw [if_pos a] at h
    cases h
    subst a
    simp [EcharValue]
  · rw [if_neg a] at h
    by_cases b : cp = 92
    · rw [if_pos b] at h
      cases h
      subst b
      simp [EcharValue]
    · rw [if_neg b] at h
      by_cases c : cp = 10
      · rw [if_pos c] at h
        cases h
        subst c
        simp [EcharValue]
      · rw [if_neg c] at h
        by_cases e : cp = 13
        · rw [if_pos e] at h
          cases h
          subst e
          simp [EcharValue]
        · rw [if_neg e] at h
          cases h

theorem escape_letter_none {cp : Nat} (h : EscapeLetter cp = none) : cp ≠ 34 ∧ cp ≠ 92 ∧ cp ≠ 10 ∧ cp ≠ 13 := by
  unfold EscapeLetter at h
  split_ifs at h with a b c e
  exact ⟨a, b, c, e⟩

/-- The characters of a string written from `i`, then `"`, are the body of a
    STRING_LITERAL_QUOTE that denotes the bytes from `i`. -/
theorem string_body_read {d : List U8} (fits : d.length ≤ Usize.max) {s : List U8} {i : Nat} {word : List Nat}
    (valid : Rowl.Regular.Utf8From s i word) :
    ∀ {p : Nat}, Occurs d p (StringText s i ++ [34#u8]) → ∀ (start stop : Usize), start.val = p →
      stop.val = p + (StringText s i).length + 1 → QuotedBody d false start (s.drop i) stop := by
  induction valid with
  | endOfInput =>
    intro p occ start stop hs hq
    rw [string_text_nil (prefix_end s)] at occ hq
    simp only [List.nil_append, List.length_nil] at occ hq
    rw [List.drop_length]
    have unit : UnitAt d start.val 34#u32 stop := by
      rw [hs]
      exact occurs_unit_ascii occ (by decide) rfl (by omega)
    exact .close unit
  | @character offset cp w tail found positive bounded rest ih =>
    intro p occ start stop hs hq
    rw [string_text_cons found] at occ hq
    obtain ⟨scalar, e, encodes, bytes⟩ := prefix_character found
    generalize hchunk : StringChar s offset (offset + w) cp = chunk at occ hq
    rw [List.append_assoc] at occ
    obtain ⟨chunkOcc, restOcc⟩ := occurs_append.mp occ
    have restBound := occurs_bound restOcc
    simp only [List.length_append, List.length_singleton] at restBound hq
    obtain ⟨c, hc⟩ := u32_of (scalar_small scalar)
    obtain ⟨mid, hm⟩ := usize_of (n := p + chunk.length) (by omega)
    have tailBody := ih restOcc mid stop hm (by omega)
    rw [drop_span s offset w, ← bytes]
    have encodes' : Rowl.Encoding.EncodeCorrect c.val (some e) := by rw [hc]; exact encodes
    unfold StringChar at hchunk
    cases letter : EscapeLetter cp with
    | none =>
      rw [letter] at hchunk
      subst hchunk
      obtain ⟨n34, n92, n10, n13⟩ := escape_letter_none letter
      rw [span_length found] at hm
      have unit : UnitAt d start.val c mid := by
        have := occurs_unit (i := 0) chunkOcc (prefix_span found) hc (by omega)
        simpa [hs] using this
      have notSlash : c ≠ 92#u32 := u32_ne (by rw [hc]; exact n92)
      have notClosing : c ≠ Closing false := u32_ne (by rw [hc]; exact n34)
      have allowed : RawAllowed false c.val := by
        simp only [RawAllowed, hc, Bool.false_eq_true, if_false, EndLine]
        omega
      exact .item unit notClosing (.raw unit notSlash allowed) encodes' tailBody
    | some m =>
      rw [letter] at hchunk
      subst hchunk
      obtain ⟨small, echar, -, -⟩ := escape_letter_echar letter
      simp only [List.length_cons, List.length_nil] at hm restBound
      obtain ⟨slashOcc, markerOcc⟩ := occurs_cons.mp chunkOcc
      have markerVal : (byte m).val = m := byte_val (by omega)
      obtain ⟨marker, hk⟩ := u32_of (n := m) (by omega)
      obtain ⟨n1, h1⟩ := usize_of (n := p + 1) (by omega)
      have slash : UnitAt d start.val 92#u32 n1 := by
        rw [hs]
        exact occurs_unit_ascii slashOcc (by decide) rfl h1
      have markerUnit : UnitAt d n1.val marker mid := by
        rw [h1]
        exact occurs_unit_ascii markerOcc (by omega) (by rw [hk, markerVal]) (by omega)
      have escape : EscapeValue d false n1.val c mid := .character rfl markerUnit (by rw [hk, hc]; exact echar)
      have notClosing : (92#u32 : U32) ≠ Closing false := u32_ne (by decide)
      exact .item slash notClosing (.escaped slash escape) encodes' tailBody


/-! ## Lengths of written text -/

theorem prefix_width {s : List U8} {i cp w : Nat} (h : Prefix s i = some (cp, w)) : w ≤ 4 := by
  obtain ⟨-, e, -, bytes⟩ := prefix_character h
  have len := span_length h
  rw [← bytes] at len
  cases e <;> simp [Rowl.Encoding.Bytes] at len <;> omega

theorem ascii_width {s : List U8} {i cp w : Nat} (h : Prefix s i = some (cp, w)) (small : cp < 128) : w = 1 := by
  obtain ⟨-, e, encodes, bytes⟩ := prefix_character h
  have len := span_length h
  rw [← bytes] at len
  cases e with
  | One a => simpa [Rowl.Encoding.Bytes] using len.symm
  | Two a b =>
    simp only [Rowl.Encoding.EncodeCorrect] at encodes
    have := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val 0 0).1 encodes.1
    have := encodes.2
    omega
  | Three a b c =>
    simp only [Rowl.Encoding.EncodeCorrect] at encodes
    have := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val c.val 0).2.1 encodes.1
    have := encodes.2
    omega
  | Four a b c e =>
    simp only [Rowl.Encoding.EncodeCorrect] at encodes
    have := (Rowl.Unicode.byte_grammar_scalar_ranges a.val b.val c.val e.val).2.2 encodes.1
    have := encodes.2
    omega

theorem iri_text_length {s : List U8} {i : Nat} {word : List Nat} (valid : Rowl.Regular.Utf8From s i word) :
    s.length - i ≤ (IriText s i).length := by
  induction valid with
  | endOfInput => simp
  | @character offset cp w tail found positive bounded rest ih =>
    rw [iri_text_cons found, List.length_append]
    split_ifs
    · rw [span_length found]
      omega
    · rw [uchar_length]
      have := prefix_width found
      omega

theorem string_text_length {s : List U8} {i : Nat} {word : List Nat} (valid : Rowl.Regular.Utf8From s i word) :
    s.length - i ≤ (StringText s i).length := by
  induction valid with
  | endOfInput => simp
  | @character offset cp w tail found positive bounded rest ih =>
    rw [string_text_cons found, List.length_append]
    unfold StringChar
    cases letter : EscapeLetter cp with
    | none =>
      simp only
      rw [span_length found]
      omega
    | some m =>
      simp only [List.length_cons, List.length_nil]
      have small : cp < 128 := by
        unfold EscapeLetter at letter
        split_ifs at letter <;> omega
      have := ascii_width found small
      omega

theorem key_text_length : ∀ (l : List U8), (KeyText l).length = 2 * l.length
  | [] => rfl
  | b :: rest => by simp [KeyText, key_text_length rest]; omega

/-- The bytes of written blank node labels after their first: lowercase
    hexadecimal digits and `_`. -/
def LabelByte (b : U8) : Prop := (48 ≤ b.val ∧ b.val ≤ 57) ∨ (97 ≤ b.val ∧ b.val ≤ 102) ∨ b.val = 95

theorem hex_lower_label {n : Nat} (h : n < 16) : LabelByte (hexLower n) := by
  unfold LabelByte hexLower
  split_ifs with small
  · rw [byte_val (by omega)]
    omega
  · rw [byte_val (by omega)]
    omega

theorem key_text_label : ∀ (l : List U8), ∀ b ∈ KeyText l, LabelByte b
  | [], b, member => by simp [KeyText] at member
  | a :: rest, b, member => by
    simp only [KeyText, List.mem_cons] at member
    rcases member with rfl | rfl | later
    · exact hex_lower_label (by scalar_tac)
    · exact hex_lower_label (Nat.mod_lt _ (by omega))
    · exact key_text_label rest b later

theorem label_tail (scope label : List U8) : ∀ b ∈ KeyText scope ++ 95#u8 :: KeyText label, LabelByte b := by
  intro b member
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with left | rfl | right
  · exact key_text_label scope b left
  · right; right; rfl
  · exact key_text_label label b right

theorem written_label_length (scope label : List U8) :
    (WrittenLabel scope label).length = 2 + 2 * scope.length + 2 * label.length := by
  simp [WrittenLabel, key_text_length]
  omega


/-! ## N-Triples tokens of written terms -/

theorem iri_token_read {d : List U8} (fits : d.length ≤ Usize.max) {s : List U8} (valid : Utf8 s) {p : Nat}
    (occ : Occurs d p (IriToken s)) (start stop : Usize) (hs : start.val = p)
    (hq : stop.val = p + (IriToken s).length) : Rowl.NTriples.QuotedToken d start true s stop := by
  obtain ⟨word, text⟩ := valid
  unfold IriToken at occ hq
  rw [List.cons_append] at occ
  obtain ⟨openOcc, bodyOcc⟩ := occurs_cons.mp occ
  have bound := occurs_bound bodyOcc
  simp only [List.length_append, List.length_singleton] at bound
  obtain ⟨next, hn⟩ := usize_of (n := p + 1) (by omega)
  refine ⟨next, ?_, ?_⟩
  · rw [hs]
    exact occurs_unit_ascii openOcc (by decide) rfl hn
  · have hq' : stop.val = p + 1 + (IriText s 0).length + 1 := by
      simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil] at hq
      omega
    have := iri_body_read fits text bodyOcc next stop hn hq'
    simpa using this

theorem iri_token_length {s : List U8} (valid : Utf8 s) : s.length < (IriToken s).length := by
  obtain ⟨word, text⟩ := valid
  have := iri_text_length text
  simp [IriToken]
  omega

/-- The IRI `s` written at `p` is read as that IRI. -/
theorem iri_read {d : List U8} (fits : d.length ≤ Usize.max) {s : List U8} (valid : AbsoluteIri s) {p : Nat}
    (occ : Occurs d p (IriToken s)) (start stop : Usize) (hs : start.val = p)
    (hq : stop.val = p + (IriToken s).length) :
    Rowl.NTriples.QuotedToken d start true s stop ∧ s.length ≤ d.length ∧ AbsoluteIri s := by
  have utf8 := absolute_utf8 valid
  refine ⟨iri_token_read fits utf8 occ start stop hs hq, ?_, valid⟩
  have := iri_token_length utf8
  have := occurs_bound occ
  omega

theorem label_byte_pn {b : U8} (h : LabelByte b) : Rowl.NTriples.Pn b.val ∧ b.val < 128 ∧ b.val ≠ 46 := by
  unfold LabelByte at h
  refine ⟨?_, by omega, by omega⟩
  simp only [Rowl.NTriples.Pn, Rowl.NTriples.PnU, Rowl.NTriples.PnBase, Rowl.NTriples.AsciiDigit]
  omega

theorem blank_tail_read {d : List U8} (fits : d.length ≤ Usize.max) :
    ∀ (L : List U8) (p : Nat), (∀ b ∈ L, LabelByte b) → Occurs d p (L ++ [32#u8]) →
      Rowl.NTriples.BlankTail d p p (p + L.length)
  | [], p, _, occ => by
    have bound := occurs_bound occ
    simp only [List.nil_append, List.length_singleton] at bound occ
    obtain ⟨c, hc⟩ := u32_of (n := 32) (by norm_num)
    obtain ⟨n, hn⟩ := usize_of (n := p + 1) (by omega)
    have unit : UnitAt d p c n := occurs_unit_ascii occ (by decide) (by rw [hc]; rfl) hn
    have notPn : ¬ Rowl.NTriples.Pn c.val := by
      rw [hc]
      simp only [Rowl.NTriples.Pn, Rowl.NTriples.PnU, Rowl.NTriples.PnBase, Rowl.NTriples.AsciiDigit]
      omega
    have := Rowl.NTriples.BlankTail.delimiter (accepted := p) unit notPn (by rw [hc]; omega)
    simpa using this
  | b :: L, p, all, occ => by
    rw [List.cons_append] at occ
    obtain ⟨first, rest⟩ := occurs_cons.mp occ
    have bound := occurs_bound rest
    simp only [List.length_append, List.length_singleton] at bound
    obtain ⟨pn, small, -⟩ := label_byte_pn (all b (by simp))
    obtain ⟨c, hc⟩ := u32_of (n := b.val) (by omega)
    obtain ⟨n, hn⟩ := usize_of (n := p + 1) (by omega)
    have unit : UnitAt d p c n := occurs_unit_ascii first small hc hn
    have tail := blank_tail_read fits L (p + 1) (fun x hx => all x (by simp [hx])) rest
    rw [← hn] at tail
    have := Rowl.NTriples.BlankTail.character (accepted := p) unit (by rw [hc]; exact pn) tail
    rw [hn] at this
    have e : p + (b :: L).length = p + 1 + L.length := by simp only [List.length_cons]; omega
    rw [e]
    exact this

/-- A blank node written at `p`, then a space, is read as the blank node of
    the reader's scope whose label is the written label. -/
theorem blank_token_read {d : List U8} (fits : d.length ≤ Usize.max) (scope : alloc.vec.Vec U8)
    (b : rdf.BlankNode) {p : Nat} (occ : Occurs d p (BlankText b.scope.val b.label.val ++ [32#u8])) :
    ∃ (node : rdf.BlankNode) (stop : Usize), stop.val = p + (BlankText b.scope.val b.label.val).length ∧
      node.scope = scope ∧ node.label.val = WrittenLabel b.scope.val b.label.val ∧
      Rowl.NTriples.BlankToken d scope.val p d.length node stop := by
  have bound := occurs_bound occ
  simp only [BlankText, List.cons_append, List.length_cons, List.length_append, List.length_singleton] at bound
  simp only [BlankText, List.cons_append] at occ
  obtain ⟨underscoreOcc, afterUnderscore⟩ := occurs_cons.mp occ
  obtain ⟨colonOcc, labelOcc⟩ := occurs_cons.mp afterUnderscore
  have labelSpan := occurs_span (occurs_append.mp labelOcc).1
  generalize hL : WrittenLabel b.scope.val b.label.val = label at labelOcc labelSpan bound
  have labelFits : label.length ≤ Usize.max := by omega
  obtain ⟨colon, hColon⟩ := usize_of (n := p + 1) (by omega)
  obtain ⟨begin, hBegin⟩ := usize_of (n := p + 1 + 1) (by omega)
  obtain ⟨stop, hStop⟩ := usize_of (n := p + 1 + 1 + label.length) (by omega)
  refine ⟨⟨scope, alloc.vec.Vec.from label labelFits⟩, stop, by simp [BlankText, hL, hStop]; omega, rfl,
    by simp [hL], ?_⟩
  rw [← hL] at labelOcc
  simp only [WrittenLabel, List.cons_append] at labelOcc
  obtain ⟨firstOcc, tailOcc⟩ := occurs_cons.mp labelOcc
  have lengthIs : label.length = 1 + (KeyText b.scope.val ++ 95#u8 :: KeyText b.label.val).length := by
    rw [← hL]
    simp [WrittenLabel]
    omega
  obtain ⟨first, hFirst⟩ := u32_of (n := 98) (by norm_num)
  obtain ⟨next, hNext⟩ := usize_of (n := p + 1 + 1 + 1) (by omega)
  have tail := blank_tail_read fits _ (p + 1 + 1 + 1) (label_tail b.scope.val b.label.val)
    (by simpa [List.append_assoc] using tailOcc)
  refine ⟨colon, begin, first, next, occurs_unit_ascii underscoreOcc (by decide) rfl hColon, ?_, ?_, ?_, ?_, ?_,
    rfl, ?_⟩
  · rw [hColon]
    exact occurs_unit_ascii colonOcc (by decide) rfl hBegin
  · rw [hBegin]
    exact occurs_unit_ascii firstOcc (by decide) (by rw [hFirst]; rfl) hNext
  · left
    rw [hFirst]
    simp only [Rowl.NTriples.PnU, Rowl.NTriples.PnBase]
    omega
  · rw [hNext, hStop, lengthIs]
    have e : p + 1 + 1 + (1 + (KeyText b.scope.val ++ 95#u8 :: KeyText b.label.val).length) =
        p + 1 + 1 + 1 + (KeyText b.scope.val ++ 95#u8 :: KeyText b.label.val).length := by omega
    rw [e]
    exact tail
  · rw [hStop, hBegin]
    omega
  · simp only [alloc.vec.Vec.from_val]
    rw [hStop, hBegin]
    unfold Span at labelSpan
    rw [show p + 1 + 1 + label.length - (p + 1 + 1) = label.length by omega] at labelSpan
    rw [show p + 1 + 1 + label.length - (p + 1 + 1) = label.length by omega]
    exact labelSpan.symm


/-! ## Trivia, language tags and literals in N-Triples -/

theorem not_spacing {b : Nat} (lines : Bool) (h : b ≠ 9 ∧ b ≠ 32 ∧ b ≠ 10 ∧ b ≠ 13) :
    ¬ Rowl.NTriples.Spacing lines b := by
  simp only [Rowl.NTriples.Spacing, Rowl.NTriples.Horizontal, EndLine]
  omega

/-- White space ends before a written character other than white space and `#`. -/
theorem trivia_stops {d : List U8} (fits : d.length ≤ Usize.max) {p : Nat} {b : U8} (occ : Occurs d p [b])
    (small : b.val < 128) (lines : Bool) (notSpace : ¬ Rowl.NTriples.Spacing lines b.val) (notHash : b.val ≠ 35) :
    Rowl.NTriples.TriviaRuns d lines p p := by
  have bound := occurs_bound occ
  simp only [List.length_singleton] at bound
  obtain ⟨c, hc⟩ := u32_of (n := b.val) (by omega)
  obtain ⟨n, hn⟩ := usize_of (n := p + 1) (by omega)
  exact .token (occurs_unit_ascii occ small hc hn) (by rw [hc]; exact notSpace) (by rw [hc]; exact notHash)

/-- A written space before such a character is white space. -/
theorem trivia_space {d : List U8} (fits : d.length ≤ Usize.max) {p : Nat} {b : U8} (occ : Occurs d p [32#u8, b])
    (small : b.val < 128) (lines : Bool) (notSpace : ¬ Rowl.NTriples.Spacing lines b.val) (notHash : b.val ≠ 35) :
    Rowl.NTriples.TriviaRuns d lines p (p + 1) := by
  obtain ⟨spaceOcc, nextOcc⟩ := occurs_cons.mp occ
  have bound := occurs_bound nextOcc
  simp only [List.length_singleton] at bound
  obtain ⟨n, hn⟩ := usize_of (n := p + 1) (by omega)
  have unit : UnitAt d p 32#u32 n := occurs_unit_ascii spaceOcc (by decide) rfl hn
  have rest := trivia_stops fits nextOcc small lines notSpace notHash
  rw [← hn] at rest ⊢
  exact .space unit (by left; right; rfl) rest

theorem tag_word_read {d : List U8} (fits : d.length ≤ Usize.max) (letters : Bool) :
    ∀ (L : List U8) (p : Nat) (c : U8), (∀ b ∈ L, b.val < 128 ∧ Rowl.NTriples.TagCharacter letters b.val) →
      c.val < 128 → ¬ Rowl.NTriples.TagCharacter letters c.val → Occurs d p (L ++ [c]) →
      ∀ (start finish : Usize), start.val = p → finish.val = p + L.length →
        Rowl.NTriples.TagWord d letters start finish
  | [], p, c, _, small, notTag, occ, start, finish, hs, hf => by
    have same : start = finish := UScalar.eq_of_val_eq (by simp at hf; omega)
    subst same
    have bound := occurs_bound occ
    simp only [List.nil_append, List.length_singleton] at bound occ
    obtain ⟨cc, hc⟩ := u32_of (n := c.val) (by omega)
    obtain ⟨n, hn⟩ := usize_of (n := p + 1) (by omega)
    have unit : UnitAt d start.val cc n := by
      rw [hs]
      exact occurs_unit_ascii occ small hc hn
    exact .stop unit (by rw [hc]; exact notTag)
  | b :: L, p, c, all, small, notTag, occ, start, finish, hs, hf => by
    rw [List.cons_append] at occ
    obtain ⟨first, rest⟩ := occurs_cons.mp occ
    have bound := occurs_bound rest
    simp only [List.length_append, List.length_singleton] at bound
    obtain ⟨smallB, tagB⟩ := all b (by simp)
    obtain ⟨cb, hcb⟩ := u32_of (n := b.val) (by omega)
    obtain ⟨n, hn⟩ := usize_of (n := p + 1) (by omega)
    have unit : UnitAt d start.val cb n := by
      rw [hs]
      exact occurs_unit_ascii first smallB hcb hn
    exact .character unit (by rw [hcb]; exact tagB)
      (tag_word_read fits letters L (p + 1) c (fun x hx => all x (by simp [hx])) small notTag rest n finish hn
        (by simp only [List.length_cons] at hf; omega))

theorem subtags_first {rest : List U8} (h : Subtags rest) :
    ∃ c tail, rest ++ [32#u8] = c :: tail ∧ (c = 32#u8 ∨ c = 45#u8) := by
  cases h with
  | nil => exact ⟨32#u8, [], rfl, Or.inl rfl⟩
  | cons _ _ _ => exact ⟨45#u8, _, rfl, Or.inr rfl⟩

theorem space_dash_not_tag {c : U8} (letters : Bool) (h : c = 32#u8 ∨ c = 45#u8) :
    c.val < 128 ∧ ¬ Rowl.NTriples.TagCharacter letters c.val := by
  rcases h with rfl | rfl
  · refine ⟨by decide, ?_⟩
    simp only [Rowl.NTriples.TagCharacter, Rowl.NTriples.AsciiAlpha, Rowl.NTriples.AsciiDigit]
    have : (32#u8 : U8).val = 32 := rfl
    rw [this]
    omega
  · refine ⟨by decide, ?_⟩
    simp only [Rowl.NTriples.TagCharacter, Rowl.NTriples.AsciiAlpha, Rowl.NTriples.AsciiDigit]
    have : (45#u8 : U8).val = 45 := rfl
    rw [this]
    omega

/-- The written words of a word followed by its next byte. -/
theorem occurs_word {d : List U8} {p : Nat} {w rest tail : List U8} {c : U8}
    (occ : Occurs d p (w ++ rest)) (first : rest = c :: tail) : Occurs d p (w ++ [c]) := by
  obtain ⟨wOcc, restOcc⟩ := occurs_append.mp occ
  rw [first] at restOcc
  exact occurs_append.mpr ⟨wOcc, (occurs_cons.mp restOcc).1⟩

theorem tag_suffix_read {d : List U8} (fits : d.length ≤ Usize.max) {rest : List U8} (h : Subtags rest) :
    ∀ (p : Nat), Occurs d p (rest ++ [32#u8]) → ∀ (start stop : Usize), start.val = p → stop.val = p + rest.length →
      Rowl.NTriples.TagSuffix d start stop := by
  induction h with
  | nil =>
    intro p occ start stop hs hq
    have same : start = stop := UScalar.eq_of_val_eq (by simp at hq; omega)
    subst same
    have bound := occurs_bound occ
    simp only [List.nil_append, List.length_singleton] at bound occ
    obtain ⟨n, hn⟩ := usize_of (n := p + 1) (by omega)
    have unit : UnitAt d start.val 32#u32 n := by
      rw [hs]
      exact occurs_unit_ascii occ (by decide) rfl hn
    exact .stop unit (u32_ne (by decide))
  | @cons w rest nonempty alnum tail ih =>
    intro p occ start stop hs hq
    simp only [List.cons_append, List.append_assoc] at occ
    obtain ⟨dashOcc, afterDash⟩ := occurs_cons.mp occ
    obtain ⟨wOcc, restOcc⟩ := occurs_append.mp afterDash
    have bound := occurs_bound restOcc
    simp only [List.length_append, List.length_singleton] at bound
    simp only [List.length_cons, List.length_append] at hq
    obtain ⟨c, more, split, cIs⟩ := subtags_first tail
    obtain ⟨cSmall, cNot⟩ := space_dash_not_tag false cIs
    obtain ⟨next, hn⟩ := usize_of (n := p + 1) (by omega)
    obtain ⟨middle, hm⟩ := usize_of (n := p + 1 + w.length) (by omega)
    have dash : UnitAt d start.val 45#u32 next := by
      rw [hs]
      exact occurs_unit_ascii dashOcc (by decide) rfl hn
    have word : Rowl.NTriples.TagWord d false next middle :=
      tag_word_read fits false w (p + 1) c (fun b hb => by
        have := alnum b hb
        unfold AlnumByte LetterByte at this
        refine ⟨by omega, ?_⟩
        simp only [Rowl.NTriples.TagCharacter, Rowl.NTriples.AsciiAlpha, Rowl.NTriples.AsciiDigit,
          true_and]
        omega) cSmall cNot (occurs_word afterDash split) next middle hn hm
    have different : next ≠ middle := by
      intro same
      have := congrArg UScalar.val same
      have positive : 0 < w.length := List.length_pos_iff.mpr nonempty
      omega
    exact .subtag dash word different (ih (p + 1 + w.length) restOcc middle stop hm (by omega))

/-- A written language tag of LANGTAG's form, then a space, is read as that tag. -/
theorem tag_token_read {d : List U8} (fits : d.length ≤ Usize.max) (t : alloc.vec.Vec U8) (form : TagForm t.val)
    (valid : LanguageTag t.val) {p : Nat} (occ : Occurs d p (64#u8 :: t.val ++ [32#u8])) (start stop : Usize)
    (hs : start.val = p) (hq : stop.val = p + 1 + t.val.length) : Rowl.NTriples.TagToken d start d.length t stop := by
  obtain ⟨head, rest, whole, nonempty, letters, tail⟩ := form
  rw [List.cons_append] at occ
  obtain ⟨atOcc, tagOcc⟩ := occurs_cons.mp occ
  have tagSpan := occurs_span (occurs_append.mp tagOcc).1
  rw [whole, List.append_assoc] at tagOcc
  obtain ⟨headOcc, restOcc⟩ := occurs_append.mp tagOcc
  have bound := occurs_bound restOcc
  simp only [List.length_append, List.length_singleton] at bound
  have tLength : t.val.length = head.length + rest.length := by rw [whole, List.length_append]
  obtain ⟨c, more, split, cIs⟩ := subtags_first tail
  obtain ⟨cSmall, cNot⟩ := space_dash_not_tag true cIs
  obtain ⟨begin, hb⟩ := usize_of (n := p + 1) (by omega)
  obtain ⟨headEnd, he⟩ := usize_of (n := p + 1 + head.length) (by omega)
  have word : Rowl.NTriples.TagWord d true begin headEnd :=
    tag_word_read fits true head (p + 1) c (fun b hb => by
      have := letters b hb
      unfold LetterByte at this
      refine ⟨by omega, ?_⟩
      simp only [Rowl.NTriples.TagCharacter, Rowl.NTriples.AsciiAlpha]
      omega) cSmall cNot (occurs_word tagOcc split) begin headEnd hb he
  refine ⟨begin, headEnd, ?_, word, ?_, tag_suffix_read fits tail _ restOcc headEnd stop he (by omega), ⟨?_, ?_⟩, valid⟩
  · rw [hs]
    exact occurs_unit_ascii atOcc (by decide) rfl hb
  · intro same
    have := congrArg UScalar.val same
    have positive : 0 < head.length := List.length_pos_iff.mpr nonempty
    omega
  · have := occurs_bound tagOcc
    simp only [List.length_append, List.length_singleton] at this
    omega
  · unfold Span at tagSpan
    rw [show p + 1 + t.val.length - (p + 1) = t.val.length by omega] at tagSpan
    rw [hq, hb, show p + 1 + t.val.length - (p + 1) = t.val.length by omega]
    exact tagSpan.symm


/-! ## Blank node renaming -/

/-- The term a written term is read as in the scope `σ`: a blank node of the
    scope `s` and the label `l` becomes the blank node of `σ` with the label
    `WrittenLabel s l`; IRIs and literals stay. -/
def renameTerm (σ : List U8) : Rowl.TurtleTokens.Term → Rowl.TurtleTokens.Term
  | .blank s l => .blank σ (WrittenLabel s l)
  | .iri v => .iri v
  | .literal v k => .literal v k

/-- The triple a written triple is read as in the scope `σ`. -/
def RenameSpo (σ : List U8) (x : Rowl.Turtle.Spo) : Rowl.Turtle.Spo :=
  ⟨renameTerm σ x.subject, x.predicate, renameTerm σ x.object⟩

theorem key_text_hex : ∀ (a : List U8), ∀ b ∈ KeyText a, (48 ≤ b.val ∧ b.val ≤ 57) ∨ (97 ≤ b.val ∧ b.val ≤ 102)
  | [], b, member => by simp [KeyText] at member
  | x :: rest, b, member => by
    simp only [KeyText, List.mem_cons] at member
    have small : x.val < 256 := by scalar_tac
    rcases member with rfl | rfl | later
    · unfold hexLower
      split_ifs <;> rw [byte_val (by omega)] <;> omega
    · have := Nat.mod_lt x.val (show 16 > 0 by omega)
      unfold hexLower
      split_ifs <;> rw [byte_val (by omega)] <;> omega
    · exact key_text_hex rest b later

theorem key_text_injective : ∀ {a b : List U8}, KeyText a = KeyText b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [KeyText] at h
  | _ :: _, [], h => by simp [KeyText] at h
  | x :: a, y :: b, h => by
    simp only [KeyText, List.cons.injEq] at h
    obtain ⟨high, low, rest⟩ := h
    have xs : x.val < 256 := by scalar_tac
    have ys : y.val < 256 := by scalar_tac
    have xm := Nat.mod_lt x.val (show 16 > 0 by omega)
    have ym := Nat.mod_lt y.val (show 16 > 0 by omega)
    have hv := congrArg UScalar.val high
    have lv := congrArg UScalar.val low
    unfold hexLower at hv lv
    have h1 : x.val / 16 = y.val / 16 := by
      split_ifs at hv <;> rw [byte_val (by omega), byte_val (by omega)] at hv <;> omega
    have h2 : x.val % 16 = y.val % 16 := by
      split_ifs at lv <;> rw [byte_val (by omega), byte_val (by omega)] at lv <;> omega
    have same : x = y := UScalar.eq_of_val_eq (by omega)
    rw [same, key_text_injective rest]

theorem key_text_no_underscore (a : List U8) : 95#u8 ∉ KeyText a := by
  intro member
  have := key_text_hex a _ member
  have v : (95#u8 : U8).val = 95 := rfl
  rw [v] at this
  omega

theorem split_unique {a : U8} : ∀ {x x' y y' : List U8}, a ∉ x → a ∉ x' → x ++ a :: y = x' ++ a :: y' →
    x = x' ∧ y = y'
  | [], [], y, y', _, _, h => by simpa using h
  | [], b :: x', y, y', _, n', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) n'
  | b :: x, [], y, y', n, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) n
  | b :: x, c :: x', y, y', n, n', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨first, rest⟩ := h
    obtain ⟨e1, e2⟩ := split_unique (fun m => n (List.mem_cons_of_mem _ m))
      (fun m => n' (List.mem_cons_of_mem _ m)) rest
    exact ⟨by rw [first, e1], e2⟩

/-- Written labels determine the blank node they were written for, so the
    renaming of blank nodes is one to one. -/
theorem written_label_injective {s l s' l' : List U8} (h : WrittenLabel s l = WrittenLabel s' l') :
    s = s' ∧ l = l' := by
  simp only [WrittenLabel, List.cons_append, List.cons.injEq, true_and] at h
  obtain ⟨e1, e2⟩ := split_unique (key_text_no_underscore s) (key_text_no_underscore s') h
  exact ⟨key_text_injective e1, key_text_injective e2⟩

/-! ## Reading written N-Triples -/

theorem literal_fault_none {resolved : Bool} {l : rdf.RdfLiteral} (h : LiteralFault resolved l = none) :
    Utf8 l.lexical.val ∧
      (∀ d, l.kind = .Datatype d → d.spelling.val ≠ LangStringBytes ∧ IriFault resolved d.spelling.val = none) ∧
      (∀ t, l.kind = .Language t → TagForm t.val ∧ LanguageTag t.val) := by
  unfold LiteralFault at h
  split_ifs at h with valid
  refine ⟨by simpa using valid, ?_, ?_⟩
  · intro d hd
    rw [hd] at h
    simp only at h
    split_ifs at h with lang
    exact ⟨lang, h⟩
  · intro t ht
    rw [ht] at h
    simp only at h
    split_ifs at h with ok
    exact ok

/-- A literal without faults written at `p`, then a space, is read as itself. -/
theorem literal_read {d : List U8} (fits : d.length ≤ Usize.max) (l : rdf.RdfLiteral)
    (ok : LiteralFault false l = none) {p : Nat} (occ : Occurs d p (LiteralText l ++ [32#u8])) (start stop : Usize)
    (hs : start.val = p) (hq : stop.val = p + (LiteralText l).length) :
    Rowl.NTriples.LiteralToken d start d.length l stop := by
  obtain ⟨⟨word, text⟩, dataOk, langOk⟩ := literal_fault_none ok
  have wholeBound := occurs_bound occ
  unfold LiteralText at occ hq wholeBound
  simp only [List.cons_append, List.append_assoc] at occ
  obtain ⟨openOcc, afterOpen⟩ := occurs_cons.mp occ
  have body := occurs_word afterOpen rfl
  obtain ⟨-, kindOcc'⟩ := occurs_append.mp afterOpen
  obtain ⟨-, kindOcc⟩ := occurs_cons.mp kindOcc'
  have lexBound := string_text_length text
  simp only [List.length_append, List.length_cons, List.length_nil] at wholeBound hq
  obtain ⟨n1, h1⟩ := usize_of (n := p + 1) (by omega)
  obtain ⟨ending, he⟩ := usize_of (n := p + 1 + (StringText l.lexical.val 0).length + 1) (by omega)
  have quoted : Rowl.NTriples.QuotedToken d start false l.lexical.val ending := by
    refine ⟨n1, ?_, ?_⟩
    · rw [hs]
      exact occurs_unit_ascii openOcc (by decide) rfl h1
    · have := string_body_read fits text body n1 ending h1 he
      simpa using this
  refine ⟨ending, ending, quoted, by omega, ?_⟩
  rw [← he] at kindOcc
  cases hk : l.kind with
  | Datatype dt =>
    obtain ⟨lang, iriOk⟩ := dataOk dt hk
    have absolute := (iri_fault_none iriOk).1
    rw [hk] at kindOcc hq wholeBound
    simp only [KindText, List.cons_append] at kindOcc
    simp only [KindText, List.length_cons] at hq wholeBound
    obtain ⟨caret1, afterCaret1⟩ := occurs_cons.mp kindOcc
    obtain ⟨caret2, iriOcc⟩ := occurs_cons.mp afterCaret1
    have iriOnly := (occurs_append.mp iriOcc).1
    have iriBound := occurs_bound iriOnly
    obtain ⟨n2, h2⟩ := usize_of (n := ending.val + 1) (by omega)
    obtain ⟨after, ha⟩ := usize_of (n := ending.val + 1 + 1) (by omega)
    refine ⟨trivia_stops fits (occurs_cons.mp kindOcc).1 (by decide) false (not_spacing false (by decide))
      (by decide), ?_⟩
    have iriFirst : Occurs d (ending.val + 1 + 1) [60#u8] := by
      unfold IriToken at iriOnly
      exact (occurs_cons.mp (by simpa [List.cons_append] using iriOnly)).1
    exact .datatype (occurs_unit_ascii caret1 (by decide) rfl h2)
      (by rw [h2]; exact occurs_unit_ascii caret2 (by decide) rfl ha)
      (by rw [ha]; exact trivia_stops fits iriFirst (by decide) false (not_spacing false (by decide)) (by decide))
      (iri_read fits absolute iriOnly after stop ha (by omega)) lang
  | Language t =>
    obtain ⟨form, valid⟩ := langOk t hk
    rw [hk] at kindOcc hq wholeBound
    simp only [KindText] at kindOcc
    simp only [KindText, List.length_cons] at hq wholeBound
    have atOcc : Occurs d ending.val [64#u8] := (occurs_cons.mp (by simpa [List.cons_append] using kindOcc)).1
    obtain ⟨n2, h2⟩ := usize_of (n := ending.val + 1) (by omega)
    refine ⟨trivia_stops fits atOcc (by decide) false (not_spacing false (by decide)) (by decide), ?_⟩
    exact .language (occurs_unit_ascii atOcc (by decide) rfl h2)
      (tag_token_read fits t form valid kindOcc ending stop rfl (by omega))


theorem subject_text_first (s : rdf.Subject) :
    ∃ c rest, SubjectText s = c :: rest ∧ (c = 60#u8 ∨ c = 95#u8) := by
  cases s with
  | Iri v => exact ⟨_, _, rfl, Or.inl rfl⟩
  | Blank b => exact ⟨_, _, rfl, Or.inr rfl⟩

theorem object_text_first (o : rdf.Object) :
    ∃ c rest, ObjectText o = c :: rest ∧ (c = 60#u8 ∨ c = 95#u8 ∨ c = 34#u8) := by
  cases o with
  | Iri v => exact ⟨_, _, rfl, Or.inl rfl⟩
  | Blank b => exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
  | Literal l => exact ⟨_, _, rfl, Or.inr (Or.inr rfl)⟩

/-- A term's first written byte ends the white space before it. -/
theorem term_trivia {d : List U8} (fits : d.length ≤ Usize.max) {p : Nat} {c : U8} {rest : List U8}
    (occ : Occurs d p (c :: rest)) (first : c = 60#u8 ∨ c = 95#u8 ∨ c = 34#u8) (lines : Bool) :
    Rowl.NTriples.TriviaRuns d lines p p := by
  have one := (occurs_cons.mp occ).1
  rcases first with rfl | rfl | rfl
  · exact trivia_stops fits one (by decide) lines (not_spacing lines (by decide)) (by decide)
  · exact trivia_stops fits one (by decide) lines (not_spacing lines (by decide)) (by decide)
  · exact trivia_stops fits one (by decide) lines (not_spacing lines (by decide)) (by decide)

/-- A space and then a term. -/
theorem space_trivia {d : List U8} (fits : d.length ≤ Usize.max) {p : Nat} {c : U8} {rest : List U8}
    (occ : Occurs d p (32#u8 :: c :: rest)) (first : c = 60#u8 ∨ c = 95#u8 ∨ c = 34#u8) (lines : Bool) :
    Rowl.NTriples.TriviaRuns d lines p (p + 1) := by
  have two : Occurs d p [32#u8, c] := by
    obtain ⟨spaceOcc, more⟩ := occurs_cons.mp occ
    exact occurs_cons.mpr ⟨spaceOcc, (occurs_cons.mp more).1⟩
  rcases first with rfl | rfl | rfl
  · exact trivia_space fits two (by decide) lines (not_spacing lines (by decide)) (by decide)
  · exact trivia_space fits two (by decide) lines (not_spacing lines (by decide)) (by decide)
  · exact trivia_space fits two (by decide) lines (not_spacing lines (by decide)) (by decide)

theorem subject_read {d : List U8} (fits : d.length ≤ Usize.max) (scope : alloc.vec.Vec U8) (s : rdf.Subject)
    (ok : SubjectFault false s = none) {p : Nat} (occ : Occurs d p (SubjectText s ++ [32#u8])) (start : Usize)
    (hs : start.val = p) :
    ∃ (value : rdf.Subject) (stop : Usize), stop.val = p + (SubjectText s).length ∧
      Rowl.TurtleTokens.subjectTerm value = renameTerm scope.val (Rowl.TurtleTokens.subjectTerm s) ∧
      Rowl.NTriples.SubjectToken d scope.val start d.length value stop := by
  have bound := occurs_bound occ
  simp only [List.length_append, List.length_singleton] at bound
  cases s with
  | Iri v =>
    obtain ⟨stop, hq⟩ := usize_of (n := p + (SubjectText (.Iri v)).length) (by omega)
    refine ⟨.Iri v, stop, hq, rfl, ?_⟩
    exact iri_read fits (iri_fault_none ok).1 (occurs_append.mp occ).1 start stop hs hq
  | Blank b =>
    obtain ⟨node, stop, hq, scopeIs, labelIs, token⟩ := blank_token_read fits scope b occ
    refine ⟨.Blank node, stop, hq, ?_, by simp only [Rowl.NTriples.SubjectToken]; rw [hs]; exact token⟩
    simp [Rowl.TurtleTokens.subjectTerm, renameTerm, scopeIs, labelIs]

theorem object_read {d : List U8} (fits : d.length ≤ Usize.max) (scope : alloc.vec.Vec U8) (o : rdf.Object)
    (ok : ObjectFault false o = none) {p : Nat} (occ : Occurs d p (ObjectText o ++ [32#u8])) (start : Usize)
    (hs : start.val = p) :
    ∃ (value : rdf.Object) (stop : Usize), stop.val = p + (ObjectText o).length ∧
      Rowl.TurtleTokens.objectTerm value = renameTerm scope.val (Rowl.TurtleTokens.objectTerm o) ∧
      Rowl.NTriples.ObjectToken d scope.val start d.length value stop := by
  have bound := occurs_bound occ
  simp only [List.length_append, List.length_singleton] at bound
  cases o with
  | Iri v =>
    obtain ⟨stop, hq⟩ := usize_of (n := p + (ObjectText (.Iri v)).length) (by omega)
    refine ⟨.Iri v, stop, hq, rfl, ?_⟩
    exact iri_read fits (iri_fault_none ok).1 (occurs_append.mp occ).1 start stop hs hq
  | Blank b =>
    obtain ⟨node, stop, hq, scopeIs, labelIs, token⟩ := blank_token_read fits scope b occ
    refine ⟨.Blank node, stop, hq, ?_, by simp only [Rowl.NTriples.ObjectToken]; rw [hs]; exact token⟩
    simp [Rowl.TurtleTokens.objectTerm, renameTerm, scopeIs, labelIs]
  | Literal l =>
    obtain ⟨stop, hq⟩ := usize_of (n := p + (ObjectText (.Literal l)).length) (by omega)
    refine ⟨.Literal l, stop, hq, ?_, literal_read fits l ok occ start stop hs hq⟩
    cases hk : l.kind <;> simp [Rowl.TurtleTokens.objectTerm, Rowl.TurtleTokens.literalTerm, renameTerm, hk]

theorem triple_fault_none {resolved : Bool} {t : rdf.Triple} (h : TripleFault resolved t = none) :
    SubjectFault resolved t.subject = none ∧ IriFault resolved t.predicate.spelling.val = none ∧
      ObjectFault resolved t.object = none := by
  unfold TripleFault at h
  simp only [Option.or_eq_none_iff] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- A triple without faults written on a line at `p` is read as the triple
    with its blank nodes renamed, and the line feed is left. -/
theorem triple_read {d : List U8} (fits : d.length ≤ Usize.max) (scope : alloc.vec.Vec U8) (t : rdf.Triple)
    (ok : TripleFault false t = none) {p : Nat} (occ : Occurs d p (LineText t)) (start : Usize)
    (hs : start.val = p) :
    ∃ (value : rdf.Triple) (stop : Usize), stop.val + 1 = p + (LineText t).length ∧
      Rowl.Turtle.spo value = RenameSpo scope.val (Rowl.Turtle.spo t) ∧
      Rowl.NTriples.TripleToken d scope.val start d.length value stop := by
  obtain ⟨subjectOk, predicateOk, objectOk⟩ := triple_fault_none ok
  have bound := occurs_bound occ
  unfold LineText TripleText at occ bound
  simp only [List.append_assoc, List.cons_append, List.length_append, List.length_cons, List.length_nil] at occ bound
  -- the subject, then a space
  obtain ⟨subjectOcc, afterSubject⟩ := occurs_append.mp occ
  obtain ⟨subjectValue, subjectEnd, hse, subjectTermIs, subjectToken⟩ :=
    subject_read fits scope t.subject subjectOk (occurs_word occ rfl) start hs
  rw [← hse] at afterSubject
  -- the predicate, then a space
  obtain ⟨predicateStart, hps⟩ := usize_of (n := subjectEnd.val + 1) (by omega)
  obtain ⟨-, predicatePart⟩ := occurs_cons.mp afterSubject
  rw [← hps] at predicatePart
  have predicateOnly := (occurs_append.mp predicatePart).1
  obtain ⟨predicateEnd, hpe⟩ := usize_of (n := predicateStart.val + (IriToken t.predicate.spelling.val).length)
    (by omega)
  have predicateToken := iri_read fits (iri_fault_none predicateOk).1 predicateOnly predicateStart predicateEnd rfl hpe
  obtain ⟨-, afterPredicate⟩ := occurs_append.mp predicatePart
  rw [← hpe] at afterPredicate
  -- the object, then ` .` and a line feed
  obtain ⟨objectStart, hos⟩ := usize_of (n := predicateEnd.val + 1) (by omega)
  obtain ⟨-, objectPart⟩ := occurs_cons.mp afterPredicate
  rw [← hos] at objectPart
  obtain ⟨objectValue, objectEnd, hoe, objectTermIs, objectToken⟩ :=
    object_read fits scope t.object objectOk (occurs_word objectPart rfl) objectStart rfl
  obtain ⟨-, afterObject⟩ := occurs_append.mp objectPart
  rw [← hoe] at afterObject
  obtain ⟨periodStart, hp1⟩ := usize_of (n := objectEnd.val + 1) (by omega)
  obtain ⟨periodEnd, hp2⟩ := usize_of (n := objectEnd.val + 1 + 1) (by omega)
  obtain ⟨spaceOcc, afterSpace⟩ := occurs_cons.mp afterObject
  obtain ⟨periodOcc, feedOcc⟩ := occurs_cons.mp afterSpace
  have feedOnly : Occurs d (objectEnd.val + 1 + 1) [10#u8] := feedOcc
  obtain ⟨feedEnd, hfe⟩ := usize_of (n := objectEnd.val + 1 + 1 + 1) (by omega)
  obtain ⟨sc, srest, sIs, sFirst⟩ := subject_text_first t.subject
  obtain ⟨pc, prest, pIs, pFirst⟩ : ∃ c rest, IriToken t.predicate.spelling.val = c :: rest ∧ c = 60#u8 :=
    ⟨_, _, rfl, rfl⟩
  obtain ⟨oc, orest, oIs, oFirst⟩ := object_text_first t.object
  have lineLength : (LineText t).length = (SubjectText t.subject).length + 1 +
      (IriToken t.predicate.spelling.val).length + 1 + (ObjectText t.object).length + 3 := by
    simp [LineText, TripleText]
    omega
  refine ⟨⟨subjectValue, t.predicate, objectValue⟩, periodEnd, by omega, ?_, ?_⟩
  · simp [Rowl.Turtle.spo, RenameSpo, subjectTermIs, objectTermIs]
  refine ⟨⟨objectEnd, periodStart, periodEnd, ⟨predicateEnd, objectStart,
    ⟨subjectEnd, predicateStart, subjectToken, ?_, predicateToken⟩, ?_, objectToken⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [hps]
    rw [pIs] at predicatePart
    have := occurs_cons.mpr ⟨(occurs_cons.mp afterSubject).1, by rw [← hps]; exact predicatePart⟩
    exact space_trivia fits (by simpa using this) (Or.inl pFirst) false
  · rw [hos]
    rw [oIs] at objectPart
    have := occurs_cons.mpr ⟨(occurs_cons.mp afterPredicate).1, by rw [← hos]; exact objectPart⟩
    exact space_trivia fits (by simpa using this) oFirst false
  · rw [hp1]
    exact trivia_space fits (occurs_cons.mpr ⟨spaceOcc, (occurs_cons.mp afterSpace).1⟩) (by decide) false
      (not_spacing false (by decide)) (by decide)
  · rw [hp1]
    exact occurs_unit_ascii (occurs_cons.mp afterSpace).1 (by decide) rfl (by omega)
  · rw [hp2]
    exact trivia_stops fits feedOnly (by decide) false
      (by simp [Rowl.NTriples.Spacing, Rowl.NTriples.Horizontal]) (by decide)
  · refine .eol (cp := 10#u32) (next := feedEnd) ?_ (by left; rfl)
    rw [hp2]
    exact occurs_unit_ascii feedOnly (by decide) rfl (by omega)


theorem line_text_length (t : rdf.Triple) : (LineText t).length = (TripleText t).length + 3 := by
  simp [LineText]

theorem lines_start {d : List U8} (fits : d.length ≤ Usize.max) {p : Nat} {ts : List rdf.Triple}
    (occ : Occurs d p (LinesText ts)) (ends : p + (LinesText ts).length = d.length) :
    Rowl.NTriples.TriviaRuns d true p p := by
  cases ts with
  | nil =>
    simp only [LinesText, List.length_nil, Nat.add_zero] at ends
    rw [ends]
    exact .eof
  | cons u rest =>
    obtain ⟨c, srest, sIs, sFirst⟩ := subject_text_first u.subject
    simp only [LinesText, LineText, TripleText, sIs, List.append_assoc, List.cons_append] at occ
    exact term_trivia fits occ (by rcases sFirst with h | h <;> simp [h]) true

/-- The lines of triples without faults written from `p` to the end are read
    as those triples with their blank nodes renamed. -/
theorem lines_read {d : List U8} (fits : d.length ≤ Usize.max) (scope : alloc.vec.Vec U8) :
    ∀ (ts : List rdf.Triple), (∀ t ∈ ts, TripleFault false t = none) → ∀ (p count : Nat) (position : Usize),
      position.val = p → Occurs d p (LinesText ts) → p + (LinesText ts).length = d.length → count ≤ p →
      ∃ ts' : List rdf.Triple,
        ts'.map Rowl.Turtle.spo = ts.map (fun t => RenameSpo scope.val (Rowl.Turtle.spo t)) ∧
        Rowl.NTriples.DocumentTail d scope.val d.length d.length position count ts'
  | [], _, p, count, position, hp, _, ends, _ =>
    ⟨[], rfl, .eof (by simp only [LinesText, List.length_nil, Nat.add_zero] at ends; omega)⟩
  | t :: ts, ok, p, count, position, hp, occ, ends, counted => by
    simp only [LinesText] at occ ends
    rw [List.length_append] at ends
    obtain ⟨lineOcc, restOcc⟩ := occurs_append.mp occ
    obtain ⟨value, stop, hstop, spoIs, token⟩ := triple_read fits scope t (ok t (by simp)) lineOcc position hp
    have lineLength := line_text_length t
    obtain ⟨next, hn⟩ := usize_of (n := p + (LineText t).length) (by omega)
    obtain ⟨tail', tailSpo, tail⟩ := lines_read fits scope ts (fun u hu => ok u (by simp [hu]))
      (p + (LineText t).length)
      (count + 1) next hn restOcc (by omega) (by omega)
    refine ⟨value :: tail', by simp [spoIs, tailSpo], .triple token (by omega) ?_ tail⟩
    have feed : Occurs d stop.val [10#u8] := by
      unfold LineText at lineOcc
      obtain ⟨-, endOcc⟩ := occurs_append.mp lineOcc
      obtain ⟨-, more⟩ := occurs_cons.mp endOcc
      obtain ⟨-, feedOcc⟩ := occurs_cons.mp more
      rw [show stop.val = p + (TripleText t).length + 1 + 1 by omega]
      exact feedOcc
    have unit : UnitAt d stop.val 10#u32 next := occurs_unit_ascii feed (by decide) rfl (by omega)
    have rest : Rowl.NTriples.TriviaRuns d true next.val next.val := by
      rw [hn]
      exact lines_start fits restOcc (by omega)
    exact .space unit (by right; exact ⟨rfl, Or.inl rfl⟩) rest

/-- The N-Triples writer is exact: the bytes `ntriples::write` returns are read
    back by `ntriples::read`, in any blank node scope `scope`, as the graph's
    triples in order, each blank node of the scope `s` and the label `l`
    becoming the blank node of `scope` with the label `WrittenLabel s l`
    (one to one by `written_label_injective`). -/
theorem ntriples_write_read (graph : rdf.RawGraph) (limit : Usize) (bytes scope : alloc.vec.Vec U8)
    (written : ntriples.write graph limit = .ok (.Bytes bytes)) :
    ∃ read, ntriples.read bytes scope = .ok (.Graph read) ∧
      read.triples.val.map Rowl.Turtle.spo =
        graph.triples.val.map (fun t => RenameSpo scope.val (Rowl.Turtle.spo t)) := by
  obtain ⟨r, run, correct⟩ := write_graph_total_correct graph false limit
  unfold ntriples.write at written
  have same : r = .Bytes bytes := Result.ok_injective (run.symm.trans written)
  subst same
  obtain ⟨fault, contents, -⟩ := correct
  have ok := graph_fault_triples fault
  have fits : bytes.val.length ≤ Usize.max := bytes.property
  have occ : Occurs bytes.val 0 (LinesText graph.triples.val) := ⟨[], [], by simp [contents], rfl⟩
  have ends : 0 + (LinesText graph.triples.val).length = bytes.val.length := by simp [contents]
  obtain ⟨ts', spoIs, tail⟩ := lines_read fits scope graph.triples.val ok 0 0 0#usize rfl occ ends (le_refl 0)
  have count : ts'.length ≤ Usize.max := by
    have := congrArg List.length spoIs
    simp only [List.length_map] at this
    have := graph.triples.property
    omega
  refine ⟨⟨alloc.vec.Vec.from ts' count⟩, ?_, by simpa using spoIs⟩
  apply (Rowl.NTriples.read_accepted_iff bytes scope _).mpr
  refine ⟨0#usize, ?_, by simpa using tail⟩
  exact lines_start fits occ ends


/-! ## Turtle tokens of written terms -/

theorem absolute_reference {s : List U8} (h : AbsoluteIri s) : Rowl.TurtleTokens.IsReference s := by
  obtain ⟨word, text, iri⟩ := h
  exact ⟨word, text, Or.inl iri⟩

/-- An IRI with a scheme resolves to the same IRI against every base. -/
theorem resolves_any_base {s base : List U8} (h : Resolves [] s s) (short : base.length < Usize.max / 8) :
    Resolves base s s := by
  obtain ⟨-, small, r⟩ := h
  refine ⟨short, small, ?_⟩
  unfold Rowl.IriResolution.resolve at r ⊢
  have noScheme : (Rowl.IriResolution.split (Rowl.References.Word [])).scheme.isSome = false := by
    simp [Rowl.IriResolution.split, Rowl.IriResolution.schemePart, Rowl.References.Word]
  split_ifs at r with c
  have scheme : (Rowl.IriResolution.split (Rowl.References.Word s)).scheme.isSome := by
    rcases c with c | c
    · exact c
    · rw [noScheme] at c
      exact absurd c (by simp)
  rw [if_pos (Or.inl scheme), ← r]
  congr 2
  unfold Rowl.IriResolution.transform
  rw [if_pos scheme, if_pos scheme]

/-- The IRI `s`, which RFC 3986 resolution leaves, written at `p` is read by
    Turtle as `s` against every base shorter than `usize::MAX / 8` bytes. -/
theorem turtle_iri_read {d : List U8} (fits : d.length ≤ Usize.max) {s : List U8} (ok : IriFault true s = none)
    {base : List U8} (short : base.length < Usize.max / 8) {p : Nat} (occ : Occurs d p (IriToken s)) :
    Rowl.TurtleTokens.IriRef d base Usize.max p (.ok (s, p + (IriToken s).length)) := by
  obtain ⟨absolute, keeps⟩ := iri_fault_none ok
  obtain ⟨start, hs⟩ := usize_of (n := p) (by have := occurs_bound occ; omega)
  obtain ⟨stop, hq⟩ := usize_of (n := p + (IriToken s).length) (by have := occurs_bound occ; omega)
  obtain ⟨token, short', -⟩ := iri_read fits absolute occ start stop hs hq
  exact .iri ⟨start, stop, hs, hq, token⟩ (by omega) (absolute_reference absolute)
    (resolves_any_base (keeps rfl) short) (by omega) absolute

theorem label_byte_chars {b : U8} (h : LabelByte b) : Rowl.TurtleTokens.PnChars b.val ∧ b.val < 128 ∧ b.val ≠ 46 := by
  unfold LabelByte at h
  refine ⟨?_, by omega, by omega⟩
  simp only [Rowl.TurtleTokens.PnChars, Rowl.TurtleTokens.PnCharsU, Rowl.NTriples.PnBase, Rowl.NTriples.AsciiDigit]
  omega

theorem name_tail_read {d : List U8} (fits : d.length ≤ Usize.max) :
    ∀ (L : List U8) (p : Nat), (∀ b ∈ L, LabelByte b) → Occurs d p (L ++ [32#u8]) →
      Rowl.TurtleTokens.NameTail d p p (.ok (p + L.length))
  | [], p, _, occ => by
    simp only [List.nil_append] at occ
    have := Rowl.TurtleTokens.NameTail.other (a := p) (occurs_turtle_ascii occ (by decide))
      (by
        have v : (32#u8 : U8).val = 32 := rfl
        rw [v]
        simp only [Rowl.TurtleTokens.PnChars, Rowl.TurtleTokens.PnCharsU, Rowl.NTriples.PnBase,
          Rowl.NTriples.AsciiDigit]
        omega)
      (by decide)
    simpa using this
  | b :: L, p, all, occ => by
    rw [List.cons_append] at occ
    obtain ⟨first, rest⟩ := occurs_cons.mp occ
    obtain ⟨chars, small, -⟩ := label_byte_chars (all b (by simp))
    have tail := name_tail_read fits L (p + 1) (fun x hx => all x (by simp [hx])) rest
    have := Rowl.TurtleTokens.NameTail.char (a := p) (occurs_turtle_ascii first small) chars tail
    have e : p + (b :: L).length = p + 1 + L.length := by simp only [List.length_cons]; omega
    rw [e]
    exact this

/-- A blank node written at `p`, then a space, is read by Turtle as the blank
    node of the reader's scope whose label is the written label. -/
theorem turtle_blank_read {d : List U8} (fits : d.length ≤ Usize.max) (scope : List U8) (b : rdf.BlankNode)
    {p : Nat} (occ : Occurs d p (BlankText b.scope.val b.label.val ++ [32#u8])) :
    Rowl.TurtleTokens.BlankLabel d scope Usize.max p
      (.ok (.blank scope (WrittenLabel b.scope.val b.label.val), p + (BlankText b.scope.val b.label.val).length)) := by
  have bound := occurs_bound occ
  simp only [BlankText, List.cons_append, List.length_cons, List.length_append, List.length_singleton] at bound
  simp only [BlankText, List.cons_append] at occ
  obtain ⟨-, afterUnderscore⟩ := occurs_cons.mp occ
  obtain ⟨colonOcc, labelOcc⟩ := occurs_cons.mp afterUnderscore
  have labelSpan := occurs_span (occurs_append.mp labelOcc).1
  have lengthIs : (WrittenLabel b.scope.val b.label.val).length =
      1 + (KeyText b.scope.val ++ 95#u8 :: KeyText b.label.val).length := by
    simp [WrittenLabel]
    omega
  have labelOcc' := labelOcc
  simp only [WrittenLabel, List.cons_append] at labelOcc'
  obtain ⟨firstOcc, tailOcc⟩ := occurs_cons.mp labelOcc'
  have tail := name_tail_read fits _ (p + 1 + 1 + 1) (label_tail b.scope.val b.label.val)
    (by simpa [List.append_assoc] using tailOcc)
  have e : p + 1 + 1 + 1 + (KeyText b.scope.val ++ 95#u8 :: KeyText b.label.val).length =
      p + 2 + (WrittenLabel b.scope.val b.label.val).length := by omega
  rw [e] at tail
  have spanIs : Span d (p + 2) (p + 2 + (WrittenLabel b.scope.val b.label.val).length) =
      WrittenLabel b.scope.val b.label.val := labelSpan
  have := Rowl.TurtleTokens.BlankLabel.label (scope := scope) (limit := Usize.max)
    (occurs_byte_is colonOcc) (occurs_turtle_ascii firstOcc (by decide))
    (by
      have v : (98#u8 : U8).val = 98 := rfl
      rw [v]
      simp only [Rowl.TurtleTokens.LabelFirst, Rowl.TurtleTokens.PnCharsU, Rowl.NTriples.PnBase]
      omega) tail (by omega)
  rw [spanIs] at this
  have e2 : p + 2 + (WrittenLabel b.scope.val b.label.val).length =
      p + (95#u8 :: 58#u8 :: WrittenLabel b.scope.val b.label.val).length := by simp; omega
  rw [e2] at this
  exact this


theorem occurs_drop {d : List U8} {p : Nat} {x : List U8} (h : Occurs d p x) : ∃ more, d.drop p = x ++ more := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨post, by simp⟩

theorem not_byte_is {d : List U8} {i : Nat} {b : U8} {v : Nat} (occ : Occurs d i [b]) (h : b.val ≠ v) :
    ¬ Rowl.TurtleTokens.ByteIs d i v := by
  unfold Rowl.TurtleTokens.ByteIs
  rw [occurs_byte occ]
  simpa using h

/-- A written string begins with a byte other than `"`, unless it is empty. -/
theorem string_text_head {s : List U8} {i : Nat} {word : List Nat} (valid : Rowl.Regular.Utf8From s i word) :
    StringText s i = [] ∨ ∃ c rest, StringText s i = c :: rest ∧ c.val ≠ 34 := by
  cases valid with
  | endOfInput => exact Or.inl (string_text_nil (prefix_end s))
  | @character _ cp w tail found positive bounded rest =>
    right
    rw [string_text_cons found]
    unfold StringChar
    cases letter : EscapeLetter cp with
    | some m => exact ⟨92#u8, _, rfl, by decide⟩
    | none =>
      have inside : i < s.length := by omega
      have first : Span s i (i + w) = s[i] :: Span s (i + 1) (i + w) := by
        unfold Span
        rw [List.drop_eq_getElem_cons inside, show i + w - i = (w - 1) + 1 by omega, List.take_succ_cons]
        congr 2
        omega
      refine ⟨s[i], _, by rw [first, List.cons_append], ?_⟩
      intro quote
      have small : s[i].val < 128 := by omega
      have decoded : Prefix s i = some (s[i].val, 1) := by
        rw [prefix_drop, List.drop_eq_getElem_cons inside]
        exact prefix_ascii _ _ small
      rw [found] at decoded
      obtain ⟨cpIs, -⟩ := Prod.mk.inj (Option.some.inj decoded)
      have := (escape_letter_none letter).1
      omega

theorem letter_iff (b : U8) : LetterByte b ↔ Rowl.TurtleTokens.Letter b.val := Iff.rfl

theorem letters_end_read {d : List U8} {i : Nat} {head rest more : List U8} (drop : d.drop i = head ++ rest ++ more)
    (letters : ∀ b ∈ head, LetterByte b) (stop : (rest ++ more).takeWhile (fun b => decide (Rowl.TurtleTokens.Letter b.val)) = []) :
    Rowl.TurtleTokens.LettersEnd d i = i + head.length := by
  unfold Rowl.TurtleTokens.LettersEnd
  rw [drop, List.append_assoc, (take_while_all (fun b hb => by
    simpa [LetterByte, Rowl.TurtleTokens.Letter] using letters b hb) stop).1]

theorem alnums_end_read {d : List U8} {i : Nat} {w rest : List U8} (drop : d.drop i = w ++ rest)
    (alnum : ∀ b ∈ w, AlnumByte b)
    (stop : rest.takeWhile (fun b => decide (Rowl.TurtleTokens.Letter b.val ∨ Rowl.TurtleTokens.Digit b.val)) = []) :
    Rowl.TurtleTokens.AlnumsEnd d i = i + w.length := by
  unfold Rowl.TurtleTokens.AlnumsEnd
  rw [drop, (take_while_all (fun b hb => by
    have := alnum b hb
    unfold AlnumByte LetterByte at this
    simpa [Rowl.TurtleTokens.Letter, Rowl.TurtleTokens.Digit] using this) stop).1]

theorem subtags_next {rest : List U8} (h : Subtags rest) (more : List U8) :
    ∃ c tail, rest ++ 32#u8 :: more = c :: tail ∧ (c = 32#u8 ∨ c = 45#u8) := by
  cases h with
  | nil => exact ⟨32#u8, more, rfl, Or.inl rfl⟩
  | @cons w rest _ _ _ => exact ⟨45#u8, w ++ (rest ++ 32#u8 :: more), by simp, Or.inr rfl⟩

theorem space_dash_letter {c : U8} (h : c = 32#u8 ∨ c = 45#u8) :
    ¬ Rowl.TurtleTokens.Letter c.val ∧ ¬ Rowl.TurtleTokens.Digit c.val := by
  rcases h with rfl | rfl
  · have v : (32#u8 : U8).val = 32 := rfl
    rw [v]
    simp only [Rowl.TurtleTokens.Letter, Rowl.TurtleTokens.Digit]
    omega
  · have v : (45#u8 : U8).val = 45 := rfl
    rw [v]
    simp only [Rowl.TurtleTokens.Letter, Rowl.TurtleTokens.Digit]
    omega

theorem subtags_end_read {d : List U8} {rest : List U8} (h : Subtags rest) :
    ∀ (i : Nat) (more : List U8), d.drop i = rest ++ 32#u8 :: more →
      Rowl.TurtleTokens.SubtagsEnd d i = i + rest.length := by
  induction h with
  | nil =>
    intro i more drop
    rw [Rowl.TurtleTokens.SubtagsEnd, dif_neg]
    · simp
    · rintro ⟨dash, -⟩
      have byte : d[i]? = some 32#u8 := by
        have := congrArg (·[0]?) drop
        simpa using this
      unfold Rowl.TurtleTokens.ByteIs at dash
      rw [byte] at dash
      simp at dash
  | @cons w rest' nonempty alnum tail ih =>
    intro i more drop
    obtain ⟨c, more', split, cIs⟩ := subtags_next tail more
    have dropNext : d.drop (i + 1) = w ++ (rest' ++ 32#u8 :: more) := by
      rw [drop_add, drop]
      simp
    have alnumsEnd : Rowl.TurtleTokens.AlnumsEnd d (i + 1) = i + 1 + w.length := by
      apply alnums_end_read dropNext alnum
      rw [split]
      obtain ⟨notLetter, notDigit⟩ := space_dash_letter cIs
      simp [List.takeWhile_cons, notLetter, notDigit]
    have dash : Rowl.TurtleTokens.ByteIs d i 45 := by
      have byte : d[i]? = some 45#u8 := by
        have := congrArg (·[0]?) drop
        simpa using this
      unfold Rowl.TurtleTokens.ByteIs
      rw [byte]
      rfl
    have positive : 0 < w.length := List.length_pos_iff.mpr nonempty
    rw [Rowl.TurtleTokens.SubtagsEnd, dif_pos ⟨dash, by omega⟩, alnumsEnd]
    have dropAfter : d.drop (i + 1 + w.length) = rest' ++ 32#u8 :: more := by
      rw [drop_add, dropNext, List.drop_left]
    rw [ih (i + 1 + w.length) more dropAfter]
    simp only [List.length_cons, List.length_append]
    omega

/-- A written language tag of LANGTAG's form after `@` at `p`, then a space,
    is read by Turtle as that tag. -/
theorem turtle_tag_read {d : List U8} (fits : d.length ≤ Usize.max) (t : List U8) (form : TagForm t) (valid : LanguageTag t) {p : Nat}
    (occ : Occurs d p (64#u8 :: t ++ [32#u8])) :
    Rowl.TurtleTokens.LanguageAt d Usize.max p (.ok (t, p + 1 + t.length)) := by
  obtain ⟨head, rest, whole, nonempty, letters, tail⟩ := form
  rw [List.cons_append] at occ
  obtain ⟨-, tagOcc⟩ := occurs_cons.mp occ
  have bound := occurs_bound tagOcc
  simp only [List.length_append, List.length_singleton] at bound
  have tagSpan := occurs_span (occurs_append.mp tagOcc).1
  obtain ⟨more, drop⟩ := occurs_drop tagOcc
  rw [whole] at drop
  have positive : 0 < head.length := List.length_pos_iff.mpr nonempty
  obtain ⟨c, more', split, cIs⟩ := subtags_next tail more
  have lettersEnd : Rowl.TurtleTokens.LettersEnd d (p + 1) = p + 1 + head.length := by
    apply letters_end_read (rest := rest ++ [32#u8]) (more := more) (by simpa [List.append_assoc] using drop) letters
    rw [List.append_assoc, List.singleton_append, split]
    simp [List.takeWhile_cons, (space_dash_letter cIs).1]
  have dropRest : d.drop (p + 1 + head.length) = rest ++ 32#u8 :: more := by
    rw [drop_add, drop]
    simp
  have subtagsEnd := subtags_end_read tail (p + 1 + head.length) more dropRest
  have tLength : t.length = head.length + rest.length := by rw [whole, List.length_append]
  have := Rowl.TurtleTokens.LanguageAt.tag (bs := d) (limit := Usize.max) (start := p) (e := p + 1 + t.length)
    (by rw [lettersEnd]; omega) (by rw [lettersEnd, subtagsEnd]; omega) (by omega) (by rw [tagSpan]; exact valid)
  rw [tagSpan] at this
  exact this


theorem string_token_read {d : List U8} (fits : d.length ≤ Usize.max) {s : List U8} (valid : Utf8 s) {p : Nat}
    (occ : Occurs d p (34#u8 :: (StringText s 0 ++ [34#u8]))) (start stop : Usize) (hs : start.val = p)
    (hq : stop.val = p + (StringText s 0).length + 2) : Rowl.NTriples.QuotedToken d start false s stop := by
  obtain ⟨word, text⟩ := valid
  obtain ⟨openOcc, bodyOcc⟩ := occurs_cons.mp occ
  have bound := occurs_bound bodyOcc
  simp only [List.length_append, List.length_singleton] at bound
  obtain ⟨next, hn⟩ := usize_of (n := p + 1) (by omega)
  refine ⟨next, ?_, ?_⟩
  · rw [hs]
    exact occurs_unit_ascii openOcc (by decide) rfl hn
  · have := string_body_read fits text bodyOcc next stop hn (by omega)
    simpa using this

/-- A literal without faults written at `p`, then a space, is read by Turtle as
    itself, with the prefixes and against the bases there may be. -/
theorem turtle_literal_read {d : List U8} (fits : d.length ≤ Usize.max) (l : rdf.RdfLiteral)
    (ok : LiteralFault true l = none) {base : List U8} (short : base.length < Usize.max / 8)
    (prefixes : List (List U8 × List U8)) {p : Nat} (occ : Occurs d p (LiteralText l ++ [32#u8])) :
    Rowl.TurtleTokens.LiteralAt d base prefixes Usize.max p
      (.ok (Rowl.TurtleTokens.literalTerm l, p + (LiteralText l).length)) := by
  obtain ⟨⟨word, text⟩, dataOk, langOk⟩ := literal_fault_none ok
  have wholeBound := occurs_bound occ
  unfold LiteralText at occ wholeBound
  simp only [List.cons_append, List.append_assoc] at occ
  simp only [List.length_append, List.length_cons, List.length_nil] at wholeBound
  obtain ⟨openOcc, afterOpen⟩ := occurs_cons.mp occ
  have body := occurs_word afterOpen rfl
  obtain ⟨-, kindOcc'⟩ := occurs_append.mp afterOpen
  have closeOcc := (occurs_cons.mp kindOcc').1
  obtain ⟨-, kindOcc⟩ := occurs_cons.mp kindOcc'
  have lexBound := string_text_length text
  obtain ⟨start, hs⟩ := usize_of (n := p) (by omega)
  obtain ⟨ending, he⟩ := usize_of (n := p + (StringText l.lexical.val 0).length + 2) (by omega)
  have quoted := string_token_read fits ⟨word, text⟩ (occurs_cons.mpr ⟨openOcc, body⟩) start ending hs he
  -- the first byte of the kind
  obtain ⟨k0, krest, kIs, kFirst⟩ : ∃ c rest, KindText l.kind ++ [32#u8] = c :: rest ∧ (c = 94#u8 ∨ c = 64#u8) := by
    cases l.kind with
    | Datatype dt => exact ⟨_, _, rfl, Or.inl rfl⟩
    | Language t => exact ⟨_, _, rfl, Or.inr rfl⟩
  have kindHead : Occurs d (p + 1 + (StringText l.lexical.val 0).length + 1) [k0] := by
    rw [kIs] at kindOcc
    exact (occurs_cons.mp kindOcc).1
  have notTriple : ¬ Rowl.TurtleTokens.TripleQuote d p 34 := by
    rcases string_text_head text with empty | ⟨c, rest, cIs, cNot⟩
    · rw [empty] at closeOcc kindHead
      simp only [List.length_nil, Nat.add_zero] at closeOcc kindHead
      intro h
      apply not_byte_is kindHead ?_ h.2.2
      rcases kFirst with rfl | rfl <;> decide
    · rw [cIs] at body
      have second := (occurs_cons.mp body).1
      exact fun h => not_byte_is second cNot h.2.1
  have stringAt : Rowl.TurtleTokens.StringAt d Usize.max p (.ok (l.lexical.val, ending.val)) :=
    .double notTriple (fun h => not_byte_is openOcc (by decide) h.1) (occurs_byte_is openOcc)
      ⟨start, ending, hs, rfl, quoted⟩ (by omega)
  rw [he] at stringAt
  have eAt : p + (StringText l.lexical.val 0).length + 2 = p + 1 + (StringText l.lexical.val 0).length + 1 := by omega
  rw [← eAt] at kindOcc kindHead
  have trivia : Rowl.NTriples.TriviaRuns d true (p + (StringText l.lexical.val 0).length + 2)
      (p + (StringText l.lexical.val 0).length + 2) := by
    rcases kFirst with rfl | rfl
    · exact trivia_stops fits kindHead (by decide) true (not_spacing true (by decide)) (by decide)
    · exact trivia_stops fits kindHead (by decide) true (not_spacing true (by decide)) (by decide)
  unfold Rowl.TurtleTokens.literalTerm
  cases hk : l.kind with
  | Datatype dt =>
    obtain ⟨lang, iriOk⟩ := dataOk dt hk
    rw [hk] at kindOcc wholeBound
    simp only [KindText, List.cons_append] at kindOcc
    simp only [KindText, List.length_cons] at wholeBound
    obtain ⟨caret1, afterCaret1⟩ := occurs_cons.mp kindOcc
    obtain ⟨caret2, iriOcc⟩ := occurs_cons.mp afterCaret1
    have iriOnly := (occurs_append.mp iriOcc).1
    have iriFirst : Occurs d (p + (StringText l.lexical.val 0).length + 2 + 1 + 1) [60#u8] := by
      unfold IriToken at iriOnly
      exact (occurs_cons.mp (by simpa [List.cons_append] using iriOnly)).1
    have iriRef := turtle_iri_read fits iriOk short iriOnly
    have target : p + (LiteralText l).length =
        p + (StringText l.lexical.val 0).length + 2 + 1 + 1 + (IriToken dt.spelling.val).length := by
      simp [LiteralText, KindText, hk]
      omega
    rw [target]
    exact .literal stringAt (.datatype trivia (not_byte_is caret1 (by decide)) (occurs_byte_is caret1)
      (.datatype (occurs_byte_is caret2)
        (trivia_stops fits iriFirst (by decide) true (not_spacing true (by decide)) (by decide))
        (.ref (occurs_byte_is iriFirst) iriRef) lang))
  | Language t =>
    obtain ⟨form, valid⟩ := langOk t hk
    rw [hk] at kindOcc wholeBound
    simp only [KindText] at kindOcc
    have tag := turtle_tag_read fits t.val form valid kindOcc
    have target : p + (LiteralText l).length = p + (StringText l.lexical.val 0).length + 2 + 1 + t.val.length := by
      simp [LiteralText, KindText, hk]
      omega
    rw [target]
    exact .literal stringAt
      (.language trivia (occurs_byte_is (occurs_cons.mp (by simpa [List.cons_append] using kindOcc)).1) tag)


/-! ## Reading written Turtle -/

theorem start_iri : Rowl.TurtleTokens.StartOf (60#u8 : U8).val = .Iri := by
  have v : (60#u8 : U8).val = 60 := rfl
  rw [v]
  simp [Rowl.TurtleTokens.StartOf]
theorem start_blank : Rowl.TurtleTokens.StartOf (95#u8 : U8).val = .Blank := by
  have v : (95#u8 : U8).val = 95 := rfl
  rw [v]
  simp [Rowl.TurtleTokens.StartOf]
theorem start_quote : Rowl.TurtleTokens.StartOf (34#u8 : U8).val = .Quote := by
  have v : (34#u8 : U8).val = 34 := rfl
  rw [v]
  simp [Rowl.TurtleTokens.StartOf, Rowl.TurtleTokens.QuoteChar]

/-- The subject of a written triple in Turtle. -/
theorem turtle_subject_read {d : List U8} (fits : d.length ≤ Usize.max) (c : Rowl.Turtle.Context)
    (hb : c.bs = d) (hl : c.termLimit = Usize.max) (short : c.base.length < Usize.max / 8) (s : rdf.Subject)
    (ok : SubjectFault true s = none) {p : Nat} (count : Nat) (occ : Occurs d p (SubjectText s ++ [32#u8])) :
    Rowl.Turtle.SubjectAt c p count
      (.ok (renameTerm c.scope (Rowl.TurtleTokens.subjectTerm s), p + (SubjectText s).length, [])) := by
  subst hb
  cases s with
  | Iri v =>
    have iriOcc := (occurs_append.mp occ).1
    have first : Occurs c.bs p [60#u8] := by
      simp only [SubjectText, IriToken, List.cons_append] at iriOcc
      exact (occurs_cons.mp iriOcc).1
    have := turtle_iri_read fits ok short iriOcc
    rw [← hl] at this
    exact .iri (occurs_turtle_ascii first (by decide)) start_iri this
  | Blank b =>
    have first : Occurs c.bs p [95#u8] := by
      simp only [SubjectText, BlankText, List.cons_append] at occ
      exact (occurs_cons.mp occ).1
    have := turtle_blank_read fits c.scope b occ
    rw [← hl] at this
    exact .blank (occurs_turtle_ascii first (by decide)) start_blank this

/-- The object of a written triple in Turtle. -/
theorem turtle_node_read {d : List U8} (fits : d.length ≤ Usize.max) (c : Rowl.Turtle.Context)
    (hb : c.bs = d) (hl : c.termLimit = Usize.max) (short : c.base.length < Usize.max / 8) (o : rdf.Object)
    (ok : ObjectFault true o = none) {p : Nat} (count : Nat) (occ : Occurs d p (ObjectText o ++ [32#u8])) :
    Rowl.Turtle.NodeAt c p count
      (.ok (renameTerm c.scope (Rowl.TurtleTokens.objectTerm o), p + (ObjectText o).length, [])) := by
  subst hb
  cases o with
  | Iri v =>
    have iriOcc := (occurs_append.mp occ).1
    have first : Occurs c.bs p [60#u8] := by
      simp only [ObjectText, IriToken, List.cons_append] at iriOcc
      exact (occurs_cons.mp iriOcc).1
    have := turtle_iri_read fits ok short iriOcc
    rw [← hl] at this
    refine .term (occurs_turtle_ascii first (by decide)) (by rw [start_iri]; simp) (by rw [start_iri]; simp) ?_
    rw [start_iri]
    exact .iri this
  | Blank b =>
    have first : Occurs c.bs p [95#u8] := by
      simp only [ObjectText, BlankText, List.cons_append] at occ
      exact (occurs_cons.mp occ).1
    have := turtle_blank_read fits c.scope b occ
    rw [← hl] at this
    refine .term (occurs_turtle_ascii first (by decide)) (by rw [start_blank]; simp) (by rw [start_blank]; simp) ?_
    rw [start_blank]
    exact .blank this
  | Literal l =>
    have first : Occurs c.bs p [34#u8] := by
      simp only [ObjectText, LiteralText, List.cons_append] at occ
      exact (occurs_cons.mp occ).1
    have := turtle_literal_read fits l ok short c.prefixes occ
    rw [← hl] at this
    have term : renameTerm c.scope (Rowl.TurtleTokens.objectTerm (.Literal l)) = Rowl.TurtleTokens.literalTerm l := by
      cases hk : l.kind <;> simp [Rowl.TurtleTokens.objectTerm, Rowl.TurtleTokens.literalTerm, renameTerm, hk]
    rw [term]
    refine .term (occurs_turtle_ascii first (by decide)) (by rw [start_quote]; simp) (by rw [start_quote]; simp) ?_
    rw [start_quote]
    exact .literal this

theorem opening_triples {d : List U8} {p : Nat} {sc : U8} (first : Occurs d p [sc]) (h : sc = 60#u8 ∨ sc = 95#u8) :
    Rowl.Turtle.OpeningAt d p (.ok .triples) := by
  have v : sc.val = 60 ∨ sc.val = 95 := by rcases h with rfl | rfl <;> decide
  refine .triples (fun k => not_byte_is first (by omega) k.1) (fun k => not_byte_is first (by omega) k.1) ?_ ?_
  · intro k
    simp only [Rowl.Turtle.PrefixUpper, Rowl.TurtleTokens.AnyCase] at k
    rcases k.1 with k | k
    · exact not_byte_is first (by omega) k
    · exact not_byte_is first (by omega) k
  · intro k
    simp only [Rowl.Turtle.BaseUpper, Rowl.TurtleTokens.AnyCase] at k
    rcases k.1 with k | k
    · exact not_byte_is first (by omega) k
    · exact not_byte_is first (by omega) k

/-- A triple without faults written on a line at `p` is a Turtle statement
    that denotes the triple with its blank nodes renamed, up to the line feed. -/
theorem turtle_line_read {d : List U8} (fits : d.length ≤ Usize.max) (scope : List U8) (e : Rowl.Turtle.Env)
    (short : e.base.length < Usize.max / 8) (t : rdf.Triple) (ok : TripleFault true t = none) {p : Nat}
    (count : Nat) (room : count < Usize.max) (occ : Occurs d p (LineText t)) :
    Rowl.Turtle.StatementAt ⟨d, scope, Usize.max, Usize.max⟩ e p count
      (.ok (p + (TripleText t).length + 2, e, [RenameSpo scope (Rowl.Turtle.spo t)])) := by
  obtain ⟨subjectOk, predicateOk, objectOk⟩ := triple_fault_none ok
  have bound := occurs_bound occ
  unfold LineText TripleText at occ bound
  simp only [List.append_assoc, List.cons_append, List.length_append, List.length_cons, List.length_nil] at occ bound
  let c : Rowl.Turtle.Context := Rowl.Turtle.Doc.at ⟨d, scope, Usize.max, Usize.max⟩ e
  have cb : c.bs = d := rfl
  have cl : c.termLimit = Usize.max := rfl
  have cs : c.scope = scope := rfl
  have ct : c.tripleLimit = Usize.max := rfl
  -- the subject
  have subjectAt := turtle_subject_read fits c cb cl short t.subject subjectOk count (occurs_word occ rfl)
  rw [cs] at subjectAt
  obtain ⟨-, afterSubject⟩ := occurs_append.mp occ
  generalize hp1 : p + (SubjectText t.subject).length = p1 at afterSubject subjectAt
  -- the predicate
  obtain ⟨spaceOcc1, predicatePart⟩ := occurs_cons.mp afterSubject
  have predicateOnly := (occurs_append.mp predicatePart).1
  have iriFirst : Occurs d (p1 + 1) [60#u8] := by
    unfold IriToken at predicateOnly
    exact (occurs_cons.mp (by simpa [List.cons_append] using predicateOnly)).1
  have predicateRef := turtle_iri_read fits predicateOk short predicateOnly
  have verb : Rowl.Turtle.VerbAt c p1
      (.ok (t.predicate.spelling.val, p1 + 1 + (IriToken t.predicate.spelling.val).length)) :=
    .iri (space_trivia fits (occurs_cons.mpr ⟨spaceOcc1, by
        unfold IriToken at predicatePart
        simpa [List.cons_append] using predicatePart⟩) (Or.inl rfl) true)
      (occurs_turtle_ascii iriFirst (by decide)) predicateRef
  obtain ⟨-, afterPredicate⟩ := occurs_append.mp predicatePart
  generalize hp3 : p1 + 1 + (IriToken t.predicate.spelling.val).length = p3 at afterPredicate verb
  -- the object
  obtain ⟨spaceOcc2, objectPart⟩ := occurs_cons.mp afterPredicate
  obtain ⟨oc, orest, oIs, oFirst⟩ := object_text_first t.object
  have node := turtle_node_read fits c cb cl short t.object objectOk count (occurs_word objectPart rfl)
  rw [cs] at node
  have objectAt : Rowl.Turtle.ObjectAt c (renameTerm scope (Rowl.TurtleTokens.subjectTerm t.subject))
      t.predicate.spelling.val p3 count
      (.ok (p3 + 1 + (ObjectText t.object).length, [] ++
        [⟨renameTerm scope (Rowl.TurtleTokens.subjectTerm t.subject), t.predicate.spelling.val,
          renameTerm scope (Rowl.TurtleTokens.objectTerm t.object)⟩])) := by
    have objectOnly := (occurs_append.mp objectPart).1
    rw [oIs] at objectOnly
    exact .object (space_trivia fits (occurs_cons.mpr ⟨spaceOcc2, objectOnly⟩) oFirst true)
      node (by rw [ct]; simpa using room)
  obtain ⟨-, afterObject⟩ := occurs_append.mp objectPart
  generalize hp5 : p3 + 1 + (ObjectText t.object).length = p5 at afterObject objectAt
  obtain ⟨spaceOcc3, afterSpace⟩ := occurs_cons.mp afterObject
  have periodOcc := (occurs_cons.mp afterSpace).1
  have periodTrivia : Rowl.NTriples.TriviaRuns d true (p5 + 1) (p5 + 1) :=
    trivia_stops fits periodOcc (by decide) true (not_spacing true (by decide)) (by decide)
  have moreObjects : Rowl.Turtle.MoreObjectsAt c (renameTerm scope (Rowl.TurtleTokens.subjectTerm t.subject))
      t.predicate.spelling.val p5 (count + ([] ++ [(⟨renameTerm scope (Rowl.TurtleTokens.subjectTerm t.subject),
        t.predicate.spelling.val, renameTerm scope (Rowl.TurtleTokens.objectTerm t.object)⟩ : Rowl.Turtle.Spo)]).length)
      (.ok (p5 + 1, [])) :=
    .finish (trivia_space fits (occurs_cons.mpr ⟨spaceOcc3, periodOcc⟩) (by decide) true
      (not_spacing true (by decide)) (by decide)) (not_byte_is periodOcc (by decide))
  have objects := Rowl.Turtle.ObjectsAt.list objectAt moreObjects
  have morePredicates : Rowl.Turtle.MorePredicatesAt c (renameTerm scope (Rowl.TurtleTokens.subjectTerm t.subject))
      (p5 + 1) (count + (([] ++ [(⟨renameTerm scope (Rowl.TurtleTokens.subjectTerm t.subject),
        t.predicate.spelling.val, renameTerm scope (Rowl.TurtleTokens.objectTerm t.object)⟩ : Rowl.Turtle.Spo)]) ++
        []).length) (.ok (p5 + 1, [])) :=
    .finish periodTrivia (not_byte_is periodOcc (by decide))
  have list := Rowl.Turtle.ListAt.list (position := p1) (count := count + ([] : List Rowl.Turtle.Spo).length)
    verb (by simpa using objects) (by simpa using morePredicates)
  obtain ⟨sc, srest, sIs, sFirst⟩ := subject_text_first t.subject
  have firstOcc : Occurs d p [sc] := by
    rw [sIs] at occ
    exact (occurs_cons.mp (by simpa [List.cons_append] using occ)).1
  have triples := Rowl.Turtle.TriplesAt.subject (c := c) (start := p) (count := count)
    (not_byte_is firstOcc (by rcases sFirst with rfl | rfl <;> decide)) subjectAt list
  have statement := Rowl.Turtle.StatementAt.triples (d := ⟨d, scope, Usize.max, Usize.max⟩) (e := e)
    (opening_triples firstOcc sFirst) triples (.period periodTrivia (occurs_byte_is periodOcc))
  have position : p5 + 1 + 1 = p + (TripleText t).length + 2 := by
    simp only [TripleText, List.length_append, List.length_cons]
    omega
  rw [position] at statement
  simpa [RenameSpo, Rowl.Turtle.spo] using statement


theorem iri_fault_weaken {s : List U8} (h : IriFault true s = none) : IriFault false s = none := by
  obtain ⟨absolute, -⟩ := iri_fault_none h
  unfold IriFault
  simp [absolute]

theorem literal_fault_weaken {l : rdf.RdfLiteral} (h : LiteralFault true l = none) : LiteralFault false l = none := by
  obtain ⟨utf8, dataOk, langOk⟩ := literal_fault_none h
  unfold LiteralFault
  rw [if_neg (not_not.mpr utf8)]
  cases hk : l.kind with
  | Datatype dt =>
    obtain ⟨lang, iriOk⟩ := dataOk dt hk
    simp only
    rw [if_neg lang]
    exact iri_fault_weaken iriOk
  | Language t =>
    obtain ⟨form, valid⟩ := langOk t hk
    simp only
    rw [if_pos ⟨form, valid⟩]

/-- A triple Turtle can be written with can be written in N-Triples. -/
theorem triple_fault_weaken {t : rdf.Triple} (h : TripleFault true t = none) : TripleFault false t = none := by
  obtain ⟨s, p, o⟩ := triple_fault_none h
  have s' : SubjectFault false t.subject = none := by
    cases hs : t.subject with
    | Iri v =>
      rw [hs] at s
      exact iri_fault_weaken s
    | Blank b => rfl
  have o' : ObjectFault false t.object = none := by
    cases ho : t.object with
    | Iri v =>
      rw [ho] at o
      exact iri_fault_weaken o
    | Blank b => rfl
    | Literal l =>
      rw [ho] at o
      exact literal_fault_weaken o
  unfold TripleFault
  rw [s', iri_fault_weaken p, o']
  rfl

/-- The lines of triples without faults written from `p` to the end are, after
    the white space from `q`, the Turtle statements that denote those triples
    with their blank nodes renamed. -/
theorem turtle_lines_read {d : List U8} (fits : d.length ≤ Usize.max) (scope base : List U8)
    (short : base.length < Usize.max / 8) :
    ∀ (ts : List rdf.Triple), (∀ t ∈ ts, TripleFault true t = none) → ∀ (q p count : Nat),
      Rowl.NTriples.TriviaRuns d true q p → Occurs d p (LinesText ts) → p + (LinesText ts).length = d.length →
      count ≤ p →
      Rowl.Turtle.StatementsAt ⟨d, scope, Usize.max, Usize.max⟩ ⟨base, []⟩ q count
        (.ok (ts.map (fun t => RenameSpo scope (Rowl.Turtle.spo t))))
  | [], _, q, p, count, trivia, _, ends, _ => by
    simp only [LinesText, List.length_nil, Nat.add_zero] at ends
    rw [ends] at trivia
    exact .finish trivia
  | t :: ts, ok, q, p, count, trivia, occ, ends, counted => by
    simp only [LinesText] at occ ends
    rw [List.length_append] at ends
    obtain ⟨lineOcc, restOcc⟩ := occurs_append.mp occ
    have lineLength := line_text_length t
    have statement := turtle_line_read fits scope ⟨base, []⟩ short t (ok t (by simp)) count (by omega) lineOcc
    have feed : Occurs d (p + (TripleText t).length + 2) [10#u8] := by
      unfold LineText at lineOcc
      obtain ⟨-, endOcc⟩ := occurs_append.mp lineOcc
      obtain ⟨-, more⟩ := occurs_cons.mp endOcc
      obtain ⟨-, feedOcc⟩ := occurs_cons.mp more
      rw [show p + (TripleText t).length + 2 = p + (TripleText t).length + 1 + 1 by omega]
      exact feedOcc
    obtain ⟨next, hn⟩ := usize_of (n := p + (LineText t).length) (by omega)
    have unit : UnitAt d (p + (TripleText t).length + 2) 10#u32 next :=
      occurs_unit_ascii feed (by decide) rfl (by omega)
    have nextTrivia : Rowl.NTriples.TriviaRuns d true (p + (TripleText t).length + 2) (p + (LineText t).length) := by
      have start := lines_start fits restOcc (by omega)
      rw [← hn] at start ⊢
      exact .space unit (by right; exact ⟨rfl, Or.inl rfl⟩) start
    have rest := turtle_lines_read fits scope base short ts (fun u hu => ok u (by simp [hu]))
      (p + (TripleText t).length + 2) (p + (LineText t).length) (count + 1) nextTrivia restOcc (by omega) (by omega)
    have := Rowl.Turtle.StatementsAt.more trivia (by simp; omega) statement rest
    simpa using this

/-- The Turtle writer is exact: the bytes `turtle::write` returns are read back
    by `turtle::read`, in any blank node scope `scope` and against any base IRI
    shorter than `usize::MAX / 8` bytes, as the graph's triples in order, each
    blank node of the scope `s` and the label `l` becoming the blank node of
    `scope` with the label `WrittenLabel s l` (one to one by
    `written_label_injective`). -/
theorem turtle_write_read (graph : rdf.RawGraph) (limit : Usize) (bytes scope base : alloc.vec.Vec U8)
    (written : turtle.write graph limit = .ok (.Bytes bytes)) (short : base.val.length < Usize.max / 8) :
    ∃ read, turtle.read bytes scope base = .ok (.Graph read) ∧
      read.triples.val.map Rowl.Turtle.spo =
        graph.triples.val.map (fun t => RenameSpo scope.val (Rowl.Turtle.spo t)) := by
  obtain ⟨r, run, correct⟩ := write_graph_total_correct graph true limit
  unfold turtle.write at written
  have same : r = .Bytes bytes := Result.ok_injective (run.symm.trans written)
  subst same
  obtain ⟨fault, contents, -⟩ := correct
  have ok := graph_fault_triples fault
  have fits : bytes.val.length ≤ Usize.max := bytes.property
  have occ : Occurs bytes.val 0 (LinesText graph.triples.val) := ⟨[], [], by simp [contents], rfl⟩
  have ends : 0 + (LinesText graph.triples.val).length = bytes.val.length := by simp [contents]
  obtain ⟨ts', spoIs, -⟩ := lines_read fits scope graph.triples.val (fun t m => triple_fault_weaken (ok t m))
    0 0 0#usize rfl occ ends (le_refl 0)
  have count : ts'.length ≤ Usize.max := by
    have := congrArg List.length spoIs
    simp only [List.length_map] at this
    have := graph.triples.property
    omega
  refine ⟨⟨alloc.vec.Vec.from ts' count⟩, ?_, by simpa using spoIs⟩
  apply (Rowl.Turtle.read_accepted_iff bytes scope base _).mpr
  simp only [alloc.vec.Vec.from_val]
  rw [spoIs]
  exact turtle_lines_read fits scope.val base.val short graph.triples.val ok 0 0 0 (lines_start fits occ ends) occ
    ends (le_refl 0)


/-! ## The terms the N-Triples reader returns can be written -/

/-- UTF-8 after other bytes. -/
theorem utf8_from_shift {l : List U8} {i : Nat} {w : List Nat} (valid : Rowl.Regular.Utf8From l i w) (pre : List U8) :
    Rowl.Regular.Utf8From (pre ++ l) (pre.length + i) w := by
  induction valid with
  | endOfInput =>
    have := Rowl.Regular.Utf8From.endOfInput (bs := pre ++ l)
    simpa using this
  | @character offset cp width tail found positive bounded rest ih =>
    refine .character (by rw [prefix_append_left]; exact found) positive (by simp; omega) ?_
    rw [Nat.add_assoc]
    exact ih

/-- The characters a quoted token denotes are UTF-8. -/
theorem quoted_body_utf8 {bs : List U8} {iri : Bool} {start stop : Usize} {word : List U8}
    (body : QuotedBody bs iri start word stop) : Utf8 word := by
  induction body with
  | close _ => exact ⟨[], .endOfInput⟩
  | @item start cp next value finish encoded word stop unit notClosing item encodes rest ih =>
    obtain ⟨chars, tail⟩ := ih
    have run := (Rowl.Encoding.encode_some_iff value encoded).mpr encodes
    have decoded := Rowl.Encoding.encode_prefix_inverse value encoded run
    have nonempty : 0 < (Rowl.Encoding.Bytes encoded).length := by cases encoded <;> simp [Rowl.Encoding.Bytes]
    refine ⟨value.val :: chars, .character (prefix_append_right word decoded) nonempty (by simp) ?_⟩
    have := utf8_from_shift tail (Rowl.Encoding.Bytes encoded)
    simpa using this

/-- A decoded ASCII character is one byte. -/
theorem prefix_small {bs : List U8} {i cp w : Nat} (h : Prefix bs i = some (cp, w)) (small : cp < 128) :
    w = 1 ∧ bs[i]? = some (byte cp) := by
  have one := ascii_width h small
  subst one
  refine ⟨rfl, ?_⟩
  obtain ⟨-, e, encodes, bytes⟩ := prefix_character h
  have bounds := prefix_bounds h
  cases e with
  | One a =>
    simp only [Rowl.Encoding.EncodeCorrect] at encodes
    unfold Span at bytes
    simp only [Rowl.Encoding.Bytes, Nat.add_sub_cancel_left] at bytes
    rw [List.drop_eq_getElem_cons bounds.1] at bytes
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at bytes
    rw [List.getElem?_eq_getElem bounds.1, ← bytes]
    congr 1
    apply UScalar.eq_of_val_eq
    rw [byte_val (by omega)]
    exact encodes.2
  | Two a b =>
    have := congrArg List.length bytes
    rw [span_length h] at this
    simp [Rowl.Encoding.Bytes] at this
  | Three a b c =>
    have := congrArg List.length bytes
    rw [span_length h] at this
    simp [Rowl.Encoding.Bytes] at this
  | Four a b c e =>
    have := congrArg List.length bytes
    rw [span_length h] at this
    simp [Rowl.Encoding.Bytes] at this

theorem span_cons {bs : List U8} {a b : Nat} {x : U8} (h : bs[a]? = some x) (le : a < b) :
    Span bs a b = x :: Span bs (a + 1) b := by
  unfold Span
  have inside := (List.getElem?_eq_some_iff.mp h).1
  rw [List.drop_eq_getElem_cons inside, show b - a = (b - (a + 1)) + 1 by omega, List.take_succ_cons]
  rw [(List.getElem?_eq_some_iff.mp h).2]

theorem span_empty (bs : List U8) (a : Nat) : Span bs a a = [] := by
  simp [Span]

theorem span_append {bs : List U8} {a b c : Nat} (ab : a ≤ b) (bc : b ≤ c) :
    Span bs a b ++ Span bs b c = Span bs a c := by
  unfold Span
  rw [show c - a = (b - a) + (c - b) by omega, List.take_add, ← drop_add, show a + (b - a) = b by omega]

theorem tag_character_small {letters : Bool} {cp : Nat} (h : Rowl.NTriples.TagCharacter letters cp) :
    cp < 128 ∧ AlnumByte (byte cp) ∧ (letters = true → LetterByte (byte cp)) := by
  simp only [Rowl.NTriples.TagCharacter, Rowl.NTriples.AsciiAlpha, Rowl.NTriples.AsciiDigit] at h
  have small : cp < 128 := by omega
  have v := byte_val (n := cp) (by omega)
  unfold AlnumByte LetterByte
  rw [v]
  refine ⟨small, by omega, ?_⟩
  intro isLetters
  subst isLetters
  simp at h
  omega

/-- The bytes of a tag word. -/
theorem tag_word_bytes {bs : List U8} {letters : Bool} {start finish : Usize}
    (word : Rowl.NTriples.TagWord bs letters start finish) :
    start.val ≤ finish.val ∧ finish.val ≤ bs.length ∧
      ∀ b ∈ Span bs start.val finish.val, AlnumByte b ∧ (letters = true → LetterByte b) := by
  induction word with
  | eof atEnd => exact ⟨le_refl _, by omega, by simp [span_empty]⟩
  | stop unit _ => exact ⟨le_refl _, by have := unit.2.1; have := unit.1; omega, by simp [span_empty]⟩
  | @character position cp next finish unit tag rest ih =>
    obtain ⟨le, inside, all⟩ := ih
    obtain ⟨small, alnum, letter⟩ := tag_character_small tag
    obtain ⟨one, byteIs⟩ := prefix_small unit.2.2 small
    have advance : next.val = position.val + 1 := by have := unit.1; omega
    refine ⟨by omega, inside, ?_⟩
    rw [span_cons byteIs (by omega), ← advance]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | later
    · exact ⟨alnum, letter⟩
    · exact all b later

theorem byte_45 : byte (45#u32 : U32).val = 45#u8 := by
  apply UScalar.eq_of_val_eq
  rw [byte_val (by decide)]
  rfl

/-- The subtags after a tag's first word. -/
theorem tag_suffix_subtags {bs : List U8} {start stop : Usize} (suffix : Rowl.NTriples.TagSuffix bs start stop) :
    start.val ≤ stop.val ∧ stop.val ≤ bs.length ∧ Subtags (Span bs start.val stop.val) := by
  induction suffix with
  | eof atEnd => exact ⟨le_refl _, by omega, by rw [span_empty]; exact .nil⟩
  | stop unit _ => exact ⟨le_refl _, by have := unit.2.1; have := unit.1; omega, by rw [span_empty]; exact .nil⟩
  | @subtag position next middle stop dash word different rest ih =>
    obtain ⟨le2, inside2, sub⟩ := ih
    obtain ⟨le1, inside1, all⟩ := tag_word_bytes word
    obtain ⟨one, byteIs⟩ := prefix_small dash.2.2 (by decide)
    rw [byte_45] at byteIs
    have advance : next.val = position.val + 1 := by have := dash.1; omega
    have longer : next.val < middle.val := by
      have : next.val ≠ middle.val := fun h => different (UScalar.eq_of_val_eq h)
      omega
    have nonempty : Span bs next.val middle.val ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [Span] at this
      omega
    refine ⟨by omega, inside2, ?_⟩
    rw [span_cons byteIs (by omega), ← advance, ← span_append le1 le2]
    exact .cons nonempty (fun b hb => (all b hb).1) sub

/-- The tags the N-Triples reader returns have LANGTAG's form. -/
theorem tag_token_form {bs : List U8} {start stop : Usize} {limit : Nat} {value : alloc.vec.Vec U8}
    (token : Rowl.NTriples.TagToken bs start limit value stop) : TagForm value.val ∧ LanguageTag value.val := by
  obtain ⟨begin, head, _, word, different, suffix, ⟨_, copied⟩, valid⟩ := token
  obtain ⟨le1, inside1, letters⟩ := tag_word_bytes word
  obtain ⟨le2, inside2, sub⟩ := tag_suffix_subtags suffix
  have longer : begin.val < head.val := by
    have : begin.val ≠ head.val := fun h => different (UScalar.eq_of_val_eq h)
    omega
  refine ⟨⟨Span bs begin.val head.val, Span bs head.val stop.val, ?_, ?_, fun b hb => (letters b hb).2 rfl, sub⟩, valid⟩
  · rw [copied, span_append le1 le2]
    rfl
  · intro h
    have := congrArg List.length h
    simp [Span] at this
    omega

/-! ### xsd:string is an absolute IRI -/

theorem ascii_utf8 : ∀ (l : List U8), (∀ b ∈ l, b.val < 128) → Rowl.Regular.Utf8From l 0 (l.map (·.val))
  | [], _ => .endOfInput
  | b :: l, small => by
    have tail := utf8_from_shift (ascii_utf8 l (fun c hc => small c (by simp [hc]))) [b]
    exact .character (prefix_ascii b l (small b (by simp))) (by omega) (by simp) (by simpa using tail)

/-- Characters an IRI may hold anywhere: ALPHA, DIGIT, `-`, `.`, `_` and `~`. -/
def UnreservedChar (c : Nat) : Prop :=
  (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 45 ∨ c = 46 ∨ c = 95 ∨ c = 126

theorem star_of_all {l : Language Nat} : ∀ {w : List Nat}, (∀ c ∈ w, [c] ∈ l) → w ∈ l∗
  | [], _ => Language.mem_kstar.mpr ⟨[], rfl, by simp⟩
  | c :: w, h => by
    obtain ⟨chunks, eq, good⟩ := Language.mem_kstar.mp (star_of_all (w := w) (fun d hd => h d (by simp [hd])))
    exact Language.mem_kstar.mpr ⟨[c] :: chunks, by simp [eq], by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | later
      · exact h c (by simp)
      · exact good y later⟩

theorem unreserved_mem {c : Nat} (h : UnreservedChar c) : [c] ∈ Rowl.Iri.Unreserved := by
  unfold UnreservedChar at h
  unfold Rowl.Iri.Unreserved Rowl.Iri.Alpha Rowl.Iri.Digit Rowl.Iri.Ch Rowl.Iri.Range
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (Or.inl ⟨c, rfl, h.1, h.2⟩)
  · exact Or.inl (Or.inr ⟨c, rfl, h.1, h.2⟩)
  · exact Or.inr (Or.inl ⟨c, rfl, h.1, h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, rfl, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl, by omega, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rfl, by omega, by omega⟩))))

theorem ch_mem (c : Nat) : [c] ∈ Rowl.Iri.Ch c := by
  unfold Rowl.Iri.Ch Rowl.Iri.Range
  exact ⟨c, rfl, le_refl _, le_refl _⟩

theorem ipchar_mem {c : Nat} (h : UnreservedChar c) : [c] ∈ Rowl.Iri.Ipchar :=
  Or.inl (Or.inl (unreserved_mem h))

/-- An IRI `scheme://host/segment…/segment#fragment` whose characters are
    unreserved, with a scheme of letters. -/
theorem simple_iri {a : Nat} {scheme host frag : List Nat} {segments : List (List Nat)}
    (ha : (65 ≤ a ∧ a ≤ 90) ∨ (97 ≤ a ∧ a ≤ 122)) (hs : ∀ c ∈ scheme, (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122))
    (hh : ∀ c ∈ host, UnreservedChar c) (hseg : ∀ seg ∈ segments, ∀ c ∈ seg, UnreservedChar c)
    (hf : ∀ c ∈ frag, UnreservedChar c) :
    (a :: scheme) ++ [58] ++ ([47, 47] ++ (host ++ (segments.map (47 :: ·)).flatten) ++ (35 :: frag)) ∈
      Rowl.Iri.IriLanguage := by
  unfold Rowl.Iri.IriLanguage
  rw [List.append_assoc]
  apply Language.append_mem_mul
  · -- the scheme
    show [a] ++ scheme ∈ _
    apply Language.append_mem_mul
    · unfold Rowl.Iri.Alpha Rowl.Iri.Range
      rcases ha with h | h
      · exact Or.inl ⟨a, rfl, h.1, h.2⟩
      · exact Or.inr ⟨a, rfl, h.1, h.2⟩
    · apply star_of_all
      intro c hc
      unfold Rowl.Iri.Alpha Rowl.Iri.Range
      rcases hs c hc with h | h
      · exact Or.inl (Or.inl ⟨c, rfl, h.1, h.2⟩)
      · exact Or.inl (Or.inr ⟨c, rfl, h.1, h.2⟩)
  · apply Language.append_mem_mul
    · exact ch_mem 58
    · rw [show [47, 47] ++ (host ++ (segments.map (47 :: ·)).flatten) ++ (35 :: frag) =
          ([47, 47] ++ (host ++ (segments.map (47 :: ·)).flatten)) ++ ([] ++ (35 :: frag)) by simp]
      apply Language.append_mem_mul
      · -- authority and path
        apply Or.inl
        apply Language.append_mem_mul
        · exact Language.append_mem_mul (ch_mem 47) (ch_mem 47)
        · apply Language.append_mem_mul
          · rw [show host = [] ++ (host ++ []) by simp]
            apply Language.append_mem_mul
            · exact Or.inl rfl
            · apply Language.append_mem_mul
              · apply Or.inr
                apply Or.inr
                unfold Rowl.Iri.RegName
                apply star_of_all
                intro c hc
                exact Or.inl (Or.inl (unreserved_mem (hh c hc)))
              · exact Or.inl rfl
          · apply Language.mem_kstar.mpr
            refine ⟨segments.map (47 :: ·), rfl, ?_⟩
            intro y hy
            obtain ⟨seg, member, rfl⟩ := List.mem_map.mp hy
            unfold Rowl.Iri.Segment
            exact Language.append_mem_mul (ch_mem 47) (star_of_all (fun c hc => ipchar_mem (hseg seg member c hc)))
      · apply Language.append_mem_mul
        · exact Or.inl rfl
        · apply Or.inr
          unfold Rowl.Iri.Fragment
          exact Language.append_mem_mul (ch_mem 35) (star_of_all (fun c hc => Or.inl (ipchar_mem (hf c hc))))


theorem xsd_string_word : XsdStringBytes.map (·.val) =
    (104 :: [116, 116, 112]) ++ [58] ++ ([47, 47] ++ ([119, 119, 119, 46, 119, 51, 46, 111, 114, 103] ++
      ([[50, 48, 48, 49], [88, 77, 76, 83, 99, 104, 101, 109, 97]].map (47 :: ·)).flatten) ++
      (35 :: [115, 116, 114, 105, 110, 103])) := rfl

/-- xsd:string, the datatype of simple literals, is an absolute IRI. -/
theorem xsd_string_absolute : AbsoluteIri XsdStringBytes := by
  have small : ∀ b ∈ XsdStringBytes, b.val < 128 := by
    intro b hb
    have member : b.val ∈ XsdStringBytes.map (·.val) := List.mem_map_of_mem hb
    rw [xsd_string_word] at member
    simp at member
    omega
  refine ⟨_, ascii_utf8 XsdStringBytes small, ?_⟩
  rw [xsd_string_word]
  apply simple_iri
  · omega
  · simp
  · simp [UnreservedChar]
  · simp [UnreservedChar]
  · simp [UnreservedChar]

theorem xsd_string_not_lang : XsdStringBytes ≠ LangStringBytes := by
  intro h
  have := congrArg List.length h
  simp [XsdStringBytes, LangStringBytes] at this

theorem absolute_fault {s : List U8} (h : AbsoluteIri s) : IriFault false s = none := by
  unfold IriFault
  simp [h]

theorem subject_token_fault {bs scope : List U8} {start : Usize} {limit : Nat} {value : rdf.Subject} {stop : Usize}
    (token : Rowl.NTriples.SubjectToken bs scope start limit value stop) : SubjectFault false value = none := by
  cases value with
  | Iri v => exact absolute_fault token.2.2
  | Blank b => rfl

theorem literal_token_fault {bs : List U8} {start : Usize} {limit : Nat} {value : rdf.RdfLiteral} {stop : Usize}
    (token : Rowl.NTriples.LiteralToken bs start limit value stop) : LiteralFault false value = none := by
  obtain ⟨ending, position, ⟨next, -, body⟩, -, -, kind⟩ := token
  have utf8 := quoted_body_utf8 body
  unfold LiteralFault
  rw [if_neg (not_not.mpr utf8)]
  generalize hk : value.kind = k at kind
  cases kind with
  | @simple datatype _ xsd =>
    simp only
    rw [if_neg (by rw [xsd]; exact xsd_string_not_lang), xsd]
    exact absolute_fault xsd_string_absolute
  | @language next tag stop _ token =>
    simp only
    rw [if_pos (tag_token_form token)]
  | @datatype next after before iri stop _ _ _ correct lang =>
    simp only
    rw [if_neg lang]
    exact absolute_fault correct.2.2

theorem object_token_fault {bs scope : List U8} {start : Usize} {limit : Nat} {value : rdf.Object} {stop : Usize}
    (token : Rowl.NTriples.ObjectToken bs scope start limit value stop) : ObjectFault false value = none := by
  cases value with
  | Iri v => exact absolute_fault token.2.2
  | Blank b => rfl
  | Literal l => exact literal_token_fault token

/-- The triples the N-Triples reader returns have no faults. -/
theorem triple_token_fault {bs scope : List U8} {start : Usize} {limit : Nat} {value : rdf.Triple} {stop : Usize}
    (token : Rowl.NTriples.TripleToken bs scope start limit value stop) : TripleFault false value = none := by
  obtain ⟨⟨objectEnd, periodStart, periodEnd, ⟨predicateEnd, objectStart,
    ⟨subjectEnd, predicateStart, subjectToken, -, predicateCorrect⟩, -, objectToken⟩, -, -, -⟩, -⟩ := token
  unfold TripleFault
  rw [subject_token_fault subjectToken, absolute_fault predicateCorrect.2.2, object_token_fault objectToken]
  rfl

theorem graph_fault_none_of {resolved : Bool} : ∀ {ts : List rdf.Triple}, (∀ t ∈ ts, TripleFault resolved t = none) →
    GraphFault resolved ts = none
  | [], _ => rfl
  | t :: ts, h => by
    simp only [GraphFault, h t (by simp), Option.none_or]
    exact graph_fault_none_of (fun u hu => h u (by simp [hu]))

theorem document_tail_faults {bs scope : List U8} {termLimit tripleLimit : Nat} {position : Usize} {count : Nat}
    {ts : List rdf.Triple} (tail : Rowl.NTriples.DocumentTail bs scope termLimit tripleLimit position count ts) :
    ∀ t ∈ ts, TripleFault false t = none := by
  induction tail with
  | eof _ => simp
  | triple token _ _ _ ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | later
    · exact triple_token_fault token
    · exact ih t later

/-- Every N-Triples document, under any limits, denotes triples without faults. -/
theorem document_writable {bs scope : List U8} {termLimit tripleLimit : Nat} {ts : List rdf.Triple}
    (document : Rowl.NTriples.Document bs scope termLimit tripleLimit ts) : GraphFault false ts = none := by
  obtain ⟨position, -, tail⟩ := document
  exact graph_fault_none_of (document_tail_faults tail)

/-! ## Faults depend on the terms, not on the blank nodes -/

/-- A term with its blank node forgotten. -/
def shapeTerm : Rowl.TurtleTokens.Term → Rowl.TurtleTokens.Term
  | .blank _ _ => .blank [] []
  | .iri v => .iri v
  | .literal v k => .literal v k

/-- A triple with its blank nodes forgotten. -/
def ShapeSpo (x : Rowl.Turtle.Spo) : Rowl.Turtle.Spo :=
  ⟨shapeTerm x.subject, x.predicate, shapeTerm x.object⟩

theorem subject_fault_shape {r : Bool} {a b : rdf.Subject}
    (h : shapeTerm (Rowl.TurtleTokens.subjectTerm a) = shapeTerm (Rowl.TurtleTokens.subjectTerm b)) :
    SubjectFault r a = SubjectFault r b := by
  cases a <;> cases b <;> simp [Rowl.TurtleTokens.subjectTerm, shapeTerm] at h <;> simp [SubjectFault, h]

theorem literal_fault_shape {r : Bool} {a b : rdf.RdfLiteral}
    (h : Rowl.TurtleTokens.literalTerm a = Rowl.TurtleTokens.literalTerm b) : LiteralFault r a = LiteralFault r b := by
  unfold Rowl.TurtleTokens.literalTerm at h
  unfold LiteralFault
  cases ha : a.kind <;> cases hb : b.kind <;> rw [ha, hb] at h <;> simp at h <;> simp [h]

theorem literal_term_shape (l : rdf.RdfLiteral) : ∃ v k, Rowl.TurtleTokens.literalTerm l = .literal v k := by
  unfold Rowl.TurtleTokens.literalTerm
  cases l.kind <;> exact ⟨_, _, rfl⟩

theorem object_fault_shape {r : Bool} {a b : rdf.Object}
    (h : shapeTerm (Rowl.TurtleTokens.objectTerm a) = shapeTerm (Rowl.TurtleTokens.objectTerm b)) :
    ObjectFault r a = ObjectFault r b := by
  cases a with
  | Iri v =>
    cases b with
    | Iri w =>
      simp [Rowl.TurtleTokens.objectTerm, shapeTerm] at h
      simp [ObjectFault, h]
    | Blank _ => simp [Rowl.TurtleTokens.objectTerm, shapeTerm] at h
    | Literal m =>
      obtain ⟨v', k', hm⟩ := literal_term_shape m
      simp [Rowl.TurtleTokens.objectTerm, hm, shapeTerm] at h
  | Blank _ =>
    cases b with
    | Iri w => simp [Rowl.TurtleTokens.objectTerm, shapeTerm] at h
    | Blank _ => rfl
    | Literal m =>
      obtain ⟨v', k', hm⟩ := literal_term_shape m
      simp [Rowl.TurtleTokens.objectTerm, hm, shapeTerm] at h
  | Literal l =>
    obtain ⟨v, k, hl⟩ := literal_term_shape l
    cases b with
    | Iri w => simp [Rowl.TurtleTokens.objectTerm, hl, shapeTerm] at h
    | Blank _ => simp [Rowl.TurtleTokens.objectTerm, hl, shapeTerm] at h
    | Literal m =>
      obtain ⟨v', k', hm⟩ := literal_term_shape m
      simp only [Rowl.TurtleTokens.objectTerm, hl, hm, shapeTerm] at h
      exact literal_fault_shape (by rw [hl, hm, h])

theorem triple_fault_shape {r : Bool} {a b : rdf.Triple}
    (h : ShapeSpo (Rowl.Turtle.spo a) = ShapeSpo (Rowl.Turtle.spo b)) : TripleFault r a = TripleFault r b := by
  simp only [ShapeSpo, Rowl.Turtle.spo, Rowl.Turtle.Spo.mk.injEq] at h
  obtain ⟨hs, hp, ho⟩ := h
  unfold TripleFault
  rw [subject_fault_shape hs, hp, object_fault_shape ho]

theorem graph_fault_shape {r : Bool} : ∀ {xs ys : List rdf.Triple},
    xs.map (fun t => ShapeSpo (Rowl.Turtle.spo t)) = ys.map (fun t => ShapeSpo (Rowl.Turtle.spo t)) →
      GraphFault r xs = GraphFault r ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [GraphFault, triple_fault_shape h.1, graph_fault_shape h.2]

/-- The N-Triples writer reports a term error exactly for graphs that no
    N-Triples document denotes, even with other blank nodes: every graph
    `ntriples::read` returns differs from such a graph in a triple other than
    by its blank nodes. -/
theorem ntriples_write_error_exact (graph : rdf.RawGraph) (limit : Usize) (e : rdf_write.WriteError)
    (written : ntriples.write graph limit = .ok (.Error e)) (term : e ≠ .ResourceLimit)
    (bytes scope : alloc.vec.Vec U8) (read : rdf.RawGraph) (h : ntriples.read bytes scope = .ok (.Graph read)) :
    read.triples.val.map (fun t => ShapeSpo (Rowl.Turtle.spo t)) ≠
      graph.triples.val.map (fun t => ShapeSpo (Rowl.Turtle.spo t)) := by
  obtain ⟨r, run, correct⟩ := write_graph_total_correct graph false limit
  unfold ntriples.write at written
  have same : r = .Error e := Result.ok_injective (run.symm.trans written)
  subst same
  have fault : GraphFault false graph.triples.val = some e := by
    rcases correct with fault | ⟨-, rfl, -⟩
    · exact fault
    · exact absurd rfl term
  intro equal
  have readable := document_writable ((Rowl.NTriples.read_accepted_iff bytes scope read).mp h)
  rw [graph_fault_shape equal, fault] at readable
  cases readable

end Rowl.RdfWriteRead
