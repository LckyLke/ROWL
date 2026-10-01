import Rowl.Generated.RowlFrontend

namespace Rowl.Unicode
open Aeneas Aeneas.Std RowlFrontendRust.unicode
attribute [local instance] Classical.propDecidable

/-- RFC 3629 §4 byte grammar, with natural numbers rather than machine arithmetic. -/
def Tail (b : Nat) : Prop := 128 ≤ b ∧ b ≤ 191
def Pair (a b : Nat) : Prop := 194 ≤ a ∧ a ≤ 223 ∧ Tail b
def Triple (a b c : Nat) : Prop :=
  ((a = 224 ∧ 160 ≤ b ∧ b ≤ 191) ∨
   (225 ≤ a ∧ a ≤ 236 ∧ Tail b) ∨
   (a = 237 ∧ 128 ≤ b ∧ b ≤ 159) ∨
   (238 ≤ a ∧ a ≤ 239 ∧ Tail b)) ∧ Tail c
def Quad (a b c d : Nat) : Prop :=
  ((a = 240 ∧ 144 ≤ b ∧ b ≤ 191) ∨
   (241 ≤ a ∧ a ≤ 243 ∧ Tail b) ∨
   (a = 244 ∧ 128 ≤ b ∧ b ≤ 143)) ∧ Tail c ∧ Tail d
def value2 (a b : Nat) : Nat := (a - 192) * 64 + (b - 128)
def value3 (a b c : Nat) : Nat := (a - 224) * 4096 + (b - 128) * 64 + (c - 128)
def value4 (a b c d : Nat) : Nat :=
  (a - 240) * 262144 + (b - 128) * 4096 + (c - 128) * 64 + (d - 128)

/-- RFC productions exclude overlong encodings, UTF-16 surrogates and values
    above U+10FFFF; their arithmetic denotes the stated Unicode scalar ranges. -/
theorem byte_grammar_scalar_ranges (a b c d : Nat) :
    (Pair a b → 128 ≤ value2 a b ∧ value2 a b ≤ 2047) ∧
    (Triple a b c →
      (2048 ≤ value3 a b c ∧ value3 a b c ≤ 55295) ∨
      (57344 ≤ value3 a b c ∧ value3 a b c ≤ 65535)) ∧
    (Quad a b c d → 65536 ≤ value4 a b c d ∧ value4 a b c d ≤ 1114111) := by
  simp only [Pair, Triple, Quad, Tail, value2, value3, value4]
  omega

/-- The XML 1.0 third edition `Char` production, not the discouraged ranges. -/
def XmlChar (cp : Nat) : Prop :=
  cp = 9 ∨ cp = 10 ∨ cp = 13 ∨ (32 ≤ cp ∧ cp ≤ 55295) ∨
  (57344 ≤ cp ∧ cp ≤ 65533) ∨ (65536 ≤ cp ∧ cp ≤ 1114111)

private theorem continuation_correct (b : U8) :
    continuation b = .ok (decide (Tail b.val)) := by simp [continuation, Tail]

private theorem two_total (a b : U8) :
    ∃ r, two a b = .ok r ∧
      r.map UScalar.val = if Pair a.val b.val then some (value2 a.val b.val) else none := by
  apply WP.spec_imp_exists
  simp [two, continuation_correct, Pair, Tail]
  split
  · rename_i h
    obtain ⟨ha, hb, hc, hd⟩ := h
    simp only [lift]
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    step as ⟨z, hz⟩
    step as ⟨r, hr⟩
    have hv : r.val = value2 a.val b.val := by
      unfold value2
      scalar_tac
    exact congrArg some hv
  · rename_i h
    simp

private theorem three_total (a b c : U8) :
    ∃ r, three a b c = .ok r ∧
      r.map UScalar.val = if Triple a.val b.val c.val then some (value3 a.val b.val c.val) else none := by
  apply WP.spec_imp_exists
  simp [three, continuation_correct, Triple, Tail, and_assoc, or_assoc, UScalar.eq_equiv]
  split
  · rename_i h
    have ha : 224 ≤ a.val := by omega
    have hb : a.val ≤ 239 := by omega
    have hc : 128 ≤ b.val := by omega
    have hd : b.val ≤ 191 := by omega
    have he : 128 ≤ c.val := by omega
    have hf : c.val ≤ 191 := by omega
    simp only [lift]
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    step as ⟨z, hz⟩
    step as ⟨p, hp⟩
    step as ⟨q, hq⟩
    step as ⟨t, ht⟩
    step as ⟨r, hr⟩
    have hv : r.val = value3 a.val b.val c.val := by
      unfold value3
      scalar_tac
    exact congrArg some hv
  · simp

private theorem four_total (a b c d : U8) :
    ∃ r, four a b c d = .ok r ∧
      r.map UScalar.val = if Quad a.val b.val c.val d.val then some (value4 a.val b.val c.val d.val) else none := by
  apply WP.spec_imp_exists
  simp [four, continuation_correct, Quad, Tail, and_assoc, or_assoc, UScalar.eq_equiv]
  split
  · rename_i h
    have ha : 240 ≤ a.val := by omega
    have hb : a.val ≤ 244 := by omega
    have hc : 128 ≤ b.val := by omega
    have hd : b.val ≤ 191 := by omega
    have he : 128 ≤ c.val := by omega
    have hf : c.val ≤ 191 := by omega
    have hg : 128 ≤ d.val := by omega
    have hh : d.val ≤ 191 := by omega
    simp only [lift]
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    step as ⟨z, hz⟩
    step as ⟨p, hp⟩
    step as ⟨q, hq⟩
    step as ⟨t, ht⟩
    step as ⟨u, hu⟩
    step as ⟨v, hv⟩
    step as ⟨w, hw⟩
    step as ⟨r, hr⟩
    have value : r.val = value4 a.val b.val c.val d.val := by
      unfold value4
      scalar_tac
    exact congrArg some value
  · simp

/-- Exact acceptance of the normative XML character predicate, for every u32. -/
theorem xml_character_total_correct (cp : U32) :
    xml_character cp = .ok (decide (XmlChar cp.val)) := by
  simp [xml_character, XmlChar, UScalar.eq_equiv, Bool.or_assoc]

/-- Mathematical unit recognizer: optional list lookup cannot panic or overflow.
    Its branches are exactly the disjoint RFC byte grammar productions above. -/
noncomputable def Prefix (bs : List U8) (offset : Nat) : Option (Nat × Nat) := do
  let a ← bs[offset]?
  if a.val < 128 then some (a.val, 1)
  else if a.val < 224 then
    let b ← bs[offset + 1]?
    if Pair a.val b.val then some (value2 a.val b.val, 2) else none
  else if a.val < 240 then
    let b ← bs[offset + 1]?
    let c ← bs[offset + 2]?
    if Triple a.val b.val c.val then some (value3 a.val b.val c.val, 3) else none
  else
    let b ← bs[offset + 1]?
    let c ← bs[offset + 2]?
    let d ← bs[offset + 3]?
    if Quad a.val b.val c.val d.val then some (value4 a.val b.val c.val d.val, 4) else none

def StepCorrect (bs : List U8) (offset : Usize) : Decoded → Prop
  | .End => offset.val = bs.length
  | .Scalar cp next =>
      offset.val < next.val ∧ next.val ≤ bs.length ∧
      Prefix bs offset.val = some (cp.val, next.val - offset.val)
  | .Error (.InvalidPosition position) => position = offset ∧ bs.length < offset.val
  | .Error (.InvalidUtf8 position) =>
      position = offset ∧ offset.val < bs.length ∧ Prefix bs offset.val = none
  | .Error (.NonXmlCharacter _ _) => False

/-- Total byte decoding, exact RFC recognition, and strictly advancing bounded offsets. -/
theorem decode_next_total_correct (bytes : alloc.vec.Vec U8) (offset : Usize) :
    ∃ r, decode_next bytes offset = .ok r ∧ StepCorrect bytes.val offset r := by
  apply WP.spec_imp_exists
  unfold decode_next
  dsimp only
  split
  · rename_i bad
    simp only [WP.spec_ok, StepCorrect]
    scalar_tac
  · rename_i inRange
    split
    · rename_i atEnd
      simp only [WP.spec_ok, StepCorrect]
      scalar_tac
    · rename_i notEnd
      have inside : offset.val < bytes.val.length := by scalar_tac
      step as ⟨first, hfirst⟩
      have firstLookup : bytes.val[offset.val]? = some first := by
        simp [List.getElem?_eq_getElem inside, hfirst]
      split
      · rename_i ascii
        change first.val < 128 at ascii
        simp only [lift]
        step as ⟨next, hnext⟩
        simp only [StepCorrect]
        refine ⟨by scalar_tac, by scalar_tac, ?_⟩
        simp only [Prefix, Option.bind_some, Option.bind_eq_bind, firstLookup, ascii, hnext]
        simp_all
      · rename_i notAscii
        change ¬ first.val < 128 at notAscii
        step as ⟨remaining, hremaining⟩
        split
        · rename_i pairLead
          change first.val < 224 at pairLead
          split
          · rename_i enough
            step as ⟨secondOffset, hs⟩
            step as ⟨second, hsecond⟩
            have secondLookup : bytes.val[offset.val + 1]? = some second := by
              have bound : offset.val + 1 < bytes.val.length := by scalar_tac
              simp [List.getElem?_eq_getElem bound, hsecond, hs]
            obtain ⟨result, hr, hv⟩ := two_total first second
            cases result with
            | none =>
              have badPair : ¬ Pair first.val second.val := by
                by_contra h; simp [h] at hv
              simp only [hr, bind_ok, WP.spec_ok]
              simp only [StepCorrect, Prefix, Option.bind_some, Option.bind_eq_bind, firstLookup, secondLookup, pairLead, notAscii, badPair]
              simp_all
            | some cp =>
              simp only [hr]
              have pair : Pair first.val second.val := by
                by_contra h; simp [h] at hv
              have value : cp.val = value2 first.val second.val := by simpa [pair] using hv
              step as ⟨next, hn⟩
              simp only [StepCorrect]
              refine ⟨by scalar_tac, by scalar_tac, ?_⟩
              simp only [Prefix, Option.bind_some, Option.bind_eq_bind, firstLookup, secondLookup, pairLead, notAscii, pair, hn, value]
              simp_all
          · rename_i short
            have absent : bytes.val[offset.val + 1]? = none := by
              apply List.getElem?_eq_none
              scalar_tac
            simp only [WP.spec_ok]
            simp only [StepCorrect, Prefix, Option.bind_some, Option.bind_none, Option.bind_eq_bind, firstLookup, pairLead, notAscii, absent]
            simp_all
        · rename_i notPairLead
          change ¬ first.val < 224 at notPairLead
          split
          · rename_i tripleLead
            change first.val < 240 at tripleLead
            split
            · rename_i enough
              step as ⟨secondOffset, hs⟩
              step as ⟨second, hsecond⟩
              step as ⟨thirdOffset, ht⟩
              step as ⟨third, hthird⟩
              have secondLookup : bytes.val[offset.val + 1]? = some second := by
                have bound : offset.val + 1 < bytes.val.length := by scalar_tac
                simp [List.getElem?_eq_getElem bound, hsecond, hs]
              have thirdLookup : bytes.val[offset.val + 2]? = some third := by
                have bound : offset.val + 2 < bytes.val.length := by scalar_tac
                simp [List.getElem?_eq_getElem bound, hthird, ht]
              obtain ⟨result, hr, hv⟩ := three_total first second third
              cases result with
              | none =>
                have badTriple : ¬ Triple first.val second.val third.val := by
                  by_contra h; simp [h] at hv
                simp only [hr, bind_ok, WP.spec_ok]
                simp only [StepCorrect, Prefix, Option.bind_some, Option.bind_eq_bind, firstLookup, secondLookup, thirdLookup,
                  notPairLead, notAscii, tripleLead, badTriple]
                simp_all
              | some cp =>
                simp only [hr]
                have triple : Triple first.val second.val third.val := by
                  by_contra h; simp [h] at hv
                have value : cp.val = value3 first.val second.val third.val := by simpa [triple] using hv
                step as ⟨next, hn⟩
                simp only [StepCorrect]
                refine ⟨by scalar_tac, by scalar_tac, ?_⟩
                simp only [Prefix, Option.bind_some, Option.bind_eq_bind, firstLookup, secondLookup, thirdLookup, notPairLead, notAscii,
                  tripleLead, triple, hn, value]
                simp_all
            · rename_i short
              have absent : bytes.val[offset.val + 2]? = none := by
                apply List.getElem?_eq_none
                scalar_tac
              simp only [WP.spec_ok]
              simp only [StepCorrect, Prefix, Option.bind_some, Option.bind_none, Option.bind_eq_bind, firstLookup, notPairLead, notAscii, tripleLead, absent]
              simp_all
          · rename_i notTripleLead
            change ¬ first.val < 240 at notTripleLead
            split
            · rename_i enough
              step as ⟨secondOffset, hs⟩
              step as ⟨second, hsecond⟩
              step as ⟨thirdOffset, ht⟩
              step as ⟨third, hthird⟩
              step as ⟨fourthOffset, hf⟩
              step as ⟨fourth, hfourth⟩
              have secondLookup : bytes.val[offset.val + 1]? = some second := by
                have bound : offset.val + 1 < bytes.val.length := by scalar_tac
                simp [List.getElem?_eq_getElem bound, hsecond, hs]
              have thirdLookup : bytes.val[offset.val + 2]? = some third := by
                have bound : offset.val + 2 < bytes.val.length := by scalar_tac
                simp [List.getElem?_eq_getElem bound, hthird, ht]
              have fourthLookup : bytes.val[offset.val + 3]? = some fourth := by
                have bound : offset.val + 3 < bytes.val.length := by scalar_tac
                simp [List.getElem?_eq_getElem bound, hfourth, hf]
              obtain ⟨result, hr, hv⟩ := four_total first second third fourth
              cases result with
              | none =>
                have badQuad : ¬ Quad first.val second.val third.val fourth.val := by
                  by_contra h; simp [h] at hv
                simp only [hr, bind_ok, WP.spec_ok]
                simp only [StepCorrect, Prefix, Option.bind_some, Option.bind_eq_bind, firstLookup, secondLookup, thirdLookup, fourthLookup,
                  notPairLead, notAscii, notTripleLead, badQuad]
                simp_all
              | some cp =>
                simp only [hr]
                have quad : Quad first.val second.val third.val fourth.val := by
                  by_contra h; simp [h] at hv
                have value : cp.val = value4 first.val second.val third.val fourth.val := by simpa [quad] using hv
                step as ⟨next, hn⟩
                simp only [StepCorrect]
                refine ⟨by scalar_tac, by scalar_tac, ?_⟩
                simp only [Prefix, Option.bind_some, Option.bind_eq_bind, firstLookup, secondLookup, thirdLookup, fourthLookup, notPairLead,
                  notAscii, notTripleLead, quad, hn, value]
                simp_all
            · rename_i short
              have absent : bytes.val[offset.val + 3]? = none := by
                apply List.getElem?_eq_none
                scalar_tac
              simp only [WP.spec_ok]
              simp only [StepCorrect, Prefix, Option.bind_some, Option.bind_none, Option.bind_eq_bind, firstLookup, notPairLead, notAscii, notTripleLead, absent]
              simp_all

/-- A complete mathematical text: RFC units consume exactly the remaining bytes,
    every character meets XML `Char`, and each recorded offset is its unit start. -/
inductive TextFrom (bs : List U8) : Nat → List (Nat × Nat) → Prop
  | endOfInput : TextFrom bs bs.length []
  | character {offset cp width tail} :
      Prefix bs offset = some (cp, width) → XmlChar cp → 0 < width →
      offset + width ≤ bs.length → TextFrom bs (offset + width) tail →
      TextFrom bs offset ((cp, offset) :: tail)

/-- The first failed unit, preceded only by valid XML characters. -/
inductive Rejected (bs : List U8) : Nat → TextError → Prop
  | position {offset position} : position.val = offset → bs.length < offset →
      Rejected bs offset (.InvalidPosition position)
  | utf8 {offset position} : position.val = offset → offset < bs.length → Prefix bs offset = none →
      Rejected bs offset (.InvalidUtf8 position)
  | xml {offset cp width position value} :
      position.val = offset → value.val = cp → Prefix bs offset = some (cp, width) → ¬ XmlChar cp →
      Rejected bs offset (.NonXmlCharacter position value)
  | later {offset cp width error} :
      Prefix bs offset = some (cp, width) → XmlChar cp → 0 < width →
      offset + width ≤ bs.length → Rejected bs (offset + width) error →
      Rejected bs offset error

def scalarValues : Scalars → List (Nat × Nat)
  | .Empty => []
  | .Cons cp offset next => (cp.val, offset.val) :: scalarValues next

def ScanCorrect (bs : List U8) (offset : Nat) : TextScan → Prop
  | .Valid scalars => TextFrom bs offset (scalarValues scalars)
  | .Invalid error => Rejected bs offset error

private theorem read_from_total (bytes : alloc.vec.Vec U8) (offset : Usize) :
    ∃ r, read_from bytes offset = .ok r ∧ ScanCorrect bytes.val offset.val r := by
  obtain ⟨step, hs, hc⟩ := decode_next_total_correct bytes offset
  rw [read_from]
  simp only [hs]
  cases step with
  | End =>
    refine ⟨.Valid .Empty, by simp, ?_⟩
    change TextFrom bytes.val offset.val []
    rw [hc]
    exact .endOfInput
  | Error error =>
    refine ⟨.Invalid error, by simp, ?_⟩
    cases error with
    | InvalidPosition position => exact .position (congrArg UScalar.val hc.1) hc.2
    | InvalidUtf8 position => exact .utf8 (congrArg UScalar.val hc.1) hc.2.1 hc.2.2
    | NonXmlCharacter _ _ => exact False.elim hc
  | Scalar cp next =>
    simp only [bind_ok]
    obtain ⟨advance, bound, unit⟩ := hc
    have width : 0 < next.val - offset.val := by omega
    have position : offset.val + (next.val - offset.val) = next.val := by omega
    have fits : offset.val + (next.val - offset.val) ≤ bytes.val.length := by omega
    rw [xml_character_total_correct]
    by_cases char : XmlChar cp.val
    · simp only [char, decide_true, bind_ok, ↓reduceIte]
      obtain ⟨result, hr, correct⟩ := read_from_total bytes next
      cases result with
      | Valid tail =>
        refine ⟨.Valid (.Cons cp offset tail), by simp [hr], ?_⟩
        change TextFrom bytes.val offset.val ((cp.val, offset.val) :: scalarValues tail)
        exact .character unit char width fits (by simpa [position, ScanCorrect] using correct)
      | Invalid error =>
        refine ⟨.Invalid error, by simp [hr], ?_⟩
        exact .later unit char width fits (by simpa [position, ScanCorrect] using correct)
    · simp only [char, decide_false, bind_ok, Bool.false_eq_true, ↓reduceIte]
      exact ⟨.Invalid (.NonXmlCharacter offset cp), by simp, .xml rfl rfl unit char⟩
termination_by bytes.val.length - offset.val
decreasing_by omega

/-- The actual recursive byte frontend terminates and returns either the whole
    decoded XML-character text or evidence of its first failed unit. -/
theorem read_text_total_correct (bytes : alloc.vec.Vec U8) :
    ∃ r, read_text bytes = .ok r ∧ ScanCorrect bytes.val 0 r := by
  simpa [read_text] using read_from_total bytes 0#usize

theorem rejected_excludes_text (bs : List U8) (offset : Nat) (error : TextError)
    (failure : Rejected bs offset error) :
    ∀ text, ¬ TextFrom bs offset text := by
  induction failure with
  | position same beyond =>
    intro text accepted
    cases accepted with
    | endOfInput => omega
    | character _ _ positive fits _ => omega
  | utf8 same inside invalid =>
    intro text accepted
    cases accepted with
    | endOfInput => omega
    | character unit _ _ _ _ => rw [invalid] at unit; cases unit
  | xml same value invalid nonXml =>
    intro text accepted
    cases accepted with
    | endOfInput =>
      simp [Prefix] at invalid
    | character unit char _ _ _ =>
      have eq := Prod.mk.inj (Option.some.inj (invalid.symm.trans unit))
      exact nonXml (eq.1.symm ▸ char)
  | later unit char positive fits failure ih =>
    intro text accepted
    cases accepted with
    | endOfInput => omega
    | character otherPrefix _ _ _ tail =>
      have eq := Prod.mk.inj (Option.some.inj (unit.symm.trans otherPrefix))
      have sameWidth := eq.2
      subst sameWidth
      exact ih _ tail

/-- Acceptance is complete as well as sound for the stated UTF-8/XML text grammar. -/
theorem read_text_valid_iff (bytes : alloc.vec.Vec U8) :
    (∃ scalars, read_text bytes = .ok (.Valid scalars)) ↔
      ∃ text, TextFrom bytes.val 0 text := by
  obtain ⟨result, hr, hc⟩ := read_text_total_correct bytes
  constructor
  · rintro ⟨scalars, accepted⟩
    have same := Result.ok_injective (hr.symm.trans accepted)
    rw [same] at hc
    exact ⟨scalarValues scalars, hc⟩
  · rintro ⟨text, accepted⟩
    cases result with
    | Valid scalars => exact ⟨scalars, hr⟩
    | Invalid error => exact False.elim (rejected_excludes_text bytes.val 0 error hc text accepted)

theorem read_text_terminates (bytes : alloc.vec.Vec U8) :
    ∃ r, read_text bytes = .ok r := by
  obtain ⟨r, hr, _⟩ := read_text_total_correct bytes
  exact ⟨r, hr⟩

end Rowl.Unicode
