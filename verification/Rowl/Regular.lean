import Rowl.Unicode
import Mathlib.Computability.Language

open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open scoped Computability

namespace Rowl.Regular
set_option linter.unusedSimpArgs false
open regular
open unicode
attribute [local instance] Classical.propDecidable

/-- Independent finite-word language, using union, concatenation and Kleene
    closure rather than the executable derivative algorithm. -/
def Denotes : Expression → Language Nat
  | .Empty => 0
  | .Epsilon => 1
  | .Interval lower upper => {word | ∃ cp, word = [cp] ∧ lower.val ≤ cp ∧ cp ≤ upper.val}
  | .Alternative left right => Denotes left + Denotes right
  | .Sequence left right => Denotes left * Denotes right
  | .Repeat inner => (Denotes inner)∗

@[simp] private theorem mem_predicate (p : List Nat → Prop) (word : List Nat) :
    word ∈ (show Language Nat from {w | p w}) ↔ p word := Iff.rfl

@[simp] private theorem mem_sup (a b : Language Nat) (word : List Nat) :
    word ∈ a ⊔ b ↔ word ∈ a ∨ word ∈ b := Iff.rfl

private theorem nil_mul (a b : Language Nat) :
    [] ∈ a * b ↔ [] ∈ a ∧ [] ∈ b := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨left, hl, right, hr, eq⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp eq
    exact ⟨hl, hr⟩
  · rintro ⟨ha, hb⟩
    exact ⟨[], ha, [], hb, rfl⟩

/-- Copying is exact, not merely language-equivalent. -/
theorem copy_expression_total (expression : Expression) :
    copy_expression expression = .ok expression := by
  induction expression <;> simp [copy_expression, *]

/-- Empty-word recognition is equivalent to the declarative language. -/
theorem nullable_total_correct (expression : Expression) :
    nullable expression = .ok (decide ([] ∈ Denotes expression)) := by
  classical
  induction expression with
  | Empty => simp [nullable, Denotes]
  | Epsilon => simp [nullable, Denotes]
  | Interval lower upper => simp [nullable, Denotes]
  | Alternative left right hl hr =>
    by_cases h : [] ∈ Denotes left <;> simp [nullable, hl, hr, Denotes, h]
  | Sequence left right hl hr =>
    by_cases h : [] ∈ Denotes left <;> simp [nullable, hl, hr, Denotes, nil_mul, h]
  | Repeat inner => simp [nullable, Denotes, Language.nil_mem_kstar]

/-- The smart union constructor preserves exactly the union language. -/
theorem alternate_total_correct (left right : Expression) :
    ∃ result, alternate left right = .ok result ∧
      Denotes result = Denotes left + Denotes right := by
  cases left <;> cases right <;> simp [alternate, Denotes]

/-- The smart concatenation constructor preserves exactly concatenation. -/
theorem sequence_total_correct (left right : Expression) :
    ∃ result, regular.sequence left right = .ok result ∧
      Denotes result = Denotes left * Denotes right := by
  cases left <;> cases right <;> simp [regular.sequence, Denotes]

/-- The smart repeat constructor preserves finite Kleene closure. -/
theorem repeat_total_correct (expression : Expression) :
    ∃ result, regular.repeat expression = .ok result ∧
      Denotes result = (Denotes expression)∗ := by
  cases expression <;> simp [regular.repeat, Denotes]

private theorem cons_mul (a b : Language Nat) (cp : Nat) (word : List Nat) :
    cp :: word ∈ a * b ↔
      (∃ left right, word = left ++ right ∧ cp :: left ∈ a ∧ right ∈ b) ∨
      ([] ∈ a ∧ cp :: word ∈ b) := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨left, hl, right, hr, eq⟩
    cases left with
    | nil => simp only [List.nil_append] at eq; exact Or.inr ⟨hl, eq ▸ hr⟩
    | cons head tail =>
      have heq := List.cons.inj eq
      rcases heq with ⟨rfl, heq⟩
      exact Or.inl ⟨tail, right, heq.symm, hl, hr⟩
  · rintro (⟨left, right, eq, hl, hr⟩ | ⟨hl, hr⟩)
    · exact ⟨cp :: left, hl, right, hr, by simp [eq]⟩
    · exact ⟨[], hl, cp :: word, hr, rfl⟩

private theorem cons_star (a : Language Nat) (cp : Nat) (word : List Nat) :
    cp :: word ∈ a∗ ↔
      ∃ left right, word = left ++ right ∧ cp :: left ∈ a ∧ right ∈ a∗ := by
  constructor
  · rw [Language.mem_kstar_iff_exists_nonempty]
    rintro ⟨chunks, eq, good⟩
    cases chunks with
    | nil => simp at eq
    | cons first rest =>
      obtain ⟨hf, hn⟩ := good first (by simp)
      cases first with
      | nil => exact False.elim (hn rfl)
      | cons head tail =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at eq
        rcases eq with ⟨rfl, eq⟩
        refine ⟨tail, rest.flatten, eq, hf, ?_⟩
        exact Language.join_mem_kstar (fun w hw => (good w (by simp [hw])).1)
  · rintro ⟨left, right, eq, hl, hr⟩
    obtain ⟨chunks, hword, good⟩ := Language.mem_kstar.mp hr
    apply Language.mem_kstar.mpr
    refine ⟨(cp :: left) :: chunks, ?_, ?_⟩
    · simp [List.flatten_cons, eq, hword]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hl
      · exact good w hw

/-- Each actual derivative terminates and recognizes exactly the suffixes of
    words whose first code point is the consumed scalar. -/
theorem derivative_total_correct (expression : Expression) (cp : U32) :
    ∃ result, derivative expression cp = .ok result ∧
      ∀ word, word ∈ Denotes result ↔ cp.val :: word ∈ Denotes expression := by
  classical
  induction expression with
  | Empty => exact ⟨.Empty, by simp [derivative], by simp [Denotes]⟩
  | Epsilon => exact ⟨.Empty, by simp [derivative], by simp [Denotes]⟩
  | Interval lower upper =>
    by_cases low : lower.val ≤ cp.val
    · by_cases high : cp.val ≤ upper.val
      · refine ⟨.Epsilon, by simp [derivative, low, high], ?_⟩
        intro word
        simp [Denotes, low, high]
      · refine ⟨.Empty, by simp [derivative, low, high], ?_⟩
        intro word
        simp [Denotes, low, high]
    · refine ⟨.Empty, by simp [derivative, low], ?_⟩
      intro word
      simp [Denotes, low]
  | Alternative left right hl hr =>
    obtain ⟨dl, hdl, sl⟩ := hl
    obtain ⟨dr, hdr, sr⟩ := hr
    obtain ⟨result, hresult, sem⟩ := alternate_total_correct dl dr
    refine ⟨result, by simp [derivative, hdl, hdr, hresult], ?_⟩
    intro word
    simp [sem, Denotes, Language.mem_add, sl, sr]
  | Sequence left right hl hr =>
    obtain ⟨dl, hdl, sl⟩ := hl
    obtain ⟨dr, hdr, sr⟩ := hr
    obtain ⟨joined, hjoined, sj⟩ := sequence_total_correct dl right
    by_cases empty : [] ∈ Denotes left
    · obtain ⟨result, hresult, sem⟩ := alternate_total_correct joined dr
      refine ⟨result, by simp [derivative, nullable_total_correct, empty,
        copy_expression_total, hdl, hdr, hjoined, hresult], ?_⟩
      intro word
      rw [sem, Language.mem_add, Denotes, cons_mul]
      simp only [empty, true_and, Language.mem_mul, sj, sl, sr]
      constructor
      · rintro (⟨a, ha, b, hb, eq⟩ | h)
        · exact Or.inl ⟨a, b, eq.symm, ha, hb⟩
        · exact Or.inr h
      · rintro (⟨a, b, eq, ha, hb⟩ | h)
        · exact Or.inl ⟨a, ha, b, hb, eq.symm⟩
        · exact Or.inr h
    · obtain ⟨result, hresult, sem⟩ := alternate_total_correct joined .Empty
      refine ⟨result, by simp [derivative, nullable_total_correct, empty, hdl, hjoined, hresult], ?_⟩
      intro word
      rw [sem, Denotes, add_zero, sj, Language.mem_mul, Denotes, cons_mul]
      simp only [empty, false_and, or_false, sl]
      constructor
      · rintro ⟨a, ha, b, hb, eq⟩
        exact ⟨a, b, eq.symm, ha, hb⟩
      · rintro ⟨a, b, eq, ha, hb⟩
        exact ⟨a, ha, b, hb, eq.symm⟩
  | Repeat inner hi =>
    obtain ⟨d, hd, sd⟩ := hi
    obtain ⟨repeated, hr, sr⟩ := repeat_total_correct inner
    obtain ⟨result, hresult, sem⟩ := sequence_total_correct d repeated
    refine ⟨result, by simp [derivative, copy_expression_total, hd, hr, hresult], ?_⟩
    intro word
    rw [sem, Language.mem_mul, Denotes, cons_star]
    simp only [sr, sd]
    constructor
    · rintro ⟨a, ha, b, hb, eq⟩
      exact ⟨a, b, eq.symm, ha, hb⟩
    · rintro ⟨a, b, eq, ha, hb⟩
      exact ⟨a, ha, b, hb, eq.symm⟩

/-- RFC units consume precisely the whole suffix, with no XML-specific filter. -/
inductive Utf8From (bs : List U8) : Nat → List Nat → Prop
  | endOfInput : Utf8From bs bs.length []
  | character {offset cp width tail} :
      Rowl.Unicode.Prefix bs offset = some (cp, width) → 0 < width →
      offset + width ≤ bs.length → Utf8From bs (offset + width) tail →
      Utf8From bs offset (cp :: tail)

/-- First malformed UTF-8 unit; preceding units need not match the grammar. -/
inductive Utf8Failure (bs : List U8) : Nat → TextError → Prop
  | position {offset position} : position.val = offset → bs.length < offset →
      Utf8Failure bs offset (.InvalidPosition position)
  | utf8 {offset position} : position.val = offset → offset < bs.length →
      Rowl.Unicode.Prefix bs offset = none → Utf8Failure bs offset (.InvalidUtf8 position)
  | later {offset cp width error} :
      Rowl.Unicode.Prefix bs offset = some (cp, width) → 0 < width →
      offset + width ≤ bs.length → Utf8Failure bs (offset + width) error →
      Utf8Failure bs offset error

def MatchCorrect (expression : Expression) (bs : List U8) (offset : Nat) : MatchResult → Prop
  | .Matched accepted => ∃ word, Utf8From bs offset word ∧
      accepted = decide (word ∈ Denotes expression)
  | .MalformedUtf8 error => Utf8Failure bs offset error

private theorem match_from_total (expression : Expression) (bytes : alloc.vec.Vec U8)
    (offset : Usize) :
    ∃ result, match_from expression bytes offset = .ok result ∧
      MatchCorrect expression bytes.val offset.val result := by
  obtain ⟨step, hs, hc⟩ := Rowl.Unicode.decode_next_total_correct bytes offset
  rw [match_from]
  simp only [hs]
  cases step with
  | End =>
    rw [nullable_total_correct]
    refine ⟨.Matched (decide ([] ∈ Denotes expression)), by simp, [], ?_, rfl⟩
    rw [hc]
    exact .endOfInput
  | Error error =>
    refine ⟨.MalformedUtf8 error, by simp, ?_⟩
    cases error with
    | InvalidPosition position => exact .position (congrArg UScalar.val hc.1) hc.2
    | InvalidUtf8 position => exact .utf8 (congrArg UScalar.val hc.1) hc.2.1 hc.2.2
    | NonXmlCharacter _ _ => exact False.elim hc
  | Scalar cp next =>
    obtain ⟨advance, bound, unit⟩ := hc
    have width : 0 < next.val - offset.val := by omega
    have position : offset.val + (next.val - offset.val) = next.val := by omega
    have fits : offset.val + (next.val - offset.val) ≤ bytes.val.length := by omega
    obtain ⟨derived, hd, language⟩ := derivative_total_correct expression cp
    simp only [bind_ok, hd]
    obtain ⟨result, hr, correct⟩ := match_from_total derived bytes next
    refine ⟨result, by simp [hr], ?_⟩
    cases result with
    | Matched accepted =>
      obtain ⟨word, hw, hb⟩ := correct
      refine ⟨cp.val :: word, .character unit width fits (by simpa [position] using hw), ?_⟩
      rw [hb]
      exact congrArg (fun p : Prop => decide p) (propext (language word))
    | MalformedUtf8 error =>
      exact .later unit width fits (by simpa [position, MatchCorrect] using correct)
termination_by bytes.val.length - offset.val
decreasing_by omega

private theorem utf8_unique (bs : List U8) (offset : Nat) (word : List Nat)
    (accepted : Utf8From bs offset word) :
    ∀ other, Utf8From bs offset other → word = other := by
  induction accepted with
  | endOfInput =>
    intro other accepted
    cases accepted with
    | endOfInput => rfl
    | character _ positive fits _ => omega
  | character unit positive fits tail ih =>
    intro other accepted
    cases accepted with
    | endOfInput => omega
    | character otherUnit _ _ otherTail =>
      have eq := Prod.mk.inj (Option.some.inj (unit.symm.trans otherUnit))
      rcases eq with ⟨rfl, rfl⟩
      exact congrArg _ (ih _ otherTail)

/-- First malformed-unit evidence excludes every complete valid UTF-8 suffix. -/
theorem failure_excludes_utf8 (bs : List U8) (offset : Nat) (error : TextError)
    (failure : Utf8Failure bs offset error) :
    ∀ word, ¬ Utf8From bs offset word := by
  induction failure with
  | position same beyond =>
    intro word accepted
    cases accepted with
    | endOfInput => omega
    | character _ positive fits _ => omega
  | utf8 same inside invalid =>
    intro word accepted
    cases accepted with
    | endOfInput => omega
    | character unit _ _ _ => rw [invalid] at unit; cases unit
  | later unit positive fits failure ih =>
    intro word accepted
    cases accepted with
    | endOfInput => omega
    | character otherPrefix _ _ tail =>
      have eq := Prod.mk.inj (Option.some.inj (unit.symm.trans otherPrefix))
      have sameWidth := eq.2
      subst sameWidth
      exact ih _ tail

/-- Total byte-to-language matching, including exact malformed-unit evidence. -/
theorem matches_utf8_total_correct (expression : Expression) (bytes : alloc.vec.Vec U8) :
    ∃ result, matches_utf8 expression bytes = .ok result ∧
      MatchCorrect expression bytes.val 0 result := by
  simpa [matches_utf8] using match_from_total expression bytes 0#usize

/-- No false accepts or false grammar rejections for a valid UTF-8 input. -/
theorem matches_utf8_accepted_iff (expression : Expression) (bytes : alloc.vec.Vec U8) :
    matches_utf8 expression bytes = .ok (.Matched true) ↔
      ∃ word, Utf8From bytes.val 0 word ∧ word ∈ Denotes expression := by
  obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct expression bytes
  constructor
  · intro success
    have same := Result.ok_injective (hr.symm.trans success)
    rw [same] at hc
    obtain ⟨word, hw, hb⟩ := hc
    exact ⟨word, hw, of_decide_eq_true hb.symm⟩
  · rintro ⟨word, hw, language⟩
    cases result with
    | Matched accepted =>
      obtain ⟨other, ho, hb⟩ := hc
      have same := utf8_unique bytes.val 0 other ho word hw
      subst other
      have isTrue : accepted = true := by simpa [language] using hb
      simpa [isTrue] using hr
    | MalformedUtf8 error => exact False.elim (failure_excludes_utf8 bytes.val 0 error hc word hw)

/-- A malformed suffix is reported even when an earlier unit missed the grammar. -/
theorem matches_utf8_malformed_iff (expression : Expression) (bytes : alloc.vec.Vec U8)
    (error : TextError) :
    matches_utf8 expression bytes = .ok (.MalformedUtf8 error) ↔
      Utf8Failure bytes.val 0 error := by
  obtain ⟨result, hr, hc⟩ := matches_utf8_total_correct expression bytes
  constructor
  · intro failure
    have same := Result.ok_injective (hr.symm.trans failure)
    rw [same] at hc
    exact hc
  · intro failure
    cases result with
    | Matched accepted =>
      obtain ⟨word, hw, _⟩ := hc
      exact False.elim (failure_excludes_utf8 bytes.val 0 error failure word hw)
    | MalformedUtf8 other =>
      -- Diagnostic determinism follows from the same deterministic byte scan.
      have same : other = error := by
        have unique : ∀ offset a, Utf8Failure bytes.val offset a →
            ∀ b, Utf8Failure bytes.val offset b → a = b := by
          intro offset a fa
          induction fa with
          | position same beyond =>
            intro b fb
            cases fb with
            | position sameB _ => exact congrArg TextError.InvalidPosition (UScalar.eq_of_val_eq (same.trans sameB.symm))
            | utf8 _ inside _ => omega
            | later _ positive fits _ => omega
          | utf8 same inside invalid =>
            intro b fb
            cases fb with
            | position _ beyond => omega
            | utf8 sameB _ _ => exact congrArg TextError.InvalidUtf8 (UScalar.eq_of_val_eq (same.trans sameB.symm))
            | later unit _ _ _ => rw [invalid] at unit; cases unit
          | later unit positive fits fa ih =>
            intro b fb
            cases fb with
            | position _ beyond => omega
            | utf8 _ _ invalid => rw [invalid] at unit; cases unit
            | later otherUnit _ _ laterFailure =>
              have eq := Prod.mk.inj (Option.some.inj (unit.symm.trans otherUnit))
              have sameWidth := eq.2
              subst sameWidth
              exact ih b laterFailure
        exact unique 0 other hc error failure
      simpa [same] using hr

end Rowl.Regular
