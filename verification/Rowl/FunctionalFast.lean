import Rowl.Functional

/-!
Terminal selection on text already known to be valid UTF-8. The lexer checks
the whole text once, and then selects each token with matchers that stop as
soon as a terminal can match no longer prefix; on a valid suffix they select
exactly what the full matchers select. The lexer also skips every terminal
whose words cannot begin with the next code point: each terminal language's
first code points pass the dispatch test, so a skipped terminal has no
candidate endpoint and the selection is unchanged.
-/
namespace Rowl.FunctionalFast
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open RowlRust.functional (Terminal Token Selection)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

theorem longest_valid_eq (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize)
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.longest_valid terminal bytes position = functional.longest terminal bytes position := by
  obtain ⟨grammar,read,_⟩ := Rowl.Functional.grammar_total_correct terminal
  rw [functional.longest_valid,functional.longest,read,bind_ok,bind_ok,
    Rowl.Longest.longest_valid_prefix_eq grammar bytes position valid]

theorem seed_valid_eq (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize)
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.seed_valid terminal bytes position = functional.seed terminal bytes position := by
  rw [functional.seed_valid,functional.seed,longest_valid_eq terminal bytes position valid]

theorem extend_valid_eq (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position : Usize)
    (previous : Selection) (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.extend_valid terminal bytes position previous = functional.extend terminal bytes position previous := by
  rw [functional.extend_valid.eq_def,functional.extend.eq_def]
  cases previous <;> simp only [seed_valid_eq terminal bytes position valid,longest_valid_eq terminal bytes position valid]

/-- On a valid suffix the early-stopping selection is the standard greatest
    selection, so every property of `next_terminal` carries over. -/
theorem next_terminal_valid_eq (bytes : alloc.vec.Vec U8) (position : Usize)
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.next_terminal_valid bytes position = functional.next_terminal bytes position := by
  rw [functional.next_terminal_valid,functional.next_terminal]
  simp only [seed_valid_eq _ bytes position valid,extend_valid_eq _ bytes position _ valid]

private theorem range_head {c lower upper : Nat} {tail : List Nat}
    (accepted : c :: tail ∈ Rowl.Iri.Range lower upper) : lower ≤ c ∧ c ≤ upper := by
  obtain ⟨cp, equal, low, high⟩ := accepted
  obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp equal
  exact ⟨low, high⟩

private theorem range_nonempty (lower upper : Nat) : [] ∉ Rowl.Iri.Range lower upper := by
  rintro ⟨cp, equal, -⟩
  cases equal

private theorem mul_head {c : Nat} {tail : List Nat} {a b : Language Nat}
    (accepted : c :: tail ∈ a * b) (nonempty : [] ∉ a) : ∃ rest, c :: rest ∈ a := by
  obtain ⟨left, inLeft, right, -, equal⟩ := Language.mem_mul.mp accepted
  cases left with
  | nil => exact absurd inLeft nonempty
  | cons x rest =>
    rw [List.cons_append,List.cons_eq_cons] at equal
    obtain ⟨rfl, -⟩ := equal
    exact ⟨rest, inLeft⟩

private theorem mul_nonempty {a b : Language Nat} (nonempty : [] ∉ a) : [] ∉ a * b := by
  intro accepted
  obtain ⟨left, inLeft, right, -, equal⟩ := Language.mem_mul.mp accepted
  obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp equal
  exact nonempty inLeft

private theorem range_mul_head {c lower upper : Nat} {tail : List Nat} {b : Language Nat}
    (accepted : c :: tail ∈ Rowl.Iri.Range lower upper * b) : lower ≤ c ∧ c ≤ upper := by
  obtain ⟨rest, first⟩ := mul_head accepted (range_nonempty lower upper)
  exact range_head first

private theorem keyword_head (key : functional.Keyword) :
    ∃ first, functional.keyword_first key = .ok first ∧
      (Rowl.Functional.KeywordWord key).head? = some first.val := by
  cases key <;> simp [functional.keyword_first, Rowl.Functional.KeywordWord]

private theorem may_start_total (terminal : Terminal) (cp : U32) :
    ∃ b, functional.may_start terminal cp = .ok b := by
  cases terminal with
  | Keyword key =>
    obtain ⟨first, computed, -⟩ := keyword_head key
    exact ⟨_, by rw [functional.may_start, computed, bind_ok]⟩
  | Integer =>
    rw [functional.may_start]
    split <;> exact ⟨_, rfl⟩
  | Whitespace =>
    rw [functional.may_start]
    split_ifs <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- Every word of a terminal language begins with a code point that passes
    the lexer's dispatch test. -/
theorem may_start_sound (terminal : Terminal) (cp : U32) (tail : List Nat)
    (accepted : cp.val :: tail ∈ Rowl.Functional.TerminalLanguage terminal) :
    functional.may_start terminal cp = .ok true := by
  cases terminal with
  | Keyword key =>
    obtain ⟨first, computed, head⟩ := keyword_head key
    have word : cp.val :: tail = Rowl.Functional.KeywordWord key := accepted
    rw [← word] at head
    have equal : cp = first := (UScalar.eq_equiv cp first).mpr (Option.some.inj head)
    simp [functional.may_start, computed, equal]
  | Open =>
    have := range_head (lower := 40) (upper := 40) accepted
    have equal : cp = 40#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | Close =>
    have := range_head (lower := 41) (upper := 41) accepted
    have equal : cp = 41#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | Equals =>
    have := range_head (lower := 61) (upper := 61) accepted
    have equal : cp = 61#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | DatatypeIndicator =>
    have := range_mul_head (lower := 94) (upper := 94) accepted
    have equal : cp = 94#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | Integer =>
    have := range_mul_head (lower := 48) (upper := 57) accepted
    have low : 48#u32 ≤ cp := by scalar_tac
    have high : cp ≤ 57#u32 := by scalar_tac
    rw [functional.may_start]
    simp only [low, high, ↓reduceIte, decide_true]
  | QuotedString =>
    have := range_mul_head (lower := 34) (upper := 34) accepted
    have equal : cp = 34#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | LanguageTag =>
    have := range_mul_head (lower := 64) (upper := 64) accepted
    have equal : cp = 64#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | NodeId =>
    obtain ⟨rest, first⟩ := mul_head (b := Rowl.Names.Local) accepted
      (mul_nonempty (range_nonempty 95 95))
    have := range_mul_head first
    have equal : cp = 95#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | FullIri =>
    have := range_mul_head (lower := 60) (upper := 60) accepted
    have equal : cp = 60#u32 := by scalar_tac
    simp [functional.may_start, equal]
  | PrefixName => rfl
  | AbbreviatedIri => rfl
  | Whitespace =>
    obtain ⟨rest, first⟩ := mul_head (a := Rowl.Functional.Space) accepted
      (by simp [Rowl.Functional.Space])
    rw [functional.may_start]
    rcases first with value | value | value | value
    · have := (List.cons.inj value).1
      have equal : cp = 32#u32 := by scalar_tac
      simp [equal]
    · have := (List.cons.inj value).1
      have equal : cp = 9#u32 := by scalar_tac
      simp [equal]
    · have := (List.cons.inj value).1
      have equal : cp = 10#u32 := by scalar_tac
      simp [equal]
    · have := (List.cons.inj value).1
      have equal : cp = 13#u32 := by scalar_tac
      simp [equal]
  | Comment =>
    have := range_mul_head (lower := 35) (upper := 35) accepted
    have equal : cp = 35#u32 := by scalar_tac
    simp [functional.may_start, equal]

/-- A terminal that fails the dispatch test on the next code point has no
    candidate endpoint, so its greatest-prefix matcher reports no match. -/
theorem longest_skip (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position next : Usize) (cp : U32)
    (decoded : unicode.decode_next bytes position = .ok (.Scalar cp next))
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word)
    (skipped : functional.may_start terminal cp = .ok false) :
    functional.longest terminal bytes position = .ok (.Matched none) := by
  rw [Rowl.Functional.longest_matched_iff]
  refine ⟨valid, ?_⟩
  simp only [Rowl.Longest.Maximal]
  rintro endpoint ⟨word, span, accepted⟩
  obtain ⟨r, executed, correct⟩ := Rowl.Unicode.decode_next_total_correct bytes position
  rw [decoded] at executed
  obtain rfl := Result.ok_injective executed
  obtain ⟨-, -, prefixed⟩ := correct
  cases span with
  | empty _ => exact Rowl.Functional.grammar_nonempty terminal accepted
  | character unit _ _ _ =>
    rw [prefixed] at unit
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj unit)
    rw [may_start_sound terminal cp _ accepted] at skipped
    cases Result.ok_injective skipped

theorem seed_from_eq (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position next : Usize) (cp : U32)
    (decoded : unicode.decode_next bytes position = .ok (.Scalar cp next))
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.seed_from terminal bytes position cp = functional.seed_valid terminal bytes position := by
  obtain ⟨b, tested⟩ := may_start_total terminal cp
  rw [functional.seed_from, tested, bind_ok]
  cases b with
  | true => simp
  | false =>
    rw [seed_valid_eq terminal bytes position valid, functional.seed,
      longest_skip terminal bytes position next cp decoded valid tested, bind_ok]
    simp

theorem extend_from_eq (terminal : Terminal) (bytes : alloc.vec.Vec U8) (position next : Usize) (cp : U32)
    (previous : Selection) (decoded : unicode.decode_next bytes position = .ok (.Scalar cp next))
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.extend_from terminal bytes position cp previous =
      functional.extend_valid terminal bytes position previous := by
  obtain ⟨b, tested⟩ := may_start_total terminal cp
  rw [functional.extend_from, tested, bind_ok]
  cases b with
  | true => simp
  | false =>
    have skip := longest_skip terminal bytes position next cp decoded valid tested
    rw [extend_valid_eq terminal bytes position previous valid, functional.extend.eq_def]
    cases previous <;> simp [functional.seed, skip]

theorem next_terminal_from_eq (bytes : alloc.vec.Vec U8) (position next : Usize) (cp : U32)
    (decoded : unicode.decode_next bytes position = .ok (.Scalar cp next))
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.next_terminal_from bytes position cp = functional.next_terminal_valid bytes position := by
  rw [functional.next_terminal_from,functional.next_terminal_valid]
  simp only [seed_from_eq _ bytes position next cp decoded valid,
    extend_from_eq _ bytes position next cp _ decoded valid]

/-- First-code-point dispatch on a valid suffix is the standard greatest
    selection, so every property of `next_terminal` carries over. -/
theorem next_terminal_fast_eq (bytes : alloc.vec.Vec U8) (position : Usize)
    (valid : ∃ word, Rowl.Regular.Utf8From bytes.val position.val word) :
    functional.next_terminal_fast bytes position = functional.next_terminal bytes position := by
  rw [← next_terminal_valid_eq bytes position valid, functional.next_terminal_fast]
  obtain ⟨r, decoded, -⟩ := Rowl.Unicode.decode_next_total_correct bytes position
  rw [decoded, bind_ok]
  cases r with
  | Scalar cp next => exact next_terminal_from_eq bytes position next cp decoded valid
  | End => rfl
  | Error _ => rfl
end Rowl.FunctionalFast
