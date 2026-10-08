import Rowl.XsdRegex
import Rowl.Regular

/-!
The kernel module `patterns` against the regular expressions of XML Schema 1.1
(`Rowl.XsdRegex`). Lists of code point intervals stand for the code points in
them (`InSpans`); their intersections, complements among the code points up to
`#x10FFFF` and differences are exact (`complement_spec`, `subtract_spec`). The
reading of an expression's code points follows the relations of
`Rowl.XsdRegex` step by step: wherever a reading function returns a result, the
code points from its index to the index it returns are read by its production,
with a meaning that agrees with the result on the code points up to
`#x10FFFF` (`SameChars`, `SameStrings`). So the expression of
`patterns::pattern_expression` has, among the strings of code points up to
`#x10FFFF`, exactly the strings of the regular expression that the bytes
encode (`pattern_expression_spec`), and `patterns::pattern_matches` tells
whether UTF-8 text is one of them (`pattern_matches_spec`).
-/
namespace Rowl.Patterns
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open regular Rowl.Regular Rowl.XsdRegex
open scoped Computability
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
attribute [local instance low] Classical.propDecidable

/-! ### Code points and their sets -/

/-- The last code point, `#x10FFFF`. -/
abbrev last : ℕ := 1114111

theorem last_val : patterns.LAST.val = last := by simp [patterns.LAST]

theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]

theorem usize_big : 4294967295 ≤ Usize.max := by
  have := Usize.max_def
  rcases System.Platform.numBits_eq with e | e <;> simp_all [Usize.numBits]

@[simp] theorem u32_ofNat_val (n : ℕ) (h) : (U32.ofNat n h).val = n := by simp

theorem u32_eq_iff (x y : U32) : x = y ↔ x.val = y.val :=
  ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩

@[simp] theorem new_val {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

/-- The code points of a list of spans. -/
def InSpans (spans : List patterns.Span) (c : ℕ) : Prop := ∃ s ∈ spans, s.lower.val ≤ c ∧ c ≤ s.upper.val

@[simp] theorem inSpans_nil (c : ℕ) : ¬ InSpans [] c := by simp [InSpans]

@[simp] theorem inSpans_cons (s : patterns.Span) (l : List patterns.Span) (c : ℕ) :
    InSpans (s :: l) c ↔ (s.lower.val ≤ c ∧ c ≤ s.upper.val) ∨ InSpans l c := by
  simp [InSpans]

@[simp] theorem inSpans_append (a b : List patterns.Span) (c : ℕ) :
    InSpans (a ++ b) c ↔ InSpans a c ∨ InSpans b c := by
  simp only [InSpans, List.mem_append]
  constructor
  · rintro ⟨s, (m | m), h⟩
    · exact .inl ⟨s, m, h⟩
    · exact .inr ⟨s, m, h⟩
  · rintro (⟨s, m, h⟩ | ⟨s, m, h⟩)
    · exact ⟨s, .inl m, h⟩
    · exact ⟨s, .inr m, h⟩

/-- A list of spans and a set of characters have the same code points up to
    `#x10FFFF`. -/
def SameChars (spans : List patterns.Span) (C : Chars) : Prop := ∀ c, c ≤ last → (InSpans spans c ↔ c ∈ C)

/-- A string of code points up to `#x10FFFF`. -/
def Bounded (w : List ℕ) : Prop := ∀ c ∈ w, c ≤ last

/-- Two languages have the same strings of code points up to `#x10FFFF`. -/
def SameStrings (L M : Language ℕ) : Prop := ∀ w, Bounded w → (w ∈ L ↔ w ∈ M)

theorem sameStrings_refl (L : Language ℕ) : SameStrings L L := fun _ _ => Iff.rfl

theorem bounded_append {u v : List ℕ} : Bounded (u ++ v) ↔ Bounded u ∧ Bounded v := by
  simp only [Bounded, List.mem_append]
  constructor
  · intro h; exact ⟨fun c m => h c (.inl m), fun c m => h c (.inr m)⟩
  · rintro ⟨hu, hv⟩ c (m | m)
    · exact hu c m
    · exact hv c m

theorem sameStrings_add {L L' M M' : Language ℕ} (hL : SameStrings L L') (hM : SameStrings M M') :
    SameStrings (L + M) (L' + M') := by
  intro w bw
  simp only [Language.mem_add]
  rw [hL w bw, hM w bw]

theorem sameStrings_mul {L L' M M' : Language ℕ} (hL : SameStrings L L') (hM : SameStrings M M') :
    SameStrings (L * M) (L' * M') := by
  intro w bw
  simp only [Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have b := bounded_append.mp bw
    exact ⟨u, (hL u b.1).mp hu, v, (hM v b.2).mp hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    have b := bounded_append.mp bw
    exact ⟨u, (hL u b.1).mpr hu, v, (hM v b.2).mpr hv, rfl⟩

theorem sameStrings_pow {L L' : Language ℕ} (h : SameStrings L L') (n : ℕ) : SameStrings (L ^ n) (L' ^ n) := by
  induction n with
  | zero => simpa using sameStrings_refl 1
  | succ n ih => simpa [pow_succ] using sameStrings_mul ih h

theorem sameStrings_star {L L' : Language ℕ} (h : SameStrings L L') : SameStrings (L∗) (L'∗) := by
  intro w bw
  rw [Language.kstar_eq_iSup_pow, Language.kstar_eq_iSup_pow]
  simp only [Language.mem_iSup]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (sameStrings_pow h n w bw).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (sameStrings_pow h n w bw).mpr hn⟩

theorem sameStrings_repeats {L L' : Language ℕ} (h : SameStrings L L') (n : ℕ) (m : Option ℕ) :
    SameStrings (Repeats L n m) (Repeats L' n m) := by
  cases m with
  | none => exact sameStrings_mul (sameStrings_pow h n) (sameStrings_star h)
  | some m =>
    intro w bw
    simp only [Repeats, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, lo, hi, hk⟩
      exact ⟨k, lo, hi, (sameStrings_pow h k w bw).mp hk⟩
    · rintro ⟨k, lo, hi, hk⟩
      exact ⟨k, lo, hi, (sameStrings_pow h k w bw).mpr hk⟩

/-- The strings of one character of a list of spans. -/
def spanStrings (spans : List patterns.Span) : Language ℕ := {w | ∃ c, w = [c] ∧ InSpans spans c}

theorem sameStrings_single {spans : List patterns.Span} {C : Chars} (h : SameChars spans C) :
    SameStrings (spanStrings spans) (single C) := by
  intro w bw
  simp only [spanStrings, single, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, rfl, hc⟩
    exact ⟨c, (h c (bw c (by simp))).mp hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, rfl, (h c (bw c (by simp))).mpr hc⟩

/-! ### Operations on spans -/

theorem span_eq (lower upper : U32) : patterns.span lower upper = .ok ⟨lower, upper⟩ := rfl

theorem append_from_spec (spans : alloc.vec.Vec patterns.Span) (index : Usize) (out : alloc.vec.Vec patterns.Span) :
    ∃ r, patterns.append_from spans index out = .ok r ∧
      ∀ v, r = some v → v.val = out.val ++ spans.val.drop index.val := by
  rw [patterns.append_from]
  by_cases inside : index.val < spans.val.length
  · have lookup : spans.index_usize index = .ok spans.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases room : out.val.length < Usize.max
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out ⟨spans.val[index.val].lower, spans.val[index.val].upper⟩ room)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, spec⟩ := append_from_spec spans next pushed
      refine ⟨r, ?_, ?_⟩
      · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, usize_max_val, room,
          alloc.vec.Vec.index_slice_index, lookup, bind_ok, span_eq, push, advance, run]
      · intro v hv
        rw [spec v hv, contents, nextIndex, List.drop_eq_getElem_cons inside]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
    · refine ⟨none, ?_, by simp⟩
      simp [UScalar.lt_equiv, inside, usize_max_val, room]
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv
    simp only [Option.some.injEq] at hv
    subst hv
    simp [List.drop_eq_nil_iff.mpr (show spans.val.length ≤ index.val by omega)]
termination_by spans.val.length - index.val
decreasing_by all_goals omega

theorem meet_from_spec (spans : alloc.vec.Vec patterns.Span) (lower upper : U32) (index : Usize)
    (out : alloc.vec.Vec patterns.Span) :
    ∃ r, patterns.meet_from spans lower upper index out = .ok r ∧
      ∀ v, r = some v → ∀ c, InSpans v.val c ↔
        InSpans out.val c ∨ (InSpans (spans.val.drop index.val) c ∧ lower.val ≤ c ∧ c ≤ upper.val) := by
  rw [patterns.meet_from]
  by_cases inside : index.val < spans.val.length
  · have lookup : spans.index_usize index = .ok spans.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    set s := spans.val[index.val] with hs
    obtain ⟨low, lowRun, lowVal⟩ : ∃ low : U32,
        (if s.lower.val < lower.val then (ok lower : Result U32) else ok s.lower) = ok low ∧
          low.val = max s.lower.val lower.val := by
      split <;> rename_i h <;> exact ⟨_, rfl, by omega⟩
    obtain ⟨high, highRun, highVal⟩ : ∃ high : U32,
        (if upper.val < s.upper.val then (ok upper : Result U32) else ok s.upper) = ok high ∧
          high.val = min s.upper.val upper.val := by
      split <;> rename_i h <;> exact ⟨_, rfl, by omega⟩
    have drop : spans.val.drop index.val = s :: spans.val.drop next.val := by
      rw [nextIndex, List.drop_eq_getElem_cons inside]
    by_cases fits : low.val ≤ high.val
    · by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out ⟨low, high⟩ room)
        obtain ⟨r, run, spec⟩ := meet_from_spec spans lower upper next pushed
        refine ⟨r, ?_, ?_⟩
        · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
            lookup, bind_ok, lowRun, highRun, UScalar.le_equiv, fits, usize_max_val, room, decide_true,
            Bool.and_self, span_eq, push, advance, run]
        · intro v hv c
          rw [spec v hv c, contents, drop]
          simp only [inSpans_append, inSpans_cons, inSpans_nil, or_false]
          rw [lowVal, highVal]
          constructor
          · rintro ((h | h) | h)
            · exact .inl h
            · exact .inr ⟨.inl (by omega), by omega, by omega⟩
            · exact .inr ⟨.inr h.1, h.2⟩
          · rintro (h | ⟨(h | h), lo, hi⟩)
            · exact .inl (.inl h)
            · exact .inl (.inr (by omega))
            · exact .inr ⟨h, lo, hi⟩
      · refine ⟨none, ?_, by simp⟩
        simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
          lookup, bind_ok, lowRun, highRun, UScalar.le_equiv, fits, usize_max_val, room, decide_true,
          decide_false, Bool.and_false, Bool.false_eq_true]
    · obtain ⟨r, run, spec⟩ := meet_from_spec spans lower upper next out
      refine ⟨r, ?_, ?_⟩
      · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
          lookup, bind_ok, lowRun, highRun, UScalar.le_equiv, fits, decide_false, Bool.false_and,
          Bool.false_eq_true, advance, run]
      · intro v hv c
        rw [spec v hv c, drop]
        simp only [inSpans_cons]
        rw [lowVal, highVal] at fits
        constructor
        · rintro (h | ⟨h, lo, hi⟩)
          · exact .inl h
          · exact .inr ⟨.inr h, lo, hi⟩
        · rintro (h | ⟨(h | h), lo, hi⟩)
          · exact .inl h
          · omega
          · exact .inr ⟨h, lo, hi⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv c
    simp only [Option.some.injEq] at hv
    subst hv
    simp [List.drop_eq_nil_iff.mpr (show spans.val.length ≤ index.val by omega)]
termination_by spans.val.length - index.val
decreasing_by all_goals omega

theorem without_lower (spans : alloc.vec.Vec patterns.Span) (lower : U32) :
    ∃ b, (if 0#u32 < lower then Std.bind (lower - 1#u32) fun i =>
        patterns.meet_from spans 0#u32 i 0#usize (alloc.vec.Vec.new patterns.Span)
      else ok (some (alloc.vec.Vec.new patterns.Span))) = .ok b ∧
      ∀ v, b = some v → ∀ c, InSpans v.val c ↔ InSpans spans.val c ∧ c < lower.val := by
  by_cases pos : 0 < lower.val
  · obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists (U32.sub_spec (x := lower) (y := 1#u32) (by scalar_tac))
    obtain ⟨b, run, spec⟩ := meet_from_spec spans 0#u32 i 0#usize (alloc.vec.Vec.new patterns.Span)
    refine ⟨b, by simp [UScalar.lt_equiv, pos, iRun, run], ?_⟩
    intro v hv c
    rw [spec v hv c]
    have : i.val = lower.val - 1 := by simp at iVal; omega
    simp only [new_val, inSpans_nil, false_or, List.drop_zero, show (0#usize : Usize).val = 0 from rfl,
      show (0#u32 : U32).val = 0 from rfl]
    constructor
    · rintro ⟨h, _, hi⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, lt⟩; exact ⟨h, by omega, by omega⟩
  · refine ⟨some (alloc.vec.Vec.new patterns.Span), by simp [UScalar.lt_equiv, pos], ?_⟩
    intro v hv c
    simp only [Option.some.injEq] at hv
    subst hv
    simp only [new_val, inSpans_nil, false_iff, not_and]
    intro _; omega

theorem without_upper (spans : alloc.vec.Vec patterns.Span) (upper : U32) (out : alloc.vec.Vec patterns.Span) :
    ∃ r, (if upper < patterns.LAST then Std.bind (upper + 1#u32) fun i =>
        patterns.meet_from spans i patterns.LAST 0#usize out
      else ok (some out)) = .ok r ∧
      ∀ v, r = some v → ∀ c, InSpans v.val c ↔ InSpans out.val c ∨ (InSpans spans.val c ∧ upper.val < c ∧ c ≤ last) := by
  by_cases top : upper.val < last
  · obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists (U32.add_spec (x := upper) (y := 1#u32)
      (by have : upper.val < 1114111 := top; scalar_tac))
    obtain ⟨r, run, spec⟩ := meet_from_spec spans i patterns.LAST 0#usize out
    refine ⟨r, by simp [UScalar.lt_equiv, last_val, top, iRun, run], ?_⟩
    intro v hv c
    rw [spec v hv c, last_val]
    have : i.val = upper.val + 1 := by simpa using iVal
    simp only [List.drop_zero, show (0#usize : Usize).val = 0 from rfl]
    constructor
    · rintro (h | ⟨h, lo, hi⟩)
      · exact .inl h
      · exact .inr ⟨h, by omega, hi⟩
    · rintro (h | ⟨h, gt, hi⟩)
      · exact .inl h
      · exact .inr ⟨h, by omega, hi⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, last_val, top], ?_⟩
    intro v hv c
    simp only [Option.some.injEq] at hv
    subst hv
    constructor
    · intro h; exact .inl h
    · rintro (h | ⟨_, gt, hi⟩)
      · exact h
      · omega

theorem without_spec (spans : alloc.vec.Vec patterns.Span) (lower upper : U32) :
    ∃ r, patterns.without spans lower upper = .ok r ∧
      ∀ v, r = some v → ∀ c, InSpans v.val c ↔ InSpans spans.val c ∧ (c < lower.val ∨ (upper.val < c ∧ c ≤ last)) := by
  rw [patterns.without]
  obtain ⟨b, bRun, bSpec⟩ := without_lower spans lower
  simp only [bRun, bind_ok]
  cases b with
  | none => exact ⟨none, by simp, by simp⟩
  | some bv =>
    obtain ⟨r, run, spec⟩ := without_upper spans upper bv
    refine ⟨r, by simpa using run, ?_⟩
    intro v hv c
    rw [spec v hv c, bSpec bv rfl c]
    constructor
    · rintro (⟨h, lt⟩ | ⟨h, gt, hi⟩)
      · exact ⟨h, .inl lt⟩
      · exact ⟨h, .inr ⟨gt, hi⟩⟩
    · rintro ⟨h, lt | ⟨gt, hi⟩⟩
      · exact .inl ⟨h, lt⟩
      · exact .inr ⟨h, gt, hi⟩

theorem without_from_spec (spans : alloc.vec.Vec patterns.Span) (index : Usize) (rest : alloc.vec.Vec patterns.Span)
    (bound : ∀ c, InSpans rest.val c → c ≤ last) :
    ∃ r, patterns.without_from spans index rest = .ok r ∧
      ∀ v, r = some v → ∀ c, InSpans v.val c ↔ InSpans rest.val c ∧ ¬ InSpans (spans.val.drop index.val) c := by
  rw [patterns.without_from]
  by_cases inside : index.val < spans.val.length
  · have lookup : spans.index_usize index = .ok spans.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    set s := spans.val[index.val] with hs
    have drop : spans.val.drop index.val = s :: spans.val.drop next.val := by
      rw [nextIndex, List.drop_eq_getElem_cons inside]
    obtain ⟨w, wRun, wSpec⟩ := without_spec rest s.lower s.upper
    cases w with
    | none =>
      refine ⟨none, ?_, by simp⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, wRun]
    | some wv =>
      have wIff := wSpec wv rfl
      obtain ⟨r, run, spec⟩ := without_from_spec spans next wv (fun c h => ((wIff c).mp h).1 |> bound c)
      refine ⟨r, ?_, ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, wRun, advance, run]
      · intro v hv c
        rw [spec v hv c, wIff c, drop, inSpans_cons]
        constructor
        · rintro ⟨⟨h, out⟩, notLater⟩
          refine ⟨h, ?_⟩
          rintro (⟨lo, hi⟩ | later)
          · omega
          · exact notLater later
        · rintro ⟨h, notIn⟩
          refine ⟨⟨h, ?_⟩, fun later => notIn (.inr later)⟩
          have := bound c h
          by_cases lt : c < s.lower.val
          · exact .inl lt
          · exact .inr ⟨by by_contra le; exact notIn (.inl ⟨by omega, by omega⟩), this⟩
  · refine ⟨some rest, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv c
    simp only [Option.some.injEq] at hv
    subst hv
    simp [List.drop_eq_nil_iff.mpr (show spans.val.length ≤ index.val by omega)]
termination_by spans.val.length - index.val
decreasing_by all_goals omega

theorem complement_spec (spans : alloc.vec.Vec patterns.Span) :
    ∃ r, patterns.complement spans = .ok r ∧
      ∀ v, r = some v → ∀ c, InSpans v.val c ↔ c ≤ last ∧ ¬ InSpans spans.val c := by
  rw [patterns.complement]
  have room : (alloc.vec.Vec.new patterns.Span).val.length < Usize.max := by simp; scalar_tac
  obtain ⟨all, push, contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new patterns.Span) ⟨0#u32, patterns.LAST⟩ room)
  have allIff : ∀ c, InSpans all.val c ↔ c ≤ last := by
    intro c
    rw [contents]
    simp [last_val]
  obtain ⟨r, run, spec⟩ := without_from_spec spans 0#usize all (fun c h => (allIff c).mp h)
  refine ⟨r, by simp [span_eq, push, run], ?_⟩
  intro v hv c
  rw [spec v hv c, allIff c]
  simp

theorem meet_all_spec (left right : alloc.vec.Vec patterns.Span) (index : Usize) (out : alloc.vec.Vec patterns.Span) :
    ∃ r, patterns.meet_all left right index out = .ok r ∧
      ∀ v, r = some v → ∀ c, InSpans v.val c ↔
        InSpans out.val c ∨ (InSpans left.val c ∧ InSpans (right.val.drop index.val) c) := by
  rw [patterns.meet_all]
  by_cases inside : index.val < right.val.length
  · have lookup : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    set s := right.val[index.val] with hs
    have drop : right.val.drop index.val = s :: right.val.drop next.val := by
      rw [nextIndex, List.drop_eq_getElem_cons inside]
    obtain ⟨m, mRun, mSpec⟩ := meet_from_spec left s.lower s.upper 0#usize out
    cases m with
    | none =>
      refine ⟨none, ?_, by simp⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, mRun]
    | some mv =>
      obtain ⟨r, run, spec⟩ := meet_all_spec left right next mv
      refine ⟨r, ?_, ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, mRun, advance, run]
      · intro v hv c
        rw [spec v hv c, mSpec mv rfl c, drop]
        simp only [List.drop_zero, inSpans_cons]
        constructor
        · rintro ((h | ⟨h, lo, hi⟩) | ⟨h, later⟩)
          · exact .inl h
          · exact .inr ⟨h, .inl ⟨lo, hi⟩⟩
          · exact .inr ⟨h, .inr later⟩
        · rintro (h | ⟨h, (⟨lo, hi⟩ | later)⟩)
          · exact .inl (.inl h)
          · exact .inl (.inr ⟨h, lo, hi⟩)
          · exact .inr ⟨h, later⟩
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], ?_⟩
    intro v hv c
    simp only [Option.some.injEq] at hv
    subst hv
    simp [List.drop_eq_nil_iff.mpr (show right.val.length ≤ index.val by omega)]
termination_by right.val.length - index.val
decreasing_by all_goals omega

theorem subtract_spec (left right : alloc.vec.Vec patterns.Span) :
    ∃ r, patterns.subtract left right = .ok r ∧
      ∀ v, r = some v → ∀ c, InSpans v.val c ↔ InSpans left.val c ∧ c ≤ last ∧ ¬ InSpans right.val c := by
  rw [patterns.subtract]
  obtain ⟨o, oRun, oSpec⟩ := complement_spec right
  cases o with
  | none => exact ⟨none, by simp [oRun], by simp⟩
  | some ov =>
    obtain ⟨r, run, spec⟩ := meet_all_spec left ov 0#usize (alloc.vec.Vec.new patterns.Span)
    refine ⟨r, by simp [oRun, run], ?_⟩
    intro v hv c
    rw [spec v hv c]
    simp only [new_val, inSpans_nil, false_or, List.drop_zero,
      show (0#usize : Usize).val = 0 from rfl]
    rw [oSpec ov rfl c]

/-! ### Fixed sets of characters -/

theorem one_spec (c : U32) : ∃ r, patterns.one c = .ok r ∧ ∀ x, InSpans r.val x ↔ x = c.val := by
  rw [patterns.one]
  have room : (alloc.vec.Vec.new patterns.Span).val.length < Usize.max := by simp; scalar_tac
  obtain ⟨r, push, contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new patterns.Span) ⟨c, c⟩ room)
  refine ⟨r, by simp [span_eq, push], ?_⟩
  intro x
  rw [contents]
  simp only [new_val, List.nil_append, inSpans_cons, inSpans_nil, or_false]
  omega

theorem two_spec (c d : U32) : ∃ r, patterns.two c d = .ok r ∧ ∀ x, InSpans r.val x ↔ x = c.val ∨ x = d.val := by
  rw [patterns.two]
  have room : (alloc.vec.Vec.new patterns.Span).val.length < Usize.max := by simp; scalar_tac
  obtain ⟨r1, push1, contents1⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new patterns.Span) ⟨c, c⟩ room)
  have room2 : r1.val.length < Usize.max := by rw [contents1]; simp; scalar_tac
  obtain ⟨r2, push2, contents2⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec r1 ⟨d, d⟩ room2)
  refine ⟨r2, by simp [span_eq, push1, push2], ?_⟩
  intro x
  rw [contents2, contents1]
  simp only [new_val, List.nil_append, List.cons_append, inSpans_cons, inSpans_nil, or_false]
  omega

@[local step] theorem span_spec (lower upper : U32) : patterns.span lower upper ⦃ s => s = ⟨lower, upper⟩ ⦄ := by
  simp [patterns.span]

theorem spaces_val : patterns.spaces ⦃ r => r.val = [⟨9#u32, 10#u32⟩, ⟨13#u32, 13#u32⟩, ⟨32#u32, 32#u32⟩] ⦄ := by
  unfold patterns.spaces
  step*

theorem name_starts_val : patterns.name_starts ⦃ r => r.val =
    [⟨58#u32, 58#u32⟩, ⟨65#u32, 90#u32⟩, ⟨95#u32, 95#u32⟩, ⟨97#u32, 122#u32⟩, ⟨192#u32, 214#u32⟩,
      ⟨216#u32, 246#u32⟩, ⟨248#u32, 767#u32⟩, ⟨880#u32, 893#u32⟩, ⟨895#u32, 8191#u32⟩, ⟨8204#u32, 8205#u32⟩,
      ⟨8304#u32, 8591#u32⟩, ⟨11264#u32, 12271#u32⟩, ⟨12289#u32, 55295#u32⟩, ⟨63744#u32, 64975#u32⟩,
      ⟨65008#u32, 65533#u32⟩, ⟨65536#u32, 983039#u32⟩] ⦄ := by
  have big := usize_big
  unfold patterns.name_starts
  step* <;> simp_all <;> omega

theorem name_chars_val : patterns.name_chars ⦃ r => r.val =
    [⟨58#u32, 58#u32⟩, ⟨65#u32, 90#u32⟩, ⟨95#u32, 95#u32⟩, ⟨97#u32, 122#u32⟩, ⟨192#u32, 214#u32⟩,
      ⟨216#u32, 246#u32⟩, ⟨248#u32, 767#u32⟩, ⟨880#u32, 893#u32⟩, ⟨895#u32, 8191#u32⟩, ⟨8204#u32, 8205#u32⟩,
      ⟨8304#u32, 8591#u32⟩, ⟨11264#u32, 12271#u32⟩, ⟨12289#u32, 55295#u32⟩, ⟨63744#u32, 64975#u32⟩,
      ⟨65008#u32, 65533#u32⟩, ⟨65536#u32, 983039#u32⟩, ⟨45#u32, 46#u32⟩, ⟨48#u32, 57#u32⟩, ⟨183#u32, 183#u32⟩,
      ⟨768#u32, 879#u32⟩, ⟨8255#u32, 8256#u32⟩] ⦄ := by
  have big := usize_big
  unfold patterns.name_chars
  have ⟨ns, nsRun, nsVal⟩ := WP.spec_imp_exists name_starts_val
  simp only [nsRun, bind_tc_ok]
  step* <;> simp_all <;> omega

theorem wildcard_val : patterns.wildcard ⦃ r => r.val = [⟨0#u32, 9#u32⟩, ⟨11#u32, 12#u32⟩, ⟨14#u32, patterns.LAST⟩] ⦄ := by
  unfold patterns.wildcard
  step*

theorem spaces_iff (c : ℕ) :
    InSpans [⟨9#u32, 10#u32⟩, ⟨13#u32, 13#u32⟩, ⟨32#u32, 32#u32⟩] c ↔ XmlGrammar.IsSpace c := by
  simp only [inSpans_cons, inSpans_nil, or_false, XmlGrammar.IsSpace]
  simp only [u32_ofNat_val]; omega

theorem name_starts_iff (c : ℕ) :
    InSpans [⟨58#u32, 58#u32⟩, ⟨65#u32, 90#u32⟩, ⟨95#u32, 95#u32⟩, ⟨97#u32, 122#u32⟩, ⟨192#u32, 214#u32⟩,
      ⟨216#u32, 246#u32⟩, ⟨248#u32, 767#u32⟩, ⟨880#u32, 893#u32⟩, ⟨895#u32, 8191#u32⟩, ⟨8204#u32, 8205#u32⟩,
      ⟨8304#u32, 8591#u32⟩, ⟨11264#u32, 12271#u32⟩, ⟨12289#u32, 55295#u32⟩, ⟨63744#u32, 64975#u32⟩,
      ⟨65008#u32, 65533#u32⟩, ⟨65536#u32, 983039#u32⟩] c ↔ XmlGrammar.NameStartChar c := by
  simp only [inSpans_cons, inSpans_nil, or_false, XmlGrammar.NameStartChar]
  simp only [u32_ofNat_val]; omega

theorem name_chars_iff (c : ℕ) :
    InSpans [⟨58#u32, 58#u32⟩, ⟨65#u32, 90#u32⟩, ⟨95#u32, 95#u32⟩, ⟨97#u32, 122#u32⟩, ⟨192#u32, 214#u32⟩,
      ⟨216#u32, 246#u32⟩, ⟨248#u32, 767#u32⟩, ⟨880#u32, 893#u32⟩, ⟨895#u32, 8191#u32⟩, ⟨8204#u32, 8205#u32⟩,
      ⟨8304#u32, 8591#u32⟩, ⟨11264#u32, 12271#u32⟩, ⟨12289#u32, 55295#u32⟩, ⟨63744#u32, 64975#u32⟩,
      ⟨65008#u32, 65533#u32⟩, ⟨65536#u32, 983039#u32⟩, ⟨45#u32, 46#u32⟩, ⟨48#u32, 57#u32⟩, ⟨183#u32, 183#u32⟩,
      ⟨768#u32, 879#u32⟩, ⟨8255#u32, 8256#u32⟩] c ↔ XmlGrammar.NameChar c := by
  simp only [inSpans_cons, inSpans_nil, or_false, XmlGrammar.NameChar, XmlGrammar.NameStartChar]
  simp only [u32_ofNat_val]; omega

theorem wildcard_iff (c : ℕ) :
    InSpans [⟨0#u32, 9#u32⟩, ⟨11#u32, 12#u32⟩, ⟨14#u32, patterns.LAST⟩] c ↔ c ≤ last ∧ c ≠ 10 ∧ c ≠ 13 := by
  simp only [inSpans_cons, inSpans_nil, or_false, last_val, last]
  simp only [u32_ofNat_val]; omega

/-! ### Escapes -/

theorem escaped_char_spec (x : U32) :
    ∃ r, patterns.escaped_char x = .ok r ∧ r.map (·.val) = escapedChar x.val := by
  unfold patterns.escaped_char escapedChar
  simp only [u32_eq_iff, u32_ofNat_val, Bool.or_eq_true, decide_eq_true_eq]
  split_ifs <;> simp_all

theorem multi_spans_spec (x : U32) :
    ∃ r, patterns.multi_spans x = .ok r ∧
      ∀ spans, r = some spans → ∀ U : UnicodeData, ∃ C, multiChars U x.val = some C ∧ SameChars spans.val C := by
  obtain ⟨sp, spRun, spVal⟩ := WP.spec_imp_exists spaces_val
  obtain ⟨ns, nsRun, nsVal⟩ := WP.spec_imp_exists name_starts_val
  obtain ⟨nc, ncRun, ncVal⟩ := WP.spec_imp_exists name_chars_val
  obtain ⟨csp, cspRun, cspSpec⟩ := complement_spec sp
  obtain ⟨cns, cnsRun, cnsSpec⟩ := complement_spec ns
  obtain ⟨cnc, cncRun, cncSpec⟩ := complement_spec nc
  unfold patterns.multi_spans multiChars
  simp only [u32_eq_iff, u32_ofNat_val]
  by_cases h1 : x.val = 115
  · refine ⟨some sp, by simp [h1, spRun], ?_⟩
    rintro spans ⟨⟩ U
    refine ⟨{c | XmlGrammar.IsSpace c}, by simp [h1], ?_⟩
    intro c _
    rw [spVal, spaces_iff]
    rfl
  by_cases h2 : x.val = 83
  · refine ⟨csp, by simp [h2, spRun, cspRun], ?_⟩
    intro spans hs U
    refine ⟨{c | ¬ XmlGrammar.IsSpace c}, by simp [h2], ?_⟩
    intro c hc
    rw [cspSpec spans hs c, spVal, spaces_iff]
    simp [hc]
  by_cases h3 : x.val = 105
  · refine ⟨some ns, by simp [h1, h2, h3, nsRun], ?_⟩
    rintro spans ⟨⟩ U
    refine ⟨{c | XmlGrammar.NameStartChar c}, by simp [h3], ?_⟩
    intro c _
    rw [nsVal, name_starts_iff]
    rfl
  by_cases h4 : x.val = 73
  · refine ⟨cns, by simp [h1, h2, h3, h4, nsRun, cnsRun], ?_⟩
    intro spans hs U
    refine ⟨{c | ¬ XmlGrammar.NameStartChar c}, by simp [h4], ?_⟩
    intro c hc
    rw [cnsSpec spans hs c, nsVal, name_starts_iff]
    simp [hc]
  by_cases h5 : x.val = 99
  · refine ⟨some nc, by simp [h1, h2, h3, h4, h5, ncRun], ?_⟩
    rintro spans ⟨⟩ U
    refine ⟨{c | XmlGrammar.NameChar c}, by simp [h5], ?_⟩
    intro c _
    rw [ncVal, name_chars_iff]
    rfl
  by_cases h6 : x.val = 67
  · refine ⟨cnc, by simp [h1, h2, h3, h4, h5, h6, ncRun, cncRun], ?_⟩
    intro spans hs U
    refine ⟨{c | ¬ XmlGrammar.NameChar c}, by simp [h6], ?_⟩
    intro c hc
    rw [cncSpec spans hs c, ncVal, name_chars_iff]
    simp [hc]
  · exact ⟨none, by simp [h1, h2, h3, h4, h5, h6], by simp⟩

/-! ### Reading code points -/

/-- The code points of a vector, from an index on. -/
def tail (cps : alloc.vec.Vec U32) (i : ℕ) : List ℕ := (cps.val.map (·.val)).drop i

theorem tail_cons (cps : alloc.vec.Vec U32) {i : ℕ} (inside : i < cps.val.length) :
    tail cps i = cps.val[i].val :: tail cps (i + 1) := by
  unfold tail
  rw [List.drop_eq_getElem_cons (by simpa using inside)]
  simp

theorem tail_end (cps : alloc.vec.Vec U32) {i : ℕ} (outside : cps.val.length ≤ i) : tail cps i = [] := by
  unfold tail
  simp only [List.drop_eq_nil_iff, List.length_map]
  exact outside

theorem tail_head (cps : alloc.vec.Vec U32) (i : ℕ) :
    (tail cps i).head? = if h : i < cps.val.length then some cps.val[i].val else none := by
  split
  · rename_i h; rw [tail_cons cps h]; rfl
  · rename_i h; rw [tail_end cps (by omega)]; rfl

theorem is_at_spec (cps : alloc.vec.Vec U32) (i : Usize) (v : U32) :
    patterns.is_at cps i v = .ok (decide ((tail cps i.val).head? = some v.val)) := by
  rw [patterns.is_at, tail_head]
  by_cases inside : i.val < cps.val.length
  · have lookup : cps.index_usize i = .ok cps.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, u32_eq_iff]
  · simp [UScalar.lt_equiv, inside]

theorem is_at_true {cps : alloc.vec.Vec U32} {i : Usize} {v : U32}
    (h : (tail cps i.val).head? = some v.val) : i.val < cps.val.length ∧ tail cps i.val = v.val :: tail cps (i.val + 1) := by
  rw [tail_head] at h
  split at h
  · rename_i inside
    simp only [Option.some.injEq] at h
    exact ⟨inside, by rw [tail_cons cps inside, h]⟩
  · simp at h

theorem pair_at_spec (cps : alloc.vec.Vec U32) (i : Usize) (a b : U32) :
    ∃ r, patterns.pair_at cps i a b = .ok r ∧ (r = true ↔ (tail cps i.val).take 2 = [a.val, b.val]) := by
  rw [patterns.pair_at]
  by_cases inside : i.val < cps.val.length
  · have lookup : cps.index_usize i = .ok cps.val[i.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    rw [tail_cons cps inside]
    by_cases first : cps.val[i.val].val = a.val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = i.val + 1 := by simpa using nextValue
      refine ⟨decide ((tail cps next.val).head? = some b.val), by simp [UScalar.lt_equiv, inside,
        alloc.vec.Vec.index_slice_index, lookup, u32_eq_iff, first, advance, is_at_spec], ?_⟩
      rw [nextIndex, tail_head]
      split
      · rename_i h; rw [tail_cons cps h]; simp [first]
      · rename_i h; rw [tail_end cps (by omega)]; simp
    · refine ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, u32_eq_iff, first], ?_⟩
      simp [first]
  · refine ⟨false, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [tail_end cps (by omega)]
    simp

theorem take_two_iff {s : List ℕ} {a b : ℕ} : s.take 2 = [a, b] ↔ ∃ rest, s = a :: b :: rest := by
  constructor
  · intro h
    match s, h with
    | x :: y :: rest, h => simp at h; exact ⟨rest, by rw [h.1, h.2]⟩
  · rintro ⟨rest, rfl⟩; rfl

theorem lookup_at {cps : alloc.vec.Vec U32} {i : Usize} (inside : i.val < cps.val.length) :
    cps.index_usize i = .ok cps.val[i.val] := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]

theorem add_one {i : Usize} {n : ℕ} (h : i.val < n) (hn : n ≤ Usize.max) :
    ∃ j : Usize, i + 1#usize = ok j ∧ j.val = i.val + 1 := by
  obtain ⟨j, run, val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
  exact ⟨j, run, by simpa using val⟩

theorem add_two {i : Usize} {n : ℕ} (h : i.val + 1 < n) (hn : n ≤ Usize.max) :
    ∃ j : Usize, i + 2#usize = ok j ∧ j.val = i.val + 2 := by
  obtain ⟨j, run, val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i) (y := 2#usize) (by scalar_tac))
  exact ⟨j, run, by simpa using val⟩

theorem single_char_spec (cps : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, patterns.single_char cps i = .ok r ∧ ∀ c j, r = some (c, j) →
      SingleChar (tail cps i.val) c.val (tail cps j.val) ∧ i.val < j.val ∧ j.val ≤ cps.val.length := by
  rw [patterns.single_char]
  have bound := cps.property
  by_cases inside : i.val < cps.val.length
  · have here := tail_cons cps inside
    by_cases slash : cps.val[i.val].val = 92
    · obtain ⟨n1, a1, v1⟩ := add_one inside bound
      by_cases more : i.val + 1 < cps.val.length
      · have lookup1 : cps.index_usize n1 = .ok cps.val[i.val + 1] := by
          simp [alloc.vec.Vec.index_usize, v1, List.getElem?_eq_getElem more]
        obtain ⟨e, eRun, eVal⟩ := escaped_char_spec cps.val[i.val + 1]
        cases e with
        | none =>
          refine ⟨none, ?_, by simp⟩
          simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup_at inside, u32_eq_iff, slash,
            a1, v1, more, lookup1, eRun]
        | some d =>
          obtain ⟨n2, a2, v2⟩ := add_two more bound
          refine ⟨some (d, n2), ?_, ?_⟩
          · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup_at inside, u32_eq_iff, slash,
              a1, v1, more, lookup1, eRun, a2]
          · intro c j h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨?_, by omega, by omega⟩
            rw [here, slash, tail_cons cps more, v2]
            exact .escape (by simpa using eVal.symm)
      · refine ⟨none, ?_, by simp⟩
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup_at inside, u32_eq_iff, slash, a1, v1,
          more]
    · obtain ⟨n1, a1, v1⟩ := add_one inside bound
      by_cases bracket : cps.val[i.val].val = 91 ∨ cps.val[i.val].val = 93
      · refine ⟨none, ?_, by simp⟩
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup_at inside, u32_eq_iff, slash, bracket]
      · refine ⟨some (cps.val[i.val], n1), ?_, ?_⟩
        · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
            lookup_at inside, bind_ok, u32_eq_iff]
          simp only [not_or] at bracket
          simp [slash, bracket.1, bracket.2, a1]
        · intro c j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, by omega, by omega⟩
          rw [here, v1]
          simp only [not_or] at bracket
          exact .plain slash bracket.1 bracket.2
  · refine ⟨none, by simp [UScalar.lt_equiv, inside], by simp⟩

theorem escape_letter_spec (cps : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, patterns.escape_letter cps i = .ok r ∧ ∀ x, r = some x →
      i.val + 1 < cps.val.length ∧ tail cps i.val = 92 :: x.val :: tail cps (i.val + 2) := by
  rw [patterns.escape_letter]
  have bound := cps.property
  by_cases inside : i.val < cps.val.length
  · by_cases slash : cps.val[i.val].val = 92
    · obtain ⟨n1, a1, v1⟩ := add_one inside bound
      by_cases more : i.val + 1 < cps.val.length
      · have lookup1 : cps.index_usize n1 = .ok cps.val[i.val + 1] := by
          simp [alloc.vec.Vec.index_usize, v1, List.getElem?_eq_getElem more]
        refine ⟨if (cps.val[i.val + 1].val = 115 ∨ cps.val[i.val + 1].val = 83 ∨ cps.val[i.val + 1].val = 105 ∨
          cps.val[i.val + 1].val = 73 ∨ cps.val[i.val + 1].val = 99 ∨ cps.val[i.val + 1].val = 67 ∨
          cps.val[i.val + 1].val = 100 ∨ cps.val[i.val + 1].val = 68 ∨ cps.val[i.val + 1].val = 119 ∨
          cps.val[i.val + 1].val = 87 ∨ cps.val[i.val + 1].val = 112 ∨ cps.val[i.val + 1].val = 80)
          then some cps.val[i.val + 1] else none, ?_, ?_⟩
        · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
            lookup_at inside, bind_ok, u32_eq_iff, slash, a1, v1, more, lookup1, patterns.class_letter]
          simp only [u32_ofNat_val, Bool.or_eq_true, decide_eq_true_eq]
          split_ifs <;> simp_all
        · intro x hx
          split at hx
          · simp only [Option.some.injEq] at hx
            subst hx
            refine ⟨more, ?_⟩
            rw [tail_cons cps inside, slash, tail_cons cps more]
          · simp at hx
      · refine ⟨none, ?_, by simp⟩
        simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup_at inside, u32_eq_iff, slash, a1, v1,
          more]
    · refine ⟨none, ?_, by simp⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup_at inside, u32_eq_iff, slash]
  · refine ⟨none, by simp [UScalar.lt_equiv, inside], by simp⟩

theorem one_chars {r : alloc.vec.Vec patterns.Span} {c : U32} (h : ∀ x, InSpans r.val x ↔ x = c.val) :
    SameChars r.val ({c.val} : Chars) := fun x _ => by rw [h x]; rfl

theorem two_chars {r : alloc.vec.Vec patterns.Span} {c d : U32} (h : ∀ x, InSpans r.val x ↔ x = c.val ∨ x = d.val) :
    SameChars r.val ({c.val, d.val} : Chars) := fun x _ => by rw [h x]; simp

theorem is_at_of {cps : alloc.vec.Vec U32} {i : Usize} {v : U32} {b : Bool}
    (h : b = decide ((tail cps i.val).head? = some v.val)) : patterns.is_at cps i v = ok b := by
  rw [is_at_spec, h]

theorem pair_at_of {cps : alloc.vec.Vec U32} {i : Usize} {a b : U32} {r : Bool}
    (h : r = decide ((tail cps i.val).take 2 = [a.val, b.val])) : patterns.pair_at cps i a b = ok r := by
  obtain ⟨r', run, spec⟩ := pair_at_spec cps i a b
  rw [run, h]
  cases r' with
  | true => simp [spec.mp rfl]
  | false =>
    have : ¬ (tail cps i.val).take 2 = [a.val, b.val] := fun e => by simpa using spec.mpr e
    simp [this]

theorem part_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, patterns.part cps i = .ok r ∧ ∀ spans j, r = some (spans, j) →
      ∃ C, Part U (tail cps i.val) C (tail cps j.val) ∧ SameChars spans.val C ∧ i.val < j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.part]
  have bound := cps.property
  obtain ⟨e, eRun, eSpec⟩ := escape_letter_spec cps i
  simp only [eRun, bind_ok]
  cases e with
  | some x =>
    obtain ⟨more, here⟩ := eSpec x rfl
    obtain ⟨m, mRun, mSpec⟩ := multi_spans_spec x
    simp only [mRun, bind_ok]
    cases m with
    | none => exact ⟨none, rfl, by simp⟩
    | some spans =>
      obtain ⟨n2, a2, v2⟩ := add_two more bound
      refine ⟨some (spans, n2), by simp only [a2, bind_ok], ?_⟩
      intro sp j h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨C, hC, same⟩ := mSpec _ rfl U
      refine ⟨C, ?_, same, by omega, by omega⟩
      rw [here, v2]
      exact .escape (.multi hC)
  | none =>
    obtain ⟨sc, scRun, scSpec⟩ := single_char_spec cps i
    simp only [scRun, bind_ok]
    cases sc with
    | none => exact ⟨none, rfl, by simp⟩
    | some p =>
      obtain ⟨c, next⟩ := p
      obtain ⟨single, lt, le⟩ := scSpec c next rfl
      simp only [uncurry_apply_pair]
      by_cases hyphen : (tail cps next.val).head? = some 45
      · have hb : patterns.is_at cps next 45#u32 = ok true := is_at_of (by simp [hyphen])
        obtain ⟨nextInside, hyphenTail⟩ := is_at_true (v := 45#u32) (by simpa using hyphen)
        simp only [u32_ofNat_val] at hyphenTail
        obtain ⟨n1, a1, v1⟩ := add_one nextInside bound
        simp only [hb, ↓reduceIte, a1, bind_ok]
        by_cases open' : (tail cps (next.val + 1)).head? = some 91
        · have hb1 : patterns.is_at cps n1 91#u32 = ok true := is_at_of (by simp [v1, open'])
          obtain ⟨one, oneRun, oneSpec⟩ := one_spec c
          simp only [hb1, ↓reduceIte, oneRun, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro sp j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨{c.val}, ?_, one_chars oneSpec, lt, le⟩
          obtain ⟨_, openTail⟩ := is_at_true (v := 91#u32) (i := n1) (by simpa [v1] using open')
          simp only [u32_ofNat_val, v1] at openTail
          have after : tail cps next.val = 45 :: 91 :: tail cps (next.val + 2) := by
            rw [hyphenTail, openTail]
          rw [after] at single ⊢
          exact .subtraction single
        have hb1 : patterns.is_at cps n1 91#u32 = ok false := is_at_of (by simp [v1, open'])
        simp only [hb1, Bool.false_eq_true, ↓reduceIte]
        by_cases close : (tail cps (next.val + 1)).head? = some 93
        · have hb2 : patterns.is_at cps n1 93#u32 = ok true := is_at_of (by simp [v1, close])
          obtain ⟨two, twoRun, twoSpec⟩ := two_spec c 45#u32
          simp only [hb2, ↓reduceIte, twoRun, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro sp j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨{c.val, 45}, ?_, two_chars twoSpec, by omega, by omega⟩
          obtain ⟨_, closeTail⟩ := is_at_true (v := 93#u32) (i := n1) (by simpa [v1] using close)
          simp only [u32_ofNat_val, v1] at closeTail
          rw [hyphenTail, closeTail] at single
          rw [v1, closeTail]
          exact .hyphen single
        have hb2 : patterns.is_at cps n1 93#u32 = ok false := is_at_of (by simp [v1, close])
        simp only [hb2, Bool.false_eq_true, ↓reduceIte]
        by_cases pair : (tail cps (next.val + 1)).take 2 = [45, 91]
        · have hb3 : patterns.pair_at cps n1 45#u32 91#u32 = ok true := pair_at_of (by simp [v1, pair])
          obtain ⟨two, twoRun, twoSpec⟩ := two_spec c 45#u32
          simp only [hb3, ↓reduceIte, twoRun, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro sp j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨{c.val, 45}, ?_, two_chars twoSpec, by omega, by omega⟩
          obtain ⟨rest, restEq⟩ := take_two_iff.mp pair
          rw [hyphenTail, restEq] at single
          rw [v1, restEq]
          exact .hyphenSubtraction single
        have hb3 : patterns.pair_at cps n1 45#u32 91#u32 = ok false := pair_at_of (by simp [v1, pair])
        simp only [hb3, Bool.false_eq_true, ↓reduceIte]
        by_cases dash : (tail cps i.val).head? = some 45 ∨ (tail cps (next.val + 1)).head? = some 45
        · rcases dash with d | d
          · have hb4 : patterns.is_at cps i 45#u32 = ok true := is_at_of (by simp [d])
            refine ⟨none, ?_, by simp⟩
            simp [hb4, is_at_spec]
          · have hb5 : patterns.is_at cps n1 45#u32 = ok true := is_at_of (by simp [v1, d])
            refine ⟨none, ?_, by simp⟩
            simp [hb5, is_at_spec]
        simp only [not_or] at dash
        have hb4 : patterns.is_at cps i 45#u32 = ok false := is_at_of (by simp [dash.1])
        have hb5 : patterns.is_at cps n1 45#u32 = ok false := is_at_of (by simp [v1, dash.2])
        simp only [hb4, hb5, bind_ok, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨sd, sdRun, sdSpec⟩ := single_char_spec cps n1
        simp only [sdRun, bind_ok]
        cases sd with
        | none => exact ⟨none, rfl, by simp⟩
        | some q =>
          obtain ⟨d, after⟩ := q
          obtain ⟨single2, lt2, le2⟩ := sdSpec d after rfl
          simp only [uncurry_apply_pair]
          have room : (alloc.vec.Vec.new patterns.Span).val.length < Usize.max := by simp; scalar_tac
          obtain ⟨sp, spRun, spVal⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec (alloc.vec.Vec.new patterns.Span) ⟨c, d⟩ room)
          simp only [span_eq, bind_ok, spRun]
          refine ⟨_, rfl, ?_⟩
          intro sp' j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨{x | c.val ≤ x ∧ x ≤ d.val}, ?_, ?_, by omega, le2⟩
          · rw [hyphenTail] at single
            rw [v1] at single2
            exact .range dash.1 single dash.2 single2
          · intro x _
            rw [spVal]
            simp
      · have hb : patterns.is_at cps next 45#u32 = ok false := is_at_of (by simp [hyphen])
        obtain ⟨one, oneRun, oneSpec⟩ := one_spec c
        simp only [hb, Bool.false_eq_true, ↓reduceIte, oneRun, bind_ok]
        refine ⟨_, rfl, ?_⟩
        intro sp j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨{c.val}, .single single hyphen, one_chars oneSpec, lt, le⟩

theorem parts_end_of {cps : alloc.vec.Vec U32} {i : Usize} {b : Bool}
    (h : b = decide (PartsEnd (tail cps i.val))) : patterns.parts_end cps i = ok b := by
  rw [patterns.parts_end, is_at_spec]
  obtain ⟨r, run, spec⟩ := pair_at_spec cps i 45#u32 91#u32
  simp only [bind_ok, run]
  rw [h]
  unfold PartsEnd
  cases r with
  | true =>
    have := spec.mp rfl
    simp only [u32_ofNat_val] at this
    simp [this]
  | false =>
    have : ¬ (tail cps i.val).take 2 = [45, 91] := fun e => by simpa using spec.mpr (by simpa using e)
    simp [this]

theorem parts_ends {U : UnicodeData} {s C rest} (h : Parts U s C rest) : PartsEnd rest := by
  induction h with
  | last _ e => exact e
  | more _ _ _ ih => exact ih

theorem parts_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) (out : alloc.vec.Vec patterns.Span) :
    ∃ r, patterns.parts cps i out = .ok r ∧ ∀ spans j, r = some (spans, j) →
      ∃ C, Parts U (tail cps i.val) C (tail cps j.val) ∧
        (∀ c, c ≤ last → (InSpans spans.val c ↔ InSpans out.val c ∨ c ∈ C)) ∧ i.val < j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.parts]
  obtain ⟨pt, ptRun, ptSpec⟩ := part_spec U cps i
  cases pt with
  | none => simp only [ptRun, bind_ok]; exact ⟨none, rfl, by simp⟩
  | some p =>
    obtain ⟨spans0, next⟩ := p
    obtain ⟨C, part, same, lt, le⟩ := ptSpec spans0 next rfl
    simp only [ptRun, bind_ok, uncurry_apply_pair]
    obtain ⟨ap, apRun, apSpec⟩ := append_from_spec spans0 0#usize out
    simp only [apRun, bind_ok]
    cases ap with
    | none => exact ⟨none, rfl, by simp⟩
    | some joined =>
      have joinedVal := apSpec joined rfl
      simp only [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at joinedVal
      by_cases ends : PartsEnd (tail cps next.val)
      · have he : patterns.parts_end cps next = ok true := parts_end_of (by simp [ends])
        simp only [he, ↓reduceIte, bind_ok]
        refine ⟨_, rfl, ?_⟩
        intro sp j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨C, .last part ends, ?_, lt, le⟩
        intro c hc
        rw [joinedVal, inSpans_append, same c hc]
      · have he : patterns.parts_end cps next = ok false := parts_end_of (by simp [ends])
        simp only [he, bind_ok, Bool.false_eq_true, ↓reduceIte, UScalar.lt_equiv, lt]
        obtain ⟨r, run, spec⟩ := parts_spec U cps next joined
        refine ⟨r, run, ?_⟩
        intro sp j h
        obtain ⟨D, parts, same', lt', le'⟩ := spec sp j h
        refine ⟨C ∪ D, .more part ends parts, ?_, by omega, le'⟩
        intro c hc
        rw [same' c hc, joinedVal, inSpans_append, same c hc]
        simp only [Set.mem_union]
        tauto
termination_by cps.val.length - i.val
decreasing_by omega

theorem head_close {s : List ℕ} (e : PartsEnd s) (n : ¬ s.head? = some 45) : s.head? = some 93 := by
  rcases e with e | e
  · exact e
  · obtain ⟨rest, rfl⟩ := take_two_iff.mp e
    simp at n

theorem minus_open {cps : alloc.vec.Vec U32} {next : ℕ} (e : PartsEnd (tail cps next))
    (inside : next < cps.val.length) (n : (tail cps next).head? = some 45) :
    tail cps next = 45 :: tail cps (next + 1) ∧ (tail cps (next + 1)).head? = some 91 := by
  rw [tail_cons cps inside] at n e ⊢
  simp only [List.head?_cons, Option.some.injEq] at n
  refine ⟨by rw [n], ?_⟩
  rcases e with e | e
  · simp [n] at e
  · obtain ⟨rest, h⟩ := take_two_iff.mp e
    simp only [List.cons.injEq] at h
    rw [h.2]
    rfl

mutual
theorem char_group_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, patterns.char_group cps i = .ok r ∧ ∀ spans j, r = some (spans, j) →
      ∃ C, CharGroup U (tail cps i.val) C (tail cps j.val) ∧ SameChars spans.val C ∧ i.val < j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.char_group]
  have bound := cps.property
  by_cases neg : (tail cps i.val).head? = some 94
  · have hn : patterns.is_at cps i 94#u32 = ok true := is_at_of (by simp [neg])
    obtain ⟨inside, negTail⟩ := is_at_true (v := 94#u32) (by simpa using neg)
    simp only [u32_ofNat_val] at negTail
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    simp only [hn, ↓reduceIte, a1, bind_ok]
    obtain ⟨ps, psRun, psSpec⟩ := parts_spec U cps n1 (alloc.vec.Vec.new patterns.Span)
    cases ps with
    | none => simp only [psRun, bind_ok]; exact ⟨none, rfl, by simp⟩
    | some p =>
      obtain ⟨spans, next⟩ := p
      obtain ⟨C, parts, same, lt, le⟩ := psSpec spans next rfl
      simp only [psRun, bind_ok, uncurry_apply_pair]
      obtain ⟨cm, cmRun, cmSpec⟩ := complement_spec spans
      simp only [cmRun, bind_ok]
      cases cm with
      | none => exact ⟨none, rfl, by simp⟩
      | some base =>
        have baseSame : SameChars base.val Cᶜ := by
          intro c hc
          rw [cmSpec base rfl c, same c hc]
          simp [hc]
        by_cases minus : (tail cps next.val).head? = some 45
        · have hm : patterns.is_at cps next 45#u32 = ok true := is_at_of (by simp [minus])
          obtain ⟨nextInside, _⟩ := is_at_true (v := 45#u32) (by simpa using minus)
          obtain ⟨hyphenTail, openNext⟩ := minus_open (parts_ends parts) nextInside minus
          obtain ⟨n2, a2, v2⟩ := add_one nextInside bound
          simp only [hm, ↓reduceIte, a2, bind_ok]
          obtain ⟨ce, ceRun, ceSpec⟩ := class_expr_spec U cps n2
          cases ce with
          | none => simp only [ceRun, bind_ok]; exact ⟨none, rfl, by simp⟩
          | some q =>
            obtain ⟨minusSpans, after⟩ := q
            obtain ⟨D, expr, sameD, lt2, le2⟩ := ceSpec minusSpans after rfl
            simp only [ceRun, bind_ok, uncurry_apply_pair]
            obtain ⟨sb, sbRun, sbSpec⟩ := subtract_spec base minusSpans
            simp only [sbRun, bind_ok]
            cases sb with
            | none => exact ⟨none, rfl, by simp⟩
            | some left =>
              refine ⟨_, rfl, ?_⟩
              intro sp j h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨Cᶜ \ D, ?_, ?_, by omega, le2⟩
              · rw [negTail, ← v1]
                rw [hyphenTail, ← v2] at parts
                exact .negativeMinus parts expr
              · intro c hc
                rw [sbSpec left rfl c, baseSame c hc, sameD c hc]
                simp [hc]
        · have hm : patterns.is_at cps next 45#u32 = ok false := is_at_of (by simp [minus])
          simp only [hm, bind_ok, Bool.false_eq_true, ↓reduceIte]
          refine ⟨_, rfl, ?_⟩
          intro sp j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Cᶜ, ?_, baseSame, by omega, le⟩
          rw [negTail, ← v1]
          exact .negative parts (head_close (parts_ends parts) minus)
  · have hn : patterns.is_at cps i 94#u32 = ok false := is_at_of (by simp [neg])
    simp only [hn, Bool.false_eq_true, ↓reduceIte, bind_ok]
    obtain ⟨ps, psRun, psSpec⟩ := parts_spec U cps i (alloc.vec.Vec.new patterns.Span)
    cases ps with
    | none => simp only [psRun, bind_ok]; exact ⟨none, rfl, by simp⟩
    | some p =>
      obtain ⟨spans, next⟩ := p
      obtain ⟨C, parts, same, lt, le⟩ := psSpec spans next rfl
      simp only [psRun, bind_ok, uncurry_apply_pair]
      have baseSame : SameChars spans.val C := by
        intro c hc
        rw [same c hc]
        simp
      by_cases minus : (tail cps next.val).head? = some 45
      · have hm : patterns.is_at cps next 45#u32 = ok true := is_at_of (by simp [minus])
        obtain ⟨nextInside, _⟩ := is_at_true (v := 45#u32) (by simpa using minus)
        obtain ⟨hyphenTail, openNext⟩ := minus_open (parts_ends parts) nextInside minus
        obtain ⟨n2, a2, v2⟩ := add_one nextInside bound
        simp only [hm, ↓reduceIte, a2, bind_ok]
        obtain ⟨ce, ceRun, ceSpec⟩ := class_expr_spec U cps n2
        cases ce with
        | none => simp only [ceRun, bind_ok]; exact ⟨none, rfl, by simp⟩
        | some q =>
          obtain ⟨minusSpans, after⟩ := q
          obtain ⟨D, expr, sameD, lt2, le2⟩ := ceSpec minusSpans after rfl
          simp only [ceRun, bind_ok, uncurry_apply_pair]
          obtain ⟨sb, sbRun, sbSpec⟩ := subtract_spec spans minusSpans
          simp only [sbRun, bind_ok]
          cases sb with
          | none => exact ⟨none, rfl, by simp⟩
          | some left =>
            refine ⟨_, rfl, ?_⟩
            intro sp j h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨C \ D, ?_, ?_, by omega, le2⟩
            · rw [hyphenTail, ← v2] at parts
              exact .positiveMinus neg parts expr
            · intro c hc
              rw [sbSpec left rfl c, baseSame c hc, sameD c hc]
              simp [hc]
      · have hm : patterns.is_at cps next 45#u32 = ok false := is_at_of (by simp [minus])
        simp only [hm, bind_ok, Bool.false_eq_true, ↓reduceIte]
        refine ⟨_, rfl, ?_⟩
        intro sp j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨C, .positive neg parts (head_close (parts_ends parts) minus), baseSame, lt, le⟩
termination_by (cps.val.length - i.val, 0)
decreasing_by all_goals (apply Prod.Lex.left; omega)

theorem class_expr_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, patterns.class_expr cps i = .ok r ∧ ∀ spans j, r = some (spans, j) →
      ∃ C, ClassExpr U (tail cps i.val) C (tail cps j.val) ∧ SameChars spans.val C ∧ i.val < j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.class_expr]
  have bound := cps.property
  by_cases open' : (tail cps i.val).head? = some 91
  · have ho : patterns.is_at cps i 91#u32 = ok true := is_at_of (by simp [open'])
    obtain ⟨inside, openTail⟩ := is_at_true (v := 91#u32) (by simpa using open')
    simp only [u32_ofNat_val] at openTail
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    simp only [ho, ↓reduceIte, a1, bind_ok]
    obtain ⟨cg, cgRun, cgSpec⟩ := char_group_spec U cps n1
    cases cg with
    | none => simp only [cgRun, bind_ok]; exact ⟨none, rfl, by simp⟩
    | some q =>
      obtain ⟨spans, next⟩ := q
      obtain ⟨C, group, same, lt, le⟩ := cgSpec spans next rfl
      simp only [cgRun, bind_ok, uncurry_apply_pair]
      by_cases close : (tail cps next.val).head? = some 93
      · have hc : patterns.is_at cps next 93#u32 = ok true := is_at_of (by simp [close])
        obtain ⟨nextInside, closeTail⟩ := is_at_true (v := 93#u32) (by simpa using close)
        simp only [u32_ofNat_val] at closeTail
        obtain ⟨n2, a2, v2⟩ := add_one nextInside bound
        simp only [hc, ↓reduceIte, a2, bind_ok]
        refine ⟨_, rfl, ?_⟩
        intro sp j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨C, ?_, same, by omega, by omega⟩
        rw [openTail, ← v1]
        rw [closeTail, ← v2] at group
        exact .mk group
      · have hc : patterns.is_at cps next 93#u32 = ok false := is_at_of (by simp [close])
        simp only [hc, bind_ok, Bool.false_eq_true, ↓reduceIte]
        exact ⟨none, rfl, by simp⟩
  · have ho : patterns.is_at cps i 91#u32 = ok false := is_at_of (by simp [open'])
    simp only [ho, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact ⟨none, rfl, by simp⟩
termination_by (cps.val.length - i.val, 1)
decreasing_by all_goals (apply Prod.Lex.left; omega)
end

theorem char_class_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, patterns.char_class cps i = .ok r ∧ ∀ spans j, r = some (spans, j) →
      ∃ C, CharClass U (tail cps i.val) C (tail cps j.val) ∧ SameChars spans.val C ∧ i.val < j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.char_class]
  have bound := cps.property
  by_cases slash : (tail cps i.val).head? = some 92
  · have hs : patterns.is_at cps i 92#u32 = ok true := is_at_of (by simp [slash])
    obtain ⟨inside, slashTail⟩ := is_at_true (v := 92#u32) (by simpa using slash)
    simp only [u32_ofNat_val] at slashTail
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    simp only [hs, ↓reduceIte, a1, bind_ok]
    by_cases more : i.val + 1 < cps.val.length
    · have lookup1 : cps.index_usize n1 = .ok cps.val[i.val + 1] := by
        simp [alloc.vec.Vec.index_usize, v1, List.getElem?_eq_getElem more]
      simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, v1, more, ↓reduceIte, alloc.vec.Vec.index_slice_index,
        lookup1, bind_ok]
      have tailEq : tail cps i.val = 92 :: cps.val[i.val + 1].val :: tail cps (i.val + 2) := by
        rw [slashTail, tail_cons cps more]
      obtain ⟨e, eRun, eVal⟩ := escaped_char_spec cps.val[i.val + 1]
      simp only [eRun, bind_ok]
      cases e with
      | some c =>
        obtain ⟨one, oneRun, oneSpec⟩ := one_spec c
        obtain ⟨n2, a2, v2⟩ := add_two more bound
        simp only [oneRun, a2, bind_ok]
        refine ⟨_, rfl, ?_⟩
        intro sp j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨{c.val}, ?_, one_chars oneSpec, by omega, by omega⟩
        rw [tailEq, v2]
        exact .single (by simpa using eVal.symm)
      | none =>
        obtain ⟨m, mRun, mSpec⟩ := multi_spans_spec cps.val[i.val + 1]
        simp only [mRun, bind_ok]
        cases m with
        | none => exact ⟨none, rfl, by simp⟩
        | some spans =>
          obtain ⟨n2, a2, v2⟩ := add_two more bound
          simp only [a2, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro sp j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨C, hC, same⟩ := mSpec _ rfl U
          refine ⟨C, ?_, same, by omega, by omega⟩
          rw [tailEq, v2]
          exact .escape (.multi hC)
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, v1, more, ↓reduceIte]
      exact ⟨none, rfl, by simp⟩
  · have hs : patterns.is_at cps i 92#u32 = ok false := is_at_of (by simp [slash])
    simp only [hs, bind_ok, Bool.false_eq_true, ↓reduceIte]
    by_cases open' : (tail cps i.val).head? = some 91
    · have ho : patterns.is_at cps i 91#u32 = ok true := is_at_of (by simp [open'])
      simp only [ho, bind_ok, ↓reduceIte]
      obtain ⟨ce, ceRun, ceSpec⟩ := class_expr_spec U cps i
      refine ⟨ce, ceRun, ?_⟩
      intro spans j h
      obtain ⟨C, expr, same, lt, le⟩ := ceSpec spans j h
      exact ⟨C, .expr expr, same, lt, le⟩
    · have ho : patterns.is_at cps i 91#u32 = ok false := is_at_of (by simp [open'])
      simp only [ho, bind_ok, Bool.false_eq_true, ↓reduceIte]
      by_cases dot : (tail cps i.val).head? = some 46
      · have hd : patterns.is_at cps i 46#u32 = ok true := is_at_of (by simp [dot])
        obtain ⟨inside, dotTail⟩ := is_at_true (v := 46#u32) (by simpa using dot)
        simp only [u32_ofNat_val] at dotTail
        obtain ⟨wc, wcRun, wcVal⟩ := WP.spec_imp_exists wildcard_val
        obtain ⟨n1, a1, v1⟩ := add_one inside bound
        simp only [hd, bind_ok, ↓reduceIte, wcRun, a1]
        refine ⟨_, rfl, ?_⟩
        intro sp j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨{c | c ≠ 10 ∧ c ≠ 13}, ?_, ?_, by omega, by omega⟩
        · rw [dotTail, v1]
          exact .wildcard
        · intro c hc
          rw [wcVal, wildcard_iff]
          simp [hc]
      · have hd : patterns.is_at cps i 46#u32 = ok false := is_at_of (by simp [dot])
        simp only [hd, bind_ok, Bool.false_eq_true, ↓reduceIte]
        exact ⟨none, rfl, by simp⟩

/-! ### Quantifiers -/

/-- The number that decimal digits continue. -/
def digitsFrom (value : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun v d => 10 * v + (d - 48)) value

theorem numbers_val : patterns.NUMBERS.val = 1048576 := by simp [patterns.NUMBERS]

theorem digits_from_spec (cps : alloc.vec.Vec U32) (i value : Usize) (seen : Bool) (small : value.val < 1048576)
    (start : i.val ≤ cps.val.length) :
    ∃ r, patterns.digits_from cps i value seen = .ok r ∧ ∀ n j, r = some (n, j) →
      ∃ ds, tail cps i.val = ds ++ tail cps j.val ∧ (∀ d ∈ ds, Digit d) ∧
        (∀ d ∈ (tail cps j.val).head?, ¬ Digit d) ∧ (seen = true ∨ ds ≠ []) ∧
        n.val = digitsFrom value.val ds ∧ n.val < 1048576 ∧ i.val ≤ j.val ∧ j.val ≤ cps.val.length := by
  rw [patterns.digits_from]
  have bound := cps.property
  by_cases inside : i.val < cps.val.length
  · have here := tail_cons cps inside
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_at inside, bind_ok]
    by_cases digit : 48 ≤ cps.val[i.val].val ∧ cps.val[i.val].val ≤ 57
    · have hdiv : patterns.NUMBERS / 10#usize = ok 104857#usize := by
        obtain ⟨q, run, val⟩ := WP.spec_imp_exists (Usize.div_spec patterns.NUMBERS (y := 10#usize) (by simp))
        rw [run]
        congr 1
        apply UScalar.eq_of_val_eq
        rw [val, numbers_val]
        rfl
      simp only [UScalar.le_equiv, u32_ofNat_val, digit, decide_true, Bool.and_self, ↓reduceIte, hdiv, bind_ok]
      by_cases fits : value.val < 104857
      · obtain ⟨n1, a1, v1⟩ := add_one inside bound
        obtain ⟨m, mRun, mVal⟩ := WP.spec_imp_exists (Usize.mul_spec (x := value) (y := 10#usize)
          (by have := usize_big; simp; omega))
        obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (U32.sub_spec (x := cps.val[i.val]) (y := 48#u32)
          (by simp; omega))
        obtain ⟨s, sRun, sVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := m) (y := UScalar.cast .Usize d)
          (by have := usize_big; simp at mVal dVal ⊢; omega))
        have sNum : s.val = 10 * value.val + (cps.val[i.val].val - 48) := by
          simp at mVal dVal sVal; omega
        obtain ⟨r, run, spec⟩ := digits_from_spec cps n1 s true (by omega) (by omega)
        refine ⟨r, ?_, ?_⟩
        · simp only [UScalar.lt_equiv, show (104857#usize : Usize).val = 104857 from rfl, fits, decide_true,
            ↓reduceIte, a1, mRun, dRun, lift, sRun, bind_ok, run]
        · intro n j h
          obtain ⟨ds, eq, digits, stop, _, nVal, small', le1, le2⟩ := spec n j h
          refine ⟨cps.val[i.val].val :: ds, ?_, ?_, stop, .inr (by simp), ?_, small', by omega, le2⟩
          · rw [here, ← v1, eq]; rfl
          · intro x mem
            simp only [List.mem_cons] at mem
            rcases mem with rfl | mem
            · exact digit
            · exact digits x mem
          · rw [nVal, sNum]
            simp [digitsFrom, List.foldl_cons]
      · simp only [UScalar.lt_equiv, show (104857#usize : Usize).val = 104857 from rfl, fits, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        exact ⟨none, rfl, by simp⟩
    · have notDigit : ¬ ((48#u32 ≤ cps.val[i.val]) && (cps.val[i.val] ≤ 57#u32)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, UScalar.le_equiv, u32_ofNat_val]
        exact digit
      simp only [notDigit, ↓reduceIte]
      cases seen with
      | true =>
        refine ⟨_, rfl, ?_⟩
        intro n j h
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], by simp, by simp, ?_, .inl rfl, by simp [digitsFrom], small, le_rfl, by omega⟩
        rw [here]
        simpa [Digit] using digit
      | false => exact ⟨none, by simp, by simp⟩
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte]
    cases seen with
    | true =>
      refine ⟨_, rfl, ?_⟩
      intro n j h
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[], by simp, by simp, ?_, .inl rfl, by simp [digitsFrom], small, le_rfl, by omega⟩
      rw [tail_end cps (by omega)]
      simp
    | false => exact ⟨none, by simp, by simp⟩
termination_by cps.val.length - i.val
decreasing_by omega

theorem numeral_of_digits {cps : alloc.vec.Vec U32} {i j : ℕ} {n : ℕ} {ds : List ℕ}
    (eq : tail cps i = ds ++ tail cps j) (digits : ∀ d ∈ ds, Digit d) (stop : ∀ d ∈ (tail cps j).head?, ¬ Digit d)
    (ne : false = true ∨ ds ≠ []) (val : n = digitsFrom 0 ds) : Numeral (tail cps i) n (tail cps j) := by
  refine ⟨ds, eq, ?_, digits, stop, val⟩
  rcases ne with h | h
  · exact absurd h (by decide)
  · exact h

theorem quantifier_spec (cps : alloc.vec.Vec U32) (i : Usize) :
    ∃ r, patterns.quantifier cps i = .ok r ∧ ∀ n m j, r = some (n, m, j) →
      Quantifier (tail cps i.val) n.val (m.map (·.val)) (tail cps j.val) ∧ n.val < 1048576 ∧
        (∀ k, m = some k → n.val ≤ k.val) ∧ i.val < j.val ∧ j.val ≤ cps.val.length := by
  rw [patterns.quantifier]
  have bound := cps.property
  by_cases q1 : (tail cps i.val).head? = some 63
  · have h1 : patterns.is_at cps i 63#u32 = ok true := is_at_of (by simp [q1])
    obtain ⟨inside, qTail⟩ := is_at_true (v := 63#u32) (by simpa using q1)
    simp only [u32_ofNat_val] at qTail
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    simp only [h1, ↓reduceIte, a1, bind_ok]
    refine ⟨_, rfl, ?_⟩
    intro n m j h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨?_, by simp, by simp, by omega, by omega⟩
    rw [qTail, v1]
    exact .optional
  have h1 : patterns.is_at cps i 63#u32 = ok false := is_at_of (by simp [q1])
  simp only [h1, bind_ok, Bool.false_eq_true, ↓reduceIte]
  by_cases q2 : (tail cps i.val).head? = some 42
  · have h2 : patterns.is_at cps i 42#u32 = ok true := is_at_of (by simp [q2])
    obtain ⟨inside, qTail⟩ := is_at_true (v := 42#u32) (by simpa using q2)
    simp only [u32_ofNat_val] at qTail
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    simp only [h2, ↓reduceIte, a1, bind_ok]
    refine ⟨_, rfl, ?_⟩
    intro n m j h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨?_, by simp, by simp, by omega, by omega⟩
    rw [qTail, v1]
    exact .star
  have h2 : patterns.is_at cps i 42#u32 = ok false := is_at_of (by simp [q2])
  simp only [h2, bind_ok, Bool.false_eq_true, ↓reduceIte]
  by_cases q3 : (tail cps i.val).head? = some 43
  · have h3 : patterns.is_at cps i 43#u32 = ok true := is_at_of (by simp [q3])
    obtain ⟨inside, qTail⟩ := is_at_true (v := 43#u32) (by simpa using q3)
    simp only [u32_ofNat_val] at qTail
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    simp only [h3, ↓reduceIte, a1, bind_ok]
    refine ⟨_, rfl, ?_⟩
    intro n m j h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨?_, by simp, by simp, by omega, by omega⟩
    rw [qTail, v1]
    exact .plus
  have h3 : patterns.is_at cps i 43#u32 = ok false := is_at_of (by simp [q3])
  simp only [h3, bind_ok, Bool.false_eq_true, ↓reduceIte]
  by_cases q4 : (tail cps i.val).head? = some 123
  · have h4 : patterns.is_at cps i 123#u32 = ok true := is_at_of (by simp [q4])
    obtain ⟨inside, qTail⟩ := is_at_true (v := 123#u32) (by simpa using q4)
    simp only [u32_ofNat_val] at qTail
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    simp only [h4, ↓reduceIte, a1, bind_ok]
    obtain ⟨dg, dgRun, dgSpec⟩ := digits_from_spec cps n1 0#usize false (by simp) (by omega)
    cases dg with
    | none => simp only [dgRun, bind_ok]; exact ⟨none, rfl, by simp⟩
    | some p =>
      obtain ⟨least, next⟩ := p
      obtain ⟨ds, eq, digits, stop, ne, leastVal, small, le1, le2⟩ := dgSpec least next rfl
      have numeral : ∀ rest, tail cps next.val = rest → Numeral (tail cps n1.val) least.val rest := by
        intro rest h
        rw [← h]
        exact numeral_of_digits eq digits stop ne (by simpa using leastVal)
      simp only [dgRun, bind_ok, uncurry_apply_pair]
      by_cases close : (tail cps next.val).head? = some 125
      · have h5 : patterns.is_at cps next 125#u32 = ok true := is_at_of (by simp [close])
        obtain ⟨nextInside, closeTail⟩ := is_at_true (v := 125#u32) (by simpa using close)
        simp only [u32_ofNat_val] at closeTail
        obtain ⟨n2, a2, v2⟩ := add_one nextInside bound
        simp only [h5, ↓reduceIte, a2, bind_ok]
        refine ⟨_, rfl, ?_⟩
        intro n m j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨?_, small, by simp, by omega, by omega⟩
        rw [qTail, ← v1, v2]
        exact .exact (numeral _ closeTail)
      have h5 : patterns.is_at cps next 125#u32 = ok false := is_at_of (by simp [close])
      simp only [h5, bind_ok, Bool.false_eq_true, ↓reduceIte]
      by_cases comma : (tail cps next.val).head? = some 44
      · have h6 : patterns.is_at cps next 44#u32 = ok true := is_at_of (by simp [comma])
        obtain ⟨nextInside, commaTail⟩ := is_at_true (v := 44#u32) (by simpa using comma)
        simp only [u32_ofNat_val] at commaTail
        obtain ⟨n2, a2, v2⟩ := add_one nextInside bound
        simp only [h6, ↓reduceIte, a2, bind_ok]
        by_cases close2 : (tail cps (next.val + 1)).head? = some 125
        · have h7 : patterns.is_at cps n2 125#u32 = ok true := is_at_of (by simp [v2, close2])
          obtain ⟨n2Inside, close2Tail⟩ := is_at_true (v := 125#u32) (i := n2) (by simpa [v2] using close2)
          simp only [u32_ofNat_val, v2] at close2Tail
          obtain ⟨n3, a3, v3⟩ := add_two (show next.val + 1 < cps.val.length by rw [v2] at n2Inside; exact n2Inside) bound
          simp only [h7, ↓reduceIte, a3, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro n m j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨?_, small, by simp, by omega, by omega⟩
          rw [qTail, ← v1, v3]
          exact .atLeast (numeral _ (by rw [commaTail, close2Tail]))
        have h7 : patterns.is_at cps n2 125#u32 = ok false := is_at_of (by simp [v2, close2])
        simp only [h7, bind_ok, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨dg2, dg2Run, dg2Spec⟩ := digits_from_spec cps n2 0#usize false (by simp) (by omega)
        cases dg2 with
        | none => simp only [dg2Run, bind_ok]; exact ⟨none, rfl, by simp⟩
        | some p2 =>
          obtain ⟨most, after⟩ := p2
          obtain ⟨ds2, eq2, digits2, stop2, ne2, mostVal, small2, le3, le4⟩ := dg2Spec most after rfl
          simp only [dg2Run, bind_ok, uncurry_apply_pair]
          by_cases ok' : least.val ≤ most.val ∧ (tail cps after.val).head? = some 125
          · have h8 : patterns.is_at cps after 125#u32 = ok true := is_at_of (by simp [ok'.2])
            obtain ⟨afterInside, close3Tail⟩ := is_at_true (v := 125#u32) (by simpa using ok'.2)
            simp only [u32_ofNat_val] at close3Tail
            obtain ⟨n4, a4, v4⟩ := add_one afterInside bound
            simp only [h8, UScalar.le_equiv, ok'.1, decide_true, Bool.and_self, ↓reduceIte, a4, bind_ok]
            refine ⟨_, rfl, ?_⟩
            intro n m j h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨?_, small, by simpa using ok'.1, by omega, by omega⟩
            rw [qTail, ← v1, v4]
            refine .between (numeral _ commaTail) ?_ ok'.1
            rw [← v2, ← close3Tail]
            exact numeral_of_digits eq2 digits2 stop2 ne2 (by simpa using mostVal)
          · have h8 : patterns.is_at cps after 125#u32 =
                ok (decide ((tail cps after.val).head? = some 125)) := is_at_of (by simp)
            simp only [h8, bind_ok]
            have : ¬ ((decide (least.val ≤ most.val)) && decide ((tail cps after.val).head? = some 125)) = true := by
              simpa using ok'
            simp only [UScalar.le_equiv, this, ↓reduceIte]
            exact ⟨none, rfl, by simp⟩
      · have h6 : patterns.is_at cps next 44#u32 = ok false := is_at_of (by simp [comma])
        simp only [h6, bind_ok, Bool.false_eq_true, ↓reduceIte]
        exact ⟨none, rfl, by simp⟩
  · have h4 : patterns.is_at cps i 123#u32 = ok false := is_at_of (by simp [q4])
    simp only [h4, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact ⟨none, rfl, by simp⟩

/-! ### Repetitions -/

/-- The concatenations of up to `n` strings of `L`. -/
def UpTo (L : Language ℕ) : ℕ → Language ℕ
  | 0 => 1
  | n + 1 => 1 + L * UpTo L n

theorem mem_upTo (L : Language ℕ) (n : ℕ) (w : List ℕ) : w ∈ UpTo L n ↔ ∃ k ≤ n, w ∈ L ^ k := by
  induction n generalizing w with
  | zero => simp [UpTo]
  | succ n ih =>
    simp only [UpTo, Language.mem_add, Language.mem_one, Language.mem_mul]
    constructor
    · rintro (rfl | ⟨u, hu, v, hv, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · obtain ⟨k, hk, mem⟩ := (ih v).mp hv
        exact ⟨k + 1, by omega, by rw [pow_succ']; exact ⟨u, hu, v, mem, rfl⟩⟩
    · rintro ⟨k, hk, mem⟩
      cases k with
      | zero => left; simpa using mem
      | succ k =>
        right
        rw [pow_succ'] at mem
        obtain ⟨u, hu, v, hv, rfl⟩ := mem
        exact ⟨u, hu, v, (ih v).mpr ⟨k, by omega, hv⟩, rfl⟩

theorem pow_mul_upTo (L : Language ℕ) (a b : ℕ) :
    L ^ a * UpTo L b = {w | ∃ k, a ≤ k ∧ k ≤ a + b ∧ w ∈ L ^ k} := by
  ext w
  simp only [Language.mem_mul, Set.mem_setOf_eq, mem_upTo]
  constructor
  · rintro ⟨u, hu, v, ⟨k, hk, hv⟩, rfl⟩
    refine ⟨a + k, by omega, by omega, ?_⟩
    rw [pow_add]
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨k, lo, hi, mem⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = a + j := ⟨k - a, by omega⟩
    rw [pow_add] at mem
    obtain ⟨u, hu, v, hv, rfl⟩ := mem
    exact ⟨u, hu, v, ⟨j, by omega, hv⟩, rfl⟩

theorem size_from_spec (e : Expression) (cap : Usize) :
    ∀ count : Usize, count.val ≤ cap.val → ∃ r, patterns.size_from e count cap = .ok r ∧ r.val ≤ cap.val := by
  have bound : cap.val ≤ Usize.max := by scalar_tac
  induction e with
  | Empty | Epsilon | Interval =>
    intro count h
    rw [patterns.size_from]
    by_cases full : cap.val ≤ count.val
    · exact ⟨cap, by simp [UScalar.le_equiv, full], le_rfl⟩
    · obtain ⟨n, a, v⟩ := add_one (i := count) (n := cap.val) (by omega) bound
      exact ⟨n, by simp [UScalar.le_equiv, full, a], by omega⟩
  | Alternative left right ihl ihr =>
    intro count h
    rw [patterns.size_from]
    by_cases full : cap.val ≤ count.val
    · exact ⟨cap, by simp [UScalar.le_equiv, full], le_rfl⟩
    · obtain ⟨n, a, v⟩ := add_one (i := count) (n := cap.val) (by omega) bound
      obtain ⟨l, lRun, lLe⟩ := ihl n (by omega)
      obtain ⟨r, rRun, rLe⟩ := ihr l lLe
      exact ⟨r, by simp [UScalar.le_equiv, full, a, lRun, rRun], rLe⟩
  | Sequence left right ihl ihr =>
    intro count h
    rw [patterns.size_from]
    by_cases full : cap.val ≤ count.val
    · exact ⟨cap, by simp [UScalar.le_equiv, full], le_rfl⟩
    · obtain ⟨n, a, v⟩ := add_one (i := count) (n := cap.val) (by omega) bound
      obtain ⟨l, lRun, lLe⟩ := ihl n (by omega)
      obtain ⟨r, rRun, rLe⟩ := ihr l lLe
      exact ⟨r, by simp [UScalar.le_equiv, full, a, lRun, rRun], rLe⟩
  | Repeat inner ih =>
    intro count h
    rw [patterns.size_from]
    by_cases full : cap.val ≤ count.val
    · exact ⟨cap, by simp [UScalar.le_equiv, full], le_rfl⟩
    · obtain ⟨n, a, v⟩ := add_one (i := count) (n := cap.val) (by omega) bound
      obtain ⟨r, rRun, rLe⟩ := ih n (by omega)
      exact ⟨r, by simp [UScalar.le_equiv, full, a, rRun], rLe⟩

theorem power_spec (e : Expression) (count : Usize) :
    ∃ r, patterns.power e count = .ok r ∧ Denotes r = (Denotes e) ^ count.val := by
  rw [patterns.power]
  by_cases zero : count.val = 0
  · have : count = 0#usize := UScalar.eq_of_val_eq (by simpa using zero)
    refine ⟨.Epsilon, by simp [this], by simp [zero, Denotes]⟩
  · have ne : ¬ count = 0#usize := fun h => zero (by simp [h])
    obtain ⟨m, mRun, mVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have mv : m.val = count.val - 1 := by simp at mVal; omega
    obtain ⟨p, pRun, pDen⟩ := power_spec e m
    obtain ⟨q, qRun, qDen⟩ := sequence_total_correct e p
    refine ⟨q, by simp [ne, copy_expression_total, mRun, pRun, qRun], ?_⟩
    rw [qDen, pDen, mv, ← pow_succ']
    congr 1
    omega
termination_by count.val
decreasing_by simp at mVal; omega

theorem at_most_spec (e : Expression) (count : Usize) :
    ∃ r, patterns.at_most e count = .ok r ∧ Denotes r = UpTo (Denotes e) count.val := by
  rw [patterns.at_most]
  by_cases zero : count.val = 0
  · have : count = 0#usize := UScalar.eq_of_val_eq (by simpa using zero)
    refine ⟨.Epsilon, by simp [this], by simp [zero, Denotes, UpTo]⟩
  · have ne : ¬ count = 0#usize := fun h => zero (by simp [h])
    obtain ⟨m, mRun, mVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have mv : m.val = count.val - 1 := by simp at mVal; omega
    obtain ⟨p, pRun, pDen⟩ := at_most_spec e m
    obtain ⟨q, qRun, qDen⟩ := sequence_total_correct e p
    obtain ⟨t, tRun, tDen⟩ := alternate_total_correct .Epsilon q
    refine ⟨t, by simp [ne, copy_expression_total, mRun, pRun, qRun, tRun], ?_⟩
    rw [tDen, qDen, pDen, mv]
    obtain ⟨k, hk⟩ : ∃ k, count.val = k + 1 := ⟨count.val - 1, by omega⟩
    rw [hk]
    simp [UpTo, Denotes]
termination_by count.val
decreasing_by simp at mVal; omega

theorem size_val : patterns.SIZE.val = 65536 := by simp [patterns.SIZE]

theorem repeated_spec (e : Expression) (least : Usize) (most : Option Usize) (small : least.val < 1048576)
    (order : ∀ m, most = some m → least.val ≤ m.val) :
    ∃ r, patterns.repeated e least most = .ok r ∧
      ∀ e', r = some e' → Denotes e' = Repeats (Denotes e) least.val (most.map (·.val)) := by
  rw [patterns.repeated.eq_def]
  have big := usize_big
  obtain ⟨cap, capRun, capVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := patterns.SIZE) (y := 1#usize)
    (by simp [size_val]; omega))
  have capV : cap.val = 65537 := by simp [size_val] at capVal; omega
  obtain ⟨size, sizeRun, sizeLe⟩ := size_from_spec e cap 0#usize (by simp)
  obtain ⟨first, fRun, fDen⟩ := power_spec e least
  cases most with
  | none =>
    obtain ⟨copies, a, _⟩ := add_one (i := least) (n := 1048576) small (by omega)
    simp only [a, capRun, sizeRun, bind_ok]
    by_cases pos : 0 < size.val
    · obtain ⟨q, qRun, qVal⟩ := WP.spec_imp_exists (Usize.div_spec patterns.SIZE (y := size) (by simp; omega))
      simp only [UScalar.lt_equiv, show (0#usize : Usize).val = 0 from rfl, pos, decide_true, ↓reduceIte, qRun,
        bind_ok]
      by_cases fits : copies.val ≤ q.val
      · obtain ⟨rp, rpRun, rpDen⟩ := repeat_total_correct e
        obtain ⟨sq, sqRun, sqDen⟩ := sequence_total_correct first rp
        simp only [UScalar.le_equiv, fits, decide_true, ↓reduceIte, fRun, rpRun, sqRun, bind_ok]
        refine ⟨_, rfl, ?_⟩
        intro e' h
        simp only [Option.some.injEq] at h
        subst h
        rw [sqDen, fDen, rpDen]
        rfl
      · simp only [UScalar.le_equiv, fits, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨none, rfl, by simp⟩
    · simp only [UScalar.lt_equiv, show (0#usize : Usize).val = 0 from rfl, pos, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact ⟨none, rfl, by simp⟩
  | some m =>
    have lm := order m rfl
    simp only [capRun, sizeRun, bind_ok]
    by_cases pos : 0 < size.val
    · obtain ⟨q, qRun, qVal⟩ := WP.spec_imp_exists (Usize.div_spec patterns.SIZE (y := size) (by simp; omega))
      simp only [UScalar.lt_equiv, show (0#usize : Usize).val = 0 from rfl, pos, decide_true, ↓reduceIte, qRun,
        bind_ok]
      by_cases fits : m.val ≤ q.val
      · obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := m) (y := least) lm)
        obtain ⟨am, amRun, amDen⟩ := at_most_spec e d
        obtain ⟨sq, sqRun, sqDen⟩ := sequence_total_correct first am
        simp only [UScalar.le_equiv, fits, decide_true, ↓reduceIte, fRun, dRun, amRun, sqRun, bind_ok]
        refine ⟨_, rfl, ?_⟩
        intro e' h
        simp only [Option.some.injEq] at h
        subst h
        rw [sqDen, fDen, amDen, pow_mul_upTo]
        simp only [Option.map_some, Repeats]
        have : least.val + d.val = m.val := by omega
        rw [this]
      · simp only [UScalar.le_equiv, fits, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨none, rfl, by simp⟩
    · simp only [UScalar.lt_equiv, show (0#usize : Usize).val = 0 from rfl, pos, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact ⟨none, rfl, by simp⟩

theorem spans_expression_spec (spans : alloc.vec.Vec patterns.Span) (index : Usize) :
    ∃ r, patterns.spans_expression spans index = .ok r ∧ Denotes r = spanStrings (spans.val.drop index.val) := by
  rw [patterns.spans_expression]
  by_cases inside : index.val < spans.val.length
  · have lookup : spans.index_usize index = .ok spans.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := add_one inside spans.property
    obtain ⟨rest, restRun, restDen⟩ := spans_expression_spec spans next
    obtain ⟨r, run, den⟩ := alternate_total_correct
      (.Interval spans.val[index.val].lower spans.val[index.val].upper) rest
    refine ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, restRun, run], ?_⟩
    rw [den, restDen, nextValue, List.drop_eq_getElem_cons inside]
    ext w
    simp only [Denotes, spanStrings, Language.mem_add, Set.mem_setOf_eq, inSpans_cons]
    constructor
    · rintro (⟨c, rfl, lo, hi⟩ | ⟨c, rfl, h⟩)
      · exact ⟨c, rfl, .inl ⟨lo, hi⟩⟩
      · exact ⟨c, rfl, .inr h⟩
    · rintro ⟨c, rfl, (⟨lo, hi⟩ | h)⟩
      · exact .inl ⟨c, rfl, lo, hi⟩
      · exact .inr ⟨c, rfl, h⟩
  · refine ⟨.Empty, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [List.drop_eq_nil_iff.mpr (by omega)]
    ext w
    simp [Denotes, spanStrings]
    exact fun h => h
termination_by spans.val.length - index.val
decreasing_by omega

/-! ### Regular expressions -/

theorem bool_eq_decide {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) : b = decide P := by
  cases b <;> simp_all

theorem meta_spec (c : U32) : patterns.meta c = ok (decide (Meta c.val)) := by
  unfold patterns.meta
  congr 1
  apply bool_eq_decide
  simp only [Meta, u32_eq_iff, u32_ofNat_val, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem atom_start_spec (cps : alloc.vec.Vec U32) (i : Usize) :
    patterns.atom_start cps i = ok (decide (∃ c ∈ (tail cps i.val).head?, AtomStart c)) := by
  rw [patterns.atom_start]
  by_cases inside : i.val < cps.val.length
  · rw [tail_cons cps inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_at inside, bind_ok, meta_spec]
    congr 1
    apply bool_eq_decide
    simp [AtomStart, u32_eq_iff]
    tauto
  · rw [tail_end cps (by omega)]
    simp [UScalar.lt_equiv, inside]

theorem quantifier_start_spec (cps : alloc.vec.Vec U32) (i : Usize) :
    patterns.quantifier_start cps i = ok (decide (∃ c ∈ (tail cps i.val).head?, QuantifierStart c)) := by
  rw [patterns.quantifier_start]
  by_cases inside : i.val < cps.val.length
  · rw [tail_cons cps inside]
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_at inside, bind_ok]
    congr 1
    apply bool_eq_decide
    simp [QuantifierStart, u32_eq_iff]
    omega
  · rw [tail_end cps (by omega)]
    simp [UScalar.lt_equiv, inside]

theorem interval_strings (c : U32) : Denotes (.Interval c c) = single {c.val} := by
  ext w
  simp only [Denotes, single, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl, lo, hi⟩; exact ⟨x, by omega, rfl⟩
  · rintro ⟨x, rfl, rfl⟩; exact ⟨c.val, rfl, le_rfl, le_rfl⟩

mutual
theorem reg_exp_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) (start : i.val ≤ cps.val.length) :
    ∃ r, patterns.reg_exp cps i = .ok r ∧ ∀ e j, r = some (e, j) →
      ∃ L, RegExp U (tail cps i.val) L (tail cps j.val) ∧ SameStrings (Denotes e) L ∧ i.val ≤ j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.reg_exp]
  have bound := cps.property
  obtain ⟨b, bRun, bSpec⟩ := branch_spec U cps i start
  cases b with
  | none => simp only [bRun, bind_ok]; exact ⟨none, rfl, by simp⟩
  | some p =>
    obtain ⟨left, next⟩ := p
    obtain ⟨L, br, same, le1, le2⟩ := bSpec left next rfl
    simp only [bRun, bind_ok, uncurry_apply_pair]
    by_cases bar : (tail cps next.val).head? = some 124
    · have hb : patterns.is_at cps next 124#u32 = ok true := is_at_of (by simp [bar])
      obtain ⟨nextInside, barTail⟩ := is_at_true (v := 124#u32) (by simpa using bar)
      simp only [u32_ofNat_val] at barTail
      obtain ⟨n1, a1, v1⟩ := add_one nextInside bound
      simp only [hb, ↓reduceIte, a1, bind_ok]
      obtain ⟨re, reRun, reSpec⟩ := reg_exp_spec U cps n1 (by omega)
      cases re with
      | none => simp only [reRun, bind_ok]; exact ⟨none, rfl, by simp⟩
      | some q =>
        obtain ⟨right, after⟩ := q
        obtain ⟨M, rest, sameM, le3, le4⟩ := reSpec right after rfl
        obtain ⟨alt, altRun, altDen⟩ := alternate_total_correct left right
        simp only [reRun, bind_ok, uncurry_apply_pair, altRun]
        refine ⟨_, rfl, ?_⟩
        intro e j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨L + M, ?_, by rw [altDen]; exact sameStrings_add same sameM, by omega, le4⟩
        rw [barTail, ← v1] at br
        exact .more br rest
    · have hb : patterns.is_at cps next 124#u32 = ok false := is_at_of (by simp [bar])
      simp only [hb, bind_ok, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      intro e j h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨L, .last br bar, same, le1, le2⟩
termination_by (cps.val.length - i.val, 3)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

theorem branch_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) (start : i.val ≤ cps.val.length) :
    ∃ r, patterns.branch cps i = .ok r ∧ ∀ e j, r = some (e, j) →
      ∃ L, Branch U (tail cps i.val) L (tail cps j.val) ∧ SameStrings (Denotes e) L ∧ i.val ≤ j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.branch, atom_start_spec]
  by_cases begins : ∃ c ∈ (tail cps i.val).head?, AtomStart c
  · simp only [begins, decide_true, bind_ok, ↓reduceIte]
    obtain ⟨pc, pcRun, pcSpec⟩ := piece_spec U cps i start
    cases pc with
    | none => simp only [pcRun, bind_ok]; exact ⟨none, rfl, by simp⟩
    | some p =>
      obtain ⟨first, next⟩ := p
      obtain ⟨L, piece, same, lt1, le1⟩ := pcSpec first next rfl
      simp only [pcRun, bind_ok, uncurry_apply_pair, UScalar.lt_equiv, lt1, ↓reduceIte]
      obtain ⟨br, brRun, brSpec⟩ := branch_spec U cps next le1
      cases br with
      | none => simp only [brRun, bind_ok]; exact ⟨none, rfl, by simp⟩
      | some q =>
        obtain ⟨rest, after⟩ := q
        obtain ⟨M, branch, sameM, le2, le3⟩ := brSpec rest after rfl
        obtain ⟨sq, sqRun, sqDen⟩ := sequence_total_correct first rest
        simp only [brRun, bind_ok, uncurry_apply_pair, sqRun]
        refine ⟨_, rfl, ?_⟩
        intro e j h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨L * M, .piece piece branch, by rw [sqDen]; exact sameStrings_mul same sameM, by omega, le3⟩
  · simp only [begins, decide_false, bind_ok, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    intro e j h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨1, .done (fun c hc start => begins ⟨c, hc, start⟩), ?_, le_rfl, start⟩
    intro w _
    simp [Denotes]
termination_by (cps.val.length - i.val, 2)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

theorem piece_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) (start : i.val ≤ cps.val.length) :
    ∃ r, patterns.piece cps i = .ok r ∧ ∀ e j, r = some (e, j) →
      ∃ L, Piece U (tail cps i.val) L (tail cps j.val) ∧ SameStrings (Denotes e) L ∧ i.val < j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.piece]
  obtain ⟨at', atRun, atSpec⟩ := atom_spec U cps i start
  cases at' with
  | none => simp only [atRun, bind_ok]; exact ⟨none, rfl, by simp⟩
  | some p =>
    obtain ⟨expression, next⟩ := p
    obtain ⟨L, atom, same, lt1, le1⟩ := atSpec expression next rfl
    simp only [atRun, bind_ok, uncurry_apply_pair, quantifier_start_spec]
    by_cases quantified : ∃ c ∈ (tail cps next.val).head?, QuantifierStart c
    · simp only [quantified, decide_true, ↓reduceIte]
      obtain ⟨qt, qtRun, qtSpec⟩ := quantifier_spec cps next
      cases qt with
      | none => simp only [qtRun, bind_ok]; exact ⟨none, rfl, by simp⟩
      | some t =>
        obtain ⟨least, most, after⟩ := t
        obtain ⟨quant, small, order, lt2, le2⟩ := qtSpec least most after rfl
        obtain ⟨rp, rpRun, rpSpec⟩ := repeated_spec expression least most small order
        simp only [qtRun, bind_ok, uncurry_apply_pair, rpRun]
        cases rp with
        | none => exact ⟨none, rfl, by simp⟩
        | some result =>
          refine ⟨_, rfl, ?_⟩
          intro e j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Repeats L least.val (most.map (·.val)), .quantified atom quant, ?_, by omega, le2⟩
          rw [rpSpec _ rfl]
          exact sameStrings_repeats same _ _
    · simp only [quantified, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      intro e j h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨L, .atom atom (fun c hc q => quantified ⟨c, hc, q⟩), same, lt1, le1⟩
termination_by (cps.val.length - i.val, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

theorem atom_spec (U : UnicodeData) (cps : alloc.vec.Vec U32) (i : Usize) (_start : i.val ≤ cps.val.length) :
    ∃ r, patterns.atom cps i = .ok r ∧ ∀ e j, r = some (e, j) →
      ∃ L, Atom U (tail cps i.val) L (tail cps j.val) ∧ SameStrings (Denotes e) L ∧ i.val < j.val ∧
        j.val ≤ cps.val.length := by
  rw [patterns.atom]
  have bound := cps.property
  by_cases inside : i.val < cps.val.length
  · have here := tail_cons cps inside
    simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte, alloc.vec.Vec.index_slice_index,
      lookup_at inside, bind_ok, u32_eq_iff, u32_ofNat_val]
    obtain ⟨n1, a1, v1⟩ := add_one inside bound
    by_cases paren : cps.val[i.val].val = 40
    · simp only [paren, ↓reduceIte, a1, bind_ok]
      obtain ⟨re, reRun, reSpec⟩ := reg_exp_spec U cps n1 (by omega)
      cases re with
      | none => simp only [reRun, bind_ok]; exact ⟨none, rfl, by simp⟩
      | some q =>
        obtain ⟨expression, next⟩ := q
        obtain ⟨L, re, same, le1, le2⟩ := reSpec expression next rfl
        simp only [reRun, bind_ok, uncurry_apply_pair]
        by_cases close : (tail cps next.val).head? = some 41
        · have hc : patterns.is_at cps next 41#u32 = ok true := is_at_of (by simp [close])
          obtain ⟨nextInside, closeTail⟩ := is_at_true (v := 41#u32) (by simpa using close)
          simp only [u32_ofNat_val] at closeTail
          obtain ⟨n2, a2, v2⟩ := add_one nextInside bound
          simp only [hc, ↓reduceIte, a2, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro e j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨L, ?_, same, by omega, by omega⟩
          rw [here, paren, ← v1, v2]
          rw [closeTail] at re
          exact .group re
        · have hc : patterns.is_at cps next 41#u32 = ok false := is_at_of (by simp [close])
          simp only [hc, bind_ok, Bool.false_eq_true, ↓reduceIte]
          exact ⟨none, rfl, by simp⟩
    · simp only [paren, ↓reduceIte]
      by_cases cls : cps.val[i.val].val = 92 ∨ cps.val[i.val].val = 91 ∨ cps.val[i.val].val = 46
      · have cond : ((decide (cps.val[i.val].val = 92) || decide (cps.val[i.val].val = 91)) ||
            decide (cps.val[i.val].val = 46)) = true := by
          rcases cls with h | h | h <;> simp [h]
        simp only [cond, ↓reduceIte]
        obtain ⟨cc, ccRun, ccSpec⟩ := char_class_spec U cps i
        cases cc with
        | none => simp only [ccRun, bind_ok]; exact ⟨none, rfl, by simp⟩
        | some q =>
          obtain ⟨spans, next⟩ := q
          obtain ⟨C, charClass, same, lt1, le1⟩ := ccSpec spans next rfl
          obtain ⟨se, seRun, seDen⟩ := spans_expression_spec spans 0#usize
          simp only [ccRun, bind_ok, uncurry_apply_pair, seRun]
          refine ⟨_, rfl, ?_⟩
          intro e j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨single C, .charClass charClass, ?_, lt1, le1⟩
          rw [seDen]
          simpa using sameStrings_single same
      · have cond : ((decide (cps.val[i.val].val = 92) || decide (cps.val[i.val].val = 91)) ||
            decide (cps.val[i.val].val = 46)) = false := by
          simp only [not_or] at cls
          simp [cls.1, cls.2.1, cls.2.2]
        simp only [cond, Bool.false_eq_true, ↓reduceIte, meta_spec, bind_ok]
        by_cases m : Meta cps.val[i.val].val
        · simp only [m, decide_true, ↓reduceIte]
          exact ⟨none, rfl, by simp⟩
        · simp only [m, decide_false, Bool.false_eq_true, ↓reduceIte, a1, bind_ok]
          refine ⟨_, rfl, ?_⟩
          intro e j h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨single {cps.val[i.val].val}, ?_, ?_, by omega, by omega⟩
          · rw [here, v1]
            exact .normal m
          · rw [interval_strings]
            exact sameStrings_refl _
  · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, inside, ↓reduceIte]
    exact ⟨none, rfl, by simp⟩
termination_by (cps.val.length - i.val, 0)
decreasing_by all_goals (apply Prod.Lex.left; omega)
end

/-! ### Whole expressions -/

theorem decode_from_spec (bytes : alloc.vec.Vec U8) (offset : Usize) (out : alloc.vec.Vec U32) :
    ∃ r, patterns.decode_from bytes offset out = .ok r ∧ ∀ v, r = some v →
      ∃ word, Utf8From bytes.val offset.val word ∧ v.val.map (·.val) = out.val.map (·.val) ++ word := by
  rw [patterns.decode_from]
  obtain ⟨step, hs, hc⟩ := Rowl.Unicode.decode_next_total_correct bytes offset
  simp only [hs, bind_ok]
  cases step with
  | End =>
    refine ⟨_, rfl, ?_⟩
    intro v h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨[], ?_, by simp⟩
    rw [show offset.val = bytes.val.length from hc]
    exact .endOfInput
  | Error error => exact ⟨none, rfl, by simp⟩
  | Scalar cp next =>
    obtain ⟨advance, bound, unit⟩ := hc
    by_cases room : out.val.length < Usize.max
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out cp room)
      obtain ⟨r, run, spec⟩ := decode_from_spec bytes next pushed
      refine ⟨r, ?_, ?_⟩
      · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, decide_true, ↓reduceIte, push,
          bind_ok, run]
      · intro v h
        obtain ⟨word, utf, eq⟩ := spec v h
        have width : offset.val + (next.val - offset.val) = next.val := by omega
        refine ⟨cp.val :: word, .character unit (by omega) (by omega) (by rw [width]; exact utf), ?_⟩
        rw [eq, contents]
        simp
    · simp only [alloc.vec.Vec.len_val, UScalar.lt_equiv, usize_max_val, room, decide_false, Bool.false_eq_true,
        ↓reduceIte]
      exact ⟨none, rfl, by simp⟩
termination_by bytes.val.length - offset.val
decreasing_by omega

/-- The expression of `patterns::pattern_expression` has, among the strings of
    code points up to `#x10FFFF`, the strings of the regular expression that the
    bytes encode, whatever the Unicode database. -/
theorem pattern_expression_spec (U : UnicodeData) (bytes : alloc.vec.Vec U8) :
    ∃ r, patterns.pattern_expression bytes = .ok r ∧ ∀ e, r = some e →
      ∃ cps L, Utf8From bytes.val 0 cps ∧ Pattern U cps L ∧ SameStrings (Denotes e) L := by
  rw [patterns.pattern_expression]
  obtain ⟨d, dRun, dSpec⟩ := decode_from_spec bytes 0#usize (alloc.vec.Vec.new U32)
  cases d with
  | none => simp only [dRun, bind_ok]; exact ⟨none, rfl, by simp⟩
  | some cps =>
    obtain ⟨word, utf, eq⟩ := dSpec cps rfl
    simp only [new_val, List.map_nil, List.nil_append] at eq
    obtain ⟨re, reRun, reSpec⟩ := reg_exp_spec U cps 0#usize (by simp)
    simp only [dRun, bind_ok, reRun]
    cases re with
    | none => exact ⟨none, rfl, by simp⟩
    | some q =>
      obtain ⟨e, next⟩ := q
      obtain ⟨L, re, same, _, le⟩ := reSpec e next rfl
      simp only [uncurry_apply_pair]
      by_cases all : next.val = cps.val.length
      · have hall : next = alloc.vec.Vec.len cps := UScalar.eq_of_val_eq (by simpa using all)
        simp only [hall, ↓reduceIte]
        refine ⟨_, rfl, ?_⟩
        intro e' h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨word, L, by simpa using utf, ?_, same⟩
        have t0 : tail cps (0#usize : Usize).val = word := by simp [tail, eq]
        have tn : tail cps next.val = [] := tail_end cps (by omega)
        rw [t0, tn] at re
        exact re
      · have hne : ¬ next = alloc.vec.Vec.len cps := fun h => all (by simp [h])
        simp only [hne, ↓reduceIte]
        exact ⟨none, rfl, by simp⟩

/-- `patterns::pattern_matches` tells whether the code points that UTF-8 bytes
    encode are a string of the expression. -/
theorem pattern_matches_spec (e : Expression) (bytes : alloc.vec.Vec U8) :
    ∃ r, patterns.pattern_matches e bytes = .ok r ∧ ∀ b, r = some b →
      ∃ word, Utf8From bytes.val 0 word ∧ (b = true ↔ word ∈ Denotes e) := by
  rw [patterns.pattern_matches, copy_expression_total]
  obtain ⟨res, run, correct⟩ := matches_utf8_total_correct e bytes
  simp only [bind_ok, run]
  cases res with
  | Matched accepted =>
    refine ⟨_, rfl, ?_⟩
    intro b h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨word, utf, hb⟩ := correct
    exact ⟨word, utf, by rw [hb]; simp⟩
  | MalformedUtf8 err => exact ⟨none, rfl, by simp⟩

end Rowl.Patterns
