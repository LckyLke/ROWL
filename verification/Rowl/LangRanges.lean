import Rowl.Datatypes
import Rowl.IriResolution

/-! # Basic language ranges

Specifications of the kernel module `lang_ranges`: the basic language ranges of
RFC 4647 §2.1, their matching by basic filtering (§3.3.1) on language tags in
lower case, and the search for the well-formed language tags in lower case that
a range matches and none of the ranges that continue it. -/

open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open scoped Computability

namespace Rowl.LangRanges
open regular Rowl.Regular
open Rowl.DatatypeMap (Lowered TagValue BasicRange RangeMatch LanguageTag)
set_option linter.unusedSimpArgs false
attribute [local instance low] Classical.propDecidable

/-- A letter of the language tags in lower case: `-`, a digit or `a` to `z`. -/
def LowerLetter (c : Nat) : Prop := c = 45 ∨ (48 ≤ c ∧ c ≤ 57) ∨ (97 ≤ c ∧ c ≤ 122)

instance (c : Nat) : Decidable (LowerLetter c) := by unfold LowerLetter; infer_instance

/-- A well-formed language tag in lower case. -/
def LowerTag (t : List U8) : Prop :=
  t.map (·.val) ∈ Rowl.LangTag.WellFormedLanguage ∧ ∀ b ∈ t, LowerLetter b.val

/-- A language range in lower case matches a language tag in lower case: `*`
    every tag, and otherwise the tag itself and the tags that continue it after
    a `-`. -/
def Matches (r t : List U8) : Prop := r = [42#u8] ∨ t = r ∨ ∃ rest, t = r ++ 45#u8 :: rest

/-- A range continues another: every range but `*` continues `*`, and the
    ranges that go on after a `-` continue a range but `*`. -/
def Continues (r r' : List U8) : Prop :=
  (r = [42#u8] ∧ r' ≠ [42#u8]) ∨ (r ≠ [42#u8] ∧ ∃ s, r' = r ++ 45#u8 :: s)

/-- A free tag of a range among ranges: a well-formed tag in lower case that the
    range matches and none of the ranges that continue it. -/
def Free (r : List U8) (ranges : List (List U8)) (t : List U8) : Prop :=
  LowerTag t ∧ Matches r t ∧ ∀ r' ∈ ranges, Continues r r' → ¬ Matches r' t

/-- The code points of bytes. -/
def codes (b : alloc.vec.Vec U8) : List Nat := b.val.map (·.val)

-- ---------------------------------------------------------------------------
-- Ranges and their matching
-- ---------------------------------------------------------------------------

theorem star_spec (bytes : alloc.vec.Vec U8) :
    lang_ranges.star bytes = .ok (decide (bytes.val = [42#u8])) := by
  rw [lang_ranges.star]
  by_cases one : bytes.val.length = 1
  · obtain ⟨b, hb⟩ : ∃ b, bytes.val = [b] := List.length_eq_one_iff.mp one
    have len : alloc.vec.Vec.len bytes = 1#usize := UScalar.eq_of_val_eq (by simp [one])
    have lookup : bytes.index_usize 0#usize = .ok b := by simp [alloc.vec.Vec.index_usize, hb]
    simp [len, alloc.vec.Vec.index_slice_index, lookup, hb]
  · have len : ¬ alloc.vec.Vec.len bytes = 1#usize := fun h => one (by simpa using congrArg UScalar.val h)
    have ne : bytes.val ≠ [42#u8] := fun h => one (by simp [h])
    simp [len, ne]

theorem basic_range_spec (bytes : alloc.vec.Vec U8) :
    lang_ranges.basic_range bytes = .ok (decide (BasicRange bytes.val)) := by
  obtain ⟨e, run, den⟩ := Rowl.LangTag.range_grammar_total_correct
  have iff := matches_utf8_accepted_iff e bytes
  rw [den] at iff
  have iff' : matches_utf8 e bytes = .ok (.Matched true) ↔ BasicRange bytes.val := iff
  obtain ⟨res, mrun, _⟩ := matches_utf8_total_correct e bytes
  rw [lang_ranges.basic_range, run]
  cases res with
  | Matched b =>
    cases b with
    | true => simp [mrun, iff'.mp mrun]
    | false =>
      have no : ¬ BasicRange bytes.val := fun h => by
        have := mrun.symm.trans (iff'.mpr h); simp at this
      simp [mrun, no]
  | MalformedUtf8 err =>
    have no : ¬ BasicRange bytes.val := fun h => by
      have := mrun.symm.trans (iff'.mpr h); simp at this
    simp [mrun, no]

/-- A byte with the ASCII capital letters in lower case, as a code point. -/
def lowerByte (b : U8) : Nat := if 65 ≤ b.val ∧ b.val ≤ 90 then b.val + 32 else b.val

private theorem lowered_from_spec (bytes : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (len : out.val.length = index.val) :
    ∃ res suffix, lang_ranges.lowered_from bytes index out = .ok res ∧ res.val = out.val ++ suffix ∧
      Lowered (bytes.val.drop index.val) suffix := by
  rw [lang_ranges.lowered_from]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have short : out.val.length < Usize.max := by have := bytes.property; omega
    have room : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      simp [UScalar.lt_equiv, core.num.Usize.MAX]; omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have tail : ∀ (low : U8), low.val = lowerByte bytes.val[index.val] → ∀ pushed : alloc.vec.Vec U8,
        pushed.val = out.val ++ [low] → ∃ res suffix, lang_ranges.lowered_from bytes next pushed = .ok res ∧
          res.val = out.val ++ suffix ∧ Lowered (bytes.val.drop index.val) suffix := by
      intro low lowValue pushed contents
      obtain ⟨res, suffix, rest, resIs, lowered⟩ := lowered_from_spec bytes next pushed
        (by rw [contents, nextIndex]; simp [len])
      refine ⟨res, low :: suffix, rest, by rw [resIs, contents]; simp, ?_⟩
      rw [nextIndex] at lowered
      rw [List.drop_eq_getElem_cons inside]
      unfold Lowered at lowered ⊢
      simp only [List.map_cons, lowered, lowValue, lowerByte]
    by_cases capital : 65 ≤ bytes.val[index.val].val ∧ bytes.val[index.val].val ≤ 90
    · obtain ⟨sum, sumRun, sumValue⟩ := WP.spec_imp_exists
        (U8.add_spec (x := bytes.val[index.val]) (y := 32#u8) (by scalar_tac))
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out sum short)
      obtain ⟨res, suffix, rest, resIs, lowered⟩ := tail sum (by simp [lowerByte, capital, sumValue]) pushed contents
      exact ⟨res, suffix, by simp [UScalar.lt_equiv, inside, room, alloc.vec.Vec.index_slice_index, lookup,
        UScalar.le_equiv, capital, sumRun, push, advance, rest], resIs, lowered⟩
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out bytes.val[index.val] short)
      obtain ⟨res, suffix, rest, resIs, lowered⟩ := tail bytes.val[index.val]
        (by simp [lowerByte, capital]) pushed contents
      refine ⟨res, suffix, ?_, resIs, lowered⟩
      simp [UScalar.lt_equiv, inside, room, alloc.vec.Vec.index_slice_index, lookup, UScalar.le_equiv,
        capital, push, advance, rest]
  · refine ⟨out, [], by simp [UScalar.lt_equiv, inside], by simp, ?_⟩
    simp [Lowered, List.drop_eq_nil_iff.mpr (show bytes.val.length ≤ index.val by omega)]
termination_by bytes.val.length - index.val
decreasing_by omega

theorem lowered_spec (bytes : alloc.vec.Vec U8) :
    ∃ res, lang_ranges.lowered bytes = .ok res ∧ Lowered bytes.val res.val := by
  obtain ⟨res, suffix, run, resIs, lowered⟩ := lowered_from_spec bytes 0#usize (alloc.vec.Vec.new U8) (by simp)
  refine ⟨res, by rw [lang_ranges.lowered, run], ?_⟩
  simpa [resIs] using lowered

private theorem prefix_from_spec (range tag : alloc.vec.Vec U8) (index : Usize) :
    lang_ranges.prefix_from range tag index =
      .ok (decide (range.val.drop index.val <+: tag.val.drop index.val)) := by
  rw [lang_ranges.prefix_from]
  by_cases inside : index.val < range.val.length
  · by_cases inTag : index.val < tag.val.length
    · have hl : range.index_usize index = .ok range.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      have hr : tag.index_usize index = .ok tag.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inTag]
      have split : (range.val.drop index.val <+: tag.val.drop index.val) ↔
          range.val[index.val] = tag.val[index.val] ∧
            range.val.drop (index.val + 1) <+: tag.val.drop (index.val + 1) := by
        rw [List.drop_eq_getElem_cons inside, List.drop_eq_getElem_cons inTag, List.cons_prefix_cons]
      by_cases heads : range.val[index.val] = tag.val[index.val]
      · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextval : next.val = index.val + 1 := by simpa using hv
        have ih := prefix_from_spec range tag next
        rw [nextval] at ih
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, inTag, ↓reduceIte,
          alloc.vec.Vec.index_slice_index, hl, hr, bind_tc_ok, bind_ok, heads, hn, ih]
        congr 1
        exact decide_eq_decide.mpr (by rw [split]; simp [heads])
      · simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, inTag, ↓reduceIte,
          alloc.vec.Vec.index_slice_index, hl, hr, bind_tc_ok, bind_ok, heads]
        congr 1
        symm
        exact decide_eq_false (by rw [split]; simp [heads])
    · have none : tag.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
      have no : ¬ (range.val.drop index.val <+: tag.val.drop index.val) := by
        rw [none]; intro pre
        have := pre.length_le
        simp only [List.length_drop, List.length_nil] at this
        omega
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, inTag, ↓reduceIte]
      congr 1
      exact (decide_eq_false no).symm
  · have none : range.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, inside, none]
termination_by range.val.length - index.val
decreasing_by omega

/-- A range but `*` matches the tags it begins that are as long or go on with a
    `-`. -/
theorem matches_iff {r t : List U8} (notStar : r ≠ [42#u8]) :
    Matches r t ↔ r <+: t ∧ (t.length = r.length ∨ ∃ h : r.length < t.length, t[r.length] = 45#u8) := by
  unfold Matches
  constructor
  · rintro (star | same | ⟨rest, rfl⟩)
    · exact absurd star notStar
    · subst same; exact ⟨List.prefix_refl _, Or.inl rfl⟩
    · refine ⟨⟨45#u8 :: rest, rfl⟩, Or.inr ⟨by simp, by simp⟩⟩
  · rintro ⟨⟨rest, rfl⟩, same | ⟨longer, dash⟩⟩
    · right; left
      have : rest = [] := by simpa using same
      simp [this]
    · right; right
      cases rest with
      | nil => simp at longer
      | cons x rest =>
        refine ⟨rest, ?_⟩
        have : x = 45#u8 := by simpa using dash
        rw [this]

theorem range_matches_spec (range tag : alloc.vec.Vec U8) :
    lang_ranges.range_matches range tag = .ok (decide (Matches range.val tag.val)) := by
  rw [lang_ranges.range_matches, star_spec]
  by_cases isStar : range.val = [42#u8]
  · simp [isStar, Matches]
  · have p := prefix_from_spec range tag 0#usize
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at p
    have iff := matches_iff (t := tag.val) isStar
    by_cases shorter : range.val.length < tag.val.length
    · have hr : tag.index_usize (alloc.vec.Vec.len range) = .ok (tag.val[range.val.length]'shorter) := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem shorter]
      have lt : alloc.vec.Vec.len range < alloc.vec.Vec.len tag := by simp [UScalar.lt_equiv]; omega
      by_cases dash : tag.val[range.val.length]'shorter = 45#u8
      · have key : decide (Matches range.val tag.val) = decide (range.val <+: tag.val) :=
          decide_eq_decide.mpr (by rw [iff]; exact ⟨fun h => h.1, fun h => ⟨h, Or.inr ⟨shorter, dash⟩⟩⟩)
        rw [key]
        simp [isStar, lt, alloc.vec.Vec.index_slice_index, hr, dash, p]
      · have no : ¬ Matches range.val tag.val := by
          rw [iff]; rintro ⟨_, same | ⟨_, d⟩⟩
          · omega
          · exact dash d
        simp [isStar, lt, alloc.vec.Vec.index_slice_index, hr, dash, no]
    · have notLt : ¬ alloc.vec.Vec.len range < alloc.vec.Vec.len tag := by simp [UScalar.lt_equiv]; omega
      by_cases equal : range.val.length = tag.val.length
      · have eq' : alloc.vec.Vec.len range = alloc.vec.Vec.len tag := UScalar.eq_of_val_eq (by simpa using equal)
        have key : decide (Matches range.val tag.val) = decide (range.val <+: tag.val) :=
          decide_eq_decide.mpr (by rw [iff]; exact ⟨fun h => h.1, fun h => ⟨h, Or.inl equal.symm⟩⟩)
        rw [key]
        simp [isStar, notLt, eq', p]
      · have ne' : ¬ alloc.vec.Vec.len range = alloc.vec.Vec.len tag := fun h => equal (by
          simpa using congrArg UScalar.val h)
        have no : ¬ Matches range.val tag.val := by
          rw [iff]; rintro ⟨pre, _⟩
          have := pre.length_le; omega
        simp [isStar, notLt, ne', no]

/-- Matching a range in lower case is matching the range by basic filtering. -/
theorem lowered_unique {r a b : List U8} (ha : Lowered r a) (hb : Lowered r b) : a = b := by
  unfold Lowered at ha hb
  have := ha.trans hb.symm
  exact List.map_injective_iff.mpr (fun x y h => UScalar.eq_of_val_eq h) this

theorem lowered_star {r lower : List U8} (low : Lowered r lower) : r = [42#u8] ↔ lower = [42#u8] := by
  unfold Lowered at low
  constructor
  · rintro rfl
    apply List.map_injective_iff.mpr (fun x y h => UScalar.eq_of_val_eq h)
    simpa using low
  · rintro rfl
    cases r with
    | nil => simp at low
    | cons x rest =>
      cases rest with
      | cons y more => simp at low
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true,
          show ((42#u8 : U8)).val = 42 from rfl] at low
        have : x.val = 42 := by split_ifs at low <;> omega
        simp only [List.cons.injEq, and_true]
        exact UScalar.eq_of_val_eq (by simpa using this)

theorem range_match_iff {r lower : List U8} (low : Lowered r lower) (t : List U8) :
    RangeMatch r t ↔ Matches lower t := by
  unfold RangeMatch Matches
  rw [lowered_star low]
  constructor
  · rintro (star | ⟨other, otherLow, rest⟩)
    · exact Or.inl star
    · rw [lowered_unique otherLow low] at rest
      exact Or.inr rest
  · rintro (star | rest)
    · exact Or.inl star
    · exact Or.inr ⟨lower, low, rest⟩

-- ---------------------------------------------------------------------------
-- Words of expressions
-- ---------------------------------------------------------------------------

theorem nonempty_spec (e : Expression) :
    lang_ranges.nonempty e = .ok (decide (∃ w, w ∈ Denotes e)) := by
  induction e with
  | Empty =>
    have no : ¬ ∃ w, w ∈ Denotes .Empty := fun ⟨w, hw⟩ => by simp [Denotes] at hw
    rw [lang_ranges.nonempty]
    exact congrArg Result.ok (decide_eq_false no).symm
  | Epsilon =>
    have yes : ∃ w, w ∈ Denotes .Epsilon := ⟨[], by simp [Denotes]⟩
    rw [lang_ranges.nonempty]
    exact congrArg Result.ok (decide_eq_true yes).symm
  | Interval lower upper =>
    rw [lang_ranges.nonempty]
    congr 1
    refine decide_eq_decide.mpr ?_
    simp only [UScalar.le_equiv, Denotes]
    constructor
    · intro h; exact ⟨[lower.val], lower.val, rfl, le_rfl, h⟩
    · rintro ⟨_, cp, _, low, high⟩; omega
  | Alternative left right hl hr =>
    rw [lang_ranges.nonempty, hl, hr]
    simp only [bind_tc_ok, bind_ok]
    congr 1
    rw [← Bool.decide_or]
    refine decide_eq_decide.mpr ?_
    simp only [Denotes]
    constructor
    · rintro (⟨w, hw⟩ | ⟨w, hw⟩)
      · exact ⟨w, (Language.mem_add _ _ _).mpr (Or.inl hw)⟩
      · exact ⟨w, (Language.mem_add _ _ _).mpr (Or.inr hw)⟩
    · rintro ⟨w, hw⟩
      rcases (Language.mem_add _ _ _).mp hw with h | h
      · exact Or.inl ⟨w, h⟩
      · exact Or.inr ⟨w, h⟩
  | Sequence left right hl hr =>
    rw [lang_ranges.nonempty, hl, hr]
    simp only [bind_tc_ok, bind_ok]
    congr 1
    rw [← Bool.decide_and]
    refine decide_eq_decide.mpr ?_
    simp only [Denotes]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨a ++ b, Language.mem_mul.mpr ⟨a, ha, b, hb, rfl⟩⟩
    · rintro ⟨w, hw⟩
      obtain ⟨a, ha, b, hb, _⟩ := Language.mem_mul.mp hw
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  | Repeat inner =>
    have yes : ∃ w, w ∈ Denotes (.Repeat inner) := ⟨[], by simp only [Denotes]; exact Language.nil_mem_kstar _⟩
    rw [lang_ranges.nonempty]
    exact congrArg Result.ok (decide_eq_true yes).symm

theorem derive_spec (e : Expression) (bytes : alloc.vec.Vec U8) (index : Usize) :
    ∃ r, lang_ranges.derive e bytes index = .ok r ∧
      ∀ w, w ∈ Denotes r ↔ (bytes.val.drop index.val).map (·.val) ++ w ∈ Denotes e := by
  rw [lang_ranges.derive]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨d, drun, dlang⟩ := derivative_total_correct e (UScalar.cast .U32 bytes.val[index.val])
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    obtain ⟨r, rrun, rlang⟩ := derive_spec d bytes next
    refine ⟨r, ?_, fun w => ?_⟩
    · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, drun, hn, rrun, lift]
    · have split : (bytes.val.drop index.val).map (·.val) =
          bytes.val[index.val].val :: (bytes.val.drop (index.val + 1)).map (·.val) := by
        rw [List.drop_eq_getElem_cons inside, List.map_cons]
      rw [rlang, nextval, split, List.cons_append, dlang, U8.cast_U32_val_eq]
  · refine ⟨e, by simp [UScalar.lt_equiv, inside], fun w => ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show bytes.val.length ≤ index.val by omega)]
termination_by bytes.val.length - index.val
decreasing_by omega

-- ---------------------------------------------------------------------------
-- The search for free tags
-- ---------------------------------------------------------------------------

/-- A word is blocked by a block it is or continues after a `-`. -/
def Blocked (b w : List Nat) : Prop := w = b ∨ ∃ rest, w = b ++ 45 :: rest

/-- Some word of a language, of the letters of the tags in lower case, is
    blocked by none of the blocks. -/
def Avoids (L : Language Nat) (blocks : List (List Nat)) : Prop :=
  ∃ w ∈ L, (∀ c ∈ w, LowerLetter c) ∧ ∀ b ∈ blocks, ¬ Blocked b w

/-- The words that complete a prefix to a word of a language. -/
def suffixes (p : List Nat) (L : Language Nat) : Language Nat := {w | p ++ w ∈ L}

theorem mem_suffixes {p w : List Nat} {L : Language Nat} : w ∈ suffixes p L ↔ p ++ w ∈ L := Iff.rfl

/-- The blocks that go on with a letter, each past it. -/
def after (c : Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | [] :: bs => after c bs
  | (d :: rest) :: bs => if d = c then rest :: after c bs else after c bs

theorem mem_after {c : Nat} {blocks : List (List Nat)} {b : List Nat} :
    b ∈ after c blocks ↔ c :: b ∈ blocks := by
  induction blocks with
  | nil => simp [after]
  | cons x bs ih =>
    cases x with
    | nil => simp [after, ih]
    | cons d rest =>
      by_cases h : d = c
      · subst h; simp [after, ih]
      · have ne : ¬ c = d := fun e => h e.symm
        simp [after, h, ih, ne]

/-- The size of blocks: their lengths, each and one more. -/
def size (blocks : List (List Nat)) : Nat := (blocks.map (·.length + 1)).sum

theorem size_after_le (c : Nat) (blocks : List (List Nat)) : size (after c blocks) ≤ size blocks := by
  induction blocks with
  | nil => simp [after, size]
  | cons x bs ih =>
    cases x with
    | nil => simp only [after, size, List.map_cons, List.sum_cons] at ih ⊢; omega
    | cons d rest =>
      by_cases h : d = c
      · simp only [after, h, ↓reduceIte, size, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega
      · simp only [after, h, ↓reduceIte, size, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem size_after_lt (c : Nat) (blocks : List (List Nat)) (h : blocks ≠ []) :
    size (after c blocks) < size blocks := by
  cases blocks with
  | nil => exact absurd rfl h
  | cons x bs =>
    have le := size_after_le c bs
    cases x with
    | nil => simp only [after, size, List.map_cons, List.sum_cons] at le ⊢; omega
    | cons d rest =>
      by_cases hd : d = c
      · simp only [after, hd, ↓reduceIte, size, List.map_cons, List.sum_cons, List.length_cons] at le ⊢; omega
      · simp only [after, hd, ↓reduceIte, size, List.map_cons, List.sum_cons, List.length_cons] at le ⊢; omega

theorem size_pos {blocks : List (List Nat)} (h : blocks ≠ []) : 0 < size blocks := by
  cases blocks with
  | nil => exact absurd rfl h
  | cons x bs => simp [size]

theorem blocked_nil_right (b : List Nat) : Blocked b [] ↔ b = [] := by
  unfold Blocked
  constructor
  · rintro (h | ⟨rest, h⟩)
    · exact h.symm
    · simp at h
  · rintro rfl; exact Or.inl rfl

theorem blocked_cons (d c : Nat) (b w : List Nat) : Blocked (d :: b) (c :: w) ↔ d = c ∧ Blocked b w := by
  unfold Blocked
  simp only [List.cons.injEq, List.cons_append]
  constructor
  · rintro (⟨e, rest⟩ | ⟨tail, e, rest⟩)
    · exact ⟨e.symm, Or.inl rest⟩
    · exact ⟨e.symm, Or.inr ⟨tail, rest⟩⟩
  · rintro ⟨e, rest | ⟨tail, rest⟩⟩
    · exact Or.inl ⟨e.symm, rest⟩
    · exact Or.inr ⟨tail, e.symm, rest⟩

/-- A word passes the blocks when it is empty and no block is, or when its
    first letter is no `-` after an empty block and the rest passes the blocks
    that go on with that letter. -/
theorem avoids_step (L : Language Nat) (blocks : List (List Nat)) :
    Avoids L blocks ↔ ((∀ b ∈ blocks, b ≠ []) ∧ [] ∈ L) ∨
      ∃ c, LowerLetter c ∧ ((∃ b ∈ blocks, b = []) → c ≠ 45) ∧
        Avoids (suffixes [c] L) (after c blocks) := by
  constructor
  · rintro ⟨w, hw, letters, pass⟩
    cases w with
    | nil =>
      left
      exact ⟨fun b hb e => pass b hb (by rw [e]; exact Or.inl rfl), hw⟩
    | cons c w =>
      right
      refine ⟨c, letters c (by simp), ?_, w, hw, fun x hx => letters x (by simp [hx]), ?_⟩
      · rintro ⟨b, hb, rfl⟩ dash
        exact pass [] hb (Or.inr ⟨w, by simp [dash]⟩)
      · intro b hb blocked
        exact pass (c :: b) (mem_after.mp hb) ((blocked_cons c c b w).mpr ⟨rfl, blocked⟩)
  · rintro (⟨nonempty, hw⟩ | ⟨c, lc, stop, w, hw, letters, pass⟩)
    · exact ⟨[], hw, by simp, fun b hb blocked => nonempty b hb ((blocked_nil_right b).mp blocked)⟩
    · refine ⟨c :: w, hw, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | inner
        · exact lc
        · exact letters x inner
      · intro b hb blocked
        cases b with
        | nil =>
          rcases blocked with e | ⟨rest, e⟩
          · simp at e
          · simp only [List.nil_append, List.cons.injEq] at e
            exact stop ⟨[], hb, rfl⟩ e.1
        | cons d b =>
          obtain ⟨e, inner⟩ := (blocked_cons d c b w).mp blocked
          subst e
          exact pass b (mem_after.mpr hb) inner

theorem lowerNat_fixed {c : Nat} (h : LowerLetter c) : Rowl.LangTag.lowerNat c = c := by
  unfold Rowl.LangTag.lowerNat LowerLetter at *
  split_ifs <;> omega

theorem lowerNat_lower {c : Nat} (h : Rowl.LangTag.TagLetter c) : LowerLetter (Rowl.LangTag.lowerNat c) := by
  unfold Rowl.LangTag.lowerNat Rowl.LangTag.TagLetter LowerLetter at *
  split_ifs <;> omega

theorem lower_tag_letter {c : Nat} (h : LowerLetter c) : Rowl.LangTag.TagLetter c := by
  unfold LowerLetter Rowl.LangTag.TagLetter at *
  omega

/-- The words completing a prefix of letters in lower case keep the language
    closed under lower case. -/
theorem closed_suffixes {L : Language Nat} (closed : Rowl.LangTag.LowerClosed L) (p : List Nat)
    (lower : ∀ c ∈ p, LowerLetter c) : Rowl.LangTag.LowerClosed (suffixes p L) := by
  intro w hw
  obtain ⟨letters, low⟩ := closed (p ++ w) hw
  refine ⟨fun c hc => letters c (List.mem_append_right p hc), ?_⟩
  show p ++ w.map Rowl.LangTag.lowerNat ∈ L
  have fixed : p.map Rowl.LangTag.lowerNat = p := by
    conv_rhs => rw [← List.map_id p]
    exact List.map_congr_left (fun c hc => lowerNat_fixed (lower c hc))
  rw [List.map_append, fixed] at low
  exact low

/-- In a language closed under lower case, some word is of the letters of tags
    in lower case as soon as there is any. -/
theorem avoids_nil {L : Language Nat} (closed : Rowl.LangTag.LowerClosed L) : Avoids L [] ↔ ∃ w, w ∈ L := by
  constructor
  · rintro ⟨w, hw, _, _⟩; exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨letters, low⟩ := closed w hw
    refine ⟨w.map Rowl.LangTag.lowerNat, low, fun c hc => ?_, fun b hb => nomatch hb⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact lowerNat_lower (letters x hx)

/-- The letter of the tags in lower case at an index below 37: `-`, the
    digits, then `a` to `z`. -/
def tagLetter (i : Nat) : Nat := if i = 0 then 45 else if i < 11 then 47 + i else 86 + i

theorem tag_letter_spec (i : U8) (h : i.val < 37) :
    ∃ b : U8, lang_ranges.tag_letter i = .ok b ∧ b.val = tagLetter i.val := by
  rw [lang_ranges.tag_letter]
  by_cases zero : i = 0#u8
  · subst zero; exact ⟨45#u8, by simp, by simp [tagLetter]⟩
  · have zero' : i.val ≠ 0 := fun e => zero (UScalar.eq_of_val_eq (by simpa using e))
    by_cases small : i.val < 11
    · obtain ⟨s, run, val⟩ := WP.spec_imp_exists (U8.add_spec (x := 47#u8) (y := i) (by scalar_tac))
      have lt : i < 11#u8 := by simp [UScalar.lt_equiv]; omega
      exact ⟨s, by simp [zero, lt, run], by simp [tagLetter, zero', small, val]⟩
    · obtain ⟨s, run, val⟩ := WP.spec_imp_exists (U8.add_spec (x := 86#u8) (y := i) (by scalar_tac))
      have lt : ¬ i < 11#u8 := by simp [UScalar.lt_equiv]; omega
      exact ⟨s, by simp [zero, lt, run], by simp [tagLetter, zero', small, val]⟩

theorem tagLetter_lower (i : Nat) (h : i < 37) : LowerLetter (tagLetter i) := by
  unfold tagLetter LowerLetter; split_ifs <;> omega

theorem lower_tagLetter {c : Nat} (h : LowerLetter c) : ∃ i < 37, tagLetter i = c := by
  rcases h with rfl | ⟨lo, hi⟩ | ⟨lo, hi⟩
  · exact ⟨0, by omega, by simp [tagLetter]⟩
  · exact ⟨c - 47, by omega, by unfold tagLetter; split_ifs <;> omega⟩
  · exact ⟨c - 86, by omega, by unfold tagLetter; split_ifs <;> omega⟩

theorem ended_spec (blocks : alloc.vec.Vec (alloc.vec.Vec U8)) (index : Usize) :
    lang_ranges.ended blocks index = .ok (decide (∃ b ∈ blocks.val.drop index.val, b.val = [])) := by
  rw [lang_ranges.ended]
  by_cases inside : index.val < blocks.val.length
  · have lookup : blocks.index_usize index = .ok blocks.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split : (∃ b ∈ blocks.val.drop index.val, b.val = []) ↔
        blocks.val[index.val].val = [] ∨ ∃ b ∈ blocks.val.drop (index.val + 1), b.val = [] := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons, exists_eq_or_imp]
    by_cases empty : blocks.val[index.val].val = []
    · have len : alloc.vec.Vec.len blocks.val[index.val] = 0#usize := UScalar.eq_of_val_eq (by simp [empty])
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, lookup, bind_tc_ok, bind_ok, len]
      exact congrArg Result.ok (decide_eq_true (split.mpr (Or.inl empty))).symm
    · have len : ¬ alloc.vec.Vec.len blocks.val[index.val] = 0#usize := fun h => empty (by
        have := congrArg UScalar.val h; simpa using this)
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := ended_spec blocks next
      rw [nextval] at ih
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, ↓reduceIte,
        alloc.vec.Vec.index_slice_index, lookup, bind_tc_ok, bind_ok, len, hn, ih]
      congr 1
      exact decide_eq_decide.mpr (by rw [split]; simp [empty])
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show blocks.val.length ≤ index.val by omega)]
termination_by blocks.val.length - index.val
decreasing_by omega

theorem copy_from_spec (bytes : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length + (bytes.val.length - index.val) ≤ Usize.max) :
    ∃ v, lang_ranges.copy_from bytes index out = .ok v ∧ v.val = out.val ++ bytes.val.drop index.val := by
  rw [lang_ranges.copy_from]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have short : out.val.length < Usize.max := by omega
    have roomLt : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      simp [UScalar.lt_equiv, core.num.Usize.MAX]; omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out bytes.val[index.val] short)
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    obtain ⟨v, run, vIs⟩ := copy_from_spec bytes next pushed (by rw [contents, nextval]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside, roomLt, alloc.vec.Vec.index_slice_index, lookup, push, hn, run]
    · rw [vIs, contents, nextval, List.drop_eq_getElem_cons inside]; simp
  · exact ⟨out, by simp [UScalar.lt_equiv, inside], by simp [List.drop_eq_nil_iff.mpr (show bytes.val.length ≤ index.val by omega)]⟩
termination_by bytes.val.length - index.val
decreasing_by omega

theorem after_cons (c : Nat) (x : List Nat) (xs : List (List Nat)) :
    after c (x :: xs) = after c [x] ++ after c xs := by
  cases x with
  | nil => simp [after]
  | cons d rest => by_cases h : d = c <;> simp [after, h]

theorem blocks_after_spec (blocks : alloc.vec.Vec (alloc.vec.Vec U8)) (letter : U8) (index : Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec U8)) (room : out.val.length + (blocks.val.length - index.val) ≤ Usize.max) :
    ∃ v, lang_ranges.blocks_after blocks letter index out = .ok v ∧
      v.val.map codes = out.val.map codes ++ after letter.val ((blocks.val.drop index.val).map codes) := by
  rw [lang_ranges.blocks_after]
  by_cases inside : index.val < blocks.val.length
  · have lookup : blocks.index_usize index = .ok blocks.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have split : (blocks.val.drop index.val).map codes =
        codes blocks.val[index.val] :: (blocks.val.drop next.val).map codes := by
      rw [List.drop_eq_getElem_cons inside, nextval, List.map_cons]
    rw [split, after_cons]
    cases hb : blocks.val[index.val].val with
    | nil =>
      have len : ¬ (0#usize < alloc.vec.Vec.len blocks.val[index.val]) := by simp [UScalar.lt_equiv, hb]
      obtain ⟨v, run, vIs⟩ := blocks_after_spec blocks letter next out (by rw [nextval]; omega)
      refine ⟨v, ?_, ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, hb, hn, run]
      · rw [vIs]; simp [codes, hb, after]
    | cons d rest =>
      have len : 0#usize < alloc.vec.Vec.len blocks.val[index.val] := by simp [UScalar.lt_equiv, hb]
      have first : blocks.val[index.val].index_usize 0#usize = .ok d := by
        simp [alloc.vec.Vec.index_usize, hb]
      by_cases same : d = letter
      · subst same
        have short : out.val.length < Usize.max := by omega
        have roomLt : alloc.vec.Vec.len out < core.num.Usize.MAX := by
          simp [UScalar.lt_equiv, core.num.Usize.MAX]; omega
        obtain ⟨copy, copyRun, copyIs⟩ := copy_from_spec blocks.val[index.val] 1#usize (alloc.vec.Vec.new U8)
          (by have := blocks.val[index.val].property; simp; omega)
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out copy short)
        obtain ⟨v, run, vIs⟩ := blocks_after_spec blocks d next pushed (by rw [contents, nextval]; simp; omega)
        refine ⟨v, ?_, ?_⟩
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, hb, first, roomLt,
            copyRun, push, hn, run]
        · rw [vIs, contents]
          simp [codes, hb, after, copyIs]
      · have ne : d.val ≠ letter.val := fun e => same (UScalar.eq_of_val_eq e)
        obtain ⟨v, run, vIs⟩ := blocks_after_spec blocks letter next out (by rw [nextval]; omega)
        refine ⟨v, ?_, ?_⟩
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, hb, first, same, hn, run]
        · rw [vIs]; simp [codes, hb, after, ne]
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show blocks.val.length ≤ index.val by omega), after]
termination_by blocks.val.length - index.val
decreasing_by all_goals omega

/-- The choice of a letter: no `-` after an ended block, and some word after
    the letter passes the blocks that go on with it. -/
def Branch (e : Expression) (blocks : List (List Nat)) (stop : Bool) (i : Nat) : Prop :=
  ¬ (stop = true ∧ tagLetter i = 45) ∧ Avoids (suffixes [tagLetter i] (Denotes e)) (after (tagLetter i) blocks)

private theorem exists_from {P : Nat → Prop} {l : Nat} (h : l < 37) :
    (∃ i, l ≤ i ∧ i < 37 ∧ P i) ↔ P l ∨ ∃ i, l + 1 ≤ i ∧ i < 37 ∧ P i := by
  constructor
  · rintro ⟨i, low, high, p⟩
    rcases Nat.eq_or_lt_of_le low with rfl | lt
    · exact Or.inl p
    · exact Or.inr ⟨i, lt, high, p⟩
  · rintro (p | ⟨i, low, high, p⟩)
    · exact ⟨l, le_rfl, h, p⟩
    · exact ⟨i, by omega, high, p⟩

private theorem letters_avoid_spec (n : Nat)
    (ih : ∀ (e : Expression) (blocks : alloc.vec.Vec (alloc.vec.Vec U8)), size (blocks.val.map codes) ≤ n →
      Rowl.LangTag.LowerClosed (Denotes e) →
        lang_ranges.avoids e blocks = .ok (decide (Avoids (Denotes e) (blocks.val.map codes))))
    (e : Expression) (blocks : alloc.vec.Vec (alloc.vec.Vec U8)) (stop : Bool)
    (sized : size (blocks.val.map codes) ≤ n + 1) (nonempty : blocks.val ≠ [])
    (closed : Rowl.LangTag.LowerClosed (Denotes e)) :
    ∀ (k : Nat) (letter : U8), letter.val + k = 37 →
      lang_ranges.letters_avoid e blocks stop letter =
        .ok (decide (∃ i, letter.val ≤ i ∧ i < 37 ∧ Branch e (blocks.val.map codes) stop i)) := by
  intro k
  induction k with
  | zero =>
    intro letter h
    have no : ¬ ∃ i, letter.val ≤ i ∧ i < 37 ∧ Branch e (blocks.val.map codes) stop i := by
      rintro ⟨i, low, high, _⟩; omega
    have notLt : ¬ letter < 37#u8 := by simp [UScalar.lt_equiv]; omega
    rw [lang_ranges.letters_avoid]
    simp [notLt, no]
  | succ k ihk =>
    intro letter h
    have lt : letter < 37#u8 := by simp [UScalar.lt_equiv]; omega
    obtain ⟨byte, byteRun, byteVal⟩ := tag_letter_spec letter (by omega)
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (U8.add_spec (x := letter) (y := 1#u8) (by scalar_tac))
    have nextval : next.val = letter.val + 1 := by simpa using hv
    have rest := ihk next (by omega)
    rw [nextval] at rest
    have from' := exists_from (P := Branch e (blocks.val.map codes) stop) (l := letter.val) (by omega)
    by_cases skip : stop = true ∧ byte = 45#u8
    · have no : ¬ Branch e (blocks.val.map codes) stop letter.val := by
        rintro ⟨notSkip, _⟩
        exact notSkip ⟨skip.1, by rw [← byteVal, skip.2]; rfl⟩
      have run : lang_ranges.letters_avoid e blocks stop letter = lang_ranges.letters_avoid e blocks stop next := by
        rw [lang_ranges.letters_avoid]; simp [lt, byteRun, skip, hn]
      rw [run, rest]
      exact congrArg Result.ok (decide_eq_decide.mpr (by rw [from']; simp [no]))
    · obtain ⟨d, drun, dlang⟩ := derivative_total_correct e (UScalar.cast .U32 byte)
      obtain ⟨v, vrun, vIs⟩ := blocks_after_spec blocks byte 0#usize (alloc.vec.Vec.new _)
        (by simp)
      have dIs : Denotes d = suffixes [tagLetter letter.val] (Denotes e) := by
        ext w
        rw [dlang, U8.cast_U32_val_eq, byteVal]
        rfl
      have dclosed : Rowl.LangTag.LowerClosed (Denotes d) := by
        rw [dIs]
        exact closed_suffixes closed _ (by simpa using tagLetter_lower letter.val (by omega))
      have vIs' : v.val.map codes = after (tagLetter letter.val) (blocks.val.map codes) := by
        simpa [byteVal] using vIs
      have vsize : size (v.val.map codes) ≤ n := by
        rw [vIs']
        have := size_after_lt (tagLetter letter.val) (blocks.val.map codes) (by simpa using nonempty)
        omega
      have here := ih d v vsize dclosed
      have skipVal : ¬ (stop = true ∧ tagLetter letter.val = 45) := by
        rintro ⟨s, t⟩
        exact skip ⟨s, UScalar.eq_of_val_eq (by rw [byteVal, t]; rfl)⟩
      have branchIff : Branch e (blocks.val.map codes) stop letter.val ↔ Avoids (Denotes d) (v.val.map codes) := by
        unfold Branch
        rw [dIs, vIs']
        simp [skipVal]
      by_cases found : Avoids (Denotes d) (v.val.map codes)
      · have run : lang_ranges.letters_avoid e blocks stop letter = .ok true := by
          rw [lang_ranges.letters_avoid]
          simp [lt, byteRun, skip, copy_expression_total, lift, drun, vrun, here, found]
        rw [run]
        exact congrArg Result.ok (decide_eq_true (from'.mpr (Or.inl (branchIff.mpr found)))).symm
      · have run : lang_ranges.letters_avoid e blocks stop letter =
            lang_ranges.letters_avoid e blocks stop next := by
          rw [lang_ranges.letters_avoid]
          simp [lt, byteRun, skip, copy_expression_total, lift, drun, vrun, here, found, hn]
        rw [run, rest]
        exact congrArg Result.ok (decide_eq_decide.mpr (by rw [from', branchIff]; simp [found]))

/-- The search finds whether some word of an expression closed under lower
    case, of the letters of tags in lower case, passes the blocks. -/
theorem avoids_spec : ∀ (n : Nat) (e : Expression) (blocks : alloc.vec.Vec (alloc.vec.Vec U8)),
    size (blocks.val.map codes) ≤ n → Rowl.LangTag.LowerClosed (Denotes e) →
      lang_ranges.avoids e blocks = .ok (decide (Avoids (Denotes e) (blocks.val.map codes))) := by
  have emptyCase : ∀ (e : Expression) (blocks : alloc.vec.Vec (alloc.vec.Vec U8)), blocks.val = [] →
      Rowl.LangTag.LowerClosed (Denotes e) →
        lang_ranges.avoids e blocks = .ok (decide (Avoids (Denotes e) (blocks.val.map codes))) := by
    intro e blocks empty closed
    have len : alloc.vec.Vec.len blocks = 0#usize := UScalar.eq_of_val_eq (by simp [empty])
    have run : lang_ranges.avoids e blocks = lang_ranges.nonempty e := by
      rw [lang_ranges.avoids]; simp [len]
    rw [run, nonempty_spec, empty, List.map_nil]
    exact congrArg Result.ok (decide_eq_decide.mpr (avoids_nil closed).symm)
  intro n
  induction n with
  | zero =>
    intro e blocks sized closed
    apply emptyCase e blocks _ closed
    by_contra h
    have := size_pos (blocks := blocks.val.map codes) (by simpa using h)
    omega
  | succ n ih =>
    intro e blocks sized closed
    by_cases empty : blocks.val = []
    · exact emptyCase e blocks empty closed
    · have len : ¬ alloc.vec.Vec.len blocks = 0#usize := fun h => empty (by
        have := congrArg UScalar.val h; simpa using this)
      have stopIs := ended_spec blocks 0#usize
      simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at stopIs
      have nullIs := nullable_total_correct e
      have step := avoids_step (Denotes e) (blocks.val.map codes)
      have endedIff : (∃ b ∈ blocks.val.map codes, b = []) ↔ ∃ b ∈ blocks.val, b.val = [] := by
        simp [codes]
      by_cases quick : (¬ ∃ b ∈ blocks.val, b.val = []) ∧ [] ∈ Denotes e
      · have holds : Avoids (Denotes e) (blocks.val.map codes) := by
          rw [step]; left
          exact ⟨fun b hb e' => quick.1 (endedIff.mp ⟨b, hb, e'⟩), quick.2⟩
        have run : lang_ranges.avoids e blocks = .ok true := by
          rw [lang_ranges.avoids]; simp [len, stopIs, nullIs, quick.1, quick.2]
        rw [run]
        exact congrArg Result.ok (decide_eq_true holds).symm
      · have letters := letters_avoid_spec n ih e blocks
          (decide (∃ b ∈ blocks.val, b.val = [])) sized empty closed 37 0#u8 (by simp)
        have run : lang_ranges.avoids e blocks =
            lang_ranges.letters_avoid e blocks (decide (∃ b ∈ blocks.val, b.val = [])) 0#u8 := by
          rw [lang_ranges.avoids]
          by_cases a : ∃ b ∈ blocks.val, b.val = []
          · simp [len, stopIs, nullIs, a]
          · have b : [] ∉ Denotes e := fun hb => quick ⟨a, hb⟩
            simp [len, stopIs, nullIs, a, b]
        rw [run, letters]
        congr 1
        refine decide_eq_decide.mpr ?_
        rw [step]
        have noLeft : ¬ ((∀ b ∈ blocks.val.map codes, b ≠ []) ∧ [] ∈ Denotes e) := by
          rintro ⟨all, hw⟩
          exact quick ⟨fun ⟨b, hb, e'⟩ => all (codes b) (List.mem_map_of_mem hb) (by simp [codes, e']), hw⟩
        simp only [noLeft, false_or, show (0#u8).val = 0 from rfl, zero_le, true_and]
        constructor
        · rintro ⟨i, high, notSkip, avoids⟩
          exact ⟨tagLetter i, tagLetter_lower i high,
            fun stopped dash => notSkip ⟨decide_eq_true (endedIff.mp stopped), dash⟩, avoids⟩
        · rintro ⟨c, lc, stopOk, avoids⟩
          obtain ⟨i, high, rfl⟩ := lower_tagLetter lc
          exact ⟨i, high, fun ⟨stopped, dash⟩ => stopOk (endedIff.mpr (of_decide_eq_true stopped)) dash, avoids⟩

-- ---------------------------------------------------------------------------
-- Free tags
-- ---------------------------------------------------------------------------

theorem byte_of {c : Nat} (h : c < 256) : ∃ b : U8, b.val = c :=
  ⟨U8.ofNatCore c (by simpa using h), U8.ofNatCore_val_eq _⟩

theorem bytes_of : ∀ (w : List Nat), (∀ c ∈ w, c < 256) → ∃ t : List U8, t.map (·.val) = w
  | [], _ => ⟨[], rfl⟩
  | c :: w, h => by
    obtain ⟨b, hb⟩ := byte_of (h c (by simp))
    obtain ⟨t, ht⟩ := bytes_of w (fun x hx => h x (by simp [hx]))
    exact ⟨b :: t, by simp [hb, ht]⟩

theorem vals_injective {a b : List U8} (h : a.map (·.val) = b.map (·.val)) : a = b :=
  List.map_injective_iff.mpr (fun _ _ e => UScalar.eq_of_val_eq e) h

/-- Blocking on code points is matching on bytes. -/
theorem blocked_vals (r t : List U8) :
    Blocked (r.map (·.val)) (t.map (·.val)) ↔ t = r ∨ ∃ rest, t = r ++ 45#u8 :: rest := by
  unfold Blocked
  constructor
  · rintro (same | ⟨rest, e⟩)
    · exact Or.inl (vals_injective same)
    · right
      obtain ⟨pre, post, rfl, preIs, postIs⟩ := List.map_eq_append_iff.mp e
      have : pre = r := vals_injective preIs
      subst this
      obtain ⟨x, more, rfl, xIs, _⟩ := List.map_eq_cons_iff.mp postIs
      exact ⟨more, by rw [show x = 45#u8 from UScalar.eq_of_val_eq (by simpa using xIs)]⟩
  · rintro (rfl | ⟨rest, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨rest.map (·.val), by simp⟩

theorem continued_not_star (r s : List U8) : r ++ 45#u8 :: s ≠ [42#u8] := by
  cases r with
  | nil => simp
  | cons x rest => intro h; have := congrArg List.length h; simp at this

theorem plain_ranges_spec (ranges : alloc.vec.Vec (alloc.vec.Vec U8)) (index : Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec U8)) (room : out.val.length + (ranges.val.length - index.val) ≤ Usize.max) :
    ∃ v, lang_ranges.plain_ranges ranges index out = .ok v ∧
      ∀ b, b ∈ v.val.map codes ↔ b ∈ out.val.map codes ∨
        ∃ r ∈ ranges.val.drop index.val, r.val ≠ [42#u8] ∧ codes r = b := by
  rw [lang_ranges.plain_ranges]
  by_cases inside : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have split : ranges.val.drop index.val = ranges.val[index.val] :: ranges.val.drop next.val := by
      rw [List.drop_eq_getElem_cons inside, nextval]
    by_cases isStar : ranges.val[index.val].val = [42#u8]
    · obtain ⟨v, run, vIs⟩ := plain_ranges_spec ranges next out (by rw [nextval]; omega)
      refine ⟨v, ?_, fun b => ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, star_spec, isStar, hn, run]
      · rw [vIs, split]
        simp only [List.mem_cons, exists_eq_or_imp, isStar, ne_eq, not_true_eq_false, false_and, false_or]
    · have short : out.val.length < Usize.max := by omega
      have roomLt : alloc.vec.Vec.len out < core.num.Usize.MAX := by
        simp [UScalar.lt_equiv, core.num.Usize.MAX]; omega
      obtain ⟨copy, copyRun, copyIs⟩ := copy_from_spec ranges.val[index.val] 0#usize (alloc.vec.Vec.new U8)
        (by simp)
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out copy short)
      obtain ⟨v, run, vIs⟩ := plain_ranges_spec ranges next pushed (by rw [contents, nextval]; simp; omega)
      refine ⟨v, ?_, fun b => ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, star_spec, isStar, roomLt,
          copyRun, push, hn, run]
      · have copyCodes : codes copy = codes ranges.val[index.val] := by
          simp [codes, copyIs, show (0#usize).val = 0 from rfl]
        rw [vIs, contents, split]
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
          copyCodes, List.mem_cons, exists_eq_or_imp, List.not_mem_nil, or_false]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨isStar, h.symm⟩)
          · exact Or.inr (Or.inr h)
        · rintro (h | ⟨_, h⟩ | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h.symm)
          · exact Or.inr h
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], fun b => ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show ranges.val.length ≤ index.val by omega)]
termination_by ranges.val.length - index.val
decreasing_by all_goals omega

/-- Whether some well-formed tag in lower case matches no range but `*`. -/
theorem root_free_spec (ranges : alloc.vec.Vec (alloc.vec.Vec U8)) :
    lang_ranges.root_free ranges =
      .ok (decide (∃ t, LowerTag t ∧ ∀ r ∈ ranges.val, r.val ≠ [42#u8] → ¬ Matches r.val t)) := by
  obtain ⟨v, vrun, vIs⟩ := plain_ranges_spec ranges 0#usize (alloc.vec.Vec.new _)
    (by simp)
  obtain ⟨e, erun, eIs⟩ := Rowl.LangTag.grammar_total_correct
  have search := avoids_spec _ e v le_rfl (by rw [eIs]; exact Rowl.LangTag.well_formed_lower)
  have nv : (alloc.vec.Vec.new (alloc.vec.Vec U8)).val = [] := rfl
  have blocks : ∀ b, b ∈ v.val.map codes ↔ ∃ r ∈ ranges.val, r.val ≠ [42#u8] ∧ codes r = b := by
    intro b
    rw [vIs]
    simp only [nv, List.map_nil, List.not_mem_nil, false_or, show (0#usize).val = 0 from rfl, List.drop_zero]
  have iff : Avoids (Denotes e) (v.val.map codes) ↔
      ∃ t, LowerTag t ∧ ∀ r ∈ ranges.val, r.val ≠ [42#u8] → ¬ Matches r.val t := by
    rw [eIs]
    constructor
    · rintro ⟨w, hw, letters, pass⟩
      obtain ⟨t, rfl⟩ := bytes_of w (fun c hc => by have := letters c hc; unfold LowerLetter at this; omega)
      refine ⟨t, ⟨hw, fun b hb => letters b.val (List.mem_map_of_mem hb)⟩, fun r hr notStar m => ?_⟩
      apply pass (codes r) ((blocks _).mpr ⟨r, hr, notStar, rfl⟩)
      rcases m with star | rest
      · exact absurd star notStar
      · exact (blocked_vals r.val t).mpr rest
    · rintro ⟨t, ⟨wf, letters⟩, none⟩
      refine ⟨t.map (·.val), wf, fun c hc => ?_, fun b hb blocked => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc; exact letters x hx
      · obtain ⟨r, hr, notStar, rfl⟩ := (blocks b).mp hb
        exact none r hr notStar (Or.inr ((blocked_vals r.val t).mp blocked))
  have run : lang_ranges.root_free ranges = lang_ranges.avoids e v := by
    rw [lang_ranges.root_free, vrun]; simp [erun]
  rw [run, search]
  exact congrArg Result.ok (decide_eq_decide.mpr iff)

theorem continuations_spec (range : alloc.vec.Vec U8) (ranges : alloc.vec.Vec (alloc.vec.Vec U8))
    (index : Usize) (out : alloc.vec.Vec (alloc.vec.Vec U8))
    (room : out.val.length + (ranges.val.length - index.val) ≤ Usize.max) :
    ∃ v, lang_ranges.continuations range ranges index out = .ok v ∧
      ∀ b, b ∈ v.val.map codes ↔ b ∈ out.val.map codes ∨
        ∃ r ∈ ranges.val.drop index.val, range.val.length < r.val.length ∧ Matches range.val r.val ∧
          (r.val.drop (range.val.length + 1)).map (·.val) = b := by
  rw [lang_ranges.continuations]
  by_cases inside : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextval : next.val = index.val + 1 := by simpa using hv
    have split : ranges.val.drop index.val = ranges.val[index.val] :: ranges.val.drop next.val := by
      rw [List.drop_eq_getElem_cons inside, nextval]
    by_cases longer : range.val.length < ranges.val[index.val].val.length
    · by_cases m : Matches range.val ranges.val[index.val].val
      · have short : out.val.length < Usize.max := by omega
        have roomLt : alloc.vec.Vec.len out < core.num.Usize.MAX := by
          simp [UScalar.lt_equiv, core.num.Usize.MAX]; omega
        have bound := ranges.val[index.val].property
        obtain ⟨plus, plusRun, plusVal⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := alloc.vec.Vec.len range) (y := 1#usize) (by simp; omega))
        have plusIs : plus.val = range.val.length + 1 := by simpa using plusVal
        obtain ⟨copy, copyRun, copyIs⟩ := copy_from_spec ranges.val[index.val] plus (alloc.vec.Vec.new U8)
          (by simp; omega)
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out copy short)
        obtain ⟨v, run, vIs⟩ := continuations_spec range ranges next pushed
          (by rw [contents, nextval]; simp; omega)
        refine ⟨v, ?_, fun b => ?_⟩
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, longer, range_matches_spec, m,
            roomLt, plusRun, copyRun, push, hn, run]
        · have copyCodes : codes copy = (ranges.val[index.val].val.drop (range.val.length + 1)).map (·.val) := by
            simp [codes, copyIs, plusIs]
          rw [vIs, contents, split]
          simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
            copyCodes, List.mem_cons, exists_eq_or_imp, List.not_mem_nil, or_false]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl ⟨longer, m, h.symm⟩)
            · exact Or.inr (Or.inr h)
          · rintro (h | ⟨_, _, h⟩ | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h.symm)
            · exact Or.inr h
      · obtain ⟨v, run, vIs⟩ := continuations_spec range ranges next out (by rw [nextval]; omega)
        refine ⟨v, ?_, fun b => ?_⟩
        · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, longer, range_matches_spec, m,
            hn, run]
        · rw [vIs, split]
          simp only [List.mem_cons, exists_eq_or_imp, m, false_and, and_false, false_or]
    · obtain ⟨v, run, vIs⟩ := continuations_spec range ranges next out (by rw [nextval]; omega)
      refine ⟨v, ?_, fun b => ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, longer, hn, run]
      · rw [vIs, split]
        simp only [List.mem_cons, exists_eq_or_imp, longer, false_and, false_or]
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], fun b => ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show ranges.val.length ≤ index.val by omega)]
termination_by ranges.val.length - index.val
decreasing_by all_goals omega

/-- Whether a range has free tags among ranges: well-formed tags in lower case
    that it matches and none of the ranges that continue it. -/
theorem free_tags_spec (range : alloc.vec.Vec U8) (ranges : alloc.vec.Vec (alloc.vec.Vec U8))
    (lower : range.val = [42#u8] ∨ ∀ b ∈ range.val, LowerLetter b.val) :
    lang_ranges.free_tags range ranges = .ok (decide (∃ t, Free range.val (ranges.val.map (·.val)) t)) := by
  by_cases isStar : range.val = [42#u8]
  · have run : lang_ranges.free_tags range ranges = lang_ranges.root_free ranges := by
      rw [lang_ranges.free_tags, star_spec]; simp [isStar]
    rw [run, root_free_spec]
    congr 1
    refine decide_eq_decide.mpr ?_
    unfold Free Continues
    constructor
    · rintro ⟨t, low, none⟩
      refine ⟨t, low, Or.inl isStar, fun r' hr' cont m => ?_⟩
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      rcases cont with ⟨_, notStar⟩ | ⟨bad, _⟩
      · exact none r hr notStar m
      · exact bad isStar
    · rintro ⟨t, low, _, none⟩
      exact ⟨t, low, fun r hr notStar m => none r.val (List.mem_map_of_mem hr) (Or.inl ⟨isStar, notStar⟩) m⟩
  · have letters := lower.resolve_left isStar
    obtain ⟨v, vrun, vIs⟩ := continuations_spec range ranges 0#usize (alloc.vec.Vec.new _)
      (by simp)
    obtain ⟨g, grun, gIs⟩ := Rowl.LangTag.grammar_total_correct
    obtain ⟨rest, restRun, restLang⟩ := derive_spec g range 0#usize
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at restLang
    have nullIs := nullable_total_correct rest
    have nv : (alloc.vec.Vec.new (alloc.vec.Vec U8)).val = [] := rfl
    have blocks : ∀ b, b ∈ v.val.map codes ↔
        ∃ r ∈ ranges.val, ∃ s, r.val = range.val ++ 45#u8 :: s ∧ s.map (·.val) = b := by
      intro b
      rw [vIs]
      simp only [nv, List.map_nil, List.not_mem_nil, false_or, show (0#usize).val = 0 from rfl, List.drop_zero]
      constructor
      · rintro ⟨r, hr, longer, m, rfl⟩
        refine ⟨r, hr, ?_⟩
        rcases m with star | same | ⟨s, rIs⟩
        · exact absurd star isStar
        · rw [same] at longer; omega
        · exact ⟨s, rIs, by rw [rIs]; simp⟩
      · rintro ⟨r, hr, s, rIs, rfl⟩
        exact ⟨r, hr, by rw [rIs]; simp, Or.inr (Or.inr ⟨s, rIs⟩), by rw [rIs]; simp⟩
    by_cases nullable : [] ∈ Denotes rest
    · have run : lang_ranges.free_tags range ranges = .ok true := by
        rw [lang_ranges.free_tags, star_spec]; simp [isStar, vrun, grun, restRun, nullIs, nullable]
      rw [run]
      have wf : range.val.map (·.val) ∈ Rowl.LangTag.WellFormedLanguage := by
        have := (restLang []).mp nullable
        simpa [gIs] using this
      refine congrArg Result.ok (decide_eq_true ⟨range.val, ⟨wf, letters⟩, Or.inr (Or.inl rfl),
        fun r' _ cont m => ?_⟩).symm
      rcases cont with ⟨bad, _⟩ | ⟨_, s, rfl⟩
      · exact isStar bad
      · rcases m with star | same | ⟨tail, e⟩
        · exact continued_not_star _ _ star
        · have := congrArg List.length same; simp at this
        · have := congrArg List.length e; simp at this
    · obtain ⟨d, drun, dlang⟩ := derivative_total_correct rest 45#u32
      have dIs : Denotes d = suffixes (range.val.map (·.val) ++ [45]) (Denotes g) := by
        ext w
        rw [dlang, restLang]
        simp [suffixes, mem_suffixes]
      have dclosed : Rowl.LangTag.LowerClosed (Denotes d) := by
        rw [dIs]
        apply closed_suffixes (by rw [gIs]; exact Rowl.LangTag.well_formed_lower)
        intro c hc
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at hc
        rcases hc with ⟨b, hb, rfl⟩ | rfl
        · exact letters b hb
        · exact Or.inl rfl
      have search := avoids_spec _ d v le_rfl dclosed
      have run : lang_ranges.free_tags range ranges = lang_ranges.avoids d v := by
        rw [lang_ranges.free_tags, star_spec]; simp [isStar, vrun, grun, restRun, nullIs, nullable, drun]
      rw [run, search]
      congr 1
      refine decide_eq_decide.mpr ?_
      rw [dIs, gIs]
      constructor
      · rintro ⟨w, hw, wl, pass⟩
        obtain ⟨tail, rfl⟩ := bytes_of w (fun c hc => by have := wl c hc; unfold LowerLetter at this; omega)
        refine ⟨range.val ++ 45#u8 :: tail, ⟨by simpa [suffixes] using hw, ?_⟩,
          Or.inr (Or.inr ⟨tail, rfl⟩), fun r' hr' cont m => ?_⟩
        · intro b hb
          simp only [List.mem_append, List.mem_cons] at hb
          rcases hb with hb | rfl | hb
          · exact letters b hb
          · exact Or.inl rfl
          · exact wl b.val (List.mem_map_of_mem hb)
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
          rcases cont with ⟨bad, _⟩ | ⟨_, s, rIs⟩
          · exact isStar bad
          · apply pass (s.map (·.val)) ((blocks _).mpr ⟨r, hr, s, rIs, rfl⟩)
            rw [rIs] at m
            rcases m with star | same | ⟨more, e⟩
            · exact absurd star (continued_not_star _ _)
            · have : tail = s := by simpa using same
              exact (blocked_vals s tail).mpr (Or.inl this)
            · have : tail = s ++ 45#u8 :: more := by simpa using e
              exact (blocked_vals s tail).mpr (Or.inr ⟨more, this⟩)
      · rintro ⟨t, ⟨wf, tl⟩, m, none⟩
        rcases m with star | same | ⟨tail, rfl⟩
        · exact absurd star isStar
        · subst same
          exact absurd ((restLang []).mpr (by simpa [gIs] using wf)) nullable
        · refine ⟨tail.map (·.val), by simpa [suffixes] using wf, fun c hc => ?_, fun b hb blocked => ?_⟩
          · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
            exact tl x (by simp [hx])
          · obtain ⟨r, hr, s, rIs, rfl⟩ := (blocks b).mp hb
            apply none r.val (List.mem_map_of_mem hr) (Or.inr ⟨isStar, s, rIs⟩)
            rw [rIs]
            rcases (blocked_vals s tail).mp blocked with same | ⟨more, e⟩
            · exact Or.inr (Or.inl (by rw [same]))
            · exact Or.inr (Or.inr ⟨more, by rw [e]; simp⟩)

-- ---------------------------------------------------------------------------
-- Tags and ranges as values
-- ---------------------------------------------------------------------------

/-- ASCII bytes are the UTF-8 of their own code points. -/
theorem utf8_ascii (bs : List U8) (ascii : ∀ b ∈ bs, b.val < 128) :
    Rowl.Regular.Utf8From bs 0 (bs.map (·.val)) := by
  have step : ∀ k, k ≤ bs.length →
      Rowl.Regular.Utf8From bs (bs.length - k) ((bs.drop (bs.length - k)).map (·.val)) := by
    intro k
    induction k with
    | zero => intro _; simpa using Rowl.Regular.Utf8From.endOfInput
    | succ k ih =>
      intro hk
      have rest := ih (by omega)
      have inside : bs.length - (k + 1) < bs.length := by omega
      have ha := ascii _ (List.getElem_mem inside)
      have next : bs.length - (k + 1) + 1 = bs.length - k := by omega
      rw [List.drop_eq_getElem_cons inside, next, List.map_cons]
      refine .character (width := 1) ?_ (by decide) (by omega) ?_
      · simp [Rowl.Unicode.Prefix, List.getElem?_eq_getElem inside, ha]
      · rw [next]; exact rest
  simpa using step bs.length le_rfl

/-- UTF-8 of ASCII code points is their bytes. -/
theorem utf8_of_ascii {bs : List U8} {word : List Nat} (h : Rowl.Regular.Utf8From bs 0 word)
    (ascii : ∀ c ∈ word, c < 128) : bs.map (·.val) = word := by
  have decoded := (Rowl.IriResolution.utf8_decoded h).1
  simp only [List.drop_zero] at decoded
  rw [decoded]
  clear decoded h
  induction word with
  | nil => simp
  | cons c w ih =>
    have hc : c < 128 := ascii c (by simp)
    rw [List.flatMap_cons, ih (fun x hx => ascii x (by simp [hx]))]
    simp [Rowl.IriResolution.utf8, hc]

/-- The language tags in lower case of the values are the well-formed tags in
    lower case. -/
theorem tag_value_iff (t : List U8) : TagValue t ↔ LowerTag t := by
  unfold TagValue LanguageTag LowerTag
  constructor
  · rintro ⟨written, ⟨word, utf, wf⟩, low⟩
    obtain ⟨letters, lowWf⟩ := Rowl.LangTag.well_formed_lower word wf
    have ascii : ∀ c ∈ word, c < 128 := fun c hc => by
      have := letters c hc; unfold Rowl.LangTag.TagLetter at this; omega
    have same := utf8_of_ascii utf ascii
    unfold Lowered at low
    have tIs : t.map (·.val) = word.map Rowl.LangTag.lowerNat := by
      rw [low, ← same, List.map_map]; rfl
    refine ⟨by rw [tIs]; exact lowWf, fun b hb => ?_⟩
    have : b.val ∈ word.map Rowl.LangTag.lowerNat := by rw [← tIs]; exact List.mem_map_of_mem hb
    obtain ⟨c, hc, e⟩ := List.mem_map.mp this
    rw [← e]; exact lowerNat_lower (letters c hc)
  · rintro ⟨wf, letters⟩
    refine ⟨t, ⟨t.map (·.val), utf8_ascii t (fun b hb => by
      have := letters b hb; unfold LowerLetter at this; omega), wf⟩, ?_⟩
    unfold Lowered
    apply List.map_congr_left
    intro b hb
    have := letters b hb
    unfold LowerLetter at this
    split_ifs <;> omega

/-- A basic language range in lower case is `*` or of letters of tags in lower
    case. -/
theorem lowered_basic {bytes lower : List U8} (basic : BasicRange bytes) (low : Lowered bytes lower) :
    lower = [42#u8] ∨ ∀ b ∈ lower, LowerLetter b.val := by
  obtain ⟨word, utf, inLang⟩ := basic
  have ascii : ∀ c ∈ word, c < 128 := by
    rcases Rowl.LangTag.range_letters word inLang with rfl | letters
    · simp
    · intro c hc; have := letters c hc; unfold Rowl.LangTag.TagLetter at this; omega
  have same := utf8_of_ascii utf ascii
  rcases Rowl.LangTag.range_letters word inLang with rfl | letters
  · left
    have : bytes = [42#u8] := vals_injective (by simpa using same)
    exact (lowered_star low).mp this
  · right
    intro b hb
    unfold Lowered at low
    have : b.val ∈ bytes.map (fun byte => if 65 ≤ byte.val ∧ byte.val ≤ 90 then byte.val + 32 else byte.val) := by
      rw [← low]; exact List.mem_map_of_mem hb
    obtain ⟨x, hx, e⟩ := List.mem_map.mp this
    have hl : Rowl.LangTag.TagLetter x.val := letters x.val (by rw [← same]; exact List.mem_map_of_mem hx)
    rw [← e]
    unfold Rowl.LangTag.TagLetter at hl; unfold LowerLetter; split_ifs <;> omega

/-- Matching goes down the ranges: a tag that a range matches is matched by the
    ranges that match the range. -/
theorem matches_trans {a b t : List U8} (hab : Matches a b) (hbt : Matches b t) : Matches a t := by
  rcases hab with star | rfl | ⟨s, rfl⟩
  · exact Or.inl star
  · exact hbt
  · rcases hbt with star | rfl | ⟨rest, rfl⟩
    · exact absurd star (continued_not_star _ _)
    · exact Or.inr (Or.inr ⟨s, rfl⟩)
    · exact Or.inr (Or.inr ⟨s ++ 45#u8 :: rest, by simp⟩)

/-- Two ranges that match a tag match one another one way. -/
theorem matches_comparable {a b t : List U8} (ma : Matches a t) (mb : Matches b t) : Matches a b ∨ Matches b a := by
  by_cases sa : a = [42#u8]
  · exact Or.inl (Or.inl sa)
  by_cases sb : b = [42#u8]
  · exact Or.inr (Or.inl sb)
  obtain ⟨pa, ea⟩ := (matches_iff sa).mp ma
  obtain ⟨pb, eb⟩ := (matches_iff sb).mp mb
  rcases Nat.lt_trichotomy a.length b.length with lt | same | gt
  · left
    have pre : a <+: b := List.prefix_of_prefix_length_le pa pb lt.le
    rw [matches_iff sa]
    refine ⟨pre, Or.inr ⟨lt, ?_⟩⟩
    have tLong : b.length ≤ t.length := pb.length_le
    rcases ea with e | ⟨h, dash⟩
    · omega
    · rw [pb.getElem lt]; exact dash
  · left
    have : a = b := by
      have pre : a <+: b := List.prefix_of_prefix_length_le pa pb same.le
      exact pre.eq_of_length same
    rw [this]; exact Or.inr (Or.inl rfl)
  · right
    have pre : b <+: a := List.prefix_of_prefix_length_le pb pa gt.le
    rw [matches_iff sb]
    refine ⟨pre, Or.inr ⟨gt, ?_⟩⟩
    have tLong : a.length ≤ t.length := pa.length_le
    rcases eb with e | ⟨h, dash⟩
    · omega
    · rw [pa.getElem gt]; exact dash

end Rowl.LangRanges
