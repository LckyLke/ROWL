import Rowl.Datatypes
import Rowl.Nnf

/-!
The actual kernel functions of `regions`: the cuts of the real line that the
data encoding uses, in their order, and the number of integers between two
cuts. A cut is a number with a side: the reals at or above it, or above it
(`InCut`). The kernel copies values exactly (`copy_value_eq`), finds and adds
cuts (`cut_index_correct`, `add_cut_correct`), compares two cuts, numbers first
and a closed cut before the open cut of its number (`after_correct`,
`CutBefore`), lists the cuts in that order (`cut_order_spec`, `Ordered`),
counts the integers in one cut and outside another exactly with signed digit
arithmetic (`between_spec`, from the floors and ceilings of the numbers,
`floor_of_spec`, `ceil_of_spec`), and caps the count (`run_size_spec`).
-/
namespace Rowl.Regions
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.DatatypeMap (Digit Digits digitsValue)
open Rowl.Datatypes (CanonicalNumeric CanonicalNumber CanonicalFraction IsNumber numValue magnitude negativeOf
  digitWidth fracValue)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

theorem new_val {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

/-! ### Copies and lists of cuts -/

/-- The kernel copies a value exactly. -/
theorem copy_value_eq (v : datatypes.DataValue) : regions.copy_value v = .ok v := by
  cases v <;> simp [regions.copy_value, Rowl.Nnf.copy_bytes_identity]

/-- The reals a cut contains: those at or above its number, or above it. -/
def InCut (c : regions.Cut) (r : ℝ) : Prop :=
  if c.open then (numValue c.value : ℝ) < r else (numValue c.value : ℝ) ≤ r

theorem cut_eq_iff (a b : regions.Cut) : a = b ↔ a.value = b.value ∧ a.open = b.open := by
  cases a; cases b; simp

/-- The kernel finds the first cut of a number on a side. -/
theorem cut_index_correct (cuts : alloc.vec.Vec regions.Cut) (value : datatypes.DataValue) («open» : Bool)
    (index : Usize) :
    ∃ r, regions.cut_index cuts value «open» index = .ok r ∧
      (r = none → ∀ j, index.val ≤ j → ∀ h : j < cuts.val.length, cuts.val[j] ≠ ⟨value, «open»⟩) ∧
      ∀ i, r = some i → ∃ h : i.val < cuts.val.length, cuts.val[i.val] = ⟨value, «open»⟩ := by
  rw [regions.cut_index]
  by_cases inside : index.val < cuts.val.length
  · have lookup : cuts.index_usize index = .ok cuts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases found : cuts.val[index.val] = ⟨value, «open»⟩
    · refine ⟨some index, ?_, by simp, fun i h => ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, Rowl.Datatypes.same_value_correct,
          found]
      · cases h; exact ⟨inside, found⟩
    · have differs : ¬ (cuts.val[index.val].value = value ∧ cuts.val[index.val].open = «open») :=
        fun both => found ((cut_eq_iff _ _).mpr both)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, absent, present⟩ := cut_index_correct cuts value «open» next
      refine ⟨r, ?_, fun none j low h => ?_, present⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, Rowl.Datatypes.same_value_correct,
          advance, run]
        intro a b; exact absurd ⟨a, b⟩ differs
      · by_cases here : j = index.val
        · subst here; exact found
        · exact absent none j (by omega) h
  · refine ⟨none, by simp [UScalar.lt_equiv, inside], fun _ j low h => by omega, by simp⟩
termination_by cuts.val.length - index.val
decreasing_by omega

/-- The kernel adds a cut that is not there yet, and keeps the cuts apart. -/
theorem add_cut_correct (cuts : alloc.vec.Vec regions.Cut) (value : datatypes.DataValue) («open» : Bool) :
    ∃ r, regions.add_cut cuts value «open» = .ok r ∧ (∀ c ∈ r.val, c ∈ cuts.val ∨ c = ⟨value, «open»⟩) ∧
      (cuts.val.Nodup → r.val.Nodup) := by
  rw [regions.add_cut]
  obtain ⟨r, run, absent, _⟩ := cut_index_correct cuts value «open» 0#usize
  rw [run]
  cases r with
  | some i => exact ⟨cuts, by simp, fun c m => .inl m, id⟩
  | none =>
    have notIn : (⟨value, «open»⟩ : regions.Cut) ∉ cuts.val := by
      intro m
      obtain ⟨j, hj, same⟩ := List.getElem_of_mem m
      exact absent rfl j (by simp) hj same
    by_cases room : cuts.val.length < Usize.max
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec cuts ⟨value, «open»⟩ room)
      refine ⟨pushed, ?_, fun c m => ?_, fun nodup => ?_⟩
      · simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, room, copy_value_eq, push]
      · rw [contents] at m; simpa using m
      · rw [contents]
        refine List.nodup_append.mpr ⟨nodup, by simp, ?_⟩
        intro a ma b mb same
        simp only [List.mem_singleton] at mb
        subst mb; subst same
        exact notIn ma
    · refine ⟨cuts, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, room], fun c m => .inl m, id⟩

/-! ### Signed integers -/

/-- The integer a signed digit vector writes. -/
def signedValue (s : regions.Signed) : ℤ :=
  if s.negative then -(digitsValue s.magnitude.val : ℤ) else (digitsValue s.magnitude.val : ℤ)

/-- A signed digit vector with canonical digits and no sign on zero. -/
def CanonicalSigned (s : regions.Signed) : Prop :=
  Rowl.Numbers.Canonical s.magnitude.val ∧ (s.negative = true → s.magnitude.val ≠ [])

theorem one_spec : ∃ o, regions.one = .ok o ∧ o.val = [49#u8] := by
  obtain ⟨o, run, value⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 49#u8 (by simp [new_val]; scalar_tac))
  exact ⟨o, by rw [regions.one, run], by rw [value]; simp [new_val]⟩

theorem one_canonical : Rowl.Numbers.Canonical [49#u8] := by
  refine ⟨fun b m => ?_, by decide⟩
  simp only [List.mem_singleton] at m
  subst m
  exact ⟨by decide, by decide⟩

theorem one_value : digitsValue [49#u8] = 1 := by decide

theorem canonical_one_le {m : List U8} (c : Rowl.Numbers.Canonical m) (ne : m ≠ []) : 1 ≤ digitsValue m := by
  have := Rowl.Numbers.canonical_low m c ne
  have : 0 < 10 ^ (m.length - 1) := by positivity
  omega

theorem signed_spec (negative : Bool) (magnitude : alloc.vec.Vec U8) (c : Rowl.Numbers.Canonical magnitude.val) :
    ∃ s, regions.signed negative magnitude = .ok s ∧ CanonicalSigned s ∧ s.magnitude = magnitude ∧
      signedValue s = if negative then -(digitsValue magnitude.val : ℤ) else (digitsValue magnitude.val : ℤ) := by
  rw [regions.signed]
  by_cases empty : magnitude.val = []
  · have len : alloc.vec.Vec.len magnitude = 0#usize := by
      apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, empty]
    refine ⟨⟨false, magnitude⟩, by simp [len], ⟨c, by simp⟩, rfl, ?_⟩
    cases negative <;> simp [signedValue, empty, Rowl.Numbers.value_nil]
  · have len : alloc.vec.Vec.len magnitude ≠ 0#usize := by
      intro h; apply empty; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
    exact ⟨⟨negative, magnitude⟩, by simp [len], ⟨c, fun _ => empty⟩, rfl, by simp [signedValue]⟩

/-! ### Floors and ceilings -/

theorem floor_add_frac (w : ℕ) (f : ℚ) (lo : 0 ≤ f) (hi : f < 1) : ⌊(w : ℚ) + f⌋ = w := by
  rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

theorem ceil_add_frac (w : ℕ) (f : ℚ) (lo : 0 < f) (hi : f < 1) : ⌈(w : ℚ) + f⌉ = w + 1 := by
  rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith

theorem div_split (a b : ℕ) (pos : 0 < b) :
    (a : ℚ) / b = ((a / b : ℕ) : ℚ) + ((a % b : ℕ) : ℚ) / b := by
  have bq : (b : ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  have eq : (a : ℚ) = b * (a / b : ℕ) + (a % b : ℕ) := by exact_mod_cast (Nat.div_add_mod a b).symm
  rw [eq]; field_simp

theorem mod_frac (a b : ℕ) (pos : 0 < b) : 0 ≤ ((a % b : ℕ) : ℚ) / b ∧ ((a % b : ℕ) : ℚ) / b < 1 := by
  have bq : (0 : ℚ) < b := by exact_mod_cast pos
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one bq]; exact_mod_cast Nat.mod_lt a pos

theorem floor_div (a b : ℕ) (pos : 0 < b) : ⌊(a : ℚ) / b⌋ = (a / b : ℕ) := by
  rw [div_split a b pos]
  exact floor_add_frac _ _ (mod_frac a b pos).1 (mod_frac a b pos).2

theorem ceil_div (a b : ℕ) (pos : 0 < b) :
    ⌈(a : ℚ) / b⌉ = if a % b = 0 then ((a / b : ℕ) : ℤ) else (a / b : ℕ) + 1 := by
  rw [div_split a b pos]
  split_ifs with zero
  · rw [zero]; simp
  · have bq : (0 : ℚ) < b := by exact_mod_cast pos
    have rpos : (0 : ℚ) < (a % b : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero zero
    exact ceil_add_frac _ _ (div_pos rpos bq) (mod_frac a b pos).2

theorem canonical_of_number {n : Bool} {w f : List U8} (c : CanonicalNumber n w f) :
    Rowl.Numbers.Canonical w :=
  ⟨c.1, c.2.2.1⟩

/-- The kernel rounds a number's magnitude down. -/
theorem floor_magnitude_spec (v : datatypes.DataValue) (c : CanonicalNumeric v)
    (small : digitWidth v + 8 < Usize.max) :
    ∃ m, regions.floor_magnitude v = .ok m ∧ Rowl.Numbers.Canonical m.val ∧
      (digitsValue m.val : ℤ) = ⌊magnitude v⌋ ∧ m.val.length ≤ digitWidth v := by
  cases v with
  | Number n w f =>
    have cn : CanonicalNumber n w.val f.val := c
    obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.canonical_spec w cn.1
    refine ⟨m, by simp [regions.floor_magnitude, run], cm, ?_, by simp only [digitWidth]; omega⟩
    rw [value]
    simp only [magnitude]
    rw [floor_add_frac _ _ (Rowl.Datatypes.fracValue_nonneg _) (Rowl.Datatypes.fracValue_lt_one _ cn.2.1)]
  | Fraction n a b =>
    have cf : CanonicalFraction a.val b.val := c
    obtain ⟨ca, cb, _, positive, _, _⟩ := cf
    simp only [digitWidth] at small
    obtain ⟨q, r, run, cq, _, qValue, _, qLen, _⟩ := Rowl.Numbers.divide_naturals_spec a b ca.1 cb positive
      (by omega)
    refine ⟨q, by simp [regions.floor_magnitude, run], cq, ?_, by simp only [digitWidth]; omega⟩
    rw [qValue]
    simp only [magnitude]
    rw [floor_div _ _ positive]
  | Text t => exact absurd c (by simp [CanonicalNumeric])
  | Tagged t g => exact absurd c (by simp [CanonicalNumeric])
  | Truth b => exact absurd c (by simp [CanonicalNumeric])

/-- The kernel rounds a number's magnitude up. -/
theorem ceil_magnitude_spec (v : datatypes.DataValue) (c : CanonicalNumeric v)
    (small : digitWidth v + 8 < Usize.max) :
    ∃ m, regions.ceil_magnitude v = .ok m ∧ Rowl.Numbers.Canonical m.val ∧
      (digitsValue m.val : ℤ) = ⌈magnitude v⌉ ∧ m.val.length ≤ digitWidth v + 1 := by
  obtain ⟨o, oRun, oValue⟩ := one_spec
  cases v with
  | Number n w f =>
    have cn : CanonicalNumber n w.val f.val := c
    simp only [digitWidth] at small
    by_cases empty : f.val = []
    · have len : alloc.vec.Vec.len f = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, empty]
      obtain ⟨m, run, cm, value, mlen⟩ := Rowl.Numbers.canonical_spec w cn.1
      refine ⟨m, by simp [regions.ceil_magnitude, len, run], cm, ?_, by simp only [digitWidth]; omega⟩
      rw [value]
      simp only [magnitude, empty, fracValue, Rowl.Numbers.value_nil]
      simp
    · have len : alloc.vec.Vec.len f ≠ 0#usize := by
        intro h; apply empty; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
      obtain ⟨m, run, cm, value, mlen⟩ := Rowl.Numbers.add_naturals_spec w o cn.1
        (by rw [oValue]; exact one_canonical.1) (by rw [oValue]; simp; omega)
      refine ⟨m, by simp [regions.ceil_magnitude, len, oRun, run], cm, ?_, ?_⟩
      · rw [value, oValue, one_value]
        simp only [magnitude]
        rw [ceil_add_frac _ _ (Rowl.Datatypes.fracValue_pos _ cn.2.1 empty cn.2.2.2.1)
          (Rowl.Datatypes.fracValue_lt_one _ cn.2.1)]
        push_cast; ring
      · rw [oValue] at mlen; simp only [digitWidth, List.length_singleton] at mlen ⊢
        have : f.val.length ≠ 0 := by simpa using empty
        omega
  | Fraction n a b =>
    have cf : CanonicalFraction a.val b.val := c
    obtain ⟨ca, cb, _, positive, _, _⟩ := cf
    simp only [digitWidth] at small
    obtain ⟨q, r, run, cq, cr, qValue, rValue, qLen, rLen⟩ := Rowl.Numbers.divide_naturals_spec a b ca.1 cb positive
      (by omega)
    simp only [magnitude]
    rw [ceil_div _ _ positive]
    by_cases zero : r.val = []
    · have len : alloc.vec.Vec.len r = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, zero]
      have mod : digitsValue a.val % digitsValue b.val = 0 := by
        rw [← rValue, zero, Rowl.Numbers.value_nil]
      refine ⟨q, by simp [regions.ceil_magnitude, run, len], cq, by rw [qValue]; simp [mod], ?_⟩
      simp only [digitWidth]; omega
    · have len : alloc.vec.Vec.len r ≠ 0#usize := by
        intro h; apply zero; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
      have mod : digitsValue a.val % digitsValue b.val ≠ 0 := by
        rw [← rValue]; exact fun h => zero ((Rowl.Numbers.canonical_zero _ cr).mp h)
      obtain ⟨m, mRun, cm, mValue, mlen⟩ := Rowl.Numbers.add_naturals_spec q o cq.1
        (by rw [oValue]; exact one_canonical.1) (by rw [oValue]; simp; omega)
      refine ⟨m, by simp [regions.ceil_magnitude, run, len, oRun, mRun], cm, ?_, ?_⟩
      · rw [mValue, oValue, one_value, qValue]; simp [mod]
      · rw [oValue] at mlen; simp only [digitWidth, List.length_singleton] at mlen ⊢
        have : 1 ≤ b.val.length := by
          by_contra h
          have : b.val = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [this, Rowl.Numbers.value_nil] at positive; omega
        omega
  | Text t => exact absurd c (by simp [CanonicalNumeric])
  | Tagged t g => exact absurd c (by simp [CanonicalNumeric])
  | Truth b => exact absurd c (by simp [CanonicalNumeric])

theorem below_zero_eq (v : datatypes.DataValue) : regions.below_zero v = .ok (negativeOf v) := by
  cases v <;> rfl

theorem numValue_of_negative (v : datatypes.DataValue) (c : CanonicalNumeric v) :
    numValue v = if negativeOf v then -magnitude v else magnitude v := by
  rw [(Rowl.Datatypes.numValue_sign v c).1]
  split_ifs <;> ring

/-- The kernel's floor of a number. -/
theorem floor_of_spec (v : datatypes.DataValue) (c : CanonicalNumeric v) (small : digitWidth v + 8 < Usize.max) :
    ∃ s, regions.floor_of v = .ok s ∧ CanonicalSigned s ∧ signedValue s = ⌊numValue v⌋ ∧
      s.magnitude.val.length ≤ digitWidth v + 1 := by
  rw [regions.floor_of, below_zero_eq, numValue_of_negative v c]
  by_cases negative : negativeOf v = true
  · obtain ⟨m, run, cm, value, len⟩ := ceil_magnitude_spec v c small
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec true m cm
    refine ⟨t, by simp [negative, run, tRun], ct, ?_, by rw [same]; exact len⟩
    rw [tValue]; simp [negative, value, Int.floor_neg]
  · obtain ⟨m, run, cm, value, len⟩ := floor_magnitude_spec v c small
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec false m cm
    refine ⟨t, by simp [negative, run, tRun], ct, ?_, by rw [same]; omega⟩
    rw [tValue]; simp [negative, value]

/-- The kernel's ceiling of a number. -/
theorem ceil_of_spec (v : datatypes.DataValue) (c : CanonicalNumeric v) (small : digitWidth v + 8 < Usize.max) :
    ∃ s, regions.ceil_of v = .ok s ∧ CanonicalSigned s ∧ signedValue s = ⌈numValue v⌉ ∧
      s.magnitude.val.length ≤ digitWidth v + 1 := by
  rw [regions.ceil_of, below_zero_eq, numValue_of_negative v c]
  by_cases negative : negativeOf v = true
  · obtain ⟨m, run, cm, value, len⟩ := floor_magnitude_spec v c small
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec true m cm
    refine ⟨t, by simp [negative, run, tRun], ct, ?_, by rw [same]; omega⟩
    rw [tValue]; simp [negative, value, Int.ceil_neg]
  · obtain ⟨m, run, cm, value, len⟩ := ceil_magnitude_spec v c small
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec false m cm
    refine ⟨t, by simp [negative, run, tRun], ct, ?_, by rw [same]; exact len⟩
    rw [tValue]; simp [negative, value]

theorem negative_value {s : regions.Signed} (cs : CanonicalSigned s) (negative : s.negative = true) :
    1 ≤ digitsValue s.magnitude.val :=
  canonical_one_le cs.1 (cs.2 negative)

/-- The kernel adds one to an integer. -/
theorem plus_one_spec (s : regions.Signed) (cs : CanonicalSigned s) (small : s.magnitude.val.length + 4 < Usize.max) :
    ∃ t, regions.plus_one s = .ok t ∧ CanonicalSigned t ∧ signedValue t = signedValue s + 1 ∧
      t.magnitude.val.length ≤ s.magnitude.val.length + 2 := by
  obtain ⟨o, oRun, oValue⟩ := one_spec
  rw [regions.plus_one]
  by_cases negative : s.negative = true
  · have one := negative_value cs negative
    obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.subtract_naturals_spec s.magnitude o cs.1
      (by rw [oValue]; exact one_canonical) (by rw [oValue, one_value]; exact one) (by omega)
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec true m cm
    refine ⟨t, by simp [negative, oRun, run, tRun], ct, ?_, by rw [same]; omega⟩
    rw [tValue, value, oValue, one_value]
    simp [signedValue, negative]; omega
  · obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.add_naturals_spec s.magnitude o cs.1.1
      (by rw [oValue]; exact one_canonical.1) (by rw [oValue]; simp; omega)
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec false m cm
    refine ⟨t, by simp [negative, oRun, run, tRun], ct, ?_, ?_⟩
    · rw [tValue, value, oValue, one_value]; simp [signedValue, negative]
    · rw [same]; rw [oValue] at len; simp at len; omega

/-- The kernel subtracts one from an integer. -/
theorem minus_one_spec (s : regions.Signed) (cs : CanonicalSigned s) (small : s.magnitude.val.length + 4 < Usize.max) :
    ∃ t, regions.minus_one s = .ok t ∧ CanonicalSigned t ∧ signedValue t = signedValue s - 1 ∧
      t.magnitude.val.length ≤ s.magnitude.val.length + 2 := by
  obtain ⟨o, oRun, oValue⟩ := one_spec
  rw [regions.minus_one]
  by_cases negative : s.negative = true
  · obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.add_naturals_spec s.magnitude o cs.1.1
      (by rw [oValue]; exact one_canonical.1) (by rw [oValue]; simp; omega)
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec true m cm
    refine ⟨t, by simp [negative, oRun, run, tRun], ct, ?_, ?_⟩
    · rw [tValue, value, oValue, one_value]; simp [signedValue, negative]; ring
    · rw [same]; rw [oValue] at len; simp at len; omega
  · by_cases empty : s.magnitude.val = []
    · have len : alloc.vec.Vec.len s.magnitude = 0#usize := by
        apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val, empty]
      obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec true o (by rw [oValue]; exact one_canonical)
      refine ⟨t, by simp [negative, len, oRun, tRun], ct, ?_, by rw [same, oValue]; simp⟩
      rw [tValue, oValue, one_value]; simp [signedValue, negative, empty, Rowl.Numbers.value_nil]
    · have len : alloc.vec.Vec.len s.magnitude ≠ 0#usize := by
        intro h; apply empty; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
      have one := canonical_one_le cs.1 empty
      obtain ⟨m, run, cm, value, mlen⟩ := Rowl.Numbers.subtract_naturals_spec s.magnitude o cs.1
        (by rw [oValue]; exact one_canonical) (by rw [oValue, one_value]; exact one) (by omega)
      obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec false m cm
      refine ⟨t, by simp [negative, len, oRun, run, tRun], ct, ?_, by rw [same]; omega⟩
      rw [tValue, value, oValue, one_value]
      simp [signedValue, negative]; omega

/-- The kernel subtracts magnitudes into a signed integer. -/
theorem magnitude_difference_spec (l r : alloc.vec.Vec U8) (cl : Rowl.Numbers.Canonical l.val)
    (cr : Rowl.Numbers.Canonical r.val) (small : l.val.length + r.val.length + 4 < Usize.max) :
    ∃ t, regions.magnitude_difference l r = .ok t ∧ CanonicalSigned t ∧
      signedValue t = (digitsValue l.val : ℤ) - digitsValue r.val ∧
      t.magnitude.val.length ≤ l.val.length + r.val.length := by
  rw [regions.magnitude_difference]
  obtain ⟨o, oRun, oValue⟩ := Rowl.Numbers.compare_naturals_spec l r cl cr
  by_cases less : digitsValue l.val < digitsValue r.val
  · have : o = 0#u8 := by
      apply UScalar.eq_of_val_eq; rw [oValue, Rowl.Numbers.order_lt less]; rfl
    subst this
    obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.subtract_naturals_spec r l cr cl less.le (by omega)
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec true m cm
    refine ⟨t, by simp [oRun, run, tRun], ct, ?_, by rw [same]; omega⟩
    rw [tValue, value]; simp only [↓reduceIte]; push_cast [less.le]; ring
  · have : o ≠ 0#u8 := by
      intro h; have := congrArg UScalar.val h; rw [oValue] at this
      unfold Rowl.Numbers.order at this; split_ifs at this <;> simp_all
    obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.subtract_naturals_spec l r cl cr (by omega) (by omega)
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec false m cm
    refine ⟨t, by simp [oRun, this, run, tRun], ct, ?_, by rw [same]; omega⟩
    rw [tValue, value]; push_cast [show digitsValue r.val ≤ digitsValue l.val by omega]; simp

/-- The kernel subtracts signed integers. -/
theorem difference_spec (a b : regions.Signed) (ca : CanonicalSigned a) (cb : CanonicalSigned b)
    (small : a.magnitude.val.length + b.magnitude.val.length + 4 < Usize.max) :
    ∃ t, regions.difference a b = .ok t ∧ CanonicalSigned t ∧ signedValue t = signedValue a - signedValue b ∧
      t.magnitude.val.length ≤ a.magnitude.val.length + b.magnitude.val.length + 1 := by
  rw [regions.difference]
  by_cases na : a.negative = true <;> by_cases nb : b.negative = true
  · obtain ⟨t, run, ct, value, len⟩ := magnitude_difference_spec b.magnitude a.magnitude cb.1 ca.1 (by omega)
    refine ⟨t, by simp [na, nb, run], ct, ?_, by omega⟩
    rw [value]; simp [signedValue, na, nb]; ring
  · obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.add_naturals_spec a.magnitude b.magnitude ca.1.1 cb.1.1
      (by omega)
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec true m cm
    refine ⟨t, by simp [na, nb, run, tRun], ct, ?_, by rw [same]; omega⟩
    rw [tValue, value]; simp [signedValue, na, nb]; ring
  · obtain ⟨m, run, cm, value, len⟩ := Rowl.Numbers.add_naturals_spec a.magnitude b.magnitude ca.1.1 cb.1.1
      (by omega)
    obtain ⟨t, tRun, ct, same, tValue⟩ := signed_spec false m cm
    refine ⟨t, by simp [na, nb, run, tRun], ct, ?_, by rw [same]; omega⟩
    rw [tValue, value]; simp [signedValue, na, nb]
  · obtain ⟨t, run, ct, value, len⟩ := magnitude_difference_spec a.magnitude b.magnitude ca.1 cb.1 (by omega)
    refine ⟨t, by simp [na, nb, run], ct, ?_, by omega⟩
    rw [value]; simp [signedValue, na, nb]

/-! ### The integers between two cuts -/

/-- The least integer in a cut. -/
noncomputable def firstIn (c : regions.Cut) : ℤ :=
  if c.open then ⌊numValue c.value⌋ + 1 else ⌈numValue c.value⌉

/-- The greatest integer outside a cut. -/
noncomputable def lastOutside (c : regions.Cut) : ℤ :=
  if c.open then ⌊numValue c.value⌋ else ⌈numValue c.value⌉ - 1

theorem first_in_spec (c : regions.Cut) (cv : CanonicalNumeric c.value)
    (small : digitWidth c.value + 16 < Usize.max) :
    ∃ s, regions.first_in c = .ok s ∧ CanonicalSigned s ∧ signedValue s = firstIn c ∧
      s.magnitude.val.length ≤ digitWidth c.value + 3 := by
  rw [regions.first_in]
  by_cases o : c.open = true
  · obtain ⟨f, run, cf, value, len⟩ := floor_of_spec c.value cv (by omega)
    obtain ⟨t, tRun, ct, tValue, tLen⟩ := plus_one_spec f cf (by omega)
    exact ⟨t, by simp [o, run, tRun], ct, by rw [tValue, value]; simp [firstIn, o], by omega⟩
  · obtain ⟨f, run, cf, value, len⟩ := ceil_of_spec c.value cv (by omega)
    exact ⟨f, by simp [o, run], cf, by rw [value]; simp [firstIn, o], by omega⟩

theorem last_outside_spec (c : regions.Cut) (cv : CanonicalNumeric c.value)
    (small : digitWidth c.value + 16 < Usize.max) :
    ∃ s, regions.last_outside c = .ok s ∧ CanonicalSigned s ∧ signedValue s = lastOutside c ∧
      s.magnitude.val.length ≤ digitWidth c.value + 3 := by
  rw [regions.last_outside]
  by_cases o : c.open = true
  · obtain ⟨f, run, cf, value, len⟩ := floor_of_spec c.value cv (by omega)
    exact ⟨f, by simp [o, run], cf, by rw [value]; simp [lastOutside, o], by omega⟩
  · obtain ⟨f, run, cf, value, len⟩ := ceil_of_spec c.value cv (by omega)
    obtain ⟨t, tRun, ct, tValue, tLen⟩ := minus_one_spec f cf (by omega)
    exact ⟨t, by simp [o, run, tRun], ct, by rw [tValue, value]; simp [lastOutside, o], by omega⟩

/-- The kernel counts the integers in the cut `low` and outside the cut
    `high`, from the least integer of the one to the greatest integer
    outside the other. -/
theorem between_spec (low high : regions.Cut) (cl : CanonicalNumeric low.value) (ch : CanonicalNumeric high.value)
    (small : digitWidth low.value + digitWidth high.value + 32 < Usize.max) :
    ∃ d, regions.between low high = .ok d ∧ Digits d.val ∧
      (digitsValue d.val : ℤ) = max 0 (lastOutside high - firstIn low + 1) := by
  obtain ⟨o, oRun, oValue⟩ := one_spec
  rw [regions.between]
  obtain ⟨f, fRun, cf, fValue, fLen⟩ := first_in_spec low cl (by omega)
  obtain ⟨l, lRun, cl', lValue, lLen⟩ := last_outside_spec high ch (by omega)
  obtain ⟨g, gRun, cg, gValue, gLen⟩ := difference_spec l f cl' cf (by omega)
  by_cases negative : g.negative = true
  · refine ⟨alloc.vec.Vec.new U8, by simp [fRun, lRun, gRun, negative], by simp [new_val, Digits], ?_⟩
    have pos := negative_value cg negative
    have : signedValue g < 0 := by simp [signedValue, negative]; omega
    rw [gValue, lValue, fValue] at this
    simp [new_val, Rowl.Numbers.value_nil]; omega
  · obtain ⟨d, dRun, cd, dValue, _⟩ := Rowl.Numbers.add_naturals_spec g.magnitude o cg.1.1
      (by rw [oValue]; exact one_canonical.1) (by rw [oValue]; simp; omega)
    refine ⟨d, by simp [fRun, lRun, gRun, negative, oRun, dRun], cd.1, ?_⟩
    have : signedValue g = digitsValue g.magnitude.val := by simp [signedValue, negative]
    rw [gValue, lValue, fValue] at this
    rw [dValue, oValue, one_value]; push_cast; omega

theorem real_int_lt (q : ℚ) (z : ℤ) : (q : ℝ) < (z : ℝ) ↔ q < (z : ℚ) := by
  rw [show (z : ℝ) = ((z : ℚ) : ℝ) by push_cast; rfl]; exact Rat.cast_lt

theorem real_int_le (q : ℚ) (z : ℤ) : (q : ℝ) ≤ (z : ℝ) ↔ q ≤ (z : ℚ) := by
  rw [show (z : ℝ) = ((z : ℚ) : ℝ) by push_cast; rfl]; exact Rat.cast_le

/-- An integer is in the cut `low` and outside the cut `high` exactly when it
    lies between the least integer of the one and the greatest integer outside
    the other. -/
theorem in_cuts_iff (low high : regions.Cut) (z : ℤ) :
    (InCut low (z : ℝ) ∧ ¬ InCut high (z : ℝ)) ↔ firstIn low ≤ z ∧ z ≤ lastOutside high := by
  have l1 : ∀ q : ℚ, q < (z : ℚ) ↔ ⌊q⌋ + 1 ≤ z := fun q => by rw [← Int.floor_lt]; omega
  have l2 : ∀ q : ℚ, q ≤ (z : ℚ) ↔ ⌈q⌉ ≤ z := fun q => Int.ceil_le.symm
  have h1 : ∀ q : ℚ, (z : ℚ) ≤ q ↔ z ≤ ⌊q⌋ := fun q => Int.le_floor.symm
  have h2 : ∀ q : ℚ, (z : ℚ) < q ↔ z ≤ ⌈q⌉ - 1 := fun q => by rw [← Int.lt_ceil]; omega
  unfold InCut firstIn lastOutside
  by_cases lo : low.open = true <;> by_cases hi : high.open = true <;>
    simp only [lo, hi, ↓reduceIte, Bool.false_eq_true, real_int_lt, real_int_le, not_lt, not_le]
  · rw [l1, h1]
  · rw [l1, h2]
  · rw [l2, h1]
  · rw [l2, h2]

/-- The integers in the cut `low` and outside the cut `high` are an interval. -/
theorem in_cuts_eq (low high : regions.Cut) :
    {z : ℤ | InCut low (z : ℝ) ∧ ¬ InCut high (z : ℝ)} = Set.Icc (firstIn low) (lastOutside high) := by
  ext z; simp only [Set.mem_setOf_eq, Set.mem_Icc]; exact in_cuts_iff low high z

theorem digit_spec (byte : U8) (d : Digit byte) : ∃ r, regions.digit byte = .ok r ∧ r.val = byte.val - 48 := by
  obtain ⟨lo, hi⟩ := d
  have c1 : (48#u8 ≤ byte) = True := by simp [UScalar.le_equiv]; omega
  have c2 : (byte ≤ 57#u8) = True := by simp [UScalar.le_equiv]; omega
  obtain ⟨i, sub, iValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := byte) (y := 48#u8) (by simp; omega))
  refine ⟨UScalar.cast .Usize i, by simp [regions.digit, c1, c2, sub], ?_⟩
  simp only [UScalar.cast_val_eq, UScalarTy.numBits]
  have : i.val = byte.val - 48 := by simpa using iValue.1
  rw [this]
  apply Nat.mod_eq_of_lt
  have : byte.val - 48 < 2 ^ 8 := by omega
  calc byte.val - 48 < 2 ^ 8 := this
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by cases System.Platform.numBits_eq <;> simp_all)

theorem value_take_succ (l : List U8) (k : Nat) (h : k < l.length) :
    digitsValue (l.take (k + 1)) = 10 * digitsValue (l.take k) + (l[k].val - 48) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, Rowl.Numbers.value_snoc]

theorem value_take_le (l : List U8) (k : Nat) : digitsValue (l.take k) ≤ digitsValue l := by
  have := Rowl.Numbers.value_append (l.take k) (l.drop k)
  rw [List.take_append_drop] at this
  rw [this]
  have : 1 ≤ 10 ^ (l.drop k).length := Nat.one_le_pow _ _ (by decide)
  nlinarith

/-- The kernel caps the number written by digits, reading them one by one. -/
theorem capped_from_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (index value cap : Usize)
    (le : index.val ≤ digits.val.length) (inv : value.val = digitsValue (digits.val.take index.val))
    (below : value.val < cap.val) (capSmall : cap.val ≤ Usize.max / 16) :
    ∃ r, regions.capped_from digits index value cap = .ok r ∧ r.val = min (digitsValue digits.val) cap.val := by
  rw [regions.capped_from]
  by_cases inside : index.val < digits.val.length
  · have lookup : digits.index_usize index = .ok digits.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have dg := dd _ (List.getElem_mem inside)
    obtain ⟨d, dRun, dValue⟩ := digit_spec _ dg
    obtain ⟨m, mul, mValue⟩ := WP.spec_imp_exists (Usize.mul_spec (x := value) (y := 10#usize) (by
      have := Usize.max_def; simp; omega))
    have mIs : m.val = value.val * 10 := by simpa using mValue
    obtain ⟨n, add, nValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := m) (y := d) (by
      have := dg.2; rw [mIs, dValue]; omega))
    have nIs : n.val = value.val * 10 + (digits.val[index.val].val - 48) := by
      have h1 : n.val = m.val + d.val := by have := nValue; omega
      rw [h1, mIs, dValue]
    have step : n.val = digitsValue (digits.val.take (index.val + 1)) := by
      rw [nIs, value_take_succ _ _ inside, ← inv]; ring
    by_cases less : n.val < cap.val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, rValue⟩ := capped_from_spec digits dd next n cap (by omega) (by rw [nextIndex, ← step])
        less capSmall
      refine ⟨r, ?_, rValue⟩
      simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, alloc.vec.Vec.index_slice_index, lookup, mul, dRun, add,
        less, advance, run]
    · refine ⟨cap, ?_, ?_⟩
      · simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, alloc.vec.Vec.index_slice_index, lookup, mul, dRun, add,
          less]
      · have := value_take_le digits.val (index.val + 1)
        omega
  · have whole : index.val = digits.val.length := by omega
    refine ⟨value, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], ?_⟩
    rw [inv, whole, List.take_length]
    rw [inv, whole, List.take_length] at below
    omega
termination_by digits.val.length - index.val
decreasing_by omega

/-- The kernel caps the number written by digits. -/
theorem capped_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (cap : Usize)
    (capSmall : cap.val ≤ Usize.max / 16) :
    ∃ r, regions.capped digits cap = .ok r ∧ r.val = min (digitsValue digits.val) cap.val := by
  rw [regions.capped]
  obtain ⟨q, div, qValue⟩ := WP.spec_imp_exists (Usize.div_spec core.num.Usize.MAX (y := 16#usize) (by simp))
  by_cases pos : 0 < cap.val
  · obtain ⟨r, run, rValue⟩ := capped_from_spec digits dd 0#usize 0#usize cap (by simp) (by simp; rfl) pos capSmall
    refine ⟨r, ?_, rValue⟩
    have c1 : (0#usize < cap) = True := by simp [UScalar.lt_equiv]; exact pos
    have c2 : (cap ≤ q) = True := by
      simp [UScalar.le_equiv]; rw [qValue]; simpa using capSmall
    simp [div, c1, c2, run]
    intro h
    exfalso
    have : q.val = Usize.max / 16 := by rw [qValue]; simp
    omega
  · have zero : cap.val = 0 := by omega
    have c1 : (0#usize < cap) = False := by simp [UScalar.lt_equiv]; omega
    refine ⟨0#usize, by simp [div, c1], by simp [zero]⟩

/-- The kernel's count of the integers in the cut `low` and outside the cut
    `high`, capped. -/
theorem run_size_spec (low high : regions.Cut) (cl : CanonicalNumeric low.value) (ch : CanonicalNumeric high.value)
    (small : digitWidth low.value + digitWidth high.value + 32 < Usize.max) (cap : Usize)
    (capSmall : cap.val ≤ Usize.max / 16) :
    ∃ r, regions.run_size low high cap = .ok r ∧
      r.val = min (lastOutside high - firstIn low + 1).toNat cap.val := by
  rw [regions.run_size]
  obtain ⟨d, dRun, dd, dValue⟩ := between_spec low high cl ch small
  obtain ⟨r, run, rValue⟩ := capped_spec d dd cap capSmall
  refine ⟨r, by simp [dRun, run], ?_⟩
  rw [rValue]
  congr 1
  omega

/-! ### The order of the cuts -/

/-- The order of cuts: by their numbers, and the closed cut of a number before
    its open cut. -/
def CutBefore (a b : regions.Cut) : Prop :=
  numValue a.value < numValue b.value ∨ (a.value = b.value ∧ a.open = false ∧ b.open = true)

/-- A cut of a canonical number written short enough to compare. -/
def Fit (c : regions.Cut) : Prop := CanonicalNumeric c.value ∧ digitWidth c.value < Usize.max / 8

theorem vec_ext {α : Type} {a b : alloc.vec.Vec α} (h : a.val = b.val) : a = b :=
  (alloc.vec.Vec.eq_iff a b).mpr h

/-- Canonical numbers with the same value are the same. -/
theorem numValue_injective {a b : datatypes.DataValue} (ca : CanonicalNumeric a) (cb : CanonicalNumeric b)
    (same : numValue a = numValue b) : a = b := by
  cases a <;> cases b <;> simp only [CanonicalNumeric] at ca cb <;> simp only [numValue] at same
  · obtain ⟨n, w, f⟩ := Rowl.Datatypes.numberOf_injective ca cb same
    subst n; rw [vec_ext w, vec_ext f]
  · exact absurd same.symm (Rowl.Datatypes.fraction_ne_number cb)
  · exact absurd same (Rowl.Datatypes.fraction_ne_number ca)
  · obtain ⟨n, x, y⟩ := Rowl.Datatypes.fractionOf_injective ca cb same
    subst n; rw [vec_ext x, vec_ext y]

theorem number_of_canonical {v : datatypes.DataValue} (c : CanonicalNumeric v) : IsNumber v := by
  cases v <;> simp_all [CanonicalNumeric, IsNumber]

theorem cutBefore_irrefl (a : regions.Cut) : ¬ CutBefore a a := by
  rintro (h | ⟨_, h1, h2⟩)
  · exact lt_irrefl _ h
  · rw [h1] at h2; exact absurd h2 (by simp)

theorem cutBefore_trans {a b c : regions.Cut} (ab : CutBefore a b) (bc : CutBefore b c) : CutBefore a c := by
  rcases ab with ab | ⟨ab, a1, b1⟩ <;> rcases bc with bc | ⟨bc, b2, c2⟩
  · exact .inl (lt_trans ab bc)
  · exact .inl (by rw [← bc]; exact ab)
  · exact .inl (by rw [ab]; exact bc)
  · rw [b1] at b2; exact absurd b2 (by simp)

theorem cutBefore_total {a b : regions.Cut} (fa : Fit a) (fb : Fit b) (differ : a ≠ b) :
    CutBefore a b ∨ CutBefore b a := by
  rcases lt_trichotomy (numValue a.value) (numValue b.value) with lt | eq | gt
  · exact .inl (.inl lt)
  · have same := numValue_injective fa.1 fb.1 eq
    have sides : a.open ≠ b.open := fun h => differ ((cut_eq_iff a b).mpr ⟨same, h⟩)
    cases ha : a.open <;> cases hb : b.open <;> simp_all [CutBefore]
  · exact .inr (.inl gt)

theorem cutBefore_asymm {a b : regions.Cut} (ab : CutBefore a b) : ¬ CutBefore b a :=
  fun ba => cutBefore_irrefl a (cutBefore_trans ab ba)

/-- The kernel compares two numbers. -/
theorem is_greater_correct (l r : datatypes.DataValue) (cl : CanonicalNumeric l) (wl : digitWidth l < Usize.max / 8)
    (cr : CanonicalNumeric r) (wr : digitWidth r < Usize.max / 8) :
    regions.is_greater l r = .ok (decide (numValue r < numValue l)) := by
  rw [regions.is_greater]
  obtain ⟨res, run, noneCase, someCase⟩ := Rowl.Datatypes.compare_values_correct l r (fun _ => cl) (fun _ => cr)
  cases res with
  | none =>
    exfalso
    rcases noneCase rfl with h | h | h | h
    · exact h (number_of_canonical cl)
    · exact h (number_of_canonical cr)
    · omega
    · omega
  | some o =>
    obtain ⟨_, _, oValue⟩ := someCase o rfl
    simp only [run, bind_ok]
    congr 1
    by_cases gt : numValue r < numValue l
    · have : o = 2#u8 := by apply UScalar.eq_of_val_eq; rw [oValue, Rowl.Datatypes.orderOf_gt gt]; rfl
      subst this
      simp [gt]
    · have ne : Rowl.Datatypes.orderOf (numValue l) (numValue r) ≠ 2 := by
        unfold Rowl.Datatypes.orderOf
        split_ifs with h1 h2
        · decide
        · decide
        · exact absurd (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)) gt
      have : o ≠ 2#u8 := fun h => ne (by rw [← oValue, h]; rfl)
      rw [decide_eq_false this, decide_eq_false gt]

/-- The kernel compares any two values whose numbers are canonical. -/
theorem is_greater_ok (l r : datatypes.DataValue) (cl : IsNumber l → CanonicalNumeric l)
    (cr : IsNumber r → CanonicalNumeric r) : ∃ b, regions.is_greater l r = .ok b := by
  rw [regions.is_greater]
  obtain ⟨res, run, _, _⟩ := Rowl.Datatypes.compare_values_correct l r cl cr
  cases res with
  | none => exact ⟨false, by simp [run]⟩
  | some o => exact ⟨decide (o = 2#u8), by simp [run]⟩

/-- The kernel's membership of a number in a cut. -/
theorem in_cut_correct (c : regions.Cut) (fc : Fit c) (v : datatypes.DataValue) (cv : CanonicalNumeric v)
    (wv : digitWidth v < Usize.max / 8) : regions.in_cut c v = .ok (decide (InCut c (numValue v))) := by
  rw [regions.in_cut]
  cases ho : c.open
  · rw [is_greater_correct c.value v fc.1 fc.2 cv wv]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, InCut, ho]
    by_cases h : numValue v < numValue c.value
    · have : ¬ ((numValue c.value : ℚ) : ℝ) ≤ ((numValue v : ℚ) : ℝ) := by exact_mod_cast not_le.mpr h
      simp [h, this]
    · have : ((numValue c.value : ℚ) : ℝ) ≤ ((numValue v : ℚ) : ℝ) := by exact_mod_cast not_lt.mp h
      simp [h, this]
  · rw [is_greater_correct v c.value cv wv fc.1 fc.2]
    simp only [↓reduceIte, InCut, ho]
    by_cases h : numValue c.value < numValue v
    · have : ((numValue c.value : ℚ) : ℝ) < ((numValue v : ℚ) : ℝ) := by exact_mod_cast h
      simp [h, this]
    · have : ¬ ((numValue c.value : ℚ) : ℝ) < ((numValue v : ℚ) : ℝ) := by exact_mod_cast h
      simp [h, this]

/-- The kernel's membership in a cut runs on every value. -/
theorem in_cut_ok (c : regions.Cut) (fc : Fit c) (v : datatypes.DataValue) (cv : IsNumber v → CanonicalNumeric v) :
    ∃ b, regions.in_cut c v = .ok b := by
  rw [regions.in_cut]
  obtain ⟨b1, run1⟩ := is_greater_ok v c.value cv (fun _ => fc.1)
  obtain ⟨b2, run2⟩ := is_greater_ok c.value v (fun _ => fc.1) cv
  cases ho : c.open
  · exact ⟨!b2, by simp [ho, run2]⟩
  · exact ⟨b1, by simp [ho, run1]⟩

/-- The kernel's order of cuts. -/
theorem after_correct (left right : regions.Cut) (fl : Fit left) (fr : Fit right) :
    regions.after left right = .ok (decide (CutBefore right left)) := by
  rw [regions.after, is_greater_correct _ _ fl.1 fl.2 fr.1 fr.2, Rowl.Datatypes.same_value_correct]
  simp only [bind_ok]
  congr 1
  unfold CutBefore
  by_cases e : right.value = left.value
  · cases hl : left.open <;> cases hr : right.open <;> simp [e]
  · have e' : ¬ left.value = right.value := fun h => e h.symm
    cases hl : left.open <;> cases hr : right.open <;> simp [e, e']

/-- The cut at an index of a list, and a cut of no number beyond the list. -/
def cutAt (cs : List regions.Cut) (j : Nat) : regions.Cut := cs.getD j ⟨.Truth false, false⟩

theorem cutAt_eq (cs : List regions.Cut) (j : Nat) (h : j < cs.length) : cutAt cs j = cs[j] := by
  simp [cutAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Whether the cut at `j` comes after the cut at the bound, or there is no
    bound. -/
def AfterBound (cs : List regions.Cut) (bound : Option Nat) (j : Nat) : Prop :=
  ∀ b, bound = some b → b < cs.length ∧ CutBefore (cutAt cs b) (cutAt cs j)

/-- Whether the cut at `j` comes before the cut at the best index, or there is
    no best one. -/
def BeforeBest (cs : List regions.Cut) (best : Option Nat) (j : Nat) : Prop :=
  ∀ b, best = some b → b < cs.length ∧ CutBefore (cutAt cs j) (cutAt cs b)

/-- Cuts of canonical numbers short enough to compare, each once. -/
def FineCuts (cs : List regions.Cut) : Prop := (∀ c ∈ cs, Fit c) ∧ cs.Nodup

theorem fine_at {cs : List regions.Cut} (fine : FineCuts cs) {j : Nat} (h : j < cs.length) : Fit (cutAt cs j) := by
  rw [cutAt_eq cs j h]; exact fine.1 _ (List.getElem_mem h)

theorem fine_apart {cs : List regions.Cut} (fine : FineCuts cs) {i j : Nat} (hi : i < cs.length)
    (hj : j < cs.length) (differ : i ≠ j) : cutAt cs i ≠ cutAt cs j := by
  rw [cutAt_eq cs i hi, cutAt_eq cs j hj]
  intro same
  exact differ ((List.Nodup.getElem_inj_iff fine.2).mp same)

theorem after_bound_correct (cuts : alloc.vec.Vec regions.Cut) (fine : FineCuts cuts.val) (bound : Option Usize)
    (j : Nat) (hj : j < cuts.val.length) :
    regions.after_bound cuts bound cuts.val[j] = .ok (decide (AfterBound cuts.val (bound.map (·.val)) j)) := by
  rw [regions.after_bound.eq_def]
  cases bound with
  | none => simp [AfterBound]
  | some b =>
    by_cases inside : b.val < cuts.val.length
    · have lookup : cuts.index_usize b = .ok cuts.val[b.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      have fb := fine_at fine inside
      have fj := fine_at fine hj
      rw [cutAt_eq _ _ inside] at fb
      rw [cutAt_eq _ _ hj] at fj
      simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, alloc.vec.Vec.index_slice_index, lookup,
        after_correct _ _ fj fb, AfterBound, cutAt_eq _ _ inside, cutAt_eq _ _ hj]
    · simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, AfterBound]

theorem before_best_correct (cuts : alloc.vec.Vec regions.Cut) (fine : FineCuts cuts.val) (best : Option Usize)
    (j : Nat) (hj : j < cuts.val.length) :
    regions.before_best cuts best cuts.val[j] = .ok (decide (BeforeBest cuts.val (best.map (·.val)) j)) := by
  rw [regions.before_best.eq_def]
  cases best with
  | none => simp [BeforeBest]
  | some b =>
    by_cases inside : b.val < cuts.val.length
    · have lookup : cuts.index_usize b = .ok cuts.val[b.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      have fb := fine_at fine inside
      have fj := fine_at fine hj
      rw [cutAt_eq _ _ inside] at fb
      rw [cutAt_eq _ _ hj] at fj
      simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, alloc.vec.Vec.index_slice_index, lookup,
        after_correct _ _ fb fj, BeforeBest, cutAt_eq _ _ inside, cutAt_eq _ _ hj]
    · simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, BeforeBest]

/-- The kernel finds the first cut after a bound. -/
theorem least_after_spec (cuts : alloc.vec.Vec regions.Cut) (fine : FineCuts cuts.val) (bound : Option Usize)
    (index : Usize) (best : Option Usize) (le : index.val ≤ cuts.val.length)
    (noBest : best = none → ∀ j < index.val, ¬ AfterBound cuts.val (bound.map (·.val)) j)
    (someBest : ∀ b, best = some b → b.val < index.val ∧ AfterBound cuts.val (bound.map (·.val)) b.val ∧
      ∀ j < index.val, AfterBound cuts.val (bound.map (·.val)) j → j = b.val ∨
        CutBefore (cutAt cuts.val b.val) (cutAt cuts.val j)) :
    ∃ r, regions.least_after cuts bound index best = .ok r ∧
      (r = none → ∀ j < cuts.val.length, ¬ AfterBound cuts.val (bound.map (·.val)) j) ∧
      ∀ b, r = some b → b.val < cuts.val.length ∧ AfterBound cuts.val (bound.map (·.val)) b.val ∧
        ∀ j < cuts.val.length, AfterBound cuts.val (bound.map (·.val)) j → j = b.val ∨
          CutBefore (cutAt cuts.val b.val) (cutAt cuts.val j) := by
  rw [regions.least_after]
  by_cases inside : index.val < cuts.val.length
  · have lookup : cuts.index_usize index = .ok cuts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have better : regions.better cuts bound best cuts.val[index.val] =
        .ok (decide (AfterBound cuts.val (bound.map (·.val)) index.val ∧
          BeforeBest cuts.val (best.map (·.val)) index.val)) := by
      rw [regions.better, after_bound_correct cuts fine bound _ inside, before_best_correct cuts fine best _ inside]
      simp
    by_cases chosen : AfterBound cuts.val (bound.map (·.val)) index.val ∧
        BeforeBest cuts.val (best.map (·.val)) index.val
    · obtain ⟨r, run, rNone, rSome⟩ := least_after_spec cuts fine bound next (some index) (by omega)
        (by simp) (fun b hb => by
          cases hb
          refine ⟨by omega, chosen.1, fun j hj after => ?_⟩
          by_cases same : j = index.val
          · exact .inl same
          · right
            have jlt : j < index.val := by omega
            cases hbest : best with
            | none => exact absurd after (noBest hbest j jlt)
            | some b =>
              obtain ⟨blt, bAfter, bLeast⟩ := someBest b hbest
              have before := (chosen.2 b.val (by simp [hbest])).2
              rcases bLeast j jlt after with eq | lt
              · rw [eq]; exact before
              · exact cutBefore_trans before lt)
      refine ⟨r, ?_, rNone, rSome⟩
      simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, alloc.vec.Vec.index_slice_index, lookup, better,
        chosen, advance, run]
    · obtain ⟨r, run, rNone, rSome⟩ := least_after_spec cuts fine bound next best (by omega)
        (fun hbest j hj after => by
          by_cases same : j = index.val
          · subst same
            exact chosen ⟨after, fun b hb => by simp [hbest] at hb⟩
          · exact noBest hbest j (by omega) after)
        (fun b hbest => by
          obtain ⟨blt, bAfter, bLeast⟩ := someBest b hbest
          refine ⟨by omega, bAfter, fun j hj after => ?_⟩
          by_cases same : j = index.val
          · subst same
            right
            have notBefore : ¬ CutBefore (cutAt cuts.val index.val) (cutAt cuts.val b.val) := fun h =>
              chosen ⟨after, fun b' hb' => by
                simp [hbest] at hb'; subst hb'; exact ⟨by omega, h⟩⟩
            have blt' : b.val < cuts.val.length := by omega
            rcases cutBefore_total (fine_at fine blt') (fine_at fine inside)
              (fine_apart fine blt' inside (by omega)) with lt | gt
            · exact lt
            · exact absurd gt notBefore
          · exact bLeast j (by omega) after)
      refine ⟨r, ?_, rNone, rSome⟩
      simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside, alloc.vec.Vec.index_slice_index, lookup, better,
        chosen, advance, run]
  · have whole : index.val = cuts.val.length := by omega
    refine ⟨best, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, inside], fun h j hj => ?_, fun b h => ?_⟩
    · exact noBest h j (by omega)
    · obtain ⟨blt, bAfter, bLeast⟩ := someBest b h
      exact ⟨by omega, bAfter, fun j hj after => bLeast j (by omega) after⟩
termination_by cuts.val.length - index.val
decreasing_by all_goals omega

/-- The cuts in their order: each once, all of them, each before the next. -/
def Ordered (cs : List regions.Cut) (order : List Nat) : Prop :=
  order.Nodup ∧ (∀ k ∈ order, k < cs.length) ∧ (∀ j < cs.length, j ∈ order) ∧
    order.IsChain (fun a b => CutBefore (cutAt cs a) (cutAt cs b))

theorem all_of_nodup {l : List Nat} {n : Nat} (nodup : l.Nodup) (bound : ∀ x ∈ l, x < n) (long : n ≤ l.length) :
    ∀ j < n, j ∈ l := by
  intro j hj
  have sub : l.toFinset ⊆ Finset.range n := fun x m => by
    simp only [List.mem_toFinset] at m; simpa using bound x m
  have card : (Finset.range n).card ≤ l.toFinset.card := by
    rw [Finset.card_range, List.toFinset_card_of_nodup nodup]; exact long
  have eq := Finset.eq_of_subset_of_card_le sub card
  have : j ∈ Finset.range n := Finset.mem_range.mpr hj
  rw [← eq] at this
  simpa using this

/-- The kernel lists the cuts after the last one listed, in order. -/
theorem order_from_spec (cuts : alloc.vec.Vec regions.Cut) (fine : FineCuts cuts.val) (last : Option Usize)
    (out : alloc.vec.Vec Usize) (nodup : (out.val.map (·.val)).Nodup)
    (inside : ∀ k ∈ out.val, k.val < cuts.val.length)
    (members : ∀ j < cuts.val.length, j ∈ out.val.map (·.val) ↔ ¬ AfterBound cuts.val (last.map (·.val)) j)
    (chain : (out.val.map (·.val)).IsChain (fun a b => CutBefore (cutAt cuts.val a) (cutAt cuts.val b)))
    (lastIs : (out.val.map (·.val)).getLast? = last.map (·.val)) :
    ∃ r, regions.order_from cuts last out = .ok r ∧ Ordered cuts.val (r.val.map (·.val)) := by
  rw [regions.order_from]
  have insideNat : ∀ k ∈ out.val.map (·.val), k < cuts.val.length := by
    intro k m; simp only [List.mem_map] at m; obtain ⟨x, mx, rfl⟩ := m; exact inside x mx
  by_cases short : out.val.length < cuts.val.length
  · obtain ⟨r, run, rNone, rSome⟩ := least_after_spec cuts fine last 0#usize none (by simp) (fun _ j hj => by simp at hj)
      (fun b h => by simp at h)
    cases r with
    | none =>
      refine ⟨out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, short, run], nodup, insideNat,
        fun j hj => (members j hj).mpr (rNone rfl j hj), chain⟩
    | some next =>
      obtain ⟨nlt, nAfter, nLeast⟩ := rSome next rfl
      obtain ⟨out1, push, contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out next (by have := cuts.property; scalar_tac))
      have notIn : next.val ∉ out.val.map (·.val) := fun m => (members _ nlt).mp m nAfter
      have map1 : out1.val.map (·.val) = out.val.map (·.val) ++ [next.val] := by rw [contents]; simp
      obtain ⟨r, rRun, ordered⟩ := order_from_spec cuts fine (some next) out1
        (by rw [map1]; exact List.nodup_append.mpr ⟨nodup, by simp, by
          intro a ma b mb same; simp at mb; subst mb; subst same; exact notIn ma⟩)
        (by intro k mk; rw [contents] at mk; simp at mk; rcases mk with mk | rfl; exact inside k mk; exact nlt)
        (fun j hj => by
          rw [map1]
          simp only [List.mem_append, List.mem_singleton, AfterBound, Option.map_some, Option.some.injEq,
            forall_eq', not_and]
          constructor
          · rintro (m | rfl)
            · intro _ before
              have notAfter := (members j hj).mp m
              apply notAfter
              intro l hl
              obtain ⟨llt, lb⟩ := nAfter l hl
              exact ⟨llt, cutBefore_trans lb before⟩
            · intro _ before; exact cutBefore_irrefl _ before
          · intro notBefore
            by_cases after : AfterBound cuts.val (last.map (·.val)) j
            · rcases nLeast j hj after with same | before
              · exact .inr same
              · exact absurd before (notBefore nlt)
            · exact .inl ((members j hj).mpr after))
        (by
          rw [map1]
          refine List.isChain_append.mpr ⟨chain, List.isChain_singleton _, fun x mx y my => ?_⟩
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at my
          subst my
          rw [lastIs] at mx
          cases hl : last with
          | none => simp [hl] at mx
          | some l =>
            simp [hl] at mx
            subst mx
            exact (nAfter l.val (by simp [hl])).2)
        (by rw [map1]; simp)
      refine ⟨r, ?_, ordered⟩
      simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, short, run, push, rRun]
  · refine ⟨out, by simp [UScalar.lt_equiv, alloc.vec.Vec.len_val, short], nodup, insideNat, ?_, chain⟩
    exact all_of_nodup nodup insideNat (by simp; omega)
termination_by cuts.val.length - out.val.length
decreasing_by
  have := congrArg List.length contents
  simp at this
  omega

/-- The kernel lists the cuts in order. -/
theorem cut_order_spec (cuts : alloc.vec.Vec regions.Cut) (fine : FineCuts cuts.val) :
    ∃ r, regions.cut_order cuts = .ok r ∧ Ordered cuts.val (r.val.map (·.val)) := by
  rw [regions.cut_order]
  exact order_from_spec cuts fine none (alloc.vec.Vec.new Usize) (by simp [new_val]) (by simp [new_val])
    (fun j hj => by simp [new_val, AfterBound]) (by simp [new_val]) (by simp [new_val])

/-! ### Which cuts the kernel can order -/

/-- A canonical number written short enough has its comparison. -/
theorem fits_spec (v : datatypes.DataValue) (cv : IsNumber v → CanonicalNumeric v) :
    ∃ b, regions.fits v = .ok b ∧ (b = true → CanonicalNumeric v ∧ digitWidth v < Usize.max / 8) := by
  rw [regions.fits]
  obtain ⟨res, run, _, someCase⟩ := Rowl.Datatypes.compare_values_correct v v cv cv
  cases res with
  | none => exact ⟨false, by simp [run], by simp⟩
  | some o =>
    obtain ⟨nv, _, _⟩ := someCase o rfl
    refine ⟨true, by simp [run], fun _ => ⟨cv nv, ?_⟩⟩
    by_contra wide
    rw [datatypes.compare_values, Rowl.Datatypes.numeric_correct] at run
    obtain ⟨x, xRun, xIff⟩ := Rowl.Datatypes.width_spec v
    obtain ⟨q, qRun, qValue⟩ := UScalar.div_spec core.num.Usize.MAX (y := 8#usize) (by simp)
    have qIs : q.val = Usize.max / 8 := by rw [qValue]; simp [core.num.Usize.MAX]
    have notLt : ¬ x.val < q.val := by rw [qIs]; exact fun h => wide (xIff.mp h)
    simp [nv, xRun, qRun, notLt, UScalar.lt_equiv] at run

/-- When the kernel finds every cut fit to compare, they are. -/
theorem cuts_fit_spec (cuts : alloc.vec.Vec regions.Cut) (index : Usize)
    (canonical : ∀ c ∈ cuts.val, IsNumber c.value → CanonicalNumeric c.value) :
    ∃ b, regions.cuts_fit cuts index = .ok b ∧
      (b = true → ∀ j, index.val ≤ j → ∀ h : j < cuts.val.length, Fit cuts.val[j]) := by
  rw [regions.cuts_fit]
  by_cases inside : index.val < cuts.val.length
  · have lookup : cuts.index_usize index = .ok cuts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨f, fRun, fFacts⟩ := fits_spec cuts.val[index.val].value (canonical _ (List.getElem_mem inside))
    cases f with
    | false => exact ⟨false, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, fRun], by simp⟩
    | true =>
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨b, run, facts⟩ := cuts_fit_spec cuts next canonical
      refine ⟨b, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, fRun, advance, run],
        fun hb j low h => ?_⟩
      by_cases same : j = index.val
      · subst same; exact fFacts rfl
      · exact facts hb j (by omega) h
  · exact ⟨true, by simp [UScalar.lt_equiv, inside], fun _ j low h => by omega⟩
termination_by cuts.val.length - index.val
decreasing_by omega

/-! ### What the order of the cuts means -/

theorem in_cut_mono {a b : regions.Cut} (before : CutBefore a b) (r : ℝ) (inB : InCut b r) : InCut a r := by
  unfold InCut at *
  rcases before with lt | ⟨same, ao, bo⟩
  · have lt' : (numValue a.value : ℝ) < numValue b.value := by exact_mod_cast lt
    split_ifs at inB ⊢ <;> linarith
  · rw [same] at *; simp [ao, bo] at inB ⊢; exact inB.le

theorem ordered_pairwise {cs : List regions.Cut} {order : List Nat} (ordered : Ordered cs order) :
    order.Pairwise (fun a b => CutBefore (cutAt cs a) (cutAt cs b)) := by
  haveI : IsTrans Nat (fun a b => CutBefore (cutAt cs a) (cutAt cs b)) := ⟨fun _ _ _ ab bc => cutBefore_trans ab bc⟩
  exact ordered.2.2.2.pairwise

end Rowl.Regions
