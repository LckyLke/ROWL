import Rowl.Floats
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorization.Basic

/-!
The order of the values of `xsd:double` and `xsd:float` as places on a line,
which the data encoding uses for their range facets. Every positive value of a
format is `M × 2^E` in exactly one normal form (`Normal`): `M` below `2^p`, the
exponent within the format, and `M` at least `2^(p−1)` unless `E` is the least
exponent. Its place among the positive values, from 1, is
`(E − least) × 2^(p−1) + M`, its IEEE 754 encoding (`placeOf`); the places
grow with the values (`placeOf_lt`) and fill `[1, T)` for
`T = (most − least + 2) × 2^(p−1)` (`placeValue`). The place of a value of the
format (`position`) puts NaN first, then negative infinity, the negative
numbers, negative zero, positive zero, the positive numbers and positive
infinity, one place for each value (`position_injective`, `valueAt`), so that
a run of places from `lo` to `hi` holds exactly `hi − lo` values (`slot_card`).
The range facets of XML Schema are runs of places (`le_iff_position` and its
siblings): a value is at or above a bound when its place is at or above the
first place of the values equal to the bound (`lowPosition`), negative zero's
for a zero, and above it when its place is beyond the last one
(`highPosition`). The kernel's `floats::position` computes these places
(`position_correct`).
-/
namespace Rowl.FloatOrder
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.DatatypeMap (Binary FloatFormat doubleFormat floatFormat)
open Rowl.Floats (fmt prec lo hi binaryOf CanonicalBinary scale)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ### Normal forms of positive values -/

/-- `q` is `M × 2^E` with `M` below `2^p`, `E` within the format, and `M` at
    least `2^(p−1)` unless `E` is the least exponent. -/
def Normal (f : FloatFormat) (q : ℚ) (E M : ℤ) : Prop :=
  q = M * (2 : ℚ) ^ E ∧ 1 ≤ M ∧ M < 2 ^ f.precision ∧ f.least ≤ E ∧ E ≤ f.most ∧
    (E = f.least ∨ 2 ^ (f.precision - 1) ≤ M)

theorem two_pow_pred {p : ℕ} (hp : 1 ≤ p) : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem normal_exists (f : FloatFormat) (hp : 1 ≤ f.precision) :
    ∀ (n : ℕ) (m e : ℤ), (e - f.least).toNat = n → 0 < m → m < 2 ^ f.precision → f.least ≤ e → e ≤ f.most →
      ∃ E M, Normal f (m * (2 : ℚ) ^ e) E M := by
  intro n
  induction n with
  | zero =>
    intro m e hn mpos mlt le ge
    exact ⟨e, m, rfl, mpos, mlt, le, ge, .inl (by omega)⟩
  | succ n ih =>
    intro m e hn mpos mlt le ge
    by_cases big : 2 ^ (f.precision - 1) ≤ m
    · exact ⟨e, m, rfl, mpos, mlt, le, ge, .inr big⟩
    · have room : 2 * m < 2 ^ f.precision := by rw [two_pow_pred hp]; omega
      obtain ⟨E, M, normal⟩ := ih (2 * m) (e - 1) (by omega) (by omega) room (by omega) (by omega)
      refine ⟨E, M, ?_⟩
      have same : ((2 * m : ℤ) : ℚ) * (2 : ℚ) ^ (e - 1) = (m : ℚ) * (2 : ℚ) ^ e := by
        rw [zpow_sub_one₀ (by norm_num)]; push_cast; field_simp
      rw [← same]
      exact normal

theorem normal_of_valid (f : FloatFormat) (hp : 1 ≤ f.precision) {q : ℚ} (valid : (Binary.finite q).Valid f)
    (pos : 0 < q) : ∃ E M, Normal f q E M := by
  obtain ⟨m, e, rfl, mpos, mlt, le, ge⟩ := valid
  have mPos : 0 < m := by
    by_contra neg
    have : (m : ℚ) ≤ 0 := by exact_mod_cast not_lt.mp neg
    have : (m : ℚ) * (2 : ℚ) ^ e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this (zpow_nonneg (by norm_num) _)
    linarith
  rw [abs_of_pos mPos] at mlt
  exact normal_exists f hp _ m e rfl mPos mlt le ge

theorem normal_pos {f : FloatFormat} {q : ℚ} {E M : ℤ} (n : Normal f q E M) : 0 < q := by
  obtain ⟨rfl, mpos, _⟩ := n
  have : (0 : ℚ) < M := by exact_mod_cast (show (0 : ℤ) < M by omega)
  exact mul_pos this (zpow_pos (by norm_num) _)

/-- A smaller exponent with a significand below `2^p` gives a smaller number
    than a larger exponent with a significand of at least `2^(p−1)`. -/
theorem lower_binade {p : ℕ} (hp : 1 ≤ p) {E E' M M' : ℤ} (lt : E < E') (small : M < 2 ^ p)
    (big : 2 ^ (p - 1) ≤ M') : (M : ℚ) * (2 : ℚ) ^ E < (M' : ℚ) * (2 : ℚ) ^ E' := by
  have e1 : (2 : ℚ) ^ E' = (2 : ℚ) ^ (E' - E - 1) * 2 * (2 : ℚ) ^ E := by
    rw [mul_assoc, ← zpow_one_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]; congr 1; ring
  have k : (1 : ℚ) ≤ (2 : ℚ) ^ (E' - E - 1) := one_le_zpow₀ (by norm_num) (by omega)
  have bigQ : ((2 : ℚ) ^ (p - 1)) ≤ (M' : ℚ) := by exact_mod_cast big
  have smallQ : (M : ℚ) < 2 * (2 : ℚ) ^ (p - 1) := by
    have := two_pow_pred (p := p) hp
    have : (M : ℚ) < ((2 ^ p : ℤ) : ℚ) := by exact_mod_cast small
    rw [two_pow_pred hp] at this; push_cast at this; exact this
  have pos : (0 : ℚ) < (2 : ℚ) ^ E := zpow_pos (by norm_num) _
  rw [e1]
  have : (M : ℚ) * (2 : ℚ) ^ E < (2 * (2 : ℚ) ^ (p - 1)) * (2 : ℚ) ^ E := by
    exact mul_lt_mul_of_pos_right smallQ pos
  calc (M : ℚ) * (2 : ℚ) ^ E < (2 * (2 : ℚ) ^ (p - 1)) * (2 : ℚ) ^ E := this
    _ ≤ (M' : ℚ) * 2 * (2 : ℚ) ^ E := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt pos)
        linarith
    _ ≤ (M' : ℚ) * ((2 : ℚ) ^ (E' - E - 1) * 2 * (2 : ℚ) ^ E) := by
        have m0 : (0 : ℚ) ≤ M' := le_trans (by positivity) bigQ
        nlinarith [mul_nonneg m0 (le_of_lt pos)]

theorem normal_unique {f : FloatFormat} (hp : 1 ≤ f.precision) {q : ℚ} {E M E' M' : ℤ} (n : Normal f q E M)
    (n' : Normal f q E' M') : E = E' ∧ M = M' := by
  obtain ⟨h, mpos, mlt, le, ge, side⟩ := n
  obtain ⟨h', mpos', mlt', le', ge', side'⟩ := n'
  have sameE : E = E' := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have big : 2 ^ (f.precision - 1) ≤ M' := side'.resolve_left (by omega)
      have := lower_binade hp lt mlt big
      rw [← h, ← h'] at this
      exact lt_irrefl _ this
    · have big : 2 ^ (f.precision - 1) ≤ M := side.resolve_left (by omega)
      have := lower_binade hp gt mlt' big
      rw [← h, ← h'] at this
      exact lt_irrefl _ this
  subst sameE
  refine ⟨rfl, ?_⟩
  have pos : (2 : ℚ) ^ E ≠ 0 := zpow_ne_zero _ (by norm_num)
  have : (M : ℚ) = M' := by
    have := h.symm.trans h'
    exact mul_right_cancel₀ pos this
  exact_mod_cast this

/-! ### Places of positive values -/

/-- The place of positive infinity among the positive values. -/
def topPlace (f : FloatFormat) : ℕ := (f.most - f.least + 2).toNat * 2 ^ (f.precision - 1)

/-- The place of a positive value in normal form `M × 2^E`. -/
def placeOfNormal (f : FloatFormat) (E M : ℤ) : ℕ := (E - f.least).toNat * 2 ^ (f.precision - 1) + M.toNat

open Classical in
/-- The place of a positive value of the format among the positive values,
    from 1: its IEEE 754 encoding. -/
noncomputable def placeOf (f : FloatFormat) (q : ℚ) : ℕ :=
  if h : ∃ E M, Normal f q E M then placeOfNormal f (Classical.choose h) (Classical.choose (Classical.choose_spec h))
  else 0

theorem placeOf_eq {f : FloatFormat} (hp : 1 ≤ f.precision) {q : ℚ} {E M : ℤ} (n : Normal f q E M) :
    placeOf f q = placeOfNormal f E M := by
  have h : ∃ E M, Normal f q E M := ⟨E, M, n⟩
  unfold placeOf
  rw [dif_pos h]
  obtain ⟨e1, e2⟩ := normal_unique hp (Classical.choose_spec (Classical.choose_spec h)) n
  exact congrArg₂ (placeOfNormal f) e1 e2

theorem placeOfNormal_bounds {f : FloatFormat} (hp : 1 ≤ f.precision) {q : ℚ} {E M : ℤ} (n : Normal f q E M) :
    1 ≤ placeOfNormal f E M ∧ placeOfNormal f E M + 1 ≤ topPlace f := by
  obtain ⟨_, mpos, mlt, le, ge, _⟩ := n
  unfold placeOfNormal topPlace
  have p2 := two_pow_pred (p := f.precision) hp
  have hM : M.toNat < 2 * 2 ^ (f.precision - 1) := by
    have : M < 2 * 2 ^ (f.precision - 1) := by rw [← p2]; exact mlt
    have c : ((2 * 2 ^ (f.precision - 1) : ℕ) : ℤ) = 2 * 2 ^ (f.precision - 1) := by push_cast; ring
    omega
  have hE : (E - f.least).toNat + 2 ≤ (f.most - f.least + 2).toNat := by omega
  constructor
  · omega
  · calc (E - f.least).toNat * 2 ^ (f.precision - 1) + M.toNat + 1
        ≤ (E - f.least).toNat * 2 ^ (f.precision - 1) + 2 * 2 ^ (f.precision - 1) := by omega
      _ = ((E - f.least).toNat + 2) * 2 ^ (f.precision - 1) := by ring
      _ ≤ (f.most - f.least + 2).toNat * 2 ^ (f.precision - 1) := Nat.mul_le_mul_right _ hE

theorem placeOfNormal_lt {f : FloatFormat} (hp : 1 ≤ f.precision) {q r : ℚ} {E M E' M' : ℤ}
    (n : Normal f q E M) (n' : Normal f r E' M') (lt : q < r) : placeOfNormal f E M < placeOfNormal f E' M' := by
  obtain ⟨rfl, mpos, mlt, le, ge, side⟩ := n
  obtain ⟨rfl, mpos', mlt', le', ge', side'⟩ := n'
  unfold placeOfNormal
  have p2 := two_pow_pred (p := f.precision) hp
  rcases lt_trichotomy E E' with lt' | rfl | gt
  · have big : 2 ^ (f.precision - 1) ≤ M' := side'.resolve_left (by omega)
    have hM : M.toNat < 2 * 2 ^ (f.precision - 1) := by
      have : M < 2 * 2 ^ (f.precision - 1) := by rw [← p2]; exact mlt
      have c : ((2 * 2 ^ (f.precision - 1) : ℕ) : ℤ) = 2 * 2 ^ (f.precision - 1) := by push_cast; ring
      omega
    have hM' : 2 ^ (f.precision - 1) ≤ M'.toNat := by
      have c : ((2 ^ (f.precision - 1) : ℕ) : ℤ) = 2 ^ (f.precision - 1) := by push_cast; ring
      omega
    have hE : (E - f.least).toNat + 1 ≤ (E' - f.least).toNat := by omega
    calc (E - f.least).toNat * 2 ^ (f.precision - 1) + M.toNat
        < (E - f.least).toNat * 2 ^ (f.precision - 1) + 2 * 2 ^ (f.precision - 1) := by omega
      _ = ((E - f.least).toNat + 1) * 2 ^ (f.precision - 1) + 2 ^ (f.precision - 1) := by ring
      _ ≤ (E' - f.least).toNat * 2 ^ (f.precision - 1) + M'.toNat :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hE) hM'
  · have : (M : ℚ) < M' := by
      have pos : (0 : ℚ) < (2 : ℚ) ^ E := zpow_pos (by norm_num) _
      exact lt_of_mul_lt_mul_right lt (le_of_lt pos)
    have : M < M' := by exact_mod_cast this
    omega
  · exfalso
    have big : 2 ^ (f.precision - 1) ≤ M := side.resolve_left (by omega)
    have := lower_binade hp gt mlt' big
    exact lt_asymm lt this

theorem placeOf_lt {f : FloatFormat} (hp : 1 ≤ f.precision) {q r : ℚ} (vq : (Binary.finite q).Valid f)
    (vr : (Binary.finite r).Valid f) (pq : 0 < q) (lt : q < r) : placeOf f q < placeOf f r := by
  obtain ⟨E, M, n⟩ := normal_of_valid f hp vq pq
  obtain ⟨E', M', n'⟩ := normal_of_valid f hp vr (lt_trans pq lt)
  rw [placeOf_eq hp n, placeOf_eq hp n']
  exact placeOfNormal_lt hp n n' lt

theorem placeOf_bounds {f : FloatFormat} (hp : 1 ≤ f.precision) {q : ℚ} (vq : (Binary.finite q).Valid f)
    (pq : 0 < q) : 1 ≤ placeOf f q ∧ placeOf f q + 1 ≤ topPlace f := by
  obtain ⟨E, M, n⟩ := normal_of_valid f hp vq pq
  rw [placeOf_eq hp n]
  exact placeOfNormal_bounds hp n

/-- The positive value at a place from 1 below `topPlace`: the least exponent
    for the places below `2^(p−1)`, and otherwise the binade of the place's
    quotient by `2^(p−1)`. -/
noncomputable def placeValue (f : FloatFormat) (n : ℕ) : ℚ :=
  if n / 2 ^ (f.precision - 1) = 0 then (n : ℚ) * (2 : ℚ) ^ f.least
  else ((2 ^ (f.precision - 1) + n % 2 ^ (f.precision - 1) : ℕ) : ℚ) *
    (2 : ℚ) ^ (f.least + (n / 2 ^ (f.precision - 1) : ℕ) - 1)

theorem placeValue_normal {f : FloatFormat} (hp : 1 ≤ f.precision) (hf : f.least ≤ f.most) {n : ℕ} (pos : 1 ≤ n)
    (lt : n + 1 ≤ topPlace f) :
    ∃ E M, Normal f (placeValue f n) E M ∧ placeOfNormal f E M = n := by
  have P : 0 < 2 ^ (f.precision - 1) := pow_pos (by norm_num) _
  have p2 := two_pow_pred (p := f.precision) hp
  have divmod : n / 2 ^ (f.precision - 1) * 2 ^ (f.precision - 1) + n % 2 ^ (f.precision - 1) = n := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod n _
  have modlt := Nat.mod_lt n P
  set P' := 2 ^ (f.precision - 1) with hP'
  set k := n / P' with hk
  set j := n % P' with hj
  set T := (f.most - f.least + 2).toNat with hT
  have Tval : (T : ℤ) = f.most - f.least + 2 := by rw [hT]; omega
  have kbound : k < T := by
    unfold topPlace at lt
    rw [← hP', ← hT] at lt
    have : k * P' < T * P' := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  by_cases zero : k = 0
  · have nlt : n < P' := by rw [zero, Nat.zero_mul, Nat.zero_add] at divmod; omega
    refine ⟨f.least, n, ⟨?_, by omega, ?_, le_refl _, hf, .inl rfl⟩, ?_⟩
    · unfold placeValue; rw [← hP', ← hk, if_pos zero]; push_cast; ring
    · have : (n : ℤ) < P' := by exact_mod_cast nlt
      have : ((P' : ℕ) : ℤ) = 2 ^ (f.precision - 1) := by rw [hP']; push_cast; ring
      rw [p2]; omega
    · unfold placeOfNormal; simp
  · have kpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr zero
    refine ⟨f.least + (k : ℤ) - 1, ((P' + j : ℕ) : ℤ), ⟨?_, ?_, ?_, by omega, ?_, .inr ?_⟩, ?_⟩
    · unfold placeValue; rw [← hP', ← hk, ← hj, if_neg zero]; push_cast; ring_nf
    · push_cast; omega
    · have : ((P' : ℕ) : ℤ) = 2 ^ (f.precision - 1) := by rw [hP']; push_cast; ring
      have : (j : ℤ) < P' := by exact_mod_cast modlt
      push_cast; rw [p2]; omega
    · have : (k : ℤ) < T := by exact_mod_cast kbound
      omega
    · have : ((P' : ℕ) : ℤ) = 2 ^ (f.precision - 1) := by rw [hP']; push_cast; ring
      push_cast; omega
    · unfold placeOfNormal
      have e1 : (f.least + (k : ℤ) - 1 - f.least).toNat = k - 1 := by omega
      rw [e1, ← hP']
      simp only [Int.toNat_natCast]
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hk'] at divmod ⊢
      simp only [Nat.add_sub_cancel]
      rw [Nat.add_mul, Nat.one_mul] at divmod
      omega

theorem normal_valid {f : FloatFormat} {q : ℚ} {E M : ℤ} (n : Normal f q E M) : (Binary.finite q).Valid f := by
  obtain ⟨rfl, mpos, mlt, le, ge, _⟩ := n
  exact ⟨M, E, rfl, by rw [abs_of_pos (by omega)]; omega, by rw [abs_of_pos (by omega)]; exact mlt, le, ge⟩

theorem neg_valid {f : FloatFormat} {q : ℚ} (v : (Binary.finite q).Valid f) : (Binary.finite (-q)).Valid f := by
  obtain ⟨m, e, rfl, a, b, c, d⟩ := v
  exact ⟨-m, e, by push_cast; ring, by rwa [abs_neg], by rwa [abs_neg], c, d⟩

theorem valid_ne_zero {f : FloatFormat} {q : ℚ} (v : (Binary.finite q).Valid f) : q ≠ 0 := by
  obtain ⟨m, e, rfl, a, _⟩ := v
  have : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by intro h; rw [h] at a; simp at a)
  exact mul_ne_zero this (zpow_ne_zero _ (by norm_num))

/-! ### Places of all values -/

/-- The place of a value of the format, from 0: NaN, negative infinity, the
    negative numbers from the least, negative zero, positive zero, the
    positive numbers and positive infinity. -/
noncomputable def position (f : FloatFormat) : Binary → ℕ
  | .nan => 0
  | .infinity negative => if negative then 1 else 2 * topPlace f + 2
  | .zero negative => if negative then topPlace f + 1 else topPlace f + 2
  | .finite q => if q < 0 then topPlace f + 1 - placeOf f (-q) else topPlace f + 2 + placeOf f q

/-- The first place of the values equal to a value: negative zero's for a
    zero, which equals positive zero. -/
noncomputable def lowPosition (f : FloatFormat) (x : Binary) : ℕ :=
  match x with
  | .zero _ => topPlace f + 1
  | _ => position f x

/-- The last place of the values equal to a value: positive zero's for a
    zero. -/
noncomputable def highPosition (f : FloatFormat) (x : Binary) : ℕ :=
  match x with
  | .zero _ => topPlace f + 2
  | _ => position f x

/-- The place of a value other than NaN among the values with their signs:
    negative infinity at `−T`, a number at its place with its sign, the zeros
    at 0 and positive infinity at `T`. -/
noncomputable def signedPlace (f : FloatFormat) : Binary → ℤ
  | .nan => 0
  | .infinity negative => if negative then -(topPlace f : ℤ) else topPlace f
  | .zero _ => 0
  | .finite q => if q < 0 then -(placeOf f (-q) : ℤ) else placeOf f q

/-- A format with a significand digit and its least exponent below its
    greatest. -/
def Proper (f : FloatFormat) : Prop := 1 ≤ f.precision ∧ f.least ≤ f.most

theorem proper_fmt (double : Bool) : Proper (fmt double) := by
  cases double <;> simp [Proper, fmt, doubleFormat, floatFormat]

theorem top_pos {f : FloatFormat} (pf : Proper f) : 2 ≤ topPlace f := by
  unfold topPlace
  have : 2 ≤ (f.most - f.least + 2).toNat := by have := pf.2; omega
  have : 1 ≤ 2 ^ (f.precision - 1) := Nat.one_le_two_pow
  nlinarith

theorem finite_place {f : FloatFormat} (pf : Proper f) {q : ℚ} (v : (Binary.finite q).Valid f) :
    (q < 0 ∧ 1 ≤ placeOf f (-q) ∧ placeOf f (-q) + 1 ≤ topPlace f) ∨
      (0 < q ∧ 1 ≤ placeOf f q ∧ placeOf f q + 1 ≤ topPlace f) := by
  rcases lt_or_gt_of_ne (valid_ne_zero v) with neg | pos
  · exact .inl ⟨neg, placeOf_bounds pf.1 (neg_valid v) (by linarith)⟩
  · exact .inr ⟨pos, placeOf_bounds pf.1 v pos⟩

/-- `lowPosition` and `highPosition` as functions of the signed place. -/
def lowOf (T : ℕ) (s : ℤ) : ℤ := if s ≤ 0 then T + 1 + s else T + 2 + s
def highOf (T : ℕ) (s : ℤ) : ℤ := if s < 0 then T + 1 + s else T + 2 + s

theorem places_of {f : FloatFormat} (pf : Proper f) {x : Binary} (v : x.Valid f) (notNan : x ≠ .nan) :
    (lowPosition f x : ℤ) = lowOf (topPlace f) (signedPlace f x) ∧
      (highPosition f x : ℤ) = highOf (topPlace f) (signedPlace f x) ∧
      lowPosition f x ≤ position f x ∧ position f x ≤ highPosition f x ∧
      -(topPlace f : ℤ) ≤ signedPlace f x ∧ signedPlace f x ≤ topPlace f := by
  have T2 := top_pos pf
  cases x with
  | nan => exact absurd rfl notNan
  | infinity negative =>
    cases negative <;> simp [lowPosition, highPosition, position, signedPlace, lowOf, highOf] <;> omega
  | zero negative =>
    cases negative <;> simp [lowPosition, highPosition, position, signedPlace, lowOf, highOf]
  | finite q =>
    rcases finite_place pf v with ⟨neg, a, b⟩ | ⟨pos, a, b⟩
    · have : ¬ (0 : ℚ) ≤ q := not_le.mpr neg
      simp only [lowPosition, highPosition, position, signedPlace, lowOf, highOf, if_pos neg]
      refine ⟨?_, ?_, le_refl _, le_refl _, by omega, by omega⟩
      · rw [if_pos (by omega)]; push_cast [show placeOf f (-q) ≤ topPlace f + 1 by omega]; ring
      · rw [if_pos (by omega)]; push_cast [show placeOf f (-q) ≤ topPlace f + 1 by omega]; ring
    · have nneg : ¬ q < 0 := not_lt.mpr (le_of_lt pos)
      simp only [lowPosition, highPosition, position, signedPlace, lowOf, highOf, if_neg nneg]
      refine ⟨?_, ?_, le_refl _, le_refl _, by omega, by omega⟩
      · rw [if_neg (by omega)]; push_cast; ring
      · rw [if_neg (by omega)]; push_cast; ring

theorem key_finite (q : ℚ) : (Binary.finite q).key = some ((q : ℝ) : EReal) := rfl
theorem key_zero (negative : Bool) : (Binary.zero negative).key = some 0 := rfl
theorem key_infinity (negative : Bool) : (Binary.infinity negative).key = some (if negative then ⊥ else ⊤) := rfl

/-- The key of a value other than NaN. -/
noncomputable def keyOf : Binary → EReal
  | .finite q => ((q : ℝ) : EReal)
  | .zero _ => 0
  | .infinity negative => if negative then ⊥ else ⊤
  | .nan => 0

theorem key_eq {x : Binary} (notNan : x ≠ .nan) : x.key = some (keyOf x) := by
  cases x <;> simp_all [Binary.key, keyOf]

theorem signed_finite {f : FloatFormat} (pf : Proper f) {q : ℚ} (v : (Binary.finite q).Valid f) :
    -(topPlace f : ℤ) < signedPlace f (.finite q) ∧ signedPlace f (.finite q) < topPlace f ∧
      (q < 0 → signedPlace f (.finite q) < 0) ∧ (0 < q → 0 < signedPlace f (.finite q)) := by
  rcases finite_place pf v with ⟨neg, x, y⟩ | ⟨pos, x, y⟩
  · simp only [signedPlace, if_pos neg]
    exact ⟨by omega, by omega, fun _ => by omega, fun h => absurd h (by linarith)⟩
  · simp only [signedPlace, if_neg (not_lt.mpr (le_of_lt pos))]
    exact ⟨by omega, by omega, fun h => absurd h (by linarith), fun _ => by omega⟩

theorem signed_infinity (f : FloatFormat) (negative : Bool) :
    signedPlace f (.infinity negative) = if negative then -(topPlace f : ℤ) else topPlace f := rfl

theorem signed_zero (f : FloatFormat) (negative : Bool) : signedPlace f (.zero negative) = 0 := rfl

theorem key_finite_lt {q r : ℚ} : keyOf (.finite q) < keyOf (.finite r) ↔ q < r := by
  simp only [keyOf]
  rw [EReal.coe_lt_coe_iff]
  exact_mod_cast Iff.rfl

theorem key_zero_lt_finite {n : Bool} {r : ℚ} : keyOf (.zero n) < keyOf (.finite r) ↔ 0 < r := by
  simp only [keyOf]
  rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, EReal.coe_lt_coe_iff]
  exact_mod_cast Iff.rfl

theorem key_finite_lt_zero {n : Bool} {q : ℚ} : keyOf (.finite q) < keyOf (.zero n) ↔ q < 0 := by
  simp only [keyOf]
  rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, EReal.coe_lt_coe_iff]
  exact_mod_cast Iff.rfl

theorem signed_lt {f : FloatFormat} (pf : Proper f) {a b : Binary} (va : a.Valid f) (vb : b.Valid f)
    (na : a ≠ .nan) (nb : b ≠ .nan) (lt : keyOf a < keyOf b) : signedPlace f a < signedPlace f b := by
  have T2 := top_pos pf
  cases a with
  | nan => exact absurd rfl na
  | infinity n1 =>
    cases n1
    · simp [keyOf] at lt
    · rw [signed_infinity]
      simp only [if_true]
      cases b with
      | nan => exact absurd rfl nb
      | infinity n2 =>
        cases n2
        · rw [signed_infinity]; simp only [Bool.false_eq_true, if_false]; omega
        · simp [keyOf] at lt
      | zero n2 => rw [signed_zero]; omega
      | finite r => have := (signed_finite pf vb).1; omega
  | zero n1 =>
    rw [signed_zero]
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 =>
      cases n2
      · rw [signed_infinity]; simp only [Bool.false_eq_true, if_false]; omega
      · simp [keyOf] at lt
    | zero n2 => simp [keyOf] at lt
    | finite r => exact (signed_finite pf vb).2.2.2 (key_zero_lt_finite.mp lt)
  | finite q =>
    have fa := signed_finite pf va
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 =>
      cases n2
      · rw [signed_infinity]; simp only [Bool.false_eq_true, if_false]; omega
      · simp [keyOf] at lt
    | zero n2 => rw [signed_zero]; exact fa.2.2.1 (key_finite_lt_zero.mp lt)
    | finite r =>
      have qr : q < r := key_finite_lt.mp lt
      have fb := signed_finite pf vb
      rcases lt_or_gt_of_ne (valid_ne_zero va) with qneg | qpos
      · rcases lt_or_gt_of_ne (valid_ne_zero vb) with rneg | rpos
        · have : placeOf f (-r) < placeOf f (-q) :=
            placeOf_lt pf.1 (neg_valid vb) (neg_valid va) (by linarith) (by linarith)
          simp only [signedPlace, if_pos qneg, if_pos rneg]; omega
        · exact lt_trans (fa.2.2.1 qneg) (fb.2.2.2 rpos)
      · have rpos : 0 < r := lt_trans qpos qr
        have : placeOf f q < placeOf f r := placeOf_lt pf.1 va vb qpos qr
        simp only [signedPlace, if_neg (not_lt.mpr (le_of_lt qpos)), if_neg (not_lt.mpr (le_of_lt rpos))]
        omega

theorem signed_eq {f : FloatFormat} {a b : Binary} (na : a ≠ .nan) (nb : b ≠ .nan) (same : keyOf a = keyOf b)
    (va : a.Valid f) (vb : b.Valid f) : signedPlace f a = signedPlace f b := by
  cases a with
  | nan => exact absurd rfl na
  | infinity n1 =>
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 => cases n1 <;> cases n2 <;> simp_all [keyOf]
    | zero n2 => cases n1 <;> simp [keyOf] at same
    | finite r => cases n1 <;> simp [keyOf] at same
  | zero n1 =>
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 => cases n2 <;> simp [keyOf] at same
    | zero n2 => simp [signedPlace]
    | finite r =>
      exfalso
      simp only [keyOf] at same
      have : ((0 : ℝ) : EReal) = ((r : ℝ) : EReal) := by simpa using same
      have : (0 : ℝ) = (r : ℝ) := EReal.coe_injective this
      exact valid_ne_zero vb (by exact_mod_cast this.symm)
  | finite q =>
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 => cases n2 <;> simp [keyOf] at same
    | zero n2 =>
      exfalso
      simp only [keyOf] at same
      have : ((q : ℝ) : EReal) = ((0 : ℝ) : EReal) := by simpa using same
      have : (q : ℝ) = (0 : ℝ) := EReal.coe_injective this
      exact valid_ne_zero va (by exact_mod_cast this)
    | finite r =>
      simp only [keyOf] at same
      have : (q : ℝ) = (r : ℝ) := EReal.coe_injective same
      have : q = r := by exact_mod_cast this
      rw [this]

theorem high_lt_low {f : FloatFormat} (pf : Proper f) {a b : Binary} (va : a.Valid f) (vb : b.Valid f)
    (na : a ≠ .nan) (nb : b ≠ .nan) (lt : keyOf a < keyOf b) : highPosition f a < lowPosition f b := by
  have s := signed_lt pf va vb na nb lt
  obtain ⟨_, ha, _⟩ := places_of pf va na
  obtain ⟨lb, _⟩ := places_of pf vb nb
  have : (highPosition f a : ℤ) < lowPosition f b := by
    rw [ha, lb]; unfold highOf lowOf; split_ifs <;> omega
  exact_mod_cast this

theorem same_places {f : FloatFormat} (pf : Proper f) {a b : Binary} (va : a.Valid f) (vb : b.Valid f)
    (na : a ≠ .nan) (nb : b ≠ .nan) (same : keyOf a = keyOf b) :
    lowPosition f a = lowPosition f b ∧ highPosition f a = highPosition f b := by
  have s := signed_eq na nb same va vb
  obtain ⟨la, ha, _⟩ := places_of pf va na
  obtain ⟨lb, hb, _⟩ := places_of pf vb nb
  constructor
  · have : (lowPosition f a : ℤ) = lowPosition f b := by rw [la, lb, s]
    exact_mod_cast this
  · have : (highPosition f a : ℤ) = highPosition f b := by rw [ha, hb, s]
    exact_mod_cast this

theorem low_pos {f : FloatFormat} (pf : Proper f) {x : Binary} (v : x.Valid f) (n : x ≠ .nan) :
    1 ≤ lowPosition f x := by
  obtain ⟨l, _, _, _, lo', _⟩ := places_of pf v n
  have : (1 : ℤ) ≤ lowPosition f x := by rw [l]; unfold lowOf; split_ifs <;> omega
  exact_mod_cast this

theorem position_nan (f : FloatFormat) : position f .nan = 0 := rfl

theorem position_pos {f : FloatFormat} (pf : Proper f) {x : Binary} (v : x.Valid f) (n : x ≠ .nan) :
    1 ≤ position f x :=
  le_trans (low_pos pf v n) (places_of pf v n).2.2.1

/-- A value is at or above a bound, other than NaN, exactly when its place is
    at or above the first place of the values equal to the bound. -/
theorem le_iff_position {f : FloatFormat} (pf : Proper f) {b x : Binary} (vb : b.Valid f) (vx : x.Valid f)
    (nb : b ≠ .nan) : b.Le x ↔ lowPosition f b ≤ position f x := by
  by_cases nx : x = .nan
  · subst nx
    have := low_pos pf vb nb
    simp only [position_nan]
    constructor
    · rintro ⟨_, _, _, h, _⟩; simp [Binary.key] at h
    · intro h; omega
  · obtain ⟨_, _, lowx, posx, _⟩ := places_of pf vx nx
    obtain ⟨_, _, lowb, posb, _⟩ := places_of pf vb nb
    simp only [Binary.Le, key_eq nb, key_eq nx, Option.some.injEq, exists_and_left, exists_eq_left']
    constructor
    · intro le
      rcases lt_or_eq_of_le le with lt | eq
      · have := high_lt_low pf vb vx nb nx lt; omega
      · rw [(same_places pf vb vx nb nx eq).1]; exact lowx
    · intro h
      by_contra not
      have := high_lt_low pf vx vb nx nb (not_le.mp not)
      omega

/-- A value is above a bound, other than NaN, exactly when its place is beyond
    the last place of the values equal to the bound. -/
theorem lt_iff_position {f : FloatFormat} (pf : Proper f) {b x : Binary} (vb : b.Valid f) (vx : x.Valid f)
    (nb : b ≠ .nan) : b.Lt x ↔ highPosition f b < position f x := by
  by_cases nx : x = .nan
  · subst nx
    simp only [position_nan]
    constructor
    · rintro ⟨_, _, _, h, _⟩; simp [Binary.key] at h
    · intro h; omega
  · obtain ⟨_, _, lowx, posx, _⟩ := places_of pf vx nx
    obtain ⟨_, _, lowb, posb, _⟩ := places_of pf vb nb
    simp only [Binary.Lt, key_eq nb, key_eq nx, Option.some.injEq, exists_and_left, exists_eq_left']
    constructor
    · intro lt
      have := high_lt_low pf vb vx nb nx lt; omega
    · intro h
      by_contra not
      rcases lt_or_eq_of_le (not_lt.mp not) with lt | eq
      · have := high_lt_low pf vx vb nx nb lt; omega
      · have := (same_places pf vx vb nx nb eq).2; omega

/-- A value other than NaN is at or below a bound exactly when its place is at
    or below the last place of the values equal to the bound. -/
theorem le_bound_iff_position {f : FloatFormat} (pf : Proper f) {b x : Binary} (vb : b.Valid f)
    (vx : x.Valid f) (nb : b ≠ .nan) : x.Le b ↔ 1 ≤ position f x ∧ position f x ≤ highPosition f b := by
  by_cases nx : x = .nan
  · subst nx
    simp only [position_nan]
    constructor
    · rintro ⟨_, _, h, _⟩; simp [Binary.key] at h
    · intro h; omega
  · obtain ⟨_, _, lowx, posx, _⟩ := places_of pf vx nx
    obtain ⟨_, _, lowb, posb, _⟩ := places_of pf vb nb
    have p1 := position_pos pf vx nx
    simp only [Binary.Le, key_eq nb, key_eq nx, Option.some.injEq, exists_and_left, exists_eq_left']
    constructor
    · intro le
      refine ⟨p1, ?_⟩
      rcases lt_or_eq_of_le le with lt | eq
      · have := high_lt_low pf vx vb nx nb lt; omega
      · rw [← (same_places pf vx vb nx nb eq).2]; exact posx
    · rintro ⟨_, h⟩
      by_contra not
      have := high_lt_low pf vb vx nb nx (not_le.mp not)
      omega

/-- A value other than NaN is below a bound exactly when its place is below the
    first place of the values equal to the bound. -/
theorem lt_bound_iff_position {f : FloatFormat} (pf : Proper f) {b x : Binary} (vb : b.Valid f)
    (vx : x.Valid f) (nb : b ≠ .nan) : x.Lt b ↔ 1 ≤ position f x ∧ position f x < lowPosition f b := by
  by_cases nx : x = .nan
  · subst nx
    simp only [position_nan]
    constructor
    · rintro ⟨_, _, h, _⟩; simp [Binary.key] at h
    · intro h; omega
  · obtain ⟨_, _, lowx, posx, _⟩ := places_of pf vx nx
    obtain ⟨_, _, lowb, posb, _⟩ := places_of pf vb nb
    have p1 := position_pos pf vx nx
    simp only [Binary.Lt, key_eq nb, key_eq nx, Option.some.injEq, exists_and_left, exists_eq_left']
    constructor
    · intro lt
      have := high_lt_low pf vx vb nx nb lt; exact ⟨p1, by omega⟩
    · rintro ⟨_, h⟩
      by_contra not
      rcases lt_or_eq_of_le (not_lt.mp not) with lt | eq
      · have := high_lt_low pf vb vx nb nx lt; omega
      · have := (same_places pf vb vx nb nx eq).1; omega

/-- NaN is comparable to no value. -/
theorem nan_not_le (x : Binary) : ¬ Binary.Le .nan x ∧ ¬ Binary.Le x .nan ∧ ¬ Binary.Lt .nan x ∧
    ¬ Binary.Lt x .nan := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨_, _, h1, h2, _⟩ <;> simp_all [Binary.key]

/-! ### Every place has one value -/

/-- The value at a place: the inverse of `position`. -/
noncomputable def valueAt (f : FloatFormat) (n : ℕ) : Binary :=
  if n = 0 then .nan
  else if n = 1 then .infinity true
  else if n ≤ topPlace f then .finite (-(placeValue f (topPlace f + 1 - n)))
  else if n = topPlace f + 1 then .zero true
  else if n = topPlace f + 2 then .zero false
  else if n ≤ 2 * topPlace f + 1 then .finite (placeValue f (n - topPlace f - 2))
  else .infinity false

theorem valueAt_spec {f : FloatFormat} (pf : Proper f) {n : ℕ} (le : n ≤ 2 * topPlace f + 2) :
    (valueAt f n).Valid f ∧ position f (valueAt f n) = n := by
  have T2 := top_pos pf
  unfold valueAt
  split_ifs with h0 h1 h2 h3 h4 h5
  · exact ⟨trivial, by rw [h0]; rfl⟩
  · exact ⟨trivial, by rw [h1]; rfl⟩
  · obtain ⟨E, M, normal, place⟩ := placeValue_normal pf.1 pf.2 (n := topPlace f + 1 - n) (by omega) (by omega)
    have pos := normal_pos normal
    refine ⟨neg_valid (normal_valid normal), ?_⟩
    simp only [position, if_pos (show -(placeValue f (topPlace f + 1 - n)) < 0 by linarith), neg_neg]
    rw [placeOf_eq pf.1 normal, place]; omega
  · exact ⟨trivial, by simp [position, h3]⟩
  · exact ⟨trivial, by simp [position, h4]⟩
  · obtain ⟨E, M, normal, place⟩ := placeValue_normal pf.1 pf.2 (n := n - topPlace f - 2) (by omega) (by omega)
    have pos := normal_pos normal
    refine ⟨normal_valid normal, ?_⟩
    simp only [position, if_neg (not_lt.mpr (le_of_lt pos))]
    rw [placeOf_eq pf.1 normal, place]; omega
  · exact ⟨trivial, by simp [position]; omega⟩

theorem position_le {f : FloatFormat} (pf : Proper f) {x : Binary} (v : x.Valid f) :
    position f x ≤ 2 * topPlace f + 2 := by
  by_cases n : x = .nan
  · rw [n, position_nan]; omega
  · obtain ⟨l, h, _, ph, _, upper⟩ := places_of pf v n
    have : (highPosition f x : ℤ) ≤ 2 * topPlace f + 2 := by rw [h]; unfold highOf; split_ifs <;> omega
    omega

theorem key_same {f : FloatFormat} {a b : Binary} (va : a.Valid f) (vb : b.Valid f) (na : a ≠ .nan)
    (nb : b ≠ .nan) (same : keyOf a = keyOf b) : a = b ∨ ∃ n1 n2, a = .zero n1 ∧ b = .zero n2 := by
  cases a with
  | nan => exact absurd rfl na
  | infinity n1 =>
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 => cases n1 <;> cases n2 <;> simp_all [keyOf]
    | zero n2 => cases n1 <;> simp [keyOf] at same
    | finite r => cases n1 <;> simp [keyOf] at same
  | zero n1 =>
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 => cases n2 <;> simp [keyOf] at same
    | zero n2 => exact .inr ⟨n1, n2, rfl, rfl⟩
    | finite r =>
      exfalso
      simp only [keyOf] at same
      have : ((0 : ℝ) : EReal) = ((r : ℝ) : EReal) := by simpa using same
      have : (0 : ℝ) = (r : ℝ) := EReal.coe_injective this
      exact valid_ne_zero vb (by exact_mod_cast this.symm)
  | finite q =>
    cases b with
    | nan => exact absurd rfl nb
    | infinity n2 => cases n2 <;> simp [keyOf] at same
    | zero n2 =>
      exfalso
      simp only [keyOf] at same
      have : ((q : ℝ) : EReal) = ((0 : ℝ) : EReal) := by simpa using same
      have : (q : ℝ) = (0 : ℝ) := EReal.coe_injective this
      exact valid_ne_zero va (by exact_mod_cast this)
    | finite r =>
      simp only [keyOf] at same
      have : (q : ℝ) = (r : ℝ) := EReal.coe_injective same
      have : q = r := by exact_mod_cast this
      exact .inl (by rw [this])

theorem position_injective {f : FloatFormat} (pf : Proper f) {a b : Binary} (va : a.Valid f) (vb : b.Valid f)
    (same : position f a = position f b) : a = b := by
  by_cases na : a = .nan
  · by_cases nb : b = .nan
    · rw [na, nb]
    · have := position_pos pf vb nb; rw [na, position_nan] at same; omega
  · by_cases nb : b = .nan
    · have := position_pos pf va na; rw [nb, position_nan] at same; omega
    · obtain ⟨_, _, la, ha, _⟩ := places_of pf va na
      obtain ⟨_, _, lb, hb, _⟩ := places_of pf vb nb
      rcases lt_trichotomy (keyOf a) (keyOf b) with lt | eq | gt
      · have := high_lt_low pf va vb na nb lt; omega
      · rcases key_same va vb na nb eq with e | ⟨n1, n2, rfl, rfl⟩
        · exact e
        · cases n1 <;> cases n2 <;> simp_all [position]
      · have := high_lt_low pf vb va nb na gt; omega

/-- The values of the format whose places run from `lo` to before `hi`. -/
def Slot (f : FloatFormat) (lo hi : ℕ) : Set Binary := {x | x.Valid f ∧ lo ≤ position f x ∧ position f x < hi}

theorem slot_eq_image {f : FloatFormat} (pf : Proper f) (lo hi : ℕ) (h : hi ≤ 2 * topPlace f + 3) :
    Slot f lo hi = valueAt f '' Set.Ico lo hi := by
  ext x
  constructor
  · rintro ⟨v, l, u⟩
    refine ⟨position f x, ⟨l, u⟩, ?_⟩
    have := valueAt_spec pf (n := position f x) (position_le pf v)
    exact position_injective pf this.1 v this.2
  · rintro ⟨n, ⟨l, u⟩, rfl⟩
    obtain ⟨v, p⟩ := valueAt_spec pf (n := n) (by omega)
    exact ⟨v, by rw [p]; exact l, by rw [p]; exact u⟩

/-- A run of places holds exactly as many values as it has places. -/
theorem slot_card {f : FloatFormat} (pf : Proper f) (lo hi : ℕ) (h : hi ≤ 2 * topPlace f + 3) :
    (Slot f lo hi).ncard = hi - lo := by
  rw [slot_eq_image pf lo hi h, Set.InjOn.ncard_image]
  · rw [Set.ncard_eq_toFinset_card', Set.toFinset_Ico, Nat.card_Ico]
  · intro m hm n hn same
    have pm := (valueAt_spec pf (n := m) (by simp at hm; omega)).2
    have pn := (valueAt_spec pf (n := n) (by simp at hn; omega)).2
    rw [← pm, ← pn, same]

theorem slot_finite (f : FloatFormat) (pf : Proper f) (lo hi : ℕ) : (Slot f lo hi).Finite := by
  apply Set.Finite.subset (slot_eq_image pf 0 (2 * topPlace f + 3) le_rfl ▸ (Set.finite_Ico 0 _).image _)
  rintro x ⟨v, _, _⟩
  exact ⟨v, Nat.zero_le _, by have := position_le pf v; omega⟩

/-! ### The kernel's places -/

/-- The number of binary digits of a natural number. -/
def bitLen : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitLen ((n + 1) / 2) + 1

theorem bitLen_bounds : ∀ {n : ℕ}, 0 < n → 2 ^ (bitLen n - 1) ≤ n ∧ n < 2 ^ bitLen n
  | 0, h => absurd h (by omega)
  | n + 1, _ => by
    by_cases one : n = 0
    · subst one; simp [bitLen]
    · have ih := bitLen_bounds (n := (n + 1) / 2) (by omega)
      simp only [bitLen, Nat.add_sub_cancel]
      have L1 : 1 ≤ bitLen ((n + 1) / 2) := by
        by_contra z
        have z' : bitLen ((n + 1) / 2) = 0 := by omega
        have := ih.2; rw [z'] at this; simp at this; omega
      have e : 2 ^ bitLen ((n + 1) / 2) = 2 * 2 ^ (bitLen ((n + 1) / 2) - 1) := by
        rw [← pow_succ']; congr 1; omega
      have e2 : 2 ^ (bitLen ((n + 1) / 2) + 1) = 2 * 2 ^ bitLen ((n + 1) / 2) := by rw [pow_succ]; ring
      constructor
      · rw [e]; have := ih.1; omega
      · rw [e2]; have := ih.2; omega
termination_by n => n
decreasing_by all_goals omega

theorem bitLen_le {n p : ℕ} (lt : n < 2 ^ p) : bitLen n ≤ p := by
  by_cases z : n = 0
  · subst z; simp [bitLen]
  · have := (bitLen_bounds (n := n) (by omega)).1
    by_contra over
    have : 2 ^ p ≤ 2 ^ (bitLen n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem length_spec (m : U64) : ∃ r, floats.length m = .ok r ∧ r.val = bitLen m.val := by
  rw [floats.length]
  by_cases zero : m.val = 0
  · have : m = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using zero
    exact ⟨0#usize, by simp [this], by simp [zero, bitLen]⟩
  · obtain ⟨half, hRun, hVal⟩ := UScalar.div_spec m (y := 2#u64) (by simp)
    have halfIs : half.val = m.val / 2 := by simpa using hVal
    obtain ⟨r, run, value⟩ := length_spec half
    have small : r.val ≤ 64 := by
      rw [value]; apply bitLen_le; rw [halfIs]; have : m.val < 2 ^ 64 := by scalar_tac
      omega
    have maxBig : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
    obtain ⟨s, sRun, sVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := 1#usize) (y := r) (by simp; omega))
    have mne : m ≠ 0#u64 := fun h => zero (by rw [h]; rfl)
    refine ⟨s, by simp [mne, hRun, run, sRun], ?_⟩
    have : s.val = 1 + r.val := by simpa using sVal
    rw [this, value, halfIs]
    obtain ⟨k, hk⟩ : ∃ k, m.val = k + 1 := ⟨m.val - 1, by omega⟩
    rw [hk]; simp [bitLen]; omega
termination_by m.val
decreasing_by rw [halfIs]; omega

/-- The odd significand of a valid value of the format is below `2^p`, its
    exponent at least the least one, and the value below `2^p × 2^most`. -/
theorem odd_bounds {double : Bool} {m s : ℕ} (odd : m % 2 = 1)
    (valid : (Binary.finite ((m : ℚ) * scale s)).Valid (fmt double)) :
    m < 2 ^ prec double ∧ lo double ≤ s ∧
      (m : ℚ) * scale s < 2 ^ prec double * (2 : ℚ) ^ ((hi double : ℤ) - 2048) := by
  obtain ⟨m', e, same, pos, lt, le, ge⟩ := valid
  rw [Rowl.Floats.fmt_precision] at lt
  rw [Rowl.Floats.fmt_least] at le
  rw [Rowl.Floats.fmt_most] at ge
  have m'pos : 0 < m' := by
    have mq : (0 : ℚ) < (m : ℚ) * scale s := mul_pos (by exact_mod_cast (show 0 < m by omega)) (Rowl.Floats.scale_pos s)
    rw [same] at mq
    by_contra neg
    have : (m' : ℚ) ≤ 0 := by exact_mod_cast not_lt.mp neg
    have := mul_nonpos_of_nonpos_of_nonneg this (le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) e))
    linarith
  rw [abs_of_pos m'pos] at lt
  obtain ⟨k, o, oOdd, ho⟩ := Nat.exists_eq_two_pow_mul_odd (n := m'.toNat) (by omega)
  have oMod : o % 2 = 1 := Nat.odd_iff.mp oOdd
  -- write the value with the odd significand `o`
  have eNat : 0 ≤ e + k + 2048 := by have := le; omega
  have rep : (m' : ℚ) * (2 : ℚ) ^ e = (o : ℚ) * scale (e + k + 2048).toNat := by
    unfold scale
    have : ((((e + k + 2048).toNat : ℕ) : ℤ) - 2048) = e + k := by omega
    rw [this, zpow_add₀ (by norm_num), zpow_natCast]
    have : (m' : ℚ) = ((m'.toNat : ℕ) : ℚ) := by
      have : ((m'.toNat : ℕ) : ℤ) = m' := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this.symm
    rw [this, ho]; push_cast; ring
  obtain ⟨mo, so⟩ := Rowl.Floats.odd_scaled_unique odd oMod (same.trans rep)
  have oLe : o ≤ m'.toNat := by
    rw [ho]; exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
  refine ⟨?_, ?_, ?_⟩
  · rw [mo]
    have : (m'.toNat : ℤ) = m' := Int.toNat_of_nonneg (by omega)
    have : m'.toNat < 2 ^ prec double := by
      have h2 : ((2 ^ prec double : ℕ) : ℤ) = 2 ^ prec double := by push_cast; ring
      omega
    omega
  · rw [so]; omega
  · rw [same]
    have two : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _
    have : (m' : ℚ) < 2 ^ prec double := by exact_mod_cast lt
    calc (m' : ℚ) * (2 : ℚ) ^ e < 2 ^ prec double * (2 : ℚ) ^ e := mul_lt_mul_of_pos_right this two
      _ ≤ 2 ^ prec double * (2 : ℚ) ^ ((hi double : ℤ) - 2048) :=
          mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) ge) (by positivity)

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by simp [core.num.Usize.MAX]

theorem cast_usize_u128 (x : Usize) : (UScalar.cast .U128 x).val = x.val := by
  have h := x.hBounds
  have : x.val < 2 ^ 64 := by
    rcases System.Platform.numBits_eq with e | e <;> (simp_all [UScalarTy.numBits]; try omega)
  simp; omega

theorem cast_u64_u128 (x : U64) : (UScalar.cast .U128 x).val = x.val := by simp

theorem two_zpow_lt {a b : ℤ} : (2 : ℚ) ^ a < (2 : ℚ) ^ b ↔ a < b := zpow_lt_zpow_iff_right₀ (by norm_num)

/-- The kernel's place of a positive value with an odd significand is its
    place among the positive values of its format. -/
theorem place_spec (m : U64) (s : Usize) (double : Bool) (odd : m.val % 2 = 1)
    (valid : (Binary.finite ((m.val : ℚ) * scale s.val)).Valid (fmt double)) :
    ∃ r, floats.place m s double = .ok r ∧ r.val = placeOf (fmt double) ((m.val : ℚ) * scale s.val) := by
  obtain ⟨mlt, los, vlt⟩ := odd_bounds odd valid
  have pp := Rowl.Floats.prec_pos double
  have ple := Rowl.Floats.prec_le double
  have lohi := Rowl.Floats.lo_le_hi double
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  have loGe : 974 ≤ lo double := by cases double <;> simp [lo]
  have maxBig : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  obtain ⟨L, lRun, lVal⟩ := length_spec m
  have mpos : 0 < m.val := by omega
  obtain ⟨b1, b2⟩ := bitLen_bounds mpos
  have Lle : L.val ≤ prec double := by rw [lVal]; exact bitLen_le mlt
  have L1 : 1 ≤ L.val := by
    rw [lVal]; by_contra z
    have : bitLen m.val = 0 := by omega
    rw [this] at b2; simp at b2; omega
  rw [← lVal] at b1 b2
  -- the value bounds the exponent
  have sSmall : s.val + L.val ≤ prec double + hi double := by
    have low : (2 : ℚ) ^ (((L.val - 1 : ℕ) : ℤ) + ((s.val : ℤ) - 2048)) ≤ (m.val : ℚ) * scale s.val := by
      rw [zpow_add₀ (by norm_num), zpow_natCast]
      unfold scale
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos (by norm_num) _))
      exact_mod_cast b1
    have high : (2 : ℚ) ^ prec double * (2 : ℚ) ^ ((hi double : ℤ) - 2048) =
        (2 : ℚ) ^ (((prec double : ℕ) : ℤ) + ((hi double : ℤ) - 2048)) := by
      rw [zpow_add₀ (by norm_num), zpow_natCast]
    have := lt_of_le_of_lt low (high ▸ vlt)
    rw [two_zpow_lt] at this
    omega
  -- the kernel's steps
  obtain ⟨p, pRun, pVal⟩ := Rowl.Floats.precision_spec double
  obtain ⟨low, lowRun, lowVal⟩ := Rowl.Floats.least_spec double
  obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := core.num.Usize.MAX) (y := 64#usize) (by simp [usize_max_val]; scalar_tac))
  have iIs : i.val = Usize.max - 64 := by simp [usize_max_val] at iVal; omega
  have sLt : s < i := by rw [UScalar.lt_equiv, iIs]; omega
  obtain ⟨high, highRun, highVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := s) (y := L) (by omega))
  obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := low) (y := p) (by omega))
  -- the exponent of the normal form, plus 2048
  obtain ⟨ex, exRun, exIs⟩ : ∃ ex : Usize, (if i2.val ≤ high.val then high - p else ok low) = .ok ex ∧
      ex.val = if lo double + prec double ≤ s.val + L.val then s.val + L.val - prec double else lo double := by
    by_cases up : lo double + prec double ≤ s.val + L.val
    · obtain ⟨e, eRun, eVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := high) (y := p) (by omega))
      have le : i2.val ≤ high.val := by omega
      exact ⟨e, by simp [le, eRun], by rw [if_pos up]; omega⟩
    · have nle : ¬ i2.val ≤ high.val := by omega
      exact ⟨low, by simp [nle], by rw [if_neg up, lowVal]⟩
  have exLo : lo double ≤ ex.val := by rw [exIs]; split_ifs <;> omega
  have exS : ex.val ≤ s.val := by rw [exIs]; split_ifs <;> omega
  have exHi : ex.val ≤ hi double := by rw [exIs]; split_ifs <;> omega
  have gap : s.val - ex.val + L.val ≤ prec double := by rw [exIs]; split_ifs <;> omega
  have exLe : ex ≤ s := by rw [UScalar.le_equiv]; exact exS
  obtain ⟨i3, i3Run, i3Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := s) (y := ex) (by omega))
  have i3Is : i3.val = s.val - ex.val := by omega
  have i3Lt : i3 < 64#usize := by rw [UScalar.lt_equiv]; simp only [i3Is]; scalar_tac
  obtain ⟨i4, i4Run, i4Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := ex) (y := low) (by omega))
  have i4Is : i4.val = ex.val - lo double := by omega
  obtain ⟨i6, i6Run, i6Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := p) (y := 1#usize) (by simp; omega))
  have i6Is : i6.val = prec double - 1 := by simp at i6Val; omega
  obtain ⟨i7, i7Run, i7Val⟩ := Rowl.Floats.native_two_spec i6 (by omega)
  have i5Is := cast_usize_u128 i4
  have pow52 : 2 ^ (prec double - 1) ≤ 2 ^ 52 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have prod1 : (ex.val - lo double) * 2 ^ (prec double - 1) ≤ 3019 * 2 ^ 52 := Nat.mul_le_mul (by omega) pow52
  obtain ⟨i8, i8Run, i8Val⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x := UScalar.cast .U128 i4) (y := i7) (by
      rw [i5Is, i4Is, i7Val, i6Is]; simp [UScalar.max, U128.max_eq]; omega))
  have i9Is := cast_u64_u128 m
  obtain ⟨i10, i10Run, i10Val⟩ := Rowl.Floats.native_two_spec i3 (by rw [i3Is]; omega)
  have mBound : m.val < 2 ^ 64 := by scalar_tac
  have shiftBound : 2 ^ i3.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by rw [i3Is]; omega)
  have prod2 : m.val * 2 ^ i3.val ≤ 2 ^ 64 * 2 ^ 63 := Nat.mul_le_mul (by omega) shiftBound
  obtain ⟨i11, i11Run, i11Val⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x := UScalar.cast .U128 m) (y := i10) (by
      rw [i9Is, i10Val]; simp [UScalar.max, U128.max_eq]; omega))
  have i8Is : i8.val = (ex.val - lo double) * 2 ^ (prec double - 1) := by rw [i8Val, i5Is, i4Is, i7Val, i6Is]
  have i11Is : i11.val = m.val * 2 ^ (s.val - ex.val) := by rw [i11Val, i9Is, i10Val, i3Is]
  have prod3 : m.val * 2 ^ (s.val - ex.val) ≤ 2 ^ 64 * 2 ^ 63 := by rw [← i3Is]; exact prod2
  obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := i8) (y := i11) (by rw [i8Is, i11Is]; simp [UScalar.max, U128.max_eq]; omega))
  have sLt' : s.val < i.val := by omega
  have i3Lt' : i3.val < 64 := by omega
  refine ⟨r, by simp [floats.place, pRun, lowRun, iRun, sLt', lRun, highRun, i2Run, exRun, exS, i3Run, i3Lt',
    i4Run, lift, i6Run, i7Run, i8Run, i10Run, i11Run, rRun], ?_⟩
  -- the normal form
  have normal : Normal (fmt double) ((m.val : ℚ) * scale s.val) ((ex.val : ℤ) - 2048)
      ((m.val * 2 ^ (s.val - ex.val) : ℕ) : ℤ) := by
    refine ⟨?_, ?_, ?_, by rw [Rowl.Floats.fmt_least]; omega, by rw [Rowl.Floats.fmt_most]; omega, ?_⟩
    · unfold scale
      push_cast
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 2
      push_cast [exS]; ring
    · have : 1 ≤ m.val * 2 ^ (s.val - ex.val) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    · have : m.val * 2 ^ (s.val - ex.val) < 2 ^ prec double := by
        calc m.val * 2 ^ (s.val - ex.val) < 2 ^ L.val * 2 ^ (s.val - ex.val) :=
              Nat.mul_lt_mul_of_pos_right b2 (by positivity)
          _ = 2 ^ (L.val + (s.val - ex.val)) := by rw [pow_add]
          _ ≤ 2 ^ prec double := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Rowl.Floats.fmt_precision]
      exact_mod_cast this
    · by_cases up : lo double + prec double ≤ s.val + L.val
      · right
        have exIs' : ex.val = s.val + L.val - prec double := by rw [exIs, if_pos up]
        have : 2 ^ (prec double - 1) ≤ m.val * 2 ^ (s.val - ex.val) := by
          calc 2 ^ (prec double - 1) = 2 ^ (L.val - 1) * 2 ^ (s.val - ex.val) := by
                rw [← pow_add]; congr 1; omega
            _ ≤ m.val * 2 ^ (s.val - ex.val) := Nat.mul_le_mul_right _ b1
        rw [Rowl.Floats.fmt_precision]
        exact_mod_cast this
      · left
        rw [Rowl.Floats.fmt_least, exIs, if_neg up]
  rw [placeOf_eq (proper_fmt double).1 normal, rVal, i8Is, i11Is]
  unfold placeOfNormal
  rw [Rowl.Floats.fmt_least, Rowl.Floats.fmt_precision]
  have : ((ex.val : ℤ) - 2048 - ((lo double : ℤ) - 2048)).toNat = ex.val - lo double := by omega
  rw [this, Int.toNat_natCast]

theorem top_place_spec (double : Bool) :
    ∃ r, floats.top_place double = .ok r ∧ r.val = topPlace (fmt double) := by
  have pp := Rowl.Floats.prec_pos double
  have ple := Rowl.Floats.prec_le double
  have lohi := Rowl.Floats.lo_le_hi double
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  have maxBig : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  obtain ⟨mo, moRun, moVal⟩ := Rowl.Floats.most_spec double
  obtain ⟨le, leRun, leVal⟩ := Rowl.Floats.least_spec double
  obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := mo) (y := le) (by omega))
  obtain ⟨i3, i3Run, i3Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i2) (y := 2#usize) (by simp; omega))
  have i3Is : i3.val = hi double - lo double + 2 := by simp at i3Val; omega
  obtain ⟨p, pRun, pVal⟩ := Rowl.Floats.precision_spec double
  obtain ⟨i6, i6Run, i6Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := p) (y := 1#usize) (by simp; omega))
  have i6Is : i6.val = prec double - 1 := by simp at i6Val; omega
  obtain ⟨i7, i7Run, i7Val⟩ := Rowl.Floats.native_two_spec i6 (by omega)
  have i4Is := cast_usize_u128 i3
  have pow52 : 2 ^ (prec double - 1) ≤ 2 ^ 52 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have prod : (hi double - lo double + 2) * 2 ^ (prec double - 1) ≤ 3021 * 2 ^ 52 := Nat.mul_le_mul (by omega) pow52
  obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x := UScalar.cast .U128 i3) (y := i7) (by
      rw [i4Is, i3Is, i7Val, i6Is]; simp [UScalar.max, U128.max_eq]; omega))
  refine ⟨r, by simp [floats.top_place, moRun, leRun, i2Run, i3Run, lift, pRun, i6Run, i7Run, rRun], ?_⟩
  rw [rVal, i4Is, i3Is, i7Val, i6Is]
  unfold topPlace
  rw [Rowl.Floats.fmt_most, Rowl.Floats.fmt_least, Rowl.Floats.fmt_precision]
  congr 1
  omega

theorem top_small (double : Bool) : topPlace (fmt double) ≤ 3021 * 2 ^ 52 := by
  cases double <;> simp [topPlace, fmt, doubleFormat, floatFormat]

theorem places_spec (double : Bool) :
    ∃ r, floats.places double = .ok r ∧ r.val = 2 * topPlace (fmt double) + 3 := by
  obtain ⟨t, tRun, tVal⟩ := top_place_spec double
  have small := top_small double
  obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x := 2#u128) (y := t) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
  have i1Is : i1.val = 2 * topPlace (fmt double) := by rw [i1Val, tVal]; simp
  obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := i1) (y := 3#u128) (by rw [i1Is]; simp [UScalar.max, U128.max_eq]; omega))
  refine ⟨r, by simp [floats.places, tRun, i1Run, rRun], ?_⟩
  rw [rVal, i1Is]; simp

theorem finite_valid_abs {double : Bool} {negative : Bool} {m : ℕ} {e : ℕ}
    (v : (Binary.finite ((if negative then -1 else 1) * (m : ℚ) * scale e)).Valid (fmt double)) :
    (Binary.finite ((m : ℚ) * scale e)).Valid (fmt double) := by
  cases negative
  · simpa using v
  · have := neg_valid v
    simpa using this

/-- The kernel computes the place of a canonical value of the format. -/
theorem position_spec (b : datatypes.Binary) (double : Bool) (c : CanonicalBinary b)
    (v : (binaryOf b).Valid (fmt double)) :
    ∃ r, floats.position b double = .ok r ∧ r.val = position (fmt double) (binaryOf b) := by
  obtain ⟨t, tRun, tVal⟩ := top_place_spec double
  have small := top_small double
  have pf := proper_fmt double
  cases b with
  | NotANumber => exact ⟨0#u128, by simp [floats.position, tRun], by simp [binaryOf, position]⟩
  | Infinite negative =>
    cases negative
    · obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists
        (UScalar.mul_spec (x := 2#u128) (y := t) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
      have iIs : i.val = 2 * topPlace (fmt double) := by rw [iVal, tVal]; simp
      obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := i) (y := 2#u128) (by rw [iIs]; simp [UScalar.max, U128.max_eq]; omega))
      refine ⟨r, by simp [floats.position, tRun, iRun, rRun], ?_⟩
      rw [rVal, iIs]; simp [binaryOf, position]
    · exact ⟨1#u128, by simp [floats.position, tRun], by simp [binaryOf, position]⟩
  | Finite negative m s =>
    by_cases zero : m.val = 0
    · have mz : m = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using zero
      cases negative
      · obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x := t) (y := 2#u128) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
        refine ⟨r, by simp [floats.position, tRun, mz, rRun], ?_⟩
        rw [rVal, tVal]; simp [binaryOf, zero, position]
      · obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x := t) (y := 1#u128) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
        refine ⟨r, by simp [floats.position, tRun, mz, rRun], ?_⟩
        rw [rVal, tVal]; simp [binaryOf, zero, position]
    · have odd : m.val % 2 = 1 := by
        simp only [CanonicalBinary] at c; omega
      have mnz : m ≠ 0#u64 := fun h => zero (by rw [h]; rfl)
      simp only [binaryOf, zero, ↓reduceIte] at v ⊢
      have vabs := finite_valid_abs v
      obtain ⟨p, pRun, pVal⟩ := place_spec m s double odd vabs
      have mpos : (0 : ℚ) < (m.val : ℚ) * scale s.val :=
        mul_pos (by exact_mod_cast (show 0 < m.val by omega)) (Rowl.Floats.scale_pos _)
      obtain ⟨p1, p2⟩ := placeOf_bounds pf.1 vabs mpos
      have pLt : p.val < t.val := by rw [pVal, tVal]; omega
      cases negative
      · obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x := t) (y := 2#u128) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
        have iIs : i.val = topPlace (fmt double) + 2 := by rw [iVal, tVal]; simp
        obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x := i) (y := p) (by rw [iIs, pVal]; simp [UScalar.max, U128.max_eq]; omega))
        refine ⟨r, by simp [floats.position, tRun, mnz, pRun, pLt, iRun, rRun], ?_⟩
        rw [rVal, iIs, pVal]
        simp only [position, Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [if_neg (not_lt.mpr (le_of_lt mpos))]
      · obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x := t) (y := 1#u128) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
        have iIs : i.val = topPlace (fmt double) + 1 := by rw [iVal, tVal]; simp
        obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists
          (UScalar.sub_spec (x := i) (y := p) (by rw [iIs, pVal]; omega))
        refine ⟨r, by simp [floats.position, tRun, mnz, pRun, pLt, iRun, rRun], ?_⟩
        have neg : -1 * (m.val : ℚ) * scale s.val < 0 := by linarith
        rw [rVal.1, iIs, pVal]
        simp only [position, ↓reduceIte]
        rw [if_pos neg]
        congr 2
        ring

theorem low_position_spec (b : datatypes.Binary) (double : Bool) (c : CanonicalBinary b)
    (v : (binaryOf b).Valid (fmt double)) :
    ∃ r, floats.low_position b double = .ok r ∧ r.val = lowPosition (fmt double) (binaryOf b) := by
  obtain ⟨t, tRun, tVal⟩ := top_place_spec double
  have small := top_small double
  obtain ⟨r, run, value⟩ := position_spec b double c v
  cases b with
  | NotANumber => exact ⟨r, by simpa [floats.low_position] using run, by simpa [lowPosition, binaryOf] using value⟩
  | Infinite n => exact ⟨r, by simpa [floats.low_position] using run, by simpa [lowPosition, binaryOf] using value⟩
  | Finite n m s =>
    by_cases zero : m.val = 0
    · have mz : m = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using zero
      obtain ⟨r', rRun, rVal⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := t) (y := 1#u128) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
      refine ⟨r', ?_, ?_⟩
      · simp only [floats.low_position, mz]
        split
        · simp [tRun, rRun]
        · next _ h => exact absurd rfl h
      · rw [rVal, tVal]; simp [binaryOf, zero, lowPosition]
    · refine ⟨r, ?_, ?_⟩
      · simp only [floats.low_position]
        split
        · exfalso; exact zero rfl
        · exact run
      · simp only [binaryOf, zero, ↓reduceIte] at value ⊢
        simpa [lowPosition] using value

theorem high_position_spec (b : datatypes.Binary) (double : Bool) (c : CanonicalBinary b)
    (v : (binaryOf b).Valid (fmt double)) :
    ∃ r, floats.high_position b double = .ok r ∧ r.val = highPosition (fmt double) (binaryOf b) := by
  obtain ⟨t, tRun, tVal⟩ := top_place_spec double
  have small := top_small double
  obtain ⟨r, run, value⟩ := position_spec b double c v
  cases b with
  | NotANumber => exact ⟨r, by simpa [floats.high_position] using run, by simpa [highPosition, binaryOf] using value⟩
  | Infinite n => exact ⟨r, by simpa [floats.high_position] using run, by simpa [highPosition, binaryOf] using value⟩
  | Finite n m s =>
    by_cases zero : m.val = 0
    · have mz : m = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using zero
      obtain ⟨r', rRun, rVal⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := t) (y := 2#u128) (by rw [tVal]; simp [UScalar.max, U128.max_eq]; omega))
      refine ⟨r', ?_, ?_⟩
      · simp only [floats.high_position, mz]
        split
        · simp [tRun, rRun]
        · next _ h => exact absurd rfl h
      · rw [rVal, tVal]; simp [binaryOf, zero, highPosition]
    · refine ⟨r, ?_, ?_⟩
      · simp only [floats.high_position]
        split
        · exfalso; exact zero rfl
        · exact run
      · simp only [binaryOf, zero, ↓reduceIte] at value ⊢
        simpa [highPosition] using value

theorem is_nan_spec (b : datatypes.Binary) : floats.is_nan b = .ok (decide (binaryOf b = .nan)) := by
  cases b with
  | NotANumber => simp [floats.is_nan, binaryOf]
  | Infinite n => simp [floats.is_nan, binaryOf]
  | Finite n m s => by_cases z : m.val = 0 <;> simp [floats.is_nan, binaryOf, z]

/-! ### Range facets as places -/

/-- Whether a value meets a range facet with a bound in the order of XML
    Schema. -/
def FacetHolds (F : datatypes.Facet) (b x : Binary) : Prop :=
  match F with
  | .MinInclusive => b.Le x
  | .MaxInclusive => x.Le b
  | .MinExclusive => b.Lt x
  | .MaxExclusive => x.Lt b

/-- The places of the values that meet a range facet with a bound other than
    NaN: from the first place of the values equal to the bound, or after the
    last; for an upper bound, from the place after NaN on and before the first
    or after the last. -/
def FacetPlaces (f : FloatFormat) (F : datatypes.Facet) (b : Binary) (n : ℕ) : Prop :=
  match F with
  | .MinInclusive => lowPosition f b ≤ n
  | .MinExclusive => highPosition f b + 1 ≤ n
  | .MaxInclusive => 1 ≤ n ∧ ¬ highPosition f b + 1 ≤ n
  | .MaxExclusive => 1 ≤ n ∧ ¬ lowPosition f b ≤ n

/-- A range facet holds of a value exactly when the bound is no NaN and the
    value's place is among the facet's places. -/
theorem facet_holds_iff {f : FloatFormat} (pf : Proper f) (F : datatypes.Facet) {b x : Binary}
    (vb : b.Valid f) (vx : x.Valid f) : FacetHolds F b x ↔ b ≠ .nan ∧ FacetPlaces f F b (position f x) := by
  by_cases nb : b = .nan
  · subst nb
    have := nan_not_le x
    cases F <;> simp_all [FacetHolds]
  · cases F
    · simp only [FacetHolds, FacetPlaces, ne_eq, nb, not_false_eq_true, true_and]
      exact le_iff_position pf vb vx nb
    · simp only [FacetHolds, FacetPlaces, ne_eq, nb, not_false_eq_true, true_and]
      rw [le_bound_iff_position pf vb vx nb]; omega
    · simp only [FacetHolds, FacetPlaces, ne_eq, nb, not_false_eq_true, true_and]
      rw [lt_iff_position pf vb vx nb]; omega
    · simp only [FacetHolds, FacetPlaces, ne_eq, nb, not_false_eq_true, true_and]
      rw [lt_bound_iff_position pf vb vx nb]; omega

/-- Every value of a format is the value of a canonical kernel value. -/
theorem canonical_exists {double : Bool} {x : Binary} (v : x.Valid (fmt double)) :
    ∃ b : datatypes.Binary, CanonicalBinary b ∧ binaryOf b = x := by
  cases x with
  | nan => exact ⟨.NotANumber, trivial, rfl⟩
  | infinity n => exact ⟨.Infinite n, trivial, rfl⟩
  | zero n => exact ⟨.Finite n 0#u64 2048#usize, .inl ⟨rfl, rfl⟩, by simp [binaryOf]⟩
  | finite q =>
    have pf := proper_fmt double
    have hq := valid_ne_zero v
    -- the magnitude in normal form, then its odd part
    obtain ⟨E, M, normal⟩ := normal_of_valid (fmt double) pf.1 (show (Binary.finite |q|).Valid (fmt double) by
      rcases le_or_gt 0 q with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact neg_valid v) (abs_pos.mpr hq)
    obtain ⟨eq, mpos, mlt, le, ge, _⟩ := normal
    have mlt' : M < 2 ^ prec double := by rw [Rowl.Floats.fmt_precision] at mlt; exact mlt
    have ple := Rowl.Floats.prec_le double
    obtain ⟨k, o, oOdd, ho⟩ := Nat.exists_eq_two_pow_mul_odd (n := M.toNat) (by omega)
    have oMod : o % 2 = 1 := Nat.odd_iff.mp oOdd
    have oLe : o ≤ M.toNat := by rw [ho]; exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
    have oSmall : o < 2 ^ 64 := by
      have : M.toNat < 2 ^ 53 := by
        have : (M.toNat : ℤ) = M := Int.toNat_of_nonneg (by omega)
        have : M < 2 ^ 53 := lt_of_lt_of_le mlt' (pow_le_pow_right₀ (by norm_num) ple)
        omega
      have : 2 ^ 53 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    have leD : (fmt double).least ≥ -1074 := by cases double <;> simp [fmt, doubleFormat, floatFormat]
    have geD : (fmt double).most ≤ 971 := by cases double <;> simp [fmt, doubleFormat, floatFormat]
    have kSmall : k < 64 := by
      by_contra big
      have : 2 ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ k ≤ M.toNat := by rw [ho]; exact Nat.le_mul_of_pos_right _ (by have := Nat.odd_iff.mp oOdd; omega)
      have : (M.toNat : ℤ) = M := Int.toNat_of_nonneg (by omega)
      have : M < 2 ^ 53 := lt_of_lt_of_le mlt' (pow_le_pow_right₀ (by norm_num) ple)
      omega
    have sNat : 0 ≤ E + k + 2048 := by omega
    have sSmall : (E + k + 2048).toNat < 2 ^ 16 := by omega
    have oBound : o < 2 ^ UScalarTy.U64.numBits := by simpa [UScalarTy.numBits] using oSmall
    have sBound : (E + k + 2048).toNat < 2 ^ UScalarTy.Usize.numBits := by
      have : 2 ^ 16 ≤ 2 ^ UScalarTy.Usize.numBits := by
        rcases System.Platform.numBits_eq with e | e <;> simp [UScalarTy.numBits, e]
      omega
    refine ⟨.Finite (decide (q < 0)) (UScalar.ofNatCore o oBound) (UScalar.ofNatCore (E + k + 2048).toNat sBound),
      .inr (by rw [UScalar.ofNatCore_val_eq]; exact oMod), ?_⟩
    have oNe : o ≠ 0 := by omega
    simp only [binaryOf, UScalar.ofNatCore_val_eq, oNe, ↓reduceIte]
    congr 1
    -- `|q| = M × 2^E = o × 2^(E + k)`
    have abs_eq : |q| = (o : ℚ) * scale (E + k + 2048).toNat := by
      rw [eq]
      unfold scale
      have : (((E + k + 2048).toNat : ℕ) : ℤ) - 2048 = E + k := by omega
      rw [this, zpow_add₀ (by norm_num), zpow_natCast]
      have : (M : ℚ) = ((M.toNat : ℕ) : ℚ) := by
        have : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this.symm
      rw [this, ho]; push_cast; ring
    rcases lt_or_gt_of_ne hq with neg | pos
    · simp only [neg, decide_true, ↓reduceIte]
      rw [mul_assoc, ← abs_eq, abs_of_neg neg]; ring
    · simp only [not_lt.mpr (le_of_lt pos), decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [mul_assoc, ← abs_eq, abs_of_pos pos]; ring

end Rowl.FloatOrder
