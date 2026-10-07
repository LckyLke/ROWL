import Rowl.Moments

/-!
The actual kernel reading of the lexical forms of `xsd:double` and `xsd:float`
(`floats::binary_value`). Its numbers are exact: the decimal number of a
numeral divided by a power of two is kept as an integer part, a remainder and
a denominator (`Quot`), and the search for the exponent halves or doubles that
quotient until the integer part has `p` binary digits, or until the least
exponent (`settleMath`). Rounding at that exponent (`roundMath`) is then
`floatingPointRound` of XML Schema (`Rowl.DatatypeMap.roundBinary`,
`settle_round`). The kernel finds the first quotient natively when the numbers
fit in 128 bits, and on decimal digit strings otherwise.
-/
namespace Rowl.Floats
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.DatatypeMap
open Rowl.Numbers (Canonical value_snoc value_nil canonical_zero canonical_low canonical_nil digits_append
  digits_cons)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! ## Formats -/

/-- The format of the kernel's `double` flag. -/
def fmt (double : Bool) : FloatFormat := if double then doubleFormat else floatFormat

/-- The digits of the significand. -/
def prec (double : Bool) : ℕ := if double then 53 else 24
/-- The least exponent of 2, plus 2048. -/
def lo (double : Bool) : ℕ := if double then 974 else 1899
/-- The greatest exponent of 2, plus 2048. -/
def hi (double : Bool) : ℕ := if double then 3019 else 2152

theorem fmt_precision (double : Bool) : (fmt double).precision = prec double := by cases double <;> rfl
theorem fmt_least (double : Bool) : (fmt double).least = (lo double : ℤ) - 2048 := by cases double <;> rfl
theorem fmt_most (double : Bool) : (fmt double).most = (hi double : ℤ) - 2048 := by cases double <;> rfl
theorem prec_pos (double : Bool) : 1 ≤ prec double := by cases double <;> simp [prec]
theorem lo_le_hi (double : Bool) : lo double ≤ hi double := by cases double <;> simp [lo, hi]

/-! ## Quotients by powers of two -/

/-- `2^(e − 2048)`. -/
def scale (e : ℕ) : ℚ := (2 : ℚ) ^ ((e : ℤ) - 2048)

theorem scale_pos (e : ℕ) : 0 < scale e := zpow_pos (by norm_num) _

theorem scale_succ (e : ℕ) : scale (e + 1) = 2 * scale e := by
  unfold scale
  rw [show ((e + 1 : ℕ) : ℤ) - 2048 = ((e : ℤ) - 2048) + 1 by push_cast; ring, zpow_add_one₀ (by norm_num)]
  ring

/-- `a / 2^(e − 2048)` is `k + rem / den`, the remainder below the
    denominator. -/
def Quot (a : ℚ) (k rem den e : ℕ) : Prop :=
  0 < den ∧ rem < den ∧ a = ((k : ℚ) + (rem : ℚ) / den) * scale e

theorem quot_bounds {a : ℚ} {k rem den e : ℕ} (q : Quot a k rem den e) :
    (k : ℚ) * scale e ≤ a ∧ a < ((k : ℚ) + 1) * scale e := by
  obtain ⟨dpos, rlt, eq⟩ := q
  have dq : (0 : ℚ) < den := by exact_mod_cast dpos
  have frac0 : (0 : ℚ) ≤ (rem : ℚ) / den := div_nonneg (by positivity) dq.le
  have frac1 : (rem : ℚ) / den < 1 := by rw [div_lt_one dq]; exact_mod_cast rlt
  have s := scale_pos e
  rw [eq]
  constructor <;> nlinarith

/-- Halving: the quotient at the next exponent. -/
theorem quot_up {a : ℚ} {k rem den e : ℕ} (q : Quot a k rem den e) :
    Quot a (k / 2) ((k % 2) * den + rem) (2 * den) (e + 1) := by
  obtain ⟨dpos, rlt, eq⟩ := q
  have bit : k % 2 ≤ 1 := by omega
  refine ⟨by omega, by nlinarith, ?_⟩
  rw [eq, scale_succ]
  have hk : (k : ℚ) = 2 * ((k / 2 : ℕ) : ℚ) + ((k % 2 : ℕ) : ℚ) := by exact_mod_cast (Nat.div_add_mod k 2).symm
  have dq : (den : ℚ) ≠ 0 := by exact_mod_cast dpos.ne'
  rw [hk]
  push_cast
  field_simp
  ring

/-- Doubling with a remainder below half the denominator. -/
theorem quot_down_low {a : ℚ} {k rem den e : ℕ} (q : Quot a k rem den (e + 1)) (low : 2 * rem < den) :
    Quot a (2 * k) (2 * rem) den e := by
  obtain ⟨dpos, _, eq⟩ := q
  refine ⟨dpos, low, ?_⟩
  rw [eq, scale_succ]
  push_cast
  ring

/-- Doubling with a remainder of half the denominator or more. -/
theorem quot_down_high {a : ℚ} {k rem den e : ℕ} (q : Quot a k rem den (e + 1)) (high : ¬ 2 * rem < den) :
    Quot a (2 * k + 1) (2 * rem - den) den e := by
  obtain ⟨dpos, rlt, eq⟩ := q
  refine ⟨dpos, by omega, ?_⟩
  rw [eq, scale_succ]
  have dq : (den : ℚ) ≠ 0 := by exact_mod_cast dpos.ne'
  have sub : ((2 * rem - den : ℕ) : ℚ) = 2 * (rem : ℚ) - den := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [sub]
  push_cast
  field_simp
  ring

/-! ## Finding the exponent -/

/-- The search for the exponent: halve the quotient while its integer part has
    more than `p` binary digits (to an infinity past the greatest exponent,
    marked by the greatest plus one), and double it while it has fewer and the
    exponent is above the least. -/
def settleMath (p lo hi : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ × ℕ)
  | 0, _, _, _, _ => none
  | fuel + 1, k, rem, den, e =>
    if 2 ^ p ≤ k then
      if e < hi then settleMath p lo hi fuel (k / 2) ((k % 2) * den + rem) (2 * den) (e + 1)
      else some (k, rem, den, e + 1)
    else if lo < e ∧ 2 * k < 2 ^ p then
      if 2 * rem < den then settleMath p lo hi fuel (2 * k) (2 * rem) den (e - 1)
      else settleMath p lo hi fuel (2 * k + 1) (2 * rem - den) den (e - 1)
    else some (k, rem, den, e)

/-- What the search ends with: past the greatest exponent with too large an
    integer part there, or at an exponent within the format with an integer
    part of at most `p` binary digits, exactly `p` above the least exponent. -/
def Settled (a : ℚ) (p lo hi k rem den e : ℕ) : Prop :=
  (e = hi + 1 ∧ Quot a k rem den hi ∧ 2 ^ p ≤ k) ∨
  (lo ≤ e ∧ e ≤ hi ∧ Quot a k rem den e ∧ k < 2 ^ p ∧ (2 ^ p ≤ 2 * k ∨ e = lo))

theorem settle_sound {a : ℚ} {p lo hi : ℕ} :
    ∀ (fuel k rem den e : ℕ), Quot a k rem den e → lo ≤ e → e ≤ hi → ∀ k' rem' den' e',
      settleMath p lo hi fuel k rem den e = some (k', rem', den', e') → Settled a p lo hi k' rem' den' e'
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [settleMath] at h
  | fuel + 1, k, rem, den, e, q, low, high, k', rem', den', e', h => by
    unfold settleMath at h
    by_cases big : 2 ^ p ≤ k
    · simp only [big, ↓reduceIte] at h
      by_cases below : e < hi
      · simp only [below, ↓reduceIte] at h
        exact settle_sound fuel _ _ _ _ (quot_up q) (by omega) (by omega) _ _ _ _ h
      · simp only [below, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have : e = hi := by omega
        subst this
        exact .inl ⟨rfl, q, big⟩
    · simp only [big, ↓reduceIte] at h
      by_cases down : lo < e ∧ 2 * k < 2 ^ p
      · simp only [down, and_self, ↓reduceIte] at h
        obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + 1 := ⟨e - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at h
        by_cases low' : 2 * rem < den
        · simp only [low', ↓reduceIte] at h
          exact settle_sound fuel _ _ _ _ (quot_down_low q low') (by omega) (by omega) _ _ _ _ h
        · simp only [low', ↓reduceIte] at h
          exact settle_sound fuel _ _ _ _ (quot_down_high q low') (by omega) (by omega) _ _ _ _ h
      · simp only [down, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine .inr ⟨low, high, q, by omega, ?_⟩
        by_cases atLeast : lo < e
        · exact .inl (by simp only [not_and, not_lt] at down; exact down atLeast)
        · exact .inr (by omega)

/-- The integer part of a quotient is at least `2^j` exactly when the number
    is at least `2^j` times the power. -/
theorem quot_ge_iff {a : ℚ} {k rem den e : ℕ} (q : Quot a k rem den e) (j : ℕ) :
    2 ^ j ≤ k ↔ (2 : ℚ) ^ j * scale e ≤ a := by
  obtain ⟨lower, upper⟩ := quot_bounds q
  have s := scale_pos e
  constructor
  · intro h
    have : ((2 ^ j : ℕ) : ℚ) ≤ k := by exact_mod_cast h
    push_cast at this
    nlinarith
  · intro h
    by_contra small
    have : (k : ℚ) + 1 ≤ ((2 ^ j : ℕ) : ℚ) := by exact_mod_cast (show k + 1 ≤ 2 ^ j by omega)
    push_cast at this
    nlinarith

/-- The steps that the search takes at most from an exponent: up to the
    greatest exponent while the number is too large there, down to the least
    while it is below half of that. -/
noncomputable def settleBound (a : ℚ) (p lo hi e : ℕ) : ℕ :=
  if (2 : ℚ) ^ p * scale e ≤ a then hi - e + 1 else if a < (2 : ℚ) ^ (p - 1) * scale e then e - lo else 0

theorem two_pow_pred {p : ℕ} (pPos : 1 ≤ p) : (2 : ℚ) ^ p = 2 * 2 ^ (p - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem two_pow_pred_nat {p : ℕ} (pPos : 1 ≤ p) : 2 ^ p = 2 * 2 ^ (p - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- With fuel beyond those steps, the search ends. -/
theorem settle_complete {a : ℚ} {p lo hi : ℕ} (pPos : 1 ≤ p) :
    ∀ (fuel k rem den e : ℕ), Quot a k rem den e → lo ≤ e → e ≤ hi → settleBound a p lo hi e < fuel →
      ∃ r, settleMath p lo hi fuel k rem den e = some r
  | 0, _, _, _, _, _, _, _, bound => by simp at bound
  | fuel + 1, k, rem, den, e, q, low, high, bound => by
    unfold settleMath
    unfold settleBound at bound
    by_cases big : 2 ^ p ≤ k
    · simp only [big, ↓reduceIte]
      have aBig := (quot_ge_iff q p).mp big
      by_cases below : e < hi
      · simp only [below, ↓reduceIte]
        refine settle_complete pPos fuel _ _ _ _ (quot_up q) (by omega) (by omega) ?_
        simp only [aBig, ↓reduceIte] at bound
        unfold settleBound
        have notHalf : ¬ a < (2 : ℚ) ^ (p - 1) * scale (e + 1) := by
          rw [scale_succ]
          rw [two_pow_pred pPos] at aBig
          intro h; nlinarith
        split_ifs <;> omega
      · simp only [below, ↓reduceIte]
        exact ⟨_, rfl⟩
    · simp only [big, ↓reduceIte]
      have aSmall : ¬ (2 : ℚ) ^ p * scale e ≤ a := fun h => big ((quot_ge_iff q p).mpr h)
      simp only [aSmall, ↓reduceIte] at bound
      by_cases down : lo < e ∧ 2 * k < 2 ^ p
      · simp only [down, and_self, ↓reduceIte]
        obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + 1 := ⟨e - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have half : ¬ 2 ^ (p - 1) ≤ k := by have := two_pow_pred_nat pPos; omega
        have aHalf : a < (2 : ℚ) ^ (p - 1) * scale (e₀ + 1) := by
          by_contra h; exact half ((quot_ge_iff q (p - 1)).mpr (not_lt.mp h))
        simp only [aHalf, ↓reduceIte] at bound
        have notUp : ¬ (2 : ℚ) ^ p * scale e₀ ≤ a := by
          rw [scale_succ] at aHalf
          rw [two_pow_pred pPos]
          intro h; nlinarith
        by_cases low' : 2 * rem < den
        · simp only [low', ↓reduceIte]
          refine settle_complete pPos fuel _ _ _ _ (quot_down_low q low') (by omega) (by omega) ?_
          unfold settleBound
          simp only [notUp, ↓reduceIte]
          split_ifs <;> omega
        · simp only [low', ↓reduceIte]
          refine settle_complete pPos fuel _ _ _ _ (quot_down_high q low') (by omega) (by omega) ?_
          unfold settleBound
          simp only [notUp, ↓reduceIte]
          split_ifs <;> omega
      · simp only [down, ↓reduceIte]
        exact ⟨_, rfl⟩

/-! ## Rounding -/

theorem log_ge {a : ℚ} (apos : 0 < a) {x : ℤ} (h : (2 : ℚ) ^ x ≤ a) : x ≤ Int.log 2 a :=
  (Int.zpow_le_iff_le_log (b := 2) (by norm_num) apos).mp (by exact_mod_cast h)

theorem log_lt {a : ℚ} (apos : 0 < a) {x : ℤ} (h : a < (2 : ℚ) ^ x) : Int.log 2 a < x :=
  (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) apos).mp (by exact_mod_cast h)

theorem two_pow_scale (j e : ℕ) : (2 : ℚ) ^ j * scale e = (2 : ℚ) ^ ((j : ℤ) + ((e : ℤ) - 2048)) := by
  unfold scale; rw [zpow_add₀ (by norm_num), zpow_natCast]

/-- The significand that rounding a quotient gives: the nearer integer, at a
    tie the even one. -/
def roundUp (k rem den : ℕ) : ℕ :=
  if 2 * rem < den then k else if den < 2 * rem then k + 1 else if k % 2 = 1 then k + 1 else k

theorem roundUp_le (k rem den : ℕ) : roundUp k rem den ≤ k + 1 := by
  unfold roundUp; split_ifs <;> omega

/-- The value of a settled quotient: past the greatest exponent, or rounded
    up to `2^p` at the greatest exponent, an infinity. -/
noncomputable def roundSettled (double negative : Bool) (k rem den e : ℕ) : Binary :=
  if hi double < e then .infinity negative
  else if roundUp k rem den = 0 then .zero negative
  else if roundUp k rem den = 2 ^ prec double ∧ e = hi double then .infinity negative
  else .finite ((if negative then -1 else 1) * (roundUp k rem den : ℚ) * scale e)

/-- Rounding a quotient as `floatingPointRound` does is `roundUp`. -/
theorem round_quot {a : ℚ} {k rem den e : ℕ} (q : Quot a k rem den e) {c : ℤ}
    (hc : Int.floor (a / (2 : ℚ) ^ ((e : ℤ) - 2048)) + 1 = c) :
    (if (c : ℚ) * (2 : ℚ) ^ ((e : ℤ) - 2048) - (2 : ℚ) ^ ((e : ℤ) - 2048 - 1) < a
      then (c : ℚ) * (2 : ℚ) ^ ((e : ℤ) - 2048)
      else if a < (c : ℚ) * (2 : ℚ) ^ ((e : ℤ) - 2048) - (2 : ℚ) ^ ((e : ℤ) - 2048 - 1)
        then ((c : ℚ) - 1) * (2 : ℚ) ^ ((e : ℤ) - 2048)
      else if c % 2 = 0 then (c : ℚ) * (2 : ℚ) ^ ((e : ℤ) - 2048)
      else ((c : ℚ) - 1) * (2 : ℚ) ^ ((e : ℤ) - 2048)) =
      (roundUp k rem den : ℚ) * scale e := by
  subst hc
  obtain ⟨dpos, rlt, eq⟩ := q
  have dq : (0 : ℚ) < den := by exact_mod_cast dpos
  have s : (2 : ℚ) ^ ((e : ℤ) - 2048) = scale e := rfl
  have spos := scale_pos e
  have div : a / scale e = (k : ℚ) + (rem : ℚ) / den := by rw [eq]; field_simp
  have frac0 : (0 : ℚ) ≤ (rem : ℚ) / den := div_nonneg (by positivity) dq.le
  have frac1 : (rem : ℚ) / den < 1 := by rw [div_lt_one dq]; exact_mod_cast rlt
  have fl : Int.floor (a / scale e) = (k : ℤ) := by
    rw [div, Int.floor_eq_iff]; push_cast; constructor <;> linarith
  have half : (2 : ℚ) ^ ((e : ℤ) - 2048 - 1) = scale e / 2 := by
    rw [zpow_sub₀ (by norm_num), zpow_one, s]
  rw [s, half, fl]
  push_cast
  have aIs : a = ((k : ℚ) + (rem : ℚ) / den) * scale e := eq
  have cmpHigh : ((k : ℚ) + 1) * scale e - scale e / 2 < a ↔ den < 2 * rem := by
    rw [aIs]
    constructor
    · intro h
      have : (1 : ℚ) / 2 < (rem : ℚ) / den := by nlinarith
      rw [lt_div_iff₀ dq] at this
      exact_mod_cast (by linarith : ((den : ℚ)) < 2 * rem)
    · intro h
      have h' : (den : ℚ) < 2 * rem := by exact_mod_cast h
      have : (1 : ℚ) / 2 < (rem : ℚ) / den := by rw [lt_div_iff₀ dq]; linarith
      nlinarith
  have cmpLow : a < ((k : ℚ) + 1) * scale e - scale e / 2 ↔ 2 * rem < den := by
    rw [aIs]
    constructor
    · intro h
      have : (rem : ℚ) / den < 1 / 2 := by nlinarith
      rw [div_lt_iff₀ dq] at this
      exact_mod_cast (by linarith : (2 * (rem : ℚ)) < den)
    · intro h
      have h' : 2 * (rem : ℚ) < den := by exact_mod_cast h
      have : (rem : ℚ) / den < 1 / 2 := by rw [div_lt_iff₀ dq]; linarith
      nlinarith
  unfold roundUp
  by_cases low : 2 * rem < den
  · have notHigh : ¬ den < 2 * rem := by omega
    rw [if_neg (by rw [cmpHigh]; exact notHigh), if_pos (cmpLow.mpr low), if_pos low]
    ring
  · by_cases high : den < 2 * rem
    · rw [if_pos (cmpHigh.mpr high), if_neg low, if_pos high]
      push_cast; ring
    · rw [if_neg (by rw [cmpHigh]; exact high), if_neg (by rw [cmpLow]; exact low), if_neg low, if_neg high]
      have parity : ((k : ℤ) + 1) % 2 = 0 ↔ k % 2 = 1 := by omega
      by_cases odd : k % 2 = 1
      · rw [if_pos (parity.mpr odd), if_pos odd]; push_cast; ring
      · rw [if_neg (by rw [parity]; exact odd), if_neg odd]; ring

theorem sign_value {a : ℚ} (apos : 0 < a) (negative : Bool) :
    abs (if negative then -a else a) = a ∧ decide ((if negative then -a else a) < 0) = negative := by
  cases negative
  · simp [abs_of_pos apos, not_lt.mpr apos.le]
  · simp [abs_of_pos apos, apos]

/-- A settled quotient rounds as `floatingPointRound` does. -/
theorem settle_round {a : ℚ} (apos : 0 < a) (double negative : Bool) {k rem den e : ℕ}
    (h : Settled a (prec double) (lo double) (hi double) k rem den e) :
    roundSettled double negative k rem den e = roundBinary (fmt double) (if negative then -a else a) := by
  obtain ⟨absv, sign⟩ := sign_value apos negative
  have pPos := prec_pos double
  unfold roundBinary
  rw [absv, sign, fmt_precision, fmt_least, fmt_most]
  rcases h with ⟨rfl, q, big⟩ | ⟨low, high, q, small, edge⟩
  · have aBig := (quot_ge_iff q _).mp big
    rw [two_pow_scale] at aBig
    have := log_ge apos aBig
    have over : (hi double : ℤ) - 2048 < Int.log 2 a - (prec double : ℤ) + 1 := by omega
    simp only [roundSettled, show hi double < hi double + 1 by omega, ↓reduceIte, over]
  · have upper : a < (2 : ℚ) ^ ((prec double : ℤ) + ((e : ℤ) - 2048)) := by
      rw [← two_pow_scale]
      have := (quot_bounds q).2
      have kq : (k : ℚ) + 1 ≤ (2 : ℚ) ^ prec double := by exact_mod_cast (show k + 1 ≤ 2 ^ prec double by omega)
      nlinarith [scale_pos e]
    have logUpper := log_lt apos upper
    have notOver : ¬ (hi double : ℤ) - 2048 < Int.log 2 a - (prec double : ℤ) + 1 := by omega
    have eIs : max (Int.log 2 a - (prec double : ℤ) + 1) ((lo double : ℤ) - 2048) = (e : ℤ) - 2048 := by
      rcases edge with edge | edge
      · have lower : (2 : ℚ) ^ (((prec double - 1 : ℕ) : ℤ) + ((e : ℤ) - 2048)) ≤ a := by
          rw [← two_pow_scale]
          exact (quot_ge_iff q _).mp (by have := two_pow_pred_nat pPos; omega)
        have := log_ge apos lower
        push_cast [Nat.cast_sub pPos] at this
        omega
      · subst edge; omega
    simp only [notOver, ↓reduceIte, eIs]
    generalize hc : Int.floor (a / (2 : ℚ) ^ ((e : ℤ) - 2048)) + 1 = c
    rw [round_quot q hc]
    have mLe : roundUp k rem den ≤ 2 ^ prec double := by have := roundUp_le k rem den; omega
    have spos := scale_pos e
    unfold roundSettled
    rw [if_neg (by omega)]
    by_cases zero : roundUp k rem den = 0
    · have nz : (roundUp k rem den : ℚ) * scale e = 0 := by rw [zero]; simp
      rw [if_pos zero, if_pos nz]
    · have nz : ¬ (roundUp k rem den : ℚ) * scale e = 0 := by
        intro h; rcases mul_eq_zero.mp h with h | h
        · exact zero (by exact_mod_cast h)
        · exact spos.ne' h
      rw [if_neg zero, if_neg nz]
      have bound : (2 : ℚ) ^ prec double * (2 : ℚ) ^ ((hi double : ℤ) - 2048) =
          (2 : ℚ) ^ prec double * scale (hi double) := rfl
      rw [bound]
      have scaleMono : scale e ≤ scale (hi double) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      by_cases top : roundUp k rem den = 2 ^ prec double ∧ e = hi double
      · have notBelow : ¬ (roundUp k rem den : ℚ) * scale e < (2 : ℚ) ^ prec double * scale (hi double) := by
          rw [top.1, top.2]; push_cast; exact lt_irrefl _
        rw [if_pos top, if_neg notBelow]
      · have below : (roundUp k rem den : ℚ) * scale e < (2 : ℚ) ^ prec double * scale (hi double) := by
          by_cases full : roundUp k rem den = 2 ^ prec double
          · have eLt : e < hi double := by
              by_contra ge; exact top ⟨full, by omega⟩
            have : scale e < scale (hi double) := zpow_lt_zpow_right₀ (by norm_num) (by omega)
            rw [full]; push_cast
            exact mul_lt_mul_of_pos_left this (by positivity)
          · have mLt : (roundUp k rem den : ℚ) < (2 : ℚ) ^ prec double := by
              exact_mod_cast (show roundUp k rem den < 2 ^ prec double by omega)
            calc (roundUp k rem den : ℚ) * scale e < (2 : ℚ) ^ prec double * scale e :=
                  mul_lt_mul_of_pos_right mLt spos
              _ ≤ (2 : ℚ) ^ prec double * scale (hi double) :=
                  mul_le_mul_of_nonneg_left scaleMono (by positivity)
        rw [if_neg top, if_pos below]
        cases negative <;> simp [apos, not_lt.mpr apos.le]

/-! ## Values of the formats -/

/-- `floatingPointRound` gives a value of the format. -/
theorem roundBinary_valid (double : Bool) (v : ℚ) : (roundBinary (fmt double) v).Valid (fmt double) := by
  have pPos := prec_pos double
  have loHi := lo_le_hi double
  unfold roundBinary
  rw [fmt_precision, fmt_least, fmt_most]
  by_cases over : (hi double : ℤ) - 2048 < Int.log 2 (abs v) - (prec double : ℤ) + 1
  · rw [if_pos over]; trivial
  · rw [if_neg over]
    dsimp only
    set e := max (Int.log 2 (abs v) - (prec double : ℤ) + 1) ((lo double : ℤ) - 2048) with he
    set c := Int.floor (abs v / (2 : ℚ) ^ e) + 1 with hc
    have epos : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _
    have cLow : 1 ≤ c := by
      have : (0 : ℚ) ≤ abs v / (2 : ℚ) ^ e := div_nonneg (abs_nonneg _) epos.le
      have := Int.floor_nonneg.mpr this
      omega
    have cHigh : c ≤ 2 ^ prec double := by
      have below : abs v < (2 : ℚ) ^ (e + prec double) := by
        have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (abs v)
        have mono : (2 : ℚ) ^ (Int.log 2 (abs v) + 1) ≤ (2 : ℚ) ^ (e + prec double) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        push_cast at this
        linarith
      have ratio : abs v / (2 : ℚ) ^ e < (2 : ℚ) ^ prec double := by
        rw [div_lt_iff₀ epos, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
        rwa [add_comm] at below
      have : Int.floor (abs v / (2 : ℚ) ^ e) < 2 ^ prec double := by
        rw [Int.floor_lt]; push_cast; exact ratio
      omega
    have eLe : e ≤ (hi double : ℤ) - 2048 := by
      rw [he]; apply max_le (by omega) (by omega)
    have eGe : (lo double : ℤ) - 2048 ≤ e := le_max_right _ _
    obtain ⟨c', nIs, c'Low, c'High⟩ : ∃ c' : ℤ, (if (c : ℚ) * (2 : ℚ) ^ e - (2 : ℚ) ^ (e - 1) < abs v
        then (c : ℚ) * (2 : ℚ) ^ e
        else if abs v < (c : ℚ) * (2 : ℚ) ^ e - (2 : ℚ) ^ (e - 1) then ((c : ℚ) - 1) * (2 : ℚ) ^ e
        else if c % 2 = 0 then (c : ℚ) * (2 : ℚ) ^ e else ((c : ℚ) - 1) * (2 : ℚ) ^ e) = (c' : ℚ) * (2 : ℚ) ^ e ∧
        0 ≤ c' ∧ c' ≤ 2 ^ prec double := by
      split_ifs
      · exact ⟨c, by ring, by omega, cHigh⟩
      · exact ⟨c - 1, by push_cast; ring, by omega, by omega⟩
      · exact ⟨c, by ring, by omega, cHigh⟩
      · exact ⟨c - 1, by push_cast; ring, by omega, by omega⟩
    rw [nIs]
    by_cases zero : (c' : ℚ) * (2 : ℚ) ^ e = 0
    · rw [if_pos zero]; trivial
    · rw [if_neg zero]
      by_cases below : (c' : ℚ) * (2 : ℚ) ^ e < (2 : ℚ) ^ prec double * (2 : ℚ) ^ ((hi double : ℤ) - 2048)
      · rw [if_pos below]
        have c'Pos : 1 ≤ c' := by
          by_contra h
          have : c' = 0 := by omega
          rw [this] at zero; simp at zero
        simp only [Binary.Valid, fmt_precision, fmt_least, fmt_most]
        by_cases full : c' = 2 ^ prec double
        · have eLt : e < (hi double : ℤ) - 2048 := by
            by_contra h
            have eEq : e = (hi double : ℤ) - 2048 := by omega
            rw [full, eEq] at below
            push_cast at below
            exact lt_irrefl _ below
          refine ⟨(if v < 0 then -1 else 1) * 2 ^ (prec double - 1), e + 1, ?_, ?_, ?_, by omega, by omega⟩
          · rw [full]
            have pow : (2 : ℚ) ^ prec double = 2 * 2 ^ (prec double - 1) := two_pow_pred pPos
            rw [zpow_add_one₀ (by norm_num)]
            split_ifs <;> push_cast <;> rw [pow] <;> ring
          · split_ifs <;> simp
          · have : (2 : ℤ) ^ (prec double - 1) < 2 ^ prec double := by
              exact_mod_cast Nat.pow_lt_pow_right (by norm_num) (by omega)
            split_ifs <;> simp [abs_of_pos (show (0 : ℤ) < 2 ^ (prec double - 1) by positivity)] <;>
              exact_mod_cast this
        · refine ⟨(if v < 0 then -1 else 1) * c', e, ?_, ?_, ?_, eGe, eLe⟩
          · split_ifs <;> push_cast <;> ring
          · split_ifs <;> simp <;> omega
          · split_ifs <;> simp [abs_of_pos (show (0 : ℤ) < c' by omega)] <;> omega
      · rw [if_neg below]; trivial

/-! ## The kernel's constants and powers -/

theorem bias_val : floats.BIAS.val = 2048 := by simp [floats.BIAS]
theorem order_bias_val : floats.ORDER_BIAS.val = 268435456 := by simp [floats.ORDER_BIAS]
theorem steps_val : floats.STEPS.val = 4096 := by simp [floats.STEPS]
theorem limit_val : floats.LIMIT.val = 1024 := by simp [floats.LIMIT]
theorem saturated_val : floats.SATURATED.val = 100000000 := by simp [floats.SATURATED]
theorem u128_max_val : (core.num.U128.MAX).val = 2 ^ 128 - 1 := by simp [core.num.U128.MAX, U128.rMax]

theorem precision_spec (double : Bool) : ∃ r, floats.precision double = .ok r ∧ r.val = prec double := by
  cases double <;> simp [floats.precision, prec]

theorem least_spec (double : Bool) : ∃ r, floats.least double = .ok r ∧ r.val = lo double := by
  unfold floats.least
  cases double
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := floats.BIAS) (y := 149#usize) (by simp [bias_val]))
    exact ⟨r, by simp [run], by simp [bias_val] at value; simp [lo]; omega⟩
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := floats.BIAS) (y := 1074#usize) (by simp [bias_val]))
    exact ⟨r, by simp [run], by simp [bias_val] at value; simp [lo]; omega⟩

theorem most_spec (double : Bool) : ∃ r, floats.most double = .ok r ∧ r.val = hi double := by
  unfold floats.most
  cases double
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := floats.BIAS) (y := 104#usize) (by simp [bias_val]; scalar_tac))
    exact ⟨r, by simp [run], by simp [bias_val] at value; simp [hi]; omega⟩
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := floats.BIAS) (y := 971#usize) (by simp [bias_val]; scalar_tac))
    exact ⟨r, by simp [run], by simp [bias_val] at value; simp [hi]; omega⟩

theorem native_two_spec (count : Usize) (small : count.val < 128) :
    ∃ r, floats.native_two count = .ok r ∧ r.val = 2 ^ count.val := by
  rw [floats.native_two]
  by_cases pos : 0 < count.val
  · obtain ⟨c1, c1Run, c1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have c1Is : c1.val = count.val - 1 := by simp at c1Val; omega
    obtain ⟨r1, r1Run, r1Val⟩ := native_two_spec c1 (by omega)
    have pow : 2 * 2 ^ (count.val - 1) = 2 ^ count.val := by rw [← pow_succ']; congr 1; omega
    have bound : 2 ^ count.val ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨r, run, value⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 2#u128) (y := r1)
      (by rw [r1Val, c1Is]; simp [UScalar.max, U128.max_eq]; omega))
    refine ⟨r, by simp [UScalar.lt_equiv, pos, c1Run, r1Run, run], ?_⟩
    rw [value, r1Val, c1Is]; simpa using pow
  · exact ⟨1#u128, by simp [UScalar.lt_equiv, pos], by simp; omega⟩
termination_by count.val
decreasing_by omega

theorem native_ten_spec (count : Usize) (small : count.val < 39) :
    ∃ r, floats.native_ten count = .ok r ∧ r.val = 10 ^ count.val := by
  rw [floats.native_ten]
  by_cases pos : 0 < count.val
  · obtain ⟨c1, c1Run, c1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have c1Is : c1.val = count.val - 1 := by simp at c1Val; omega
    obtain ⟨r1, r1Run, r1Val⟩ := native_ten_spec c1 (by omega)
    have pow : 10 * 10 ^ (count.val - 1) = 10 ^ count.val := by rw [← pow_succ']; congr 1; omega
    have bound : 10 ^ count.val ≤ 10 ^ 38 := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨r, run, value⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 10#u128) (y := r1)
      (by rw [r1Val, c1Is]; simp [UScalar.max, U128.max_eq]; omega))
    refine ⟨r, by simp [UScalar.lt_equiv, pos, c1Run, r1Run, run], ?_⟩
    rw [value, r1Val, c1Is]; simpa using pow
  · exact ⟨1#u128, by simp [UScalar.lt_equiv, pos], by simp; omega⟩
termination_by count.val
decreasing_by omega

theorem top_spec (double : Bool) : ∃ r, floats.top double = .ok r ∧ r.val = 2 ^ prec double := by
  obtain ⟨p, pRun, pVal⟩ := precision_spec double
  obtain ⟨r, run, value⟩ := native_two_spec p (by rw [pVal]; cases double <;> simp [prec])
  exact ⟨r, by simp [floats.top, pRun, run], by rw [value, pVal]⟩

theorem prec_le (double : Bool) : prec double ≤ 53 := by cases double <;> simp [prec]

/-! ## Kernel values -/

/-- The value of a kernel value of `xsd:double` or `xsd:float`. -/
noncomputable def binaryOf : datatypes.Binary → Binary
  | .Finite negative m s => if m.val = 0 then .zero negative
      else .finite ((if negative then -1 else 1) * (m.val : ℚ) * scale s.val)
  | .Infinite negative => .infinity negative
  | .NotANumber => .nan

/-- The kernel values that `binary_value` returns: a zero with the scale
    `BIAS`, and an odd significand otherwise. -/
def CanonicalBinary : datatypes.Binary → Prop
  | .Finite _ m s => (m.val = 0 ∧ s.val = 2048) ∨ m.val % 2 = 1
  | _ => True

theorem u64_eq_zero (x : U64) : x = 0#u64 ↔ x.val = 0 := by rw [UScalar.eq_equiv]; simp

theorem odd_form_spec (m : U64) (e fuel : Usize) (room : e.val + fuel.val ≤ Usize.max) :
    ∃ r, floats.odd_form m e fuel = .ok r ∧ (r.1.val : ℚ) * scale r.2.val = (m.val : ℚ) * scale e.val ∧
      (0 < m.val → m.val < 2 ^ fuel.val → r.1.val % 2 = 1) := by
  rw [floats.odd_form]
  by_cases pos : 0 < fuel.val
  · obtain ⟨b, bRun, bVal⟩ := WP.spec_imp_exists (UScalar.rem_spec m (y := 2#u64) (by simp))
    by_cases even : m.val % 2 = 0
    · obtain ⟨half, hRun, hVal⟩ := UScalar.div_spec m (y := 2#u64) (by simp)
      obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := e) (y := 1#usize) (by simp; omega))
      obtain ⟨f1, f1Run, f1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
      have e1Is : e1.val = e.val + 1 := by simpa using e1Val
      have f1Is : f1.val = fuel.val - 1 := by simp at f1Val; omega
      have halfIs : half.val = m.val / 2 := by simpa using hVal
      obtain ⟨r, run, value, odd⟩ := odd_form_spec half e1 f1 (by omega)
      have bZero : b = 0#u64 := by rw [u64_eq_zero]; simpa [bVal] using even
      refine ⟨r, by simp [UScalar.lt_equiv, pos, bRun, bZero, hRun, e1Run, f1Run, run], ?_, ?_⟩
      · rw [value, e1Is, halfIs, scale_succ]
        have : ((m.val / 2 : ℕ) : ℚ) * 2 = m.val := by
          have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero even); exact_mod_cast this
        rw [← this]; ring
      · intro mPos mLt
        apply odd (by rw [halfIs]; omega)
        rw [halfIs, f1Is]
        have : 2 ^ fuel.val = 2 * 2 ^ (fuel.val - 1) := by rw [← pow_succ']; congr 1; omega
        omega
    · have bNot : b ≠ 0#u64 := by rw [ne_eq, u64_eq_zero]; simpa [bVal] using even
      exact ⟨(m, e), by simp [UScalar.lt_equiv, pos, bRun, bNot], rfl, fun _ _ => by show m.val % 2 = 1; omega⟩
  · exact ⟨(m, e), by simp [UScalar.lt_equiv, pos], rfl, fun mPos mLt => by
      have : fuel.val = 0 := by omega
      rw [this] at mLt; omega⟩
termination_by fuel.val
decreasing_by omega

theorem finite_spec (negative : Bool) (m : U64) (e : Usize) (room : e.val + 64 ≤ Usize.max) :
    ∃ b, floats.finite negative m e = .ok b ∧ CanonicalBinary b ∧
      binaryOf b = if m.val = 0 then .zero negative
        else .finite ((if negative then -1 else 1) * (m.val : ℚ) * scale e.val) := by
  rw [floats.finite]
  by_cases zero : m.val = 0
  · have mZero : m = 0#u64 := by rw [u64_eq_zero]; exact zero
    exact ⟨.Finite negative 0#u64 floats.BIAS, by simp [mZero], .inl ⟨by simp, bias_val⟩,
      by simp [binaryOf, zero]⟩
  · have mNot : m ≠ 0#u64 := by rw [ne_eq, u64_eq_zero]; exact zero
    obtain ⟨⟨r1, r2⟩, run, value, odd⟩ := odd_form_spec m e 64#usize (by simpa using room)
    have mLt : m.val < 2 ^ 64 := by scalar_tac
    have rOdd := odd (by omega) (by simpa using mLt)
    refine ⟨.Finite negative r1 r2, by simp [mNot, run], .inr rOdd, ?_⟩
    have rNot : r1.val ≠ 0 := by simp at rOdd; omega
    simp only [binaryOf, rNot, zero, ↓reduceIte]
    rw [mul_assoc, value, ← mul_assoc]

/-! ## Rounding natively -/

theorem u128_eq_iff (x y : U128) : x = y ↔ x.val = y.val := by
  constructor
  · rintro rfl; rfl
  · intro h; exact UScalar.eq_of_val_eq h

theorem cast_small (x : U128) (small : x.val < 2 ^ 64) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]; simp; omega

/-- The end of `native_round`, from the rounded significand on. -/
theorem round_tail (double negative : Bool) (m : U128) (e : Usize) (mLe : m.val ≤ 2 ^ prec double)
    (eLe : e.val ≤ hi double) :
    ∃ r, (do
        let i2 ← floats.top double
        if m = i2 then do
            let i3 ← floats.most double
            if e < i3 then do
                let i4 ← i2 / 2#u128
                let i5 ← lift (UScalar.cast UScalarTy.U64 i4)
                let i6 ← e + 1#usize
                let b ← floats.finite negative i5 i6
                ok (some b)
              else ok (some (datatypes.Binary.Infinite negative))
          else do
            let i3 ← lift (UScalar.cast UScalarTy.U64 m)
            let b ← floats.finite negative i3 e
            ok (some b) : Result (Option datatypes.Binary)) = .ok r ∧
      ∀ b, r = some b → CanonicalBinary b ∧
        binaryOf b = (if m.val = 0 then .zero negative
          else if m.val = 2 ^ prec double ∧ e.val = hi double then .infinity negative
          else .finite ((if negative then -1 else 1) * (m.val : ℚ) * scale e.val)) := by
  obtain ⟨t, tRun, tVal⟩ := top_spec double
  have pLe := prec_le double
  have pPos := prec_pos double
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  have room : e.val + 1 + 64 ≤ Usize.max := by scalar_tac
  have pow53 : 2 ^ prec double ≤ 2 ^ 53 := Nat.pow_le_pow_right (by norm_num) pLe
  by_cases full : m.val = 2 ^ prec double
  · have same : m = t := by rw [u128_eq_iff, full, tVal]
    obtain ⟨mo, moRun, moVal⟩ := most_spec double
    by_cases below : e.val < hi double
    · have belowLt : e < mo := by rw [UScalar.lt_equiv, moVal]; exact below
      obtain ⟨h2, h2Run, h2Val⟩ := UScalar.div_spec t (y := 2#u128) (by simp)
      have h2Is : h2.val = 2 ^ (prec double - 1) := by
        rw [h2Val, tVal]; simp
        rw [two_pow_pred_nat pPos]; simp
      have h2Small : 2 ^ (prec double - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have castIs := cast_small h2 (by rw [h2Is]; exact h2Small)
      obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := e) (y := 1#usize) (by simp; omega))
      have e1Is : e1.val = e.val + 1 := by simpa using e1Val
      obtain ⟨b, bRun, bCanon, bValue⟩ := finite_spec negative (UScalar.cast .U64 h2) e1 (by omega)
      refine ⟨some b, by simp [tRun, same, moRun, belowLt, moVal, show ¬ hi double ≤ e.val by omega, h2Run, lift,
        e1Run, bRun], ?_⟩
      intro b' hb'
      cases hb'
      refine ⟨bCanon, ?_⟩
      rw [bValue, castIs, h2Is, e1Is]
      have mNot : m.val ≠ 0 := by rw [full]; positivity
      have hNot : 2 ^ (prec double - 1) ≠ 0 := by positivity
      have pNot : 2 ^ prec double ≠ 0 := by positivity
      simp only [hNot, pNot, full, true_and, show e.val ≠ hi double by omega, ↓reduceIte]
      rw [scale_succ]
      have : (2 : ℚ) ^ prec double = 2 * 2 ^ (prec double - 1) := two_pow_pred pPos
      push_cast
      rw [this]; congr 1; ring
    · have notBelow : ¬ e < mo := by rw [UScalar.lt_equiv, moVal]; exact below
      refine ⟨some (.Infinite negative), by simp [tRun, same, moRun, moVal, below], ?_⟩
      intro b' hb'
      cases hb'
      refine ⟨trivial, ?_⟩
      have mNot : m.val ≠ 0 := by rw [full]; positivity
      simp [binaryOf, mNot, full, show e.val = hi double by omega]
  · have differ : m ≠ t := by rw [ne_eq, u128_eq_iff, tVal]; exact full
    have castIs := cast_small m (by omega)
    obtain ⟨b, bRun, bCanon, bValue⟩ := finite_spec negative (UScalar.cast .U64 m) e (by omega)
    refine ⟨some b, by simp [tRun, differ, lift, bRun], ?_⟩
    intro b' hb'
    cases hb'
    refine ⟨bCanon, ?_⟩
    rw [bValue, castIs]
    simp [full]

theorem native_round_spec (double negative : Bool) (k rest den : U128) (e : Usize)
    (kLt : k.val < 2 ^ prec double) (eLe : e.val ≤ hi double) :
    ∃ r, floats.native_round k rest den e negative double = .ok r ∧
      ∀ b, r = some b → CanonicalBinary b ∧ binaryOf b = roundSettled double negative k.val rest.val den.val e.val := by
  rw [floats.native_round]
  obtain ⟨half, halfRun, halfVal⟩ := UScalar.div_spec core.num.U128.MAX (y := 2#u128) (by simp)
  have halfIs : half.val = (2 ^ 128 - 1) / 2 := by rw [halfVal, u128_max_val]; simp
  have pLe := prec_le double
  have pow53 : 2 ^ prec double ≤ 2 ^ 53 := Nat.pow_le_pow_right (by norm_num) pLe
  have settled : ∀ m : U128, m.val = roundUp k.val rest.val den.val →
      (if m.val = 0 then Binary.zero negative
        else if m.val = 2 ^ prec double ∧ e.val = hi double then .infinity negative
        else .finite ((if negative then -1 else 1) * (m.val : ℚ) * scale e.val)) =
      roundSettled double negative k.val rest.val den.val e.val := by
    intro m mIs
    simp only [roundSettled, show ¬ hi double < e.val by omega, ↓reduceIte, mIs]
  by_cases fits : rest.val ≤ half.val
  · have fitsLe : rest ≤ half := by rw [UScalar.le_equiv]; exact fits
    obtain ⟨twice, twiceRun, twiceVal⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 2#u128) (y := rest)
      (by simp [UScalar.max, U128.max_eq]; omega))
    have twiceIs : twice.val = 2 * rest.val := by simpa using twiceVal
    have keep : ∀ (rounded : U128), rounded.val = roundUp k.val rest.val den.val → ∀ r,
        (do
          let i2 ← floats.top double
          if rounded = i2 then do
              let i3 ← floats.most double
              if e < i3 then do
                  let i4 ← i2 / 2#u128
                  let i5 ← lift (UScalar.cast UScalarTy.U64 i4)
                  let i6 ← e + 1#usize
                  let b ← floats.finite negative i5 i6
                  ok (some b)
                else ok (some (datatypes.Binary.Infinite negative))
            else do
              let i3 ← lift (UScalar.cast UScalarTy.U64 rounded)
              let b ← floats.finite negative i3 e
              ok (some b) : Result (Option datatypes.Binary)) = .ok r →
        ∀ b, r = some b → CanonicalBinary b ∧
          binaryOf b = roundSettled double negative k.val rest.val den.val e.val := by
      intro rounded roundedIs r run b hb
      obtain ⟨r', run', prop⟩ := round_tail double negative rounded e
        (by rw [roundedIs]; have := roundUp_le k.val rest.val den.val; omega) eLe
      rw [run] at run'
      simp only [ok.injEq] at run'
      subst run'
      obtain ⟨canon, value⟩ := prop b hb
      exact ⟨canon, by rw [value, settled rounded roundedIs]⟩
    have tailOk : ∀ (rounded : U128), rounded.val ≤ 2 ^ prec double → ∃ r,
        (do
          let i2 ← floats.top double
          if rounded = i2 then do
              let i3 ← floats.most double
              if e < i3 then do
                  let i4 ← i2 / 2#u128
                  let i5 ← lift (UScalar.cast UScalarTy.U64 i4)
                  let i6 ← e + 1#usize
                  let b ← floats.finite negative i5 i6
                  ok (some b)
                else ok (some (datatypes.Binary.Infinite negative))
            else do
              let i3 ← lift (UScalar.cast UScalarTy.U64 rounded)
              let b ← floats.finite negative i3 e
              ok (some b) : Result (Option datatypes.Binary)) = .ok r := by
      intro rounded le
      obtain ⟨r, run, _⟩ := round_tail double negative rounded e le eLe
      exact ⟨r, run⟩
    by_cases low : 2 * rest.val < den.val
    · have c1 : twice < den := by rw [UScalar.lt_equiv, twiceIs]; exact low
      have kIs : k.val = roundUp k.val rest.val den.val := by simp [roundUp, low]
      obtain ⟨r, run⟩ := tailOk k (by omega)
      refine ⟨r, ?_, keep k kIs r run⟩
      simp only [halfRun, bind_ok, fitsLe, ↓reduceIte, twiceRun, c1, Bool.false_eq_true]
      exact run
    · have c1 : ¬ twice < den := by rw [UScalar.lt_equiv, twiceIs]; exact low
      obtain ⟨k1, k1Run, k1Val⟩ := WP.spec_imp_exists (UScalar.add_spec (x := k) (y := 1#u128)
        (by simp [UScalar.max, U128.max_eq]; omega))
      have k1Is : k1.val = k.val + 1 := by simpa using k1Val
      by_cases high : den.val < 2 * rest.val
      · have c2 : den < twice := by rw [UScalar.lt_equiv, twiceIs]; exact high
        have upIs : k1.val = roundUp k.val rest.val den.val := by simp [roundUp, low, high, k1Is]
        obtain ⟨r, run⟩ := tailOk k1 (by omega)
        refine ⟨r, ?_, keep k1 upIs r run⟩
        simp only [halfRun, bind_ok, fitsLe, ↓reduceIte, twiceRun, c1, c2, k1Run]
        exact run
      · have c2 : ¬ den < twice := by rw [UScalar.lt_equiv, twiceIs]; exact high
        obtain ⟨parity, pRun, pVal⟩ := WP.spec_imp_exists (UScalar.rem_spec k (y := 2#u128) (by simp))
        have pIs : parity.val = k.val % 2 := by simpa using pVal
        by_cases odd : k.val % 2 = 1
        · have oddB : (parity != 0#u128) = true := by
            rw [bne_iff_ne, ne_eq, u128_eq_iff]; simp [pIs, odd]
          have upIs : k1.val = roundUp k.val rest.val den.val := by simp [roundUp, low, high, odd, k1Is]
          obtain ⟨r, run⟩ := tailOk k1 (by omega)
          refine ⟨r, ?_, keep k1 upIs r run⟩
          simp only [halfRun, bind_ok, fitsLe, ↓reduceIte, twiceRun, c1, c2, pRun, oddB, k1Run]
          exact run
        · have evenB : (parity != 0#u128) = false := by
            rw [bne_eq_false_iff_eq, u128_eq_iff]; simp [pIs]; omega
          have kIs : k.val = roundUp k.val rest.val den.val := by simp [roundUp, low, high, odd]
          obtain ⟨r, run⟩ := tailOk k (by omega)
          refine ⟨r, ?_, keep k kIs r run⟩
          simp only [halfRun, bind_ok, fitsLe, ↓reduceIte, twiceRun, c1, c2, pRun, evenB, Bool.false_eq_true]
          exact run
  · have notFits : ¬ rest ≤ half := by rw [UScalar.le_equiv]; exact fits
    exact ⟨none, by simp [halfRun, fits], fun b hb => by cases hb⟩

theorem u128_half_val : (170141183460469231731687303715884105727 : ℕ) = (2 ^ 128 - 1) / 2 := by norm_num

/-- `native_settle` is the search for the exponent, where it does not run out
    of room. -/
theorem native_settle_spec (double : Bool) (fuel : Usize) (k rest den : U128) (e : Usize)
    (rlt : rest.val < den.val) (eLe : e.val ≤ hi double) :
    ∃ r, floats.native_settle k rest den e double fuel = .ok r ∧
      ∀ k' rest' den' e', r = some (k', rest', den', e') →
        settleMath (prec double) (lo double) (hi double) fuel.val k.val rest.val den.val e.val =
          some (k'.val, rest'.val, den'.val, e'.val) := by
  rw [floats.native_settle]
  have pLe := prec_le double
  have pPos := prec_pos double
  have pow53 : 2 ^ prec double ≤ 2 ^ 53 := Nat.pow_le_pow_right (by norm_num) pLe
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  have loHi := lo_le_hi double
  by_cases fuelPos : 0 < fuel.val
  · obtain ⟨n, hn⟩ : ∃ n, fuel.val = n + 1 := ⟨fuel.val - 1, by omega⟩
    obtain ⟨t, tRun, tVal⟩ := top_spec double
    obtain ⟨f1, f1Run, f1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
    have f1Is : f1.val = n := by simp at f1Val; omega
    obtain ⟨hm, hmRun, hmVal⟩ := UScalar.div_spec core.num.U128.MAX (y := 2#u128) (by simp)
    have hmIs : hm.val = (2 ^ 128 - 1) / 2 := by rw [hmVal, u128_max_val]; simp
    by_cases big : 2 ^ prec double ≤ k.val
    · have bigT : t.val ≤ k.val := by rw [tVal]; exact big
      obtain ⟨mo, moRun, moVal⟩ := most_spec double
      by_cases below : e.val < hi double
      · have belowM : e.val < mo.val := by rw [moVal]; exact below
        by_cases fits : den.val ≤ hm.val
        · obtain ⟨k2, k2Run, k2Val⟩ := UScalar.div_spec k (y := 2#u128) (by simp)
          obtain ⟨b, bRun, bVal⟩ := WP.spec_imp_exists (UScalar.rem_spec k (y := 2#u128) (by simp))
          have k2Is : k2.val = k.val / 2 := by simpa using k2Val
          have bIs : b.val = k.val % 2 := by simpa using bVal
          have kmod : k.val % 2 ≤ 1 := by omega
          have bdBound : k.val % 2 * den.val ≤ den.val := by nlinarith
          obtain ⟨bd, bdRun, bdVal⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := b) (y := den)
            (by rw [bIs]; simp [UScalar.max, U128.max_eq]; omega))
          have bdIs : bd.val = k.val % 2 * den.val := by rw [bdVal, bIs]
          have bdLe : bd.val ≤ den.val := by rw [bdIs]; exact bdBound
          obtain ⟨r1, r1Run, r1Val⟩ := WP.spec_imp_exists (UScalar.add_spec (x := bd) (y := rest)
            (by simp [UScalar.max, U128.max_eq]; omega))
          have r1Is : r1.val = k.val % 2 * den.val + rest.val := by rw [r1Val, bdIs]
          obtain ⟨d2, d2Run, d2Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 2#u128) (y := den)
            (by simp [UScalar.max, U128.max_eq]; omega))
          have d2Is : d2.val = 2 * den.val := by simpa using d2Val
          obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := e) (y := 1#usize)
            (by simp; scalar_tac))
          have e1Is : e1.val = e.val + 1 := by simpa using e1Val
          obtain ⟨r, run, prop⟩ := native_settle_spec double f1 k2 r1 d2 e1 (by omega) (by omega)
          refine ⟨r, by simp [fuelPos, tRun, bigT, moRun, belowM, hmRun, fits, k2Run, bRun, bdRun, r1Run,
            d2Run, e1Run, f1Run, run], ?_⟩
          intro k' rest' den' e' hr
          rw [hn]
          simp only [settleMath, big, below, ↓reduceIte]
          rw [← prop k' rest' den' e' hr, f1Is, k2Is, r1Is, d2Is, e1Is]
        · exact ⟨none, by simp [fuelPos, tRun, bigT, moRun, belowM, hmRun, fits], fun _ _ _ _ h => by cases h⟩
      · have belowM : ¬ e.val < mo.val := by rw [moVal]; exact below
        obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := e) (y := 1#usize)
          (by simp; scalar_tac))
        have e1Is : e1.val = e.val + 1 := by simpa using e1Val
        refine ⟨some (k, rest, den, e1), by simp [fuelPos, tRun, bigT, moRun, belowM, e1Run], ?_⟩
        intro k' rest' den' e' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
        rw [hn]
        simp only [settleMath, big, below, ↓reduceIte, e1Is]
    · have bigT : ¬ t.val ≤ k.val := by rw [tVal]; exact big
      obtain ⟨le, leRun, leVal⟩ := least_spec double
      by_cases above : lo double < e.val
      · have aboveL : le.val < e.val := by rw [leVal]; exact above
        obtain ⟨k2, k2Run, k2Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 2#u128) (y := k)
          (by simp [UScalar.max, U128.max_eq]; omega))
        have k2Is : k2.val = 2 * k.val := by simpa using k2Val
        by_cases halfSmall : 2 * k.val < 2 ^ prec double
        · have halfT : k2.val < t.val := by rw [k2Is, tVal]; exact halfSmall
          by_cases rfits : rest.val ≤ hm.val
          · obtain ⟨r2, r2Run, r2Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 2#u128) (y := rest)
              (by simp [UScalar.max, U128.max_eq]; omega))
            have r2Is : r2.val = 2 * rest.val := by simpa using r2Val
            obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := e) (y := 1#usize)
              (by simp; omega))
            have e1Is : e1.val = e.val - 1 := by simp at e1Val; omega
            have downStep : settleMath (prec double) (lo double) (hi double) fuel.val k.val rest.val den.val e.val =
                if 2 * rest.val < den.val then
                  settleMath (prec double) (lo double) (hi double) n (2 * k.val) (2 * rest.val) den.val (e.val - 1)
                else settleMath (prec double) (lo double) (hi double) n (2 * k.val + 1) (2 * rest.val - den.val)
                  den.val (e.val - 1) := by
              rw [hn]; simp only [settleMath, big, above, halfSmall, and_self, ↓reduceIte]
            by_cases low : 2 * rest.val < den.val
            · have lowD : r2.val < den.val := by rw [r2Is]; exact low
              obtain ⟨r, run, prop⟩ := native_settle_spec double f1 k2 r2 den e1 (by omega) (by omega)
              refine ⟨r, by simp [fuelPos, tRun, bigT, leRun, aboveL, k2Run, halfT, hmRun, rfits, r2Run, lowD,
                e1Run, f1Run, run], ?_⟩
              intro k' rest' den' e' hr
              rw [downStep, if_pos low, ← prop k' rest' den' e' hr, f1Is, k2Is, r2Is, e1Is]
            · have lowD : ¬ r2.val < den.val := by rw [r2Is]; exact low
              obtain ⟨k3, k3Run, k3Val⟩ := WP.spec_imp_exists (UScalar.add_spec (x := k2) (y := 1#u128)
                (by simp [UScalar.max, U128.max_eq]; omega))
              have k3Is : k3.val = 2 * k.val + 1 := by simp at k3Val; omega
              obtain ⟨r3, r3Run, r3Val⟩ := WP.spec_imp_exists (UScalar.sub_spec (x := r2) (y := den)
                (by omega))
              have r3Is : r3.val = 2 * rest.val - den.val := by rw [r3Val.1, r2Is]
              obtain ⟨r, run, prop⟩ := native_settle_spec double f1 k3 r3 den e1 (by omega) (by omega)
              refine ⟨r, by simp [fuelPos, tRun, bigT, leRun, aboveL, k2Run, halfT, hmRun, rfits, r2Run, lowD,
                k3Run, r3Run, e1Run, f1Run, run], ?_⟩
              intro k' rest' den' e' hr
              rw [downStep, if_neg low, ← prop k' rest' den' e' hr, f1Is, k3Is, r3Is, e1Is]
          · exact ⟨none, by simp [fuelPos, tRun, bigT, leRun, aboveL, k2Run, halfT, hmRun, rfits],
              fun _ _ _ _ h => by cases h⟩
        · have halfT : ¬ k2.val < t.val := by rw [k2Is, tVal]; exact halfSmall
          refine ⟨some (k, rest, den, e), by simp [fuelPos, tRun, bigT, leRun, aboveL, k2Run, halfT], ?_⟩
          intro k' rest' den' e' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
          rw [hn]
          simp only [settleMath, big, halfSmall, and_false, ↓reduceIte]
      · have aboveL : ¬ le.val < e.val := by rw [leVal]; exact above
        refine ⟨some (k, rest, den, e), by simp [fuelPos, tRun, bigT, leRun, aboveL], ?_⟩
        intro k' rest' den' e' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
        rw [hn]
        simp only [settleMath, big, above, false_and, ↓reduceIte]
  · exact ⟨none, by simp [fuelPos], fun _ _ _ _ h => by cases h⟩
termination_by fuel.val
decreasing_by all_goals omega

/-! ## The first quotient, natively -/

theorem quot_scaled_up {num den0 j : ℕ} (dpos : 0 < den0) :
    Quot ((num : ℚ) / den0) (num / (den0 * 2 ^ j)) (num % (den0 * 2 ^ j)) (den0 * 2 ^ j) (2048 + j) := by
  have D : 0 < den0 * 2 ^ j := by positivity
  refine ⟨D, Nat.mod_lt _ D, ?_⟩
  have h := Nat.div_add_mod num (den0 * 2 ^ j)
  have sc : scale (2048 + j) = (2 : ℚ) ^ j := by
    unfold scale; rw [show ((2048 + j : ℕ) : ℤ) - 2048 = (j : ℤ) by push_cast; ring, zpow_natCast]
  rw [sc]
  have hq : (num : ℚ) = ((den0 : ℚ) * 2 ^ j) * ((num / (den0 * 2 ^ j) : ℕ) : ℚ) +
      ((num % (den0 * 2 ^ j) : ℕ) : ℚ) := by exact_mod_cast h.symm
  have dq : (den0 : ℚ) ≠ 0 := by exact_mod_cast dpos.ne'
  have pq : (2 : ℚ) ^ j ≠ 0 := by positivity
  rw [hq]
  push_cast
  field_simp

theorem quot_scaled_down {num den0 j : ℕ} (dpos : 0 < den0) (hj : j ≤ 2048) :
    Quot ((num : ℚ) / den0) (num * 2 ^ j / den0) (num * 2 ^ j % den0) den0 (2048 - j) := by
  refine ⟨dpos, Nat.mod_lt _ dpos, ?_⟩
  have h := Nat.div_add_mod (num * 2 ^ j) den0
  have sc : scale (2048 - j) = ((2 : ℚ) ^ j)⁻¹ := by
    unfold scale; rw [show ((2048 - j : ℕ) : ℤ) - 2048 = -(j : ℤ) by rw [Nat.cast_sub hj]; ring, zpow_neg,
      zpow_natCast]
  rw [sc]
  have hq : (num : ℚ) * 2 ^ j = (den0 : ℚ) * ((num * 2 ^ j / den0 : ℕ) : ℚ) + ((num * 2 ^ j % den0 : ℕ) : ℚ) := by
    exact_mod_cast h.symm
  have dq : (den0 : ℚ) ≠ 0 := by exact_mod_cast dpos.ne'
  have pq : (2 : ℚ) ^ j ≠ 0 := by positivity
  have : (num : ℚ) = ((den0 : ℚ) * ((num * 2 ^ j / den0 : ℕ) : ℚ) + ((num * 2 ^ j % den0 : ℕ) : ℚ)) / 2 ^ j := by
    rw [← hq]; field_simp
  rw [this]
  field_simp

/-- The end of `native_state`, from the numerator and the denominator on. -/
theorem state_tail (num den0 : U128) (e : Usize) (dpos : 0 < den0.val) :
    ∃ r, (if floats.BIAS <= e
      then
        do
        let i ← e - floats.BIAS
        if i < 127#usize
        then
          do
          let power ← floats.native_two i
          let i1 ← core.num.U128.MAX / 2#u128
          let i2 ← i1 / power
          if den0 <= i2
          then
            do
            let scaled ← den0 * power
            let i3 ← num / scaled
            let i4 ← num % scaled
            ok (some (i3, i4, scaled))
          else ok none
        else ok none
      else
        do
        let i ← floats.BIAS - e
        if i < 127#usize
        then
          do
          let power ← floats.native_two i
          let i1 ← core.num.U128.MAX / power
          if num <= i1
          then
            do
            let scaled ← num * power
            let i2 ← scaled / den0
            let i3 ← scaled % den0
            ok (some (i2, i3, den0))
          else ok none
        else ok none : Result (Option (U128 × U128 × U128))) = .ok r ∧
      ∀ k rest den, r = some (k, rest, den) → Quot ((num.val : ℚ) / den0.val) k.val rest.val den.val e.val := by
  by_cases up : 2048 ≤ e.val
  · have upB : floats.BIAS ≤ e := by rw [UScalar.le_equiv, bias_val]; exact up
    obtain ⟨j, jRun, jVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := e) (y := floats.BIAS) (by rw [bias_val]; exact up))
    have jIs : j.val = e.val - 2048 := by rw [jVal.1, bias_val]
    by_cases small : j.val < 127
    · have smallB : j < 127#usize := by rw [UScalar.lt_equiv]; simpa using small
      obtain ⟨power, pRun, pVal⟩ := native_two_spec j (by omega)
      obtain ⟨hm, hmRun, hmVal⟩ := UScalar.div_spec core.num.U128.MAX (y := 2#u128) (by simp)
      have ppos : power.val ≠ 0 := by rw [pVal]; positivity
      obtain ⟨lim, limRun, limVal⟩ := UScalar.div_spec hm (y := power) ppos
      by_cases fits : den0.val ≤ lim.val
      · have fitsB : den0 ≤ lim := by rw [UScalar.le_equiv]; exact fits
        have hmIs : hm.val = (2 ^ 128 - 1) / 2 := by rw [hmVal, u128_max_val]; simp
        have prod : den0.val * power.val ≤ hm.val := by
          have := Nat.mul_le_mul_right power.val fits
          rw [limVal] at this
          exact le_trans this (Nat.div_mul_le_self _ _)
        obtain ⟨sc, scRun, scVal⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := den0) (y := power)
          (by simp [UScalar.max, U128.max_eq]; omega))
        have scPos : sc.val ≠ 0 := by rw [scVal]; exact Nat.mul_ne_zero (by omega) ppos
        obtain ⟨q, qRun, qVal⟩ := UScalar.div_spec num (y := sc) scPos
        obtain ⟨m, mRun, mVal⟩ := WP.spec_imp_exists (UScalar.rem_spec num (y := sc) scPos)
        refine ⟨some (q, m, sc), by simp only [upB, ↓reduceIte, jRun, bind_ok, smallB, pRun, hmRun, limRun, fitsB,
          scRun, qRun, mRun], ?_⟩
        intro k rest den h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have eIs : e.val = 2048 + j.val := by omega
        rw [qVal, mVal, scVal, pVal, eIs]
        exact quot_scaled_up dpos
      · have fitsB : ¬ den0 ≤ lim := by rw [UScalar.le_equiv]; exact fits
        exact ⟨none, by simp only [upB, ↓reduceIte, jRun, bind_ok, smallB, pRun, hmRun, limRun, fitsB],
          fun _ _ _ h => by cases h⟩
    · have smallB : ¬ j < 127#usize := by rw [UScalar.lt_equiv]; simpa using small
      exact ⟨none, by simp only [upB, ↓reduceIte, jRun, bind_ok, smallB], fun _ _ _ h => by cases h⟩
  · have upB : ¬ floats.BIAS ≤ e := by rw [UScalar.le_equiv, bias_val]; exact up
    obtain ⟨j, jRun, jVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := floats.BIAS) (y := e)
      (by rw [bias_val]; omega))
    have jIs : j.val = 2048 - e.val := by rw [jVal.1, bias_val]
    by_cases small : j.val < 127
    · have smallB : j < 127#usize := by rw [UScalar.lt_equiv]; simpa using small
      obtain ⟨power, pRun, pVal⟩ := native_two_spec j (by omega)
      have ppos : power.val ≠ 0 := by rw [pVal]; positivity
      obtain ⟨lim, limRun, limVal⟩ := UScalar.div_spec core.num.U128.MAX (y := power) ppos
      by_cases fits : num.val ≤ lim.val
      · have fitsB : num ≤ lim := by rw [UScalar.le_equiv]; exact fits
        have prod : num.val * power.val ≤ 2 ^ 128 - 1 := by
          have := Nat.mul_le_mul_right power.val fits
          rw [limVal, u128_max_val] at this
          exact le_trans this (Nat.div_mul_le_self _ _)
        obtain ⟨sc, scRun, scVal⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := num) (y := power)
          (by simp [UScalar.max, U128.max_eq]; omega))
        have dne : den0.val ≠ 0 := by omega
        obtain ⟨q, qRun, qVal⟩ := UScalar.div_spec sc (y := den0) dne
        obtain ⟨m, mRun, mVal⟩ := WP.spec_imp_exists (UScalar.rem_spec sc (y := den0) dne)
        refine ⟨some (q, m, den0), by simp only [upB, ↓reduceIte, jRun, bind_ok, smallB, pRun, limRun, fitsB,
          scRun, qRun, mRun], ?_⟩
        intro k rest den h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have eIs : e.val = 2048 - j.val := by omega
        rw [qVal, mVal, scVal, pVal, eIs]
        exact quot_scaled_down dpos (by omega)
      · have fitsB : ¬ num ≤ lim := by rw [UScalar.le_equiv]; exact fits
        exact ⟨none, by simp only [upB, ↓reduceIte, jRun, bind_ok, smallB, pRun, limRun, fitsB],
          fun _ _ _ h => by cases h⟩
    · have smallB : ¬ j < 127#usize := by rw [UScalar.lt_equiv]; simpa using small
      exact ⟨none, by simp only [upB, ↓reduceIte, jRun, bind_ok, smallB], fun _ _ _ h => by cases h⟩

/-- `native_state` is the first quotient of `d × 10^scale` (`up`) or
    `d / 10^scale` at the exponent, where it fits. -/
theorem native_state_spec (d : U128) (up : Bool) (sc e : Usize) (scSmall : sc.val < 39)
    (fits : up = true → d.val * 10 ^ sc.val ≤ 2 ^ 128 - 1) :
    ∃ r, floats.native_state d up sc e = .ok r ∧
      ∀ k rest den, r = some (k, rest, den) →
        Quot (if up then (d.val : ℚ) * 10 ^ sc.val else (d.val : ℚ) / 10 ^ sc.val) k.val rest.val den.val e.val := by
  rw [floats.native_state]
  obtain ⟨ten, tenRun, tenVal⟩ := native_ten_spec sc scSmall
  cases up
  · obtain ⟨r, run, prop⟩ := state_tail d ten e (by rw [tenVal]; positivity)
    refine ⟨r, by simp only [tenRun, bind_ok, Bool.false_eq_true, ↓reduceIte]; exact run, ?_⟩
    intro k rest den h
    have := prop k rest den h
    simpa [tenVal] using this
  · obtain ⟨prod, prodRun, prodVal⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := d) (y := ten)
      (by rw [tenVal]; have := fits rfl; simp [UScalar.max, U128.max_eq]; omega))
    obtain ⟨r, run, prop⟩ := state_tail prod 1#u128 e (by simp)
    refine ⟨r, by simp only [tenRun, bind_ok, prodRun, ↓reduceIte]; exact run, ?_⟩
    intro k rest den h
    have := prop k rest den h
    simpa [prodVal, tenVal] using this

/-- A quotient that the search settles rounds as `floatingPointRound` does,
    from either of the kernel's roundings. -/
theorem settled_round_value {a : ℚ} (apos : 0 < a) (double negative : Bool) {k rem den e : ℕ}
    (h : Settled a (prec double) (lo double) (hi double) k rem den e) :
    roundSettled double negative k rem den e = roundBinary (fmt double) (if negative then -a else a) :=
  settle_round apos double negative h

/-- `native` is the value of `d × 10^scale` (`up`) or `d / 10^scale`, with the
    sign, where its numbers fit. -/
theorem native_spec (d : U128) (up : Bool) (sc e : Usize) (negative double : Bool)
    (scSmall : sc.val < 39) (fits : up = true → d.val * 10 ^ sc.val ≤ 2 ^ 128 - 1)
    (dpos : 0 < d.val) (eLo : lo double ≤ e.val) (eHi : e.val ≤ hi double) :
    ∃ r, floats.native d up sc e negative double = .ok r ∧
      ∀ b, r = some b → CanonicalBinary b ∧
        binaryOf b = roundBinary (fmt double)
          (if negative then -(if up then (d.val : ℚ) * 10 ^ sc.val else (d.val : ℚ) / 10 ^ sc.val)
           else (if up then (d.val : ℚ) * 10 ^ sc.val else (d.val : ℚ) / 10 ^ sc.val)) := by
  rw [floats.native]
  have apos : 0 < (if up then (d.val : ℚ) * 10 ^ sc.val else (d.val : ℚ) / 10 ^ sc.val) := by
    have : (0 : ℚ) < d.val := by exact_mod_cast dpos
    split <;> positivity
  obtain ⟨r0, run0, prop0⟩ := native_state_spec d up sc e scSmall fits
  rcases r0 with _ | ⟨k, rest, den⟩
  · exact ⟨none, by simp only [run0, bind_ok], fun b h => by cases h⟩
  · have q := prop0 k rest den rfl
    obtain ⟨r1, run1, prop1⟩ := native_settle_spec double floats.STEPS k rest den e q.2.1 eHi
    rcases r1 with _ | ⟨k1, rest1, den1, e1⟩
    · exact ⟨none, by simp [run0, run1], fun b h => by cases h⟩
    · have settled := settle_sound _ _ _ _ _ q eLo eHi _ _ _ _ (prop1 k1 rest1 den1 e1 rfl)
      obtain ⟨mo, moRun, moVal⟩ := most_spec double
      by_cases over : hi double < e1.val
      · have overB : mo < e1 := by rw [UScalar.lt_equiv, moVal]; exact over
        refine ⟨some (.Infinite negative), by simp [run0, run1, moRun, moVal, over], ?_⟩
        intro b h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨trivial, ?_⟩
        rw [← settled_round_value apos double negative settled]
        simp [roundSettled, over, binaryOf]
      · have overB : ¬ mo < e1 := by rw [UScalar.lt_equiv, moVal]; exact over
        have inner : lo double ≤ e1.val ∧ e1.val ≤ hi double ∧ k1.val < 2 ^ prec double := by
          rcases settled with ⟨eq, _, _⟩ | ⟨l, h, _, small, _⟩
          · omega
          · exact ⟨l, h, small⟩
        obtain ⟨r, run, prop⟩ := native_round_spec double negative k1 rest1 den1 e1 inner.2.2 inner.2.1
        refine ⟨r, by simp [run0, run1, moRun, moVal, over, run], ?_⟩
        intro b h
        obtain ⟨canon, value⟩ := prop b h
        exact ⟨canon, by rw [value, settled_round_value apos double negative settled]⟩

/-! ## Numbers on decimal digits -/

theorem new_val : (alloc.vec.Vec.new U8).val = [] := rfl

theorem digits_of_spec (value : U128) :
    ∃ v, floats.digits_of value = .ok v ∧ Canonical v.val ∧ digitsValue v.val = value.val ∧
      ∀ j, value.val < 10 ^ j → v.val.length ≤ j := by
  rw [floats.digits_of]
  by_cases zero : value.val = 0
  · have z : value = 0#u128 := by rw [u128_eq_iff]; simpa using zero
    exact ⟨alloc.vec.Vec.new U8, by simp [z], canonical_nil, by simp [new_val, zero, value_nil],
      fun j _ => by simp [new_val]⟩
  · have nz : value ≠ 0#u128 := by rw [ne_eq, u128_eq_iff]; simpa using zero
    obtain ⟨q, qRun, qVal⟩ := UScalar.div_spec value (y := 10#u128) (by simp)
    have qIs : q.val = value.val / 10 := by simpa using qVal
    obtain ⟨out, outRun, outC, outV, outL⟩ := digits_of_spec q
    obtain ⟨r, rRun, rVal⟩ := WP.spec_imp_exists (UScalar.rem_spec value (y := 10#u128) (by simp))
    have rIs : r.val = value.val % 10 := by simpa using rVal
    have castIs : (UScalar.cast .U8 r).val = value.val % 10 := by
      rw [UScalar.cast_val_eq, rIs]; simp; omega
    obtain ⟨dig, digRun, digVal⟩ := WP.spec_imp_exists (UScalar.add_spec (x := 48#u8) (y := UScalar.cast .U8 r)
      (by have c := castIs; have : value.val % 10 < 10 := Nat.mod_lt _ (by norm_num); scalar_tac))
    have digIs : dig.val = 48 + value.val % 10 := by rw [digVal, castIs]; simp
    have qSmall : q.val < 10 ^ 39 := by
      have : value.val < 2 ^ 128 := by scalar_tac
      rw [qIs]; omega
    have outShort : out.val.length < Usize.max := by
      have := outL 39 qSmall
      scalar_tac
    obtain ⟨v, vRun, vVal⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out dig outShort)
    have digDigit : Digit dig := ⟨by omega, by omega⟩
    refine ⟨v, by simp [nz, qRun, outRun, rRun, lift, digRun, vRun], ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [vVal]
      intro b member
      rcases List.mem_append.mp member with early | late
      · exact outC.1 b early
      · simp at late; rw [late]; exact digDigit
    · rw [vVal]
      by_cases empty : out.val = []
      · have : q.val = 0 := by rw [← outV, empty, value_nil]
        rw [empty]
        simp only [List.nil_append, List.head?_cons, ne_eq, Option.some.injEq]
        intro same
        rw [same] at digIs
        simp at digIs
        omega
      · rw [List.head?_append_of_ne_nil _ empty]
        exact outC.2
    · rw [vVal, value_snoc, outV, qIs, digIs]; omega
    · intro j hj
      rw [vVal]
      simp only [List.length_append, List.length_singleton]
      cases j with
      | zero => simp at hj; omega
      | succ j =>
        have := outL j (by rw [qIs]; rw [pow_succ] at hj; omega)
        omega
termination_by value.val
decreasing_by omega

theorem one_spec : ∃ v, floats.one = .ok v ∧ v.val = [49#u8] := by
  obtain ⟨v, run, value⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 49#u8 (by simp [new_val]; scalar_tac))
  exact ⟨v, by simp [floats.one, run], by rw [value, new_val]; rfl⟩

theorem one_canonical : Canonical [49#u8] := Rowl.Moments.one_canonical

theorem one_value : digitsValue [49#u8] = 1 := by simp [digitsValue]

/-- A bound on the lengths of the digits that the wide arithmetic handles. -/
def W : ℕ := 1048576

theorem w_room : 2 * W + 8 < Usize.max := by unfold W; scalar_tac

theorem two_canonical : Canonical [50#u8] := by
  refine ⟨fun b m => ?_, by simp⟩
  simp at m; subst m; exact ⟨by simp, by simp⟩

theorem two_value : digitsValue [50#u8] = 2 := by simp [digitsValue]

theorem doubled_spec (d : alloc.vec.Vec U8) (cd : Canonical d.val) (count : Usize)
    (room : 2 * (d.val.length + count.val) + 2 < Usize.max) :
    ∃ v, floats.doubled d count = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = digitsValue d.val * 2 ^ count.val ∧ v.val.length ≤ d.val.length + count.val := by
  rw [floats.doubled]
  by_cases pos : 0 < count.val
  · obtain ⟨v1, v1Run, cv1, v1Val, v1Len⟩ := Rowl.Numbers.add_naturals_spec d d cd.1 cd.1 (by omega)
    obtain ⟨c1, c1Run, c1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have c1Is : c1.val = count.val - 1 := by simp at c1Val; omega
    have v1Le : v1.val.length ≤ d.val.length + 1 := by simpa using v1Len
    obtain ⟨v, run, cv, vVal, vLen⟩ := doubled_spec v1 cv1 c1 (by omega)
    refine ⟨v, by simp [pos, v1Run, c1Run, run], cv, ?_, by omega⟩
    rw [vVal, v1Val, c1Is]
    have : 2 ^ count.val = 2 * 2 ^ (count.val - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  · have zero : count.val = 0 := by omega
    exact ⟨d, by simp [pos], cd, by simp [zero], by omega⟩
termination_by count.val
decreasing_by omega

/-- `wide_state` is the first quotient of `n / q` at the exponent. -/
theorem wide_state_spec (double : Bool) (n q : alloc.vec.Vec U8) (e : Usize) (dn : Canonical n.val)
    (cq : Canonical q.val) (qpos : 0 < digitsValue q.val) (eLo : lo double ≤ e.val) (eHi : e.val ≤ hi double)
    (small : n.val.length + q.val.length ≤ 10000) :
    ∃ k rest den, floats.wide_state n q e = .ok (k, rest, den) ∧ Canonical k.val ∧ Canonical rest.val ∧
      Canonical den.val ∧
      Quot ((digitsValue n.val : ℚ) / digitsValue q.val) (digitsValue k.val) (digitsValue rest.val)
        (digitsValue den.val) e.val ∧
      k.val.length ≤ 20000 ∧ rest.val.length ≤ 20000 ∧ den.val.length ≤ 20000 := by
  rw [floats.wide_state]
  have room := w_room
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  have loGe : 974 ≤ lo double := by cases double <;> simp [lo]
  by_cases up : 2048 ≤ e.val
  · have upB : floats.BIAS ≤ e := by rw [UScalar.le_equiv, bias_val]; exact up
    obtain ⟨c, cRun, cc, cVal, cLen⟩ := Rowl.Numbers.canonical_spec q cq.1
    obtain ⟨j, jRun, jVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := e) (y := floats.BIAS) (by rw [bias_val]; exact up))
    have jIs : j.val = e.val - 2048 := by rw [jVal.1, bias_val]
    obtain ⟨den, dRun, cden, dVal, dLen⟩ := doubled_spec c cc j (by unfold W at room; omega)
    have dpos : 0 < digitsValue den.val := by rw [dVal, cVal]; positivity
    obtain ⟨k, rest, divRun, ck, cr, kVal, rVal, kLen, rLen⟩ := Rowl.Numbers.divide_naturals_spec n den dn.1 cden dpos
      (by unfold W at room; omega)
    refine ⟨k, rest, den, by simp [upB, cRun, jRun, dRun, divRun], ck, cr, cden, ?_, by omega, by omega, by omega⟩
    rw [kVal, rVal, dVal, cVal]
    have eIs : e.val = 2048 + j.val := by omega
    rw [eIs]
    exact quot_scaled_up qpos
  · have upB : ¬ floats.BIAS ≤ e := by rw [UScalar.le_equiv, bias_val]; exact up
    obtain ⟨c, cRun, cc, cVal, cLen⟩ := Rowl.Numbers.canonical_spec n dn.1
    obtain ⟨j, jRun, jVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := floats.BIAS) (y := e)
      (by rw [bias_val]; omega))
    have jIs : j.val = 2048 - e.val := by rw [jVal.1, bias_val]
    obtain ⟨sc, sRun, csc, sVal, sLen⟩ := doubled_spec c cc j (by unfold W at room; omega)
    obtain ⟨k, rest, divRun, ck, cr, kVal, rVal, kLen, rLen⟩ := Rowl.Numbers.divide_naturals_spec sc q csc.1 cq qpos
      (by unfold W at room; omega)
    obtain ⟨c2, c2Run, cc2, c2Val, c2Len⟩ := Rowl.Numbers.canonical_spec q cq.1
    refine ⟨k, rest, c2, by simp [upB, cRun, jRun, sRun, divRun, c2Run], ck, cr, cc2, ?_, by omega, by omega,
      by omega⟩
    rw [kVal, rVal, sVal, cVal, c2Val]
    have eIs : e.val = 2048 - j.val := by omega
    rw [eIs]
    exact quot_scaled_down qpos (by omega)

/-- The numbers of a quotient on decimal digits. -/
def wideVals (x : alloc.vec.Vec U8 × alloc.vec.Vec U8 × alloc.vec.Vec U8 × Usize) : ℕ × ℕ × ℕ × ℕ :=
  (digitsValue x.1.val, digitsValue x.2.1.val, digitsValue x.2.2.1.val, x.2.2.2.val)

theorem u8_eq_zero (x : U8) : x = 0#u8 ↔ x.val = 0 := by rw [UScalar.eq_equiv]; simp

theorem usize_eq_zero (x : Usize) : x = 0#usize ↔ x.val = 0 := by rw [UScalar.eq_equiv]; simp

/-- `wide_settle` is the search for the exponent on decimal digits. -/
theorem wide_settle_spec (double : Bool) (fuel : Usize) (k rest den : alloc.vec.Vec U8) (e : Usize)
    (ck : Canonical k.val) (cr : Canonical rest.val) (cd : Canonical den.val) (eLe : e.val ≤ hi double)
    (lk : k.val.length + 2 * fuel.val ≤ W) (lr : rest.val.length + 2 * fuel.val ≤ W)
    (ld : den.val.length + 2 * fuel.val ≤ W) :
    ∃ r, floats.wide_settle k rest den e double fuel = .ok r ∧
      r.map wideVals = settleMath (prec double) (lo double) (hi double) fuel.val
        (digitsValue k.val) (digitsValue rest.val) (digitsValue den.val) e.val ∧
      ∀ x, r = some x → Canonical x.1.val ∧ Canonical x.2.1.val ∧ Canonical x.2.2.1.val ∧
        x.1.val.length ≤ W ∧ x.2.1.val.length ≤ W ∧ x.2.2.1.val.length ≤ W := by
  rw [floats.wide_settle]
  have room := w_room
  have wIs : W = 1048576 := rfl
  have pLe := prec_le double
  have pPos := prec_pos double
  have pow53 : 2 ^ prec double ≤ 2 ^ 53 := Nat.pow_le_pow_right (by norm_num) pLe
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  have loHi := lo_le_hi double
  by_cases fuelPos : 0 < fuel.val
  · obtain ⟨n, hn⟩ : ∃ n, fuel.val = n + 1 := ⟨fuel.val - 1, by omega⟩
    obtain ⟨t, tRun, tVal⟩ := top_spec double
    obtain ⟨tv, tvRun, ctv, tvVal, tvLen⟩ := digits_of_spec t
    have tvShort : tv.val.length ≤ 39 := tvLen 39 (by rw [tVal]; calc 2 ^ prec double ≤ 2 ^ 53 := pow53
      _ < 10 ^ 39 := by norm_num)
    obtain ⟨c1, c1Run, c1Val⟩ := Rowl.Numbers.compare_naturals_spec k tv ck ctv
    obtain ⟨f1, f1Run, f1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := fuel) (y := 1#usize) (by simp; omega))
    have f1Is : f1.val = n := by simp at f1Val; omega
    by_cases big : 2 ^ prec double ≤ digitsValue k.val
    · have c1B : ¬ c1.val = 0 := by
        rw [c1Val, tvVal, tVal]
        simp [Rowl.Numbers.order, not_lt.mpr big]
        split <;> simp
      obtain ⟨mo, moRun, moVal⟩ := most_spec double
      by_cases below : e.val < hi double
      · have belowM : e < mo := by rw [UScalar.lt_equiv, moVal]; exact below
        obtain ⟨two, twoRun, twoVal⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 50#u8 (by simp [new_val]; scalar_tac))
        have twoIs : two.val = [50#u8] := by rw [twoVal, new_val]; rfl
        have twoC : Canonical two.val := by rw [twoIs]; exact two_canonical
        have twoPos : 0 < digitsValue two.val := by rw [twoIs, two_value]; norm_num
        obtain ⟨half, low, divRun, chalf, clow, halfVal, lowVal, halfLen, lowLen⟩ :=
          Rowl.Numbers.divide_naturals_spec k two ck.1 twoC twoPos (by rw [twoIs, List.length_singleton]; omega)
        rw [twoIs, two_value] at halfVal lowVal
        obtain ⟨d2, d2Run, cd2, d2Val, d2Len⟩ := Rowl.Numbers.add_naturals_spec den den cd.1 cd.1
          (by unfold W at ld; omega)
        obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := e) (y := 1#usize) (by simp; omega))
        have e1Is : e1.val = e.val + 1 := by simpa using e1Val
        have d2Le : d2.val.length ≤ den.val.length + 1 := by simpa using d2Len
        by_cases even : digitsValue k.val % 2 = 0
        · have lowEmpty : low.val = [] := (canonical_zero low.val clow).mp (by rw [lowVal]; exact even)
          have lenZero : alloc.vec.Vec.len low = 0#usize := by rw [usize_eq_zero]; simp [lowEmpty]
          obtain ⟨r, run, rMap, rProp⟩ := wide_settle_spec double f1 half rest d2 e1 chalf cr cd2 (by omega)
            (by omega) (by omega) (by omega)
          refine ⟨r, by simp [fuelPos, tRun, tvRun, c1Run, c1B, moRun, moVal, below, twoRun, divRun, lenZero, d2Run,
            e1Run, f1Run, run], ?_, rProp⟩
          rw [rMap, hn]
          simp only [settleMath, big, below, ↓reduceIte, f1Is, halfVal, d2Val, e1Is, even, zero_mul, zero_add]
          congr 1; ring
        · have lowNot : low.val ≠ [] := fun h => even (by rw [← lowVal, h, value_nil])
          have lenNot : ¬ alloc.vec.Vec.len low = 0#usize := by
            rw [usize_eq_zero]; simp only [alloc.vec.Vec.len_val]
            exact fun h => lowNot (List.eq_nil_of_length_eq_zero h)
          obtain ⟨r1, r1Run, cr1, r1Val, r1Len⟩ := Rowl.Numbers.add_naturals_spec den rest cd.1 cr.1
            (by unfold W at ld lr; omega)
          have r1Le : r1.val.length ≤ max den.val.length rest.val.length + 1 := r1Len
          obtain ⟨r, run, rMap, rProp⟩ := wide_settle_spec double f1 half r1 d2 e1 chalf cr1 cd2 (by omega)
            (by omega) (by have := Nat.max_le.mpr ⟨ld, lr⟩; omega) (by omega)
          refine ⟨r, by simp [fuelPos, tRun, tvRun, c1Run, c1B, moRun, moVal, below, twoRun, divRun, lenNot, r1Run,
            d2Run, e1Run, f1Run, run], ?_, rProp⟩
          rw [rMap, hn]
          have odd : digitsValue k.val % 2 = 1 := by omega
          simp only [settleMath, big, below, ↓reduceIte, f1Is, halfVal, d2Val, e1Is, r1Val, odd, one_mul]
          congr 1; ring
      · have belowM : ¬ e < mo := by rw [UScalar.lt_equiv, moVal]; exact below
        obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := e) (y := 1#usize) (by simp; omega))
        have e1Is : e1.val = e.val + 1 := by simpa using e1Val
        refine ⟨some (k, rest, den, e1), by simp [fuelPos, tRun, tvRun, c1Run, c1B, moRun, moVal, below, e1Run], ?_, ?_⟩
        · rw [hn]; simp [settleMath, big, below, wideVals, e1Is]
        · intro x hx
          simp only [Option.some.injEq] at hx
          subst hx
          exact ⟨ck, cr, cd, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
    · have c1B : c1.val = 0 := by
        rw [c1Val, tvVal, tVal]
        simp [Rowl.Numbers.order, lt_of_not_ge big]
      obtain ⟨le, leRun, leVal⟩ := least_spec double
      by_cases above : lo double < e.val
      · have aboveL : le < e := by rw [UScalar.lt_equiv, leVal]; exact above
        obtain ⟨th, thRun, thVal⟩ := UScalar.div_spec t (y := 2#u128) (by simp)
        have thIs : th.val = 2 ^ (prec double - 1) := by
          rw [thVal, tVal]; simp; rw [two_pow_pred_nat pPos]; simp
        obtain ⟨hv, hvRun, chv, hvVal, hvLen⟩ := digits_of_spec th
        obtain ⟨c2, c2Run, c2Val⟩ := Rowl.Numbers.compare_naturals_spec k hv ck chv
        by_cases halfSmall : 2 * digitsValue k.val < 2 ^ prec double
        · have c2B : c2.val = 0 := by
            rw [c2Val, hvVal, thIs]
            have := two_pow_pred_nat pPos
            simp [Rowl.Numbers.order]; omega
          have c2E : c2 = 0#u8 := by rw [u8_eq_zero]; exact c2B
          obtain ⟨tw, twRun, ctw, twVal, twLen⟩ := Rowl.Numbers.add_naturals_spec rest rest cr.1 cr.1
            (by unfold W at lr; omega)
          obtain ⟨dk, dkRun, cdk, dkVal, dkLen⟩ := Rowl.Numbers.add_naturals_spec k k ck.1 ck.1
            (by unfold W at lk; omega)
          have twLe : tw.val.length ≤ rest.val.length + 1 := by simpa using twLen
          have dkLe : dk.val.length ≤ k.val.length + 1 := by simpa using dkLen
          obtain ⟨c3, c3Run, c3Val⟩ := Rowl.Numbers.compare_naturals_spec tw den ctw cd
          obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := e) (y := 1#usize) (by simp; omega))
          have e1Is : e1.val = e.val - 1 := by simp at e1Val; omega
          have downStep : settleMath (prec double) (lo double) (hi double) fuel.val (digitsValue k.val)
              (digitsValue rest.val) (digitsValue den.val) e.val =
              if 2 * digitsValue rest.val < digitsValue den.val then
                settleMath (prec double) (lo double) (hi double) n (2 * digitsValue k.val)
                  (2 * digitsValue rest.val) (digitsValue den.val) (e.val - 1)
              else settleMath (prec double) (lo double) (hi double) n (2 * digitsValue k.val + 1)
                (2 * digitsValue rest.val - digitsValue den.val) (digitsValue den.val) (e.val - 1) := by
            rw [hn]; simp only [settleMath, big, above, halfSmall, and_self, ↓reduceIte]
          by_cases lowR : 2 * digitsValue rest.val < digitsValue den.val
          · have c3B : c3.val = 0 := by
              rw [c3Val, twVal]; simp [Rowl.Numbers.order]; omega
            have c3E : c3 = 0#u8 := by rw [u8_eq_zero]; exact c3B
            obtain ⟨r, run, rMap, rProp⟩ := wide_settle_spec double f1 dk tw den e1 cdk ctw cd (by omega)
              (by omega) (by omega) (by omega)
            refine ⟨r, by simp [fuelPos, tRun, tvRun, c1Run, c1B, leRun, leVal, above, thRun, hvRun, c2Run, c2B, c2E, twRun,
              dkRun, c3Run, c3B, c3E, e1Run, f1Run, run], ?_, rProp⟩
            rw [rMap, downStep, if_pos lowR, f1Is, dkVal, twVal, e1Is]
            congr 1 <;> ring
          · have c3B : ¬ c3.val = 0 := by
              rw [c3Val, twVal]; simp [Rowl.Numbers.order]; split <;> omega
            have c3E : ¬ c3 = 0#u8 := by rw [u8_eq_zero]; exact c3B
            obtain ⟨r1, r1Run, cr1, r1Val, r1Len⟩ := Rowl.Numbers.subtract_naturals_spec tw den ctw cd
              (by rw [twVal]; omega) (by unfold W at lr; omega)
            obtain ⟨one, oneRun, oneVal⟩ := one_spec
            obtain ⟨k3, k3Run, ck3, k3Val, k3Len⟩ := Rowl.Numbers.add_naturals_spec dk one cdk.1
              (by rw [oneVal]; exact one_canonical.1) (by rw [oneVal]; unfold W at lk; simp; omega)
            have k3Le : k3.val.length ≤ k.val.length + 2 := by
              have : max dk.val.length one.val.length ≤ k.val.length + 1 := by
                rw [oneVal]; simp; omega
              omega
            obtain ⟨r, run, rMap, rProp⟩ := wide_settle_spec double f1 k3 r1 den e1 ck3 cr1 cd (by omega)
              (by omega) (by omega) (by omega)
            refine ⟨r, by simp [fuelPos, tRun, tvRun, c1Run, c1B, leRun, leVal, above, thRun, hvRun, c2Run, c2B, c2E, twRun,
              dkRun, c3Run, c3B, c3E, r1Run, oneRun, k3Run, e1Run, f1Run, run], ?_, rProp⟩
            rw [rMap, downStep, if_neg lowR, f1Is, k3Val, dkVal, oneVal, one_value, r1Val, twVal, e1Is]
            congr 1 <;> omega
        · have c2B : ¬ c2.val = 0 := by
            rw [c2Val, hvVal, thIs]
            have := two_pow_pred_nat pPos
            simp [Rowl.Numbers.order]; split <;> omega
          have c2E : ¬ c2 = 0#u8 := by rw [u8_eq_zero]; exact c2B
          refine ⟨some (k, rest, den, e), by simp [fuelPos, tRun, tvRun, c1Run, c1B, leRun, leVal, above, thRun, hvRun,
            c2Run, c2B, c2E], ?_, ?_⟩
          · rw [hn]; simp [settleMath, big, halfSmall, wideVals]
          · intro x hx
            simp only [Option.some.injEq] at hx
            subst hx
            exact ⟨ck, cr, cd, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
      · have aboveL : ¬ le < e := by rw [UScalar.lt_equiv, leVal]; exact above
        refine ⟨some (k, rest, den, e), by simp [fuelPos, tRun, tvRun, c1Run, c1B, leRun, leVal, above], ?_, ?_⟩
        · rw [hn]; simp [settleMath, big, above, wideVals]
        · intro x hx
          simp only [Option.some.injEq] at hx
          subst hx
          exact ⟨ck, cr, cd, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
  · refine ⟨none, by simp [fuelPos], ?_, fun x hx => by cases hx⟩
    have : fuel.val = 0 := by omega
    rw [this]; rfl
termination_by fuel.val
decreasing_by all_goals omega

/-! ## Rounding on decimal digits -/

theorem small_number_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (index : Usize) (total : U64)
    (inside : index.val ≤ digits.val.length)
    (fits : total.val * 10 ^ (digits.val.length - index.val) + digitsValue (digits.val.drop index.val) ≤ U64.max) :
    ∃ r, floats.small_number digits index total = .ok r ∧
      r.val = total.val * 10 ^ (digits.val.length - index.val) + digitsValue (digits.val.drop index.val) := by
  rw [floats.small_number]
  by_cases before : index.val < digits.val.length
  · have lookup : digits.index_usize index = .ok digits.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem before]
    have dig := dd _ (List.getElem_mem before)
    have dropEq : digits.val.drop index.val = digits.val[index.val] :: digits.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons before
    have restLen : (digits.val.drop (index.val + 1)).length = digits.val.length - index.val - 1 := by simp; omega
    have powEq : 10 ^ (digits.val.length - index.val) = 10 * 10 ^ (digits.val.length - index.val - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [dropEq, Rowl.Numbers.value_cons, restLen] at fits
    obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have i1Is : i1.val = index.val + 1 := by simpa using i1Val
    have tenTotal : 10 * total.val ≤ U64.max := by
      have : 10 * total.val ≤ total.val * 10 ^ (digits.val.length - index.val) := by
        rw [powEq]; nlinarith [Nat.one_le_pow (digits.val.length - index.val - 1) 10 (by norm_num)]
      omega
    obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 10#u64) (y := total)
      (by simp [UScalar.max]; omega))
    have i2Is : i2.val = 10 * total.val := by simpa using i2Val
    obtain ⟨i4, i4Run, i4Val⟩ := WP.spec_imp_exists (U8.sub_spec (x := digits.val[index.val]) (y := 48#u8)
      (by simpa using dig.1))
    have i4Is : i4.val = digits.val[index.val].val - 48 := by simpa using i4Val.1
    have castIs : (UScalar.cast .U64 i4).val = i4.val := by simp
    have sumBound : 10 * total.val + (digits.val[index.val].val - 48) ≤ U64.max := by
      have : (10 * total.val + (digits.val[index.val].val - 48)) * 1 ≤
          (10 * total.val + (digits.val[index.val].val - 48)) * 10 ^ (digits.val.length - index.val - 1) :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by norm_num))
      have expand : total.val * 10 ^ (digits.val.length - index.val) +
          ((digits.val[index.val].val - 48) * 10 ^ (digits.val.length - index.val - 1) +
            digitsValue (digits.val.drop (index.val + 1))) =
          (10 * total.val + (digits.val[index.val].val - 48)) * 10 ^ (digits.val.length - index.val - 1) +
            digitsValue (digits.val.drop (index.val + 1)) := by rw [powEq]; ring
      omega
    obtain ⟨i6, i6Run, i6Val⟩ := WP.spec_imp_exists (UScalar.add_spec (x := i2) (y := UScalar.cast .U64 i4)
      (by rw [castIs, i4Is, i2Is]; simp [UScalar.max]; omega))
    have i6Is : i6.val = 10 * total.val + (digits.val[index.val].val - 48) := by
      rw [i6Val, castIs, i4Is, i2Is]
    have expand : total.val * 10 ^ (digits.val.length - index.val) +
        ((digits.val[index.val].val - 48) * 10 ^ (digits.val.length - index.val - 1) +
          digitsValue (digits.val.drop (index.val + 1))) =
        i6.val * 10 ^ (digits.val.length - i1.val) + digitsValue (digits.val.drop i1.val) := by
      rw [i6Is, i1Is, powEq, show digits.val.length - (index.val + 1) = digits.val.length - index.val - 1 by omega]
      ring
    obtain ⟨r, run, value⟩ := small_number_spec digits dd i1 i6 (by omega) (by rw [← expand]; exact fits)
    refine ⟨r, by simp [before, i1Run, i2Run, alloc.vec.Vec.index_slice_index, lookup, i4Run, lift, i6Run, run], ?_⟩
    rw [value, ← expand, dropEq, Rowl.Numbers.value_cons, restLen]
  · have atEnd : index.val = digits.val.length := by omega
    refine ⟨total, by simp [before], ?_⟩
    rw [atEnd]; simp [value_nil]
termination_by digits.val.length - index.val
decreasing_by omega

/-- The rounded significand gives the value of a settled quotient. -/
theorem settled_of_round (double negative : Bool) (k rem den e m : ℕ) (mIs : m = roundUp k rem den)
    (eLe : e ≤ hi double) :
    (if m = 0 then Binary.zero negative
      else if m = 2 ^ prec double ∧ e = hi double then .infinity negative
      else .finite ((if negative then -1 else 1) * (m : ℚ) * scale e)) =
    roundSettled double negative k rem den e := by
  simp only [roundSettled, show ¬ hi double < e by omega, ↓reduceIte, mIs]

theorem odd_digit (b : U8) (d : Digit b) :
    ((((decide (b = 49#u8) || decide (b = 51#u8)) || decide (b = 53#u8)) || decide (b = 55#u8)) ||
      decide (b = 57#u8)) = decide (b.val % 2 = 1) := by
  have eq : ∀ c : U8, (b = c) ↔ b.val = c.val := fun c => ⟨fun h => by rw [h], fun h => UScalar.eq_of_val_eq h⟩
  simp only [eq]
  obtain ⟨lo, hi⟩ := d
  generalize b.val = n at lo hi ⊢
  rcases (by omega : n = 48 ∨ n = 49 ∨ n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨ n = 55 ∨ n = 56 ∨ n = 57) with
    h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

theorem order_le (a b : ℕ) : Rowl.Numbers.order a b ≤ 2 := by
  unfold Rowl.Numbers.order
  by_cases h1 : a < b
  · rw [if_pos h1]; omega
  · rw [if_neg h1]; by_cases h2 : a = b
    · rw [if_pos h2]; omega
    · rw [if_neg h2]
theorem order_zero_iff (a b : ℕ) : Rowl.Numbers.order a b = 0 ↔ a < b := by
  unfold Rowl.Numbers.order
  by_cases h1 : a < b
  · rw [if_pos h1]; simpa using h1
  · rw [if_neg h1]; by_cases h2 : a = b
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega
theorem order_one_iff (a b : ℕ) : Rowl.Numbers.order a b = 1 ↔ a = b := by
  unfold Rowl.Numbers.order
  by_cases h1 : a < b
  · rw [if_pos h1]; omega
  · rw [if_neg h1]; by_cases h2 : a = b
    · rw [if_pos h2]; simpa using h2
    · rw [if_neg h2]; omega
theorem order_two_iff (a b : ℕ) : Rowl.Numbers.order a b = 2 ↔ b < a := by
  unfold Rowl.Numbers.order
  by_cases h1 : a < b
  · rw [if_pos h1]; omega
  · rw [if_neg h1]; by_cases h2 : a = b
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

theorem value_parity (l : List U8) (d : Digits l) (ne : l ≠ []) :
    digitsValue l % 2 = (l.getLast ne).val % 2 := by
  have split := List.dropLast_append_getLast ne
  have last := d _ (List.getLast_mem ne)
  conv_lhs => rw [← split]
  rw [value_snoc]
  have := last.1
  omega

/-- The end of `wide_round`, from the rounded significand on. -/
theorem wide_tail (double negative : Bool) (m : alloc.vec.Vec U8) (e : Usize) (cm : Canonical m.val)
    (mLe : digitsValue m.val ≤ 2 ^ prec double) (eLe : e.val ≤ hi double) :
    (do
      let i1 ← floats.top double
      let v ← floats.digits_of i1
      let i2 ← numbers.compare_naturals m v
      if i2 = 1#u8
      then
        let i3 ← floats.most double
        if e < i3
        then
          let i4 ← i1 / 2#u128
          let i5 ← lift (UScalar.cast .U64 i4)
          let i6 ← e + 1#usize
          floats.finite negative i5 i6
        else ok (datatypes.Binary.Infinite negative)
      else
        let i3 ← floats.small_number m 0#usize 0#u64
        floats.finite negative i3 e : Result datatypes.Binary) ⦃ b => CanonicalBinary b ∧
        binaryOf b = (if digitsValue m.val = 0 then .zero negative
          else if digitsValue m.val = 2 ^ prec double ∧ e.val = hi double then .infinity negative
          else .finite ((if negative then -1 else 1) * (digitsValue m.val : ℚ) * scale e.val)) ⦄ := by
  apply WP.exists_imp_spec
  obtain ⟨t, tRun, tVal⟩ := top_spec double
  obtain ⟨tv, tvRun, ctv, tvVal, tvLen⟩ := digits_of_spec t
  obtain ⟨c, cRun, cVal⟩ := Rowl.Numbers.compare_naturals_spec m tv cm ctv
  have pLe := prec_le double
  have pPos := prec_pos double
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  have room : e.val + 1 + 64 ≤ Usize.max := by scalar_tac
  have pow53 : 2 ^ prec double ≤ 2 ^ 53 := Nat.pow_le_pow_right (by norm_num) pLe
  by_cases full : digitsValue m.val = 2 ^ prec double
  · have cOne : c = 1#u8 := by
      rw [UScalar.eq_equiv, cVal, tvVal, tVal, full]; simp [Rowl.Numbers.order]
    obtain ⟨mo, moRun, moVal⟩ := most_spec double
    by_cases below : e.val < hi double
    · obtain ⟨h2, h2Run, h2Val⟩ := UScalar.div_spec t (y := 2#u128) (by simp)
      have h2Is : h2.val = 2 ^ (prec double - 1) := by
        rw [h2Val, tVal]; simp
        rw [two_pow_pred_nat pPos]; simp
      have h2Small : 2 ^ (prec double - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have castIs := cast_small h2 (by rw [h2Is]; exact h2Small)
      obtain ⟨e1, e1Run, e1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := e) (y := 1#usize) (by simp; omega))
      have e1Is : e1.val = e.val + 1 := by simpa using e1Val
      obtain ⟨b, bRun, bCanon, bValue⟩ := finite_spec negative (UScalar.cast .U64 h2) e1 (by omega)
      refine ⟨b, by simp [tRun, tvRun, cRun, cOne, moRun, moVal, below, h2Run, lift, e1Run, bRun], bCanon, ?_⟩
      rw [bValue, castIs, h2Is, e1Is]
      have hNot : 2 ^ (prec double - 1) ≠ 0 := by positivity
      have pNot : 2 ^ prec double ≠ 0 := by positivity
      simp only [hNot, pNot, full, true_and, show e.val ≠ hi double by omega, ↓reduceIte]
      rw [scale_succ]
      have : (2 : ℚ) ^ prec double = 2 * 2 ^ (prec double - 1) := two_pow_pred pPos
      push_cast
      rw [this]; congr 1; ring
    · refine ⟨.Infinite negative, by simp [tRun, tvRun, cRun, cOne, moRun, moVal, below], trivial, ?_⟩
      have pNot : 2 ^ prec double ≠ 0 := by positivity
      simp [binaryOf, full, pNot, show e.val = hi double by omega]
  · have cNot : ¬ c = 1#u8 := by
      rw [UScalar.eq_equiv, cVal, tvVal, tVal]; simp [Rowl.Numbers.order]; split <;> omega
    have mLt : digitsValue m.val < 2 ^ 53 := by omega
    obtain ⟨sn, snRun, snVal⟩ := small_number_spec m cm.1 0#usize 0#u64 (by simp)
      (by simp; have : (2 : ℕ) ^ 53 ≤ U64.max := by simp [U64.max_eq]
          omega)
    have snIs : sn.val = digitsValue m.val := by simpa using snVal
    obtain ⟨b, bRun, bCanon, bValue⟩ := finite_spec negative sn e (by omega)
    refine ⟨b, by simp [tRun, tvRun, cRun, cNot, snRun, bRun], bCanon, ?_⟩
    rw [bValue, snIs]
    simp [full]

/-- `wide_round` rounds a settled quotient on decimal digits. -/
theorem wide_round_spec (double negative : Bool) (k rest den : alloc.vec.Vec U8) (e : Usize)
    (ck : Canonical k.val) (cr : Canonical rest.val) (cd : Canonical den.val)
    (kLt : digitsValue k.val < 2 ^ prec double) (eLe : e.val ≤ hi double)
    (lk : k.val.length ≤ W) (lr : rest.val.length ≤ W) :
    floats.wide_round k rest den e negative double ⦃ b => CanonicalBinary b ∧
      binaryOf b = roundSettled double negative (digitsValue k.val) (digitsValue rest.val) (digitsValue den.val)
        e.val ⦄ := by
  unfold floats.wide_round
  have room := w_room
  have wIs : W = 1048576 := rfl
  obtain ⟨tw, twRun, ctw, twVal, twLen⟩ := Rowl.Numbers.add_naturals_spec rest rest cr.1 cr.1 (by omega)
  obtain ⟨i, iRun, iVal⟩ := Rowl.Numbers.compare_naturals_spec tw den ctw cd
  rw [twVal] at iVal
  simp only [twRun, iRun, bind_ok]
  have viaUp : ∀ m : alloc.vec.Vec U8, Canonical m.val →
      digitsValue m.val = roundUp (digitsValue k.val) (digitsValue rest.val) (digitsValue den.val) →
      WP.qimp (fun b => CanonicalBinary b ∧
        binaryOf b = (if digitsValue m.val = 0 then .zero negative
          else if digitsValue m.val = 2 ^ prec double ∧ e.val = hi double then .infinity negative
          else .finite ((if negative then -1 else 1) * (digitsValue m.val : ℚ) * scale e.val)))
        (fun b => CanonicalBinary b ∧
          binaryOf b = roundSettled double negative (digitsValue k.val) (digitsValue rest.val)
            (digitsValue den.val) e.val) := by
    intro m cm mIs b hb
    exact ⟨hb.1, by rw [hb.2, settled_of_round double negative _ _ _ _ _ mIs eLe]⟩
  have bound := roundUp_le (digitsValue k.val) (digitsValue rest.val) (digitsValue den.val)
  obtain ⟨one, oneRun, oneVal⟩ := one_spec
  obtain ⟨k1, k1Run, ck1, k1Val, k1Len⟩ := Rowl.Numbers.add_naturals_spec k one ck.1
    (by rw [oneVal]; exact one_canonical.1) (by rw [oneVal]; simp; omega)
  rw [oneVal, one_value] at k1Val
  split
  · have low : 2 * digitsValue rest.val < digitsValue den.val := by
      have := (order_zero_iff _ _).mp (by rw [← iVal]; rfl); omega
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
    try simp only [bind_ok]
    exact WP.spec_mono (wide_tail double negative k e ck (by omega) eLe)
      (viaUp k ck (by simp [roundUp, low]))
  · have high : digitsValue den.val < 2 * digitsValue rest.val := by
      have := (order_two_iff _ _).mp (by rw [← iVal]; rfl); omega
    simp only [bind_ok, ↓reduceIte, oneRun, k1Run]
    try simp only [bind_ok]
    exact WP.spec_mono (wide_tail double negative k1 e ck1 (by omega) eLe)
      (viaUp k1 ck1 (by rw [k1Val]; simp [roundUp, high, show ¬ 2 * digitsValue rest.val < digitsValue den.val by omega]))
  · rename_i not0 not2
    have i1 : i.val = 1 := by
      have : i.val ≠ 0 := fun h => not0 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have : i.val ≠ 2 := fun h => not2 (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have := order_le (digitsValue rest.val + digitsValue rest.val) (digitsValue den.val)
      rw [← iVal] at this
      omega
    have tie : 2 * digitsValue rest.val = digitsValue den.val := by
      have := (order_one_iff _ _).mp (by rw [← iVal]; exact i1); omega
    by_cases empty : k.val = []
    · have zero : digitsValue k.val = 0 := by rw [empty, value_nil]
      have lenZero : ¬ (0#usize) < alloc.vec.Vec.len k := by
        rw [UScalar.lt_equiv]; simp [empty]
      simp only [lenZero, ↓reduceIte, bind_ok]
      have b48 : ((((decide ((48#u8 : U8) = 49#u8) || decide ((48#u8 : U8) = 51#u8)) || decide ((48#u8 : U8) = 53#u8)) ||
          decide ((48#u8 : U8) = 55#u8)) || decide ((48#u8 : U8) = 57#u8)) = false := by decide
      simp only [b48, Bool.false_eq_true, ↓reduceIte]
      try simp only [bind_ok]
      exact WP.spec_mono (wide_tail double negative k e ck (by omega) eLe)
        (viaUp k ck (by simp [roundUp, tie, zero]))
    · have lenPos : (0#usize) < alloc.vec.Vec.len k := by
        rw [UScalar.lt_equiv]; simp; exact List.length_pos_of_ne_nil empty
      obtain ⟨j, jRun, jVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := alloc.vec.Vec.len k) (y := 1#usize)
        (by simp; exact List.length_pos_of_ne_nil empty))
      have jIs : j.val = k.val.length - 1 := by simpa using jVal.1
      have jLt : j.val < k.val.length := by have := List.length_pos_of_ne_nil empty; omega
      have lookup : k.index_usize j = .ok k.val[j.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem jLt]
      have lastIs : k.val[j.val] = k.val.getLast empty := by
        rw [List.getLast_eq_getElem]; congr 1
      have parity := value_parity k.val ck.1 empty
      have oddIs := odd_digit (k.val.getLast empty) (ck.1 _ (List.getLast_mem empty))
      simp only [lenPos, ↓reduceIte, bind_ok, jRun, alloc.vec.Vec.index_slice_index, lookup, lastIs, oddIs]
      by_cases odd : digitsValue k.val % 2 = 1
      · have lastOdd : (k.val.getLast empty).val % 2 = 1 := by omega
        simp only [lastOdd, decide_true, ↓reduceIte, oneRun, k1Run, bind_ok]
        try simp only [bind_ok]
        exact WP.spec_mono (wide_tail double negative k1 e ck1 (by omega) eLe)
          (viaUp k1 ck1 (by rw [k1Val]; simp [roundUp, tie, odd]))
      · have lastEven : ¬ (k.val.getLast empty).val % 2 = 1 := by omega
        simp only [lastEven, decide_false, Bool.false_eq_true, ↓reduceIte]
        try simp only [bind_ok]
        exact WP.spec_mono (wide_tail double negative k e ck (by omega) eLe)
          (viaUp k ck (by simp [roundUp, tie, odd]))

theorem settleBound_le (a : ℚ) (p lo hi e : ℕ) (eLo : lo ≤ e) (eHi : e ≤ hi) :
    settleBound a p lo hi e ≤ hi - lo + 1 := by
  unfold settleBound; split_ifs <;> omega

/-- `wide` is the value of `n / q`, with the sign. -/
theorem wide_spec (n q : alloc.vec.Vec U8) (e : Usize) (negative double : Bool)
    (cn : Canonical n.val) (cq : Canonical q.val) (npos : 0 < digitsValue n.val) (qpos : 0 < digitsValue q.val)
    (eLo : lo double ≤ e.val) (eHi : e.val ≤ hi double) (small : n.val.length + q.val.length ≤ 10000) :
    ∃ b, floats.wide n q e negative double = .ok (some b) ∧ CanonicalBinary b ∧
      binaryOf b = roundBinary (fmt double)
        (if negative then -((digitsValue n.val : ℚ) / digitsValue q.val) else (digitsValue n.val : ℚ) / digitsValue q.val) := by
  rw [floats.wide]
  have wIs : W = 1048576 := rfl
  have apos : 0 < (digitsValue n.val : ℚ) / digitsValue q.val := by
    have : (0 : ℚ) < digitsValue n.val := by exact_mod_cast npos
    have : (0 : ℚ) < digitsValue q.val := by exact_mod_cast qpos
    positivity
  have loHi := lo_le_hi double
  have hiLe : hi double ≤ 3019 := by cases double <;> simp [hi]
  obtain ⟨k, rest, den, stRun, ck, cr, cd, q0, lk, lr, ld⟩ := wide_state_spec double n q e cn cq qpos eLo eHi small
  obtain ⟨r, run, rMap, rProp⟩ := wide_settle_spec double floats.STEPS k rest den e ck cr cd eHi
    (by rw [steps_val]; omega) (by rw [steps_val]; omega) (by rw [steps_val]; omega)
  obtain ⟨x, hx⟩ := settle_complete (prec_pos double) floats.STEPS.val _ _ _ _ q0 eLo eHi
    (by have := settleBound_le ((digitsValue n.val : ℚ) / digitsValue q.val) (prec double) (lo double) (hi double)
          e.val eLo eHi
        rw [steps_val]; omega)
  rw [hx] at rMap
  rcases r with _ | ⟨k1, rest1, den1, e1⟩
  · simp at rMap
  · simp only [Option.map_some, Option.some.injEq] at rMap
    have settled := settle_sound _ _ _ _ _ q0 eLo eHi _ _ _ _ (by rw [hx, ← rMap])
    obtain ⟨ck1, cr1, cd1, lk1, lr1, ld1⟩ := rProp _ rfl
    obtain ⟨mo, moRun, moVal⟩ := most_spec double
    by_cases over : hi double < e1.val
    · refine ⟨.Infinite negative, by simp [stRun, run, moRun, moVal, over], trivial, ?_⟩
      rw [← settled_round_value apos double negative settled]
      simp [roundSettled, over, binaryOf, wideVals]
    · have inner : digitsValue k1.val < 2 ^ prec double ∧ e1.val ≤ hi double := by
        rcases settled with ⟨eq, _, _⟩ | ⟨_, h, _, small, _⟩
        · simp [wideVals] at eq; omega
        · exact ⟨small, h⟩
      obtain ⟨b, bRun, bCanon, bValue⟩ := WP.spec_imp_exists (wide_round_spec double negative k1 rest1 den1 e1
        ck1 cr1 cd1 inner.1 inner.2 lk1 lr1)
      refine ⟨b, by simp [stRun, run, moRun, moVal, over, bRun], bCanon, ?_⟩
      rw [bValue, ← settled_round_value apos double negative settled]
      rfl

/-! ## The value of a digit string -/

theorem native_value_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (index : Usize) (total : U128)
    (inside : index.val ≤ digits.val.length)
    (fits : total.val * 10 ^ (digits.val.length - index.val) + digitsValue (digits.val.drop index.val) ≤ U128.max) :
    ∃ r, floats.native_value digits index total = .ok r ∧
      r.val = total.val * 10 ^ (digits.val.length - index.val) + digitsValue (digits.val.drop index.val) := by
  rw [floats.native_value]
  by_cases before : index.val < digits.val.length
  · have lookup : digits.index_usize index = .ok digits.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem before]
    have dig := dd _ (List.getElem_mem before)
    have dropEq : digits.val.drop index.val = digits.val[index.val] :: digits.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons before
    have restLen : (digits.val.drop (index.val + 1)).length = digits.val.length - index.val - 1 := by simp; omega
    have powEq : 10 ^ (digits.val.length - index.val) = 10 * 10 ^ (digits.val.length - index.val - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [dropEq, Rowl.Numbers.value_cons, restLen] at fits
    obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have i1Is : i1.val = index.val + 1 := by simpa using i1Val
    have tenTotal : 10 * total.val ≤ U128.max := by
      have : 10 * total.val ≤ total.val * 10 ^ (digits.val.length - index.val) := by
        rw [powEq]; nlinarith [Nat.one_le_pow (digits.val.length - index.val - 1) 10 (by norm_num)]
      omega
    obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 10#u128) (y := total)
      (by simp [UScalar.max]; omega))
    have i2Is : i2.val = 10 * total.val := by simpa using i2Val
    obtain ⟨i4, i4Run, i4Val⟩ := WP.spec_imp_exists (U8.sub_spec (x := digits.val[index.val]) (y := 48#u8)
      (by simpa using dig.1))
    have i4Is : i4.val = digits.val[index.val].val - 48 := by simpa using i4Val.1
    have castIs : (UScalar.cast .U128 i4).val = i4.val := by simp
    have sumBound : 10 * total.val + (digits.val[index.val].val - 48) ≤ U128.max := by
      have : (10 * total.val + (digits.val[index.val].val - 48)) * 1 ≤
          (10 * total.val + (digits.val[index.val].val - 48)) * 10 ^ (digits.val.length - index.val - 1) :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by norm_num))
      have expand : total.val * 10 ^ (digits.val.length - index.val) +
          ((digits.val[index.val].val - 48) * 10 ^ (digits.val.length - index.val - 1) +
            digitsValue (digits.val.drop (index.val + 1))) =
          (10 * total.val + (digits.val[index.val].val - 48)) * 10 ^ (digits.val.length - index.val - 1) +
            digitsValue (digits.val.drop (index.val + 1)) := by rw [powEq]; ring
      omega
    obtain ⟨i6, i6Run, i6Val⟩ := WP.spec_imp_exists (UScalar.add_spec (x := i2) (y := UScalar.cast .U128 i4)
      (by rw [castIs, i4Is, i2Is]; simp [UScalar.max]; omega))
    have i6Is : i6.val = 10 * total.val + (digits.val[index.val].val - 48) := by
      rw [i6Val, castIs, i4Is, i2Is]
    have expand : total.val * 10 ^ (digits.val.length - index.val) +
        ((digits.val[index.val].val - 48) * 10 ^ (digits.val.length - index.val - 1) +
          digitsValue (digits.val.drop (index.val + 1))) =
        i6.val * 10 ^ (digits.val.length - i1.val) + digitsValue (digits.val.drop i1.val) := by
      rw [i6Is, i1Is, powEq, show digits.val.length - (index.val + 1) = digits.val.length - index.val - 1 by omega]
      ring
    obtain ⟨r, run, value⟩ := native_value_spec digits dd i1 i6 (by omega) (by rw [← expand]; exact fits)
    refine ⟨r, by simp [before, i1Run, i2Run, alloc.vec.Vec.index_slice_index, lookup, i4Run, lift, i6Run, run], ?_⟩
    rw [value, ← expand, dropEq, Rowl.Numbers.value_cons, restLen]
  · have atEnd : index.val = digits.val.length := by omega
    refine ⟨total, by simp [before], ?_⟩
    rw [atEnd]; simp [value_nil]
termination_by digits.val.length - index.val
decreasing_by omega

/-- `estimate` is an exponent within the format. -/
theorem estimate_spec (order : Usize) (double : Bool) (low : 268435456 ≤ order.val + 400)
    (high : order.val < 268435456 + 400) :
    ∃ e, floats.estimate order double = .ok e ∧ lo double ≤ e.val ∧ e.val ≤ hi double := by
  rw [floats.estimate]
  obtain ⟨pr, prRun, prVal⟩ := precision_spec double
  obtain ⟨le, leRun, leVal⟩ := least_spec double
  obtain ⟨mo, moRun, moVal⟩ := most_spec double
  have pLe := prec_le double
  have pPos := prec_pos double
  have loHi := lo_le_hi double
  have big : 4294967295 ≤ Usize.max := by scalar_tac
  have clamp : ∀ guess : Usize, ∃ e, (do
      let i ← floats.least double
      if guess < i then ok i
      else do
        let i1 ← floats.most double
        if i1 < guess then ok i1 else ok guess : Result Usize) = .ok e ∧ lo double ≤ e.val ∧ e.val ≤ hi double := by
    intro guess
    by_cases under : guess.val < lo double
    · exact ⟨le, by simp [leRun, leVal, under], by omega, by omega⟩
    · by_cases over : hi double < guess.val
      · exact ⟨mo, by simp [leRun, leVal, under, moRun, moVal, over], by omega, by omega⟩
      · exact ⟨guess, by simp [leRun, leVal, under, moRun, moVal, over], by omega, by omega⟩
  by_cases above : 268435456 < order.val
  · have aboveB : floats.ORDER_BIAS < order := by rw [UScalar.lt_equiv, order_bias_val]; exact above
    obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := floats.BIAS) (y := 1#usize)
      (by rw [bias_val]; simp; omega))
    obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := order) (y := floats.ORDER_BIAS)
      (by rw [order_bias_val]; omega))
    have i1Is : i1.val = order.val - 268435456 := by rw [i1Val.1, order_bias_val]
    obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i1) (y := 1#usize) (by simp; omega))
    have i2Is : i2.val = order.val - 268435456 - 1 := by simp at i2Val; omega
    obtain ⟨i3, i3Run, i3Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := i2) (y := 3321928#usize)
      (by rw [i2Is]; simp [UScalar.max_USize_eq]; omega))
    have i3Is : i3.val = (order.val - 268435456 - 1) * 3321928 := by rw [i3Val, i2Is]; simp
    obtain ⟨i4, i4Run, i4Val⟩ := UScalar.div_spec i3 (y := 1000000#usize) (by simp)
    have i4Is : i4.val = (order.val - 268435456 - 1) * 3321928 / 1000000 := by rw [i4Val, i3Is]; simp
    have i4Le : i4.val ≤ 1400 := by rw [i4Is]; omega
    obtain ⟨i5, i5Run, i5Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i) (y := i4)
      (by rw [iVal, bias_val]; simp; omega))
    have i5Is : i5.val = 2049 + i4.val := by rw [i5Val, iVal, bias_val]; simp
    obtain ⟨g, gRun, gVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i5) (y := pr) (by rw [i5Is, prVal]; omega))
    obtain ⟨e, eRun, eLo, eHi⟩ := clamp g
    refine ⟨e, ?_, eLo, eHi⟩
    simp only [aboveB, ↓reduceIte, iRun, i1Run, i2Run, i3Run, i4Run, i5Run, prRun, gRun, bind_ok]
    exact eRun
  · have aboveB : ¬ floats.ORDER_BIAS < order := by rw [UScalar.lt_equiv, order_bias_val]; exact above
    obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := floats.ORDER_BIAS) (y := 1#usize)
      (by rw [order_bias_val]; simp; omega))
    have iIs : i.val = 268435457 := by rw [iVal, order_bias_val]; simp
    obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i) (y := order) (by rw [iIs]; omega))
    have i1Is : i1.val = 268435457 - order.val := by rw [i1Val.1, iIs]
    obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := i1) (y := 3321928#usize)
      (by rw [i1Is]; simp [UScalar.max_USize_eq]; omega))
    have i2Is : i2.val = (268435457 - order.val) * 3321928 := by rw [i2Val, i1Is]; simp
    obtain ⟨down, dRun, dVal⟩ := UScalar.div_spec i2 (y := 1000000#usize) (by simp)
    have dIs : down.val = (268435457 - order.val) * 3321928 / 1000000 := by rw [dVal, i2Is]; simp
    have dLe : down.val ≤ 1400 := by rw [dIs]; omega
    obtain ⟨i4, i4Run, i4Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := pr) (y := down)
      (by rw [prVal]; omega))
    have i4Is : i4.val = prec double + down.val := by rw [i4Val, prVal]
    obtain ⟨i5, i5Run, i5Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := floats.BIAS) (y := 1#usize)
      (by rw [bias_val]; simp; omega))
    have i5Is : i5.val = 2049 := by rw [i5Val, bias_val]; simp
    by_cases fits : i4.val < i5.val
    · have fitsB : i4 < i5 := by rw [UScalar.lt_equiv]; exact fits
      obtain ⟨i6, i6Run, i6Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i5) (y := pr) (by omega))
      obtain ⟨g, gRun, gVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i6) (y := down)
        (by rw [i6Val.1]; omega))
      obtain ⟨e, eRun, eLo, eHi⟩ := clamp g
      refine ⟨e, ?_, eLo, eHi⟩
      simp only [aboveB, ↓reduceIte, iRun, i1Run, i2Run, dRun, prRun, i4Run, i5Run, fitsB, i6Run, gRun, bind_ok]
      exact eRun
    · have fitsB : ¬ i4 < i5 := by rw [UScalar.lt_equiv]; exact fits
      obtain ⟨e, eRun, eLo, eHi⟩ := clamp 0#usize
      refine ⟨e, ?_, eLo, eHi⟩
      simp only [aboveB, ↓reduceIte, iRun, i1Run, i2Run, dRun, prRun, i4Run, i5Run, fitsB, bind_ok]
      exact eRun

/-- The number `digits × 10^(order − ORDER_BIAS − length)`. -/
noncomputable def exactValue (digits : List U8) (order : ℕ) : ℚ :=
  (digitsValue digits : ℚ) * 10 ^ ((order : ℤ) - 268435456 - digits.length)

/-- `exact` is the value of the number of the digits at the decimal order. -/
theorem exact_spec (digits : alloc.vec.Vec U8) (order : Usize) (negative double : Bool)
    (cd : Canonical digits.val) (nonempty : digits.val ≠ []) (short : digits.val.length ≤ 1100)
    (low : 268435456 ≤ order.val + 400) (high : order.val < 268435456 + 400) :
    ∃ b, floats.exact digits order negative double = .ok (some b) ∧ CanonicalBinary b ∧
      binaryOf b = roundBinary (fmt double)
        (if negative then -exactValue digits.val order.val else exactValue digits.val order.val) := by
  rw [floats.exact]
  have big : 4294967295 ≤ Usize.max := by scalar_tac
  have dpos : 0 < digitsValue digits.val := by
    have := (canonical_zero digits.val cd).not.mpr nonempty; omega
  obtain ⟨e, eRun, eLo, eHi⟩ := estimate_spec order double low high
  obtain ⟨i, iRun, iVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := floats.ORDER_BIAS)
    (y := alloc.vec.Vec.len digits) (by rw [order_bias_val]; simp; omega))
  have iIs : i.val = 268435456 + digits.val.length := by rw [iVal, order_bias_val]; simp
  have dLt := Rowl.Numbers.value_lt digits.val cd.1
  by_cases up : 268435456 + digits.val.length ≤ order.val
  · have upB : i ≤ order := by rw [UScalar.le_equiv, iIs]; exact up
    obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := order) (y := floats.ORDER_BIAS)
      (by rw [order_bias_val]; omega))
    have i1Is : i1.val = order.val - 268435456 := by rw [i1Val.1, order_bias_val]
    obtain ⟨sc, scRun, scVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i1) (y := alloc.vec.Vec.len digits)
      (by simp; omega))
    have scIs : sc.val = order.val - 268435456 - digits.val.length := by rw [scVal.1, i1Is]; simp
    have value : exactValue digits.val order.val = (digitsValue digits.val : ℚ) * 10 ^ sc.val := by
      unfold exactValue
      rw [show (order.val : ℤ) - 268435456 - digits.val.length = (sc.val : ℤ) by omega, zpow_natCast]
    rw [value]
    -- the wide path
    obtain ⟨n, nRun, cn, nVal, nLen⟩ := Rowl.Numbers.times_power_spec digits cd sc (by omega)
    obtain ⟨one, oneRun, oneVal⟩ := one_spec
    obtain ⟨wb, wRun, wCanon, wValue⟩ := wide_spec n one e negative double cn (by rw [oneVal]; exact one_canonical)
      (by rw [nVal]; positivity) (by rw [oneVal, one_value]; norm_num) eLo eHi (by rw [oneVal]; simp; omega)
    rw [nVal, oneVal, one_value] at wValue
    push_cast at wValue
    rw [div_one] at wValue
    by_cases quick : digits.val.length ≤ 17 ∧ sc.val ≤ 21
    · have lenB : alloc.vec.Vec.len digits ≤ 17#usize := by rw [UScalar.le_equiv]; simpa using quick.1
      have scB : sc ≤ 21#usize := by rw [UScalar.le_equiv]; simpa using quick.2
      have dSmall : digitsValue digits.val < 10 ^ 17 :=
        lt_of_lt_of_le dLt (Nat.pow_le_pow_right (by norm_num) quick.1)
      obtain ⟨d, dRun, dVal⟩ := native_value_spec digits cd.1 0#usize 0#u128 (by simp)
        (by simp [U128.max_eq]; omega)
      have dIs : d.val = digitsValue digits.val := by simpa using dVal
      obtain ⟨r, run, prop⟩ := native_spec d true sc e negative double (by omega)
        (fun _ => by
          rw [dIs]
          have : 10 ^ sc.val ≤ 10 ^ 21 := Nat.pow_le_pow_right (by norm_num) quick.2
          have : digitsValue digits.val * 10 ^ sc.val < 10 ^ 17 * 10 ^ 21 := by
            calc digitsValue digits.val * 10 ^ sc.val < 10 ^ 17 * 10 ^ sc.val :=
                  Nat.mul_lt_mul_of_pos_right dSmall (by positivity)
              _ ≤ 10 ^ 17 * 10 ^ 21 := Nat.mul_le_mul_left _ this
          omega)
        (by rw [dIs]; exact dpos) eLo eHi
      rcases r with _ | b
      · refine ⟨wb, ?_, wCanon, wValue⟩
        simp [iRun, iIs, up, i1Run, scRun, eRun, quick.1, quick.2, dRun, run, nRun, oneRun, wRun]
      · obtain ⟨canon, bValue⟩ := prop b rfl
        refine ⟨b, ?_, canon, ?_⟩
        · simp [iRun, iIs, up, i1Run, scRun, eRun, quick.1, quick.2, dRun, run]
        · rw [bValue, dIs]; simp
    · refine ⟨wb, ?_, wCanon, wValue⟩
      by_cases l17 : digits.val.length ≤ 17
      · have scB : ¬ sc.val ≤ 21 := fun h => quick ⟨l17, h⟩
        simp [iRun, iIs, up, i1Run, scRun, eRun, l17, scB, nRun, oneRun, wRun]
      · simp [iRun, iIs, up, i1Run, scRun, eRun, l17, nRun, oneRun, wRun]
  · have upB : ¬ i ≤ order := by rw [UScalar.le_equiv, iIs]; exact up
    obtain ⟨sc, scRun, scVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i) (y := order) (by omega))
    have scIs : sc.val = 268435456 + digits.val.length - order.val := by rw [scVal.1, iIs]
    have value : exactValue digits.val order.val = (digitsValue digits.val : ℚ) / 10 ^ sc.val := by
      unfold exactValue
      rw [show (order.val : ℤ) - 268435456 - digits.val.length = -(sc.val : ℤ) by omega, zpow_neg, zpow_natCast,
        div_eq_mul_inv]
    rw [value]
    obtain ⟨q, qRun, cq, qVal, qLen⟩ := Rowl.Numbers.ten_power_spec sc (by omega)
    obtain ⟨wb, wRun, wCanon, wValue⟩ := wide_spec digits q e negative double cd cq dpos
      (by rw [qVal]; positivity) eLo eHi (by omega)
    rw [qVal] at wValue
    push_cast at wValue
    by_cases quick : digits.val.length ≤ 17 ∧ sc.val ≤ 21
    · have lenB : alloc.vec.Vec.len digits ≤ 17#usize := by rw [UScalar.le_equiv]; simpa using quick.1
      have scB : sc ≤ 21#usize := by rw [UScalar.le_equiv]; simpa using quick.2
      have dSmall : digitsValue digits.val < 10 ^ 17 :=
        lt_of_lt_of_le dLt (Nat.pow_le_pow_right (by norm_num) quick.1)
      obtain ⟨d, dRun, dVal⟩ := native_value_spec digits cd.1 0#usize 0#u128 (by simp)
        (by simp [U128.max_eq]; omega)
      have dIs : d.val = digitsValue digits.val := by simpa using dVal
      obtain ⟨r, run, prop⟩ := native_spec d false sc e negative double (by omega) (fun h => by cases h)
        (by rw [dIs]; exact dpos) eLo eHi
      rcases r with _ | b
      · refine ⟨wb, ?_, wCanon, wValue⟩
        simp [iRun, iIs, up, scRun, eRun, quick.1, quick.2, dRun, run, qRun, wRun]
      · obtain ⟨canon, bValue⟩ := prop b rfl
        refine ⟨b, ?_, canon, ?_⟩
        · simp [iRun, iIs, up, scRun, eRun, quick.1, quick.2, dRun, run]
        · rw [bValue, dIs]; simp
    · refine ⟨wb, ?_, wCanon, wValue⟩
      by_cases l17 : digits.val.length ≤ 17
      · have scB : ¬ sc.val ≤ 21 := fun h => quick ⟨l17, h⟩
        simp [iRun, iIs, up, scRun, eRun, l17, scB, qRun, wRun]
      · simp [iRun, iIs, up, scRun, eRun, l17, qRun, wRun]

/-! ## Numbers past the format -/

/-- `floatingPointRound` gives an infinity for a number of `2^p × 2^eMax` or
    more. -/
theorem roundBinary_huge (double : Bool) {v : ℚ} (vne : v ≠ 0)
    (big : (2 : ℚ) ^ ((prec double : ℤ) + ((hi double : ℤ) - 2048)) ≤ abs v) :
    roundBinary (fmt double) v = .infinity (decide (v < 0)) := by
  have apos : 0 < abs v := abs_pos.mpr vne
  have := log_ge apos big
  unfold roundBinary
  rw [fmt_precision, fmt_most]
  rw [if_pos (by omega)]

/-- `floatingPointRound` gives a zero for a number below half the least
    positive value. -/
theorem roundBinary_tiny (double : Bool) {v : ℚ} (vne : v ≠ 0)
    (small : abs v < (2 : ℚ) ^ ((lo double : ℤ) - 2048 - 1)) :
    roundBinary (fmt double) v = .zero (decide (v < 0)) := by
  have apos : 0 < abs v := abs_pos.mpr vne
  have logLt := log_lt apos small
  have pPos := prec_pos double
  have loHi := lo_le_hi double
  unfold roundBinary
  rw [fmt_precision, fmt_most, fmt_least]
  rw [if_neg (by omega)]
  have eIs : max (Int.log 2 (abs v) - (prec double : ℤ) + 1) ((lo double : ℤ) - 2048) = (lo double : ℤ) - 2048 := by
    omega
  simp only [eIs]
  have spos : (0 : ℚ) < (2 : ℚ) ^ ((lo double : ℤ) - 2048) := zpow_pos (by norm_num) _
  have half : (2 : ℚ) ^ ((lo double : ℤ) - 2048 - 1) = (2 : ℚ) ^ ((lo double : ℤ) - 2048) / 2 := by
    rw [zpow_sub₀ (by norm_num), zpow_one]
  have ratio : abs v / (2 : ℚ) ^ ((lo double : ℤ) - 2048) < 1 / 2 := by
    rw [div_lt_iff₀ spos]; rw [half] at small; linarith
  have fl : Int.floor (abs v / (2 : ℚ) ^ ((lo double : ℤ) - 2048)) = 0 := by
    rw [Int.floor_eq_iff]; constructor
    · simp; positivity
    · push_cast; linarith
  rw [fl]
  rw [half] at small ⊢
  simp only [zero_add, Int.cast_one, one_mul]
  have notAbove : ¬ (2 : ℚ) ^ ((lo double : ℤ) - 2048) - (2 : ℚ) ^ ((lo double : ℤ) - 2048) / 2 < abs v := by
    intro h; linarith
  have below : abs v < (2 : ℚ) ^ ((lo double : ℤ) - 2048) - (2 : ℚ) ^ ((lo double : ℤ) - 2048) / 2 := by linarith
  rw [if_neg notAbove, if_pos below]
  simp

/-- The bounds of a number of `L` digits, the first not zero, times a power
    of ten. -/
theorem decimal_bounds (D L : ℕ) (E : ℤ) (low : 10 ^ (L - 1) ≤ D) (high : D < 10 ^ L) (Lpos : 1 ≤ L) :
    (10 : ℚ) ^ ((L : ℤ) - 1 + E) ≤ D * 10 ^ E ∧ (D : ℚ) * 10 ^ E < 10 ^ ((L : ℤ) + E) := by
  have tpos : (0 : ℚ) < 10 ^ E := zpow_pos (by norm_num) _
  constructor
  · rw [zpow_add₀ (by norm_num)]
    have : (10 : ℚ) ^ ((L : ℤ) - 1) ≤ D := by
      rw [show (L : ℤ) - 1 = ((L - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast low
    exact mul_le_mul_of_nonneg_right this tpos.le
  · rw [zpow_add₀ (by norm_num), zpow_natCast]
    have : (D : ℚ) < 10 ^ L := by exact_mod_cast high
    exact mul_lt_mul_of_pos_right this tpos

theorem ten_pow_mono {a b : ℤ} (h : a ≤ b) : (10 : ℚ) ^ a ≤ 10 ^ b := zpow_le_zpow_right₀ (by norm_num) h

set_option exponentiation.threshold 2048 in
/-- A number of decimal order 310 or more (40 for `xsd:float`) is past the
    greatest value. -/
theorem huge_of_order (double : Bool) {v : ℚ} {O : ℤ} (bound : (10 : ℚ) ^ (O - 1) ≤ abs v)
    (big : (if double then 310 else 40 : ℤ) ≤ O) :
    (2 : ℚ) ^ ((prec double : ℤ) + ((hi double : ℤ) - 2048)) ≤ abs v := by
  cases double
  · simp only [Bool.false_eq_true, ↓reduceIte] at big
    have : (10 : ℚ) ^ (39 : ℤ) ≤ 10 ^ (O - 1) := ten_pow_mono (by omega)
    have two : (2 : ℚ) ^ ((prec false : ℤ) + ((hi false : ℤ) - 2048)) ≤ 10 ^ (39 : ℤ) := by
      simp only [prec, hi, Bool.false_eq_true, ↓reduceIte]; norm_num
    linarith
  · simp only [↓reduceIte] at big
    have : (10 : ℚ) ^ (309 : ℤ) ≤ 10 ^ (O - 1) := ten_pow_mono (by omega)
    have two : (2 : ℚ) ^ ((prec true : ℤ) + ((hi true : ℤ) - 2048)) ≤ 10 ^ (309 : ℤ) := by
      simp only [prec, hi, ↓reduceIte]; norm_num
    linarith

set_option exponentiation.threshold 2048 in
/-- A number of decimal order −324 or less (−46 for `xsd:float`) is below half
    the least positive value. -/
theorem tiny_of_order (double : Bool) {v : ℚ} {O : ℤ} (bound : abs v < (10 : ℚ) ^ O)
    (small : O ≤ (if double then -324 else -46 : ℤ)) :
    abs v < (2 : ℚ) ^ ((lo double : ℤ) - 2048 - 1) := by
  cases double
  · simp only [Bool.false_eq_true, ↓reduceIte] at small
    have : (10 : ℚ) ^ O ≤ 10 ^ (-46 : ℤ) := ten_pow_mono small
    have two : (10 : ℚ) ^ (-46 : ℤ) ≤ (2 : ℚ) ^ ((lo false : ℤ) - 2048 - 1) := by
      simp only [lo, Bool.false_eq_true, ↓reduceIte]; norm_num
    linarith
  · simp only [↓reduceIte] at small
    have : (10 : ℚ) ^ O ≤ 10 ^ (-324 : ℤ) := ten_pow_mono small
    have two : (10 : ℚ) ^ (-324 : ℤ) ≤ (2 : ℚ) ^ ((lo true : ℤ) - 2048 - 1) := by
      simp only [lo, ↓reduceIte]; norm_num
    linarith

/-! ## The value of a numeral -/

/-- The bytes from `start` up to `finish`. -/
def span (bytes : List U8) (start finish : ℕ) : List U8 := (bytes.take finish).drop start

theorem over_spec (double : Bool) :
    ∃ r, floats.over double = .ok r ∧ r.val = 268435456 + (if double then 310 else 40) := by
  unfold floats.over
  cases double
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := floats.ORDER_BIAS) (y := 40#usize) (by simp [order_bias_val]; scalar_tac))
    exact ⟨r, by simp [run], by simp [order_bias_val] at value; simp; omega⟩
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := floats.ORDER_BIAS) (y := 310#usize) (by simp [order_bias_val]; scalar_tac))
    exact ⟨r, by simp [run], by simp [order_bias_val] at value; simp; omega⟩

theorem under_spec (double : Bool) :
    ∃ r, floats.under double = .ok r ∧ r.val = 268435456 - (if double then 324 else 46) := by
  unfold floats.under
  cases double
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := floats.ORDER_BIAS) (y := 46#usize) (by simp [order_bias_val]))
    exact ⟨r, by simp [run], by simp [order_bias_val] at value; simp; omega⟩
  · obtain ⟨r, run, value⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := floats.ORDER_BIAS) (y := 324#usize) (by simp [order_bias_val]))
    exact ⟨r, by simp [run], by simp [order_bias_val] at value; simp; omega⟩

/-- The value that a numeral with these digits and exponent gets: the zero of
    its sign for zero, and the rounding of its number otherwise. -/
noncomputable def numeralValue (double negative : Bool) (digits : List U8) (x : ℤ) (places : ℕ) : Binary :=
  if digitsValue digits = 0 then .zero negative
  else roundBinary (fmt double) ((if negative then -1 else 1) * (digitsValue digits : ℚ) * (10 : ℚ) ^ (x - places))

/-- `numeral_value` is the value of the numeral with the digits `whole` and
    `fraction` and the exponent, saturated at `SATURATED`. -/
theorem numeral_value_spec (lexical : alloc.vec.Vec U8) (ws we fs fe : Usize) (expNeg : Bool) (exponent : Usize)
    (x0 : ℕ) (negative double : Bool)
    (o1 : ws.val ≤ we.val) (o2 : we.val ≤ fs.val) (o3 : fs.val ≤ fe.val) (fits : fe.val ≤ lexical.val.length)
    (short : lexical.val.length < 1024)
    (dw : Digits (span lexical.val ws.val we.val)) (df : Digits (span lexical.val fs.val fe.val))
    (expIs : exponent.val = min x0 100000000) :
    ∃ b, floats.numeral_value lexical ws we fs fe expNeg exponent negative double = .ok (some b) ∧
      CanonicalBinary b ∧
      binaryOf b = numeralValue double negative (span lexical.val ws.val we.val ++ span lexical.val fs.val fe.val)
        (if expNeg then -(x0 : ℤ) else x0) (fe.val - fs.val) := by
  rw [floats.numeral_value]
  have big : 4294967295 ≤ Usize.max := by scalar_tac
  obtain ⟨v, vRun, vVal⟩ := Rowl.Moments.copy_span_spec lexical ws we (alloc.vec.Vec.new U8) (by omega)
    (by simp [new_val]; omega)
  have vIs : v.val = span lexical.val ws.val we.val := by rw [vVal, new_val]; rfl
  have spanLen : ∀ a b, a ≤ b → b ≤ lexical.val.length → (span lexical.val a b).length = b - a := by
    intro a b ab bl; simp [span]; omega
  obtain ⟨w, wRun, wVal⟩ := Rowl.Moments.copy_span_spec lexical fs fe v fits
    (by rw [vIs, spanLen _ _ o1 (by omega)]; omega)
  have wIs : w.val = span lexical.val ws.val we.val ++ span lexical.val fs.val fe.val := by rw [wVal, vIs]; rfl
  have dW : Digits w.val := by rw [wIs]; exact digits_append.mpr ⟨dw, df⟩
  obtain ⟨digits, dRun, cd, dVal, dLen⟩ := Rowl.Numbers.canonical_spec w dW
  have wLen : w.val.length ≤ 1024 := by
    rw [wIs, List.length_append, spanLen _ _ o1 (by omega), spanLen _ _ o3 fits]; omega
  set D := digitsValue (span lexical.val ws.val we.val ++ span lexical.val fs.val fe.val) with hD
  have dValue : digitsValue digits.val = D := by rw [dVal, wIs]
  by_cases empty : digits.val = []
  · have lenZero : alloc.vec.Vec.len digits = 0#usize := by rw [usize_eq_zero]; simp [empty]
    have zero : D = 0 := by rw [← dValue, empty, value_nil]
    refine ⟨.Finite negative 0#u64 floats.BIAS, by simp [vRun, wRun, dRun, lenZero], .inl ⟨by simp, bias_val⟩, ?_⟩
    simp [binaryOf, numeralValue, ← hD, zero]
  · have lenNot : ¬ alloc.vec.Vec.len digits = 0#usize := by
      rw [usize_eq_zero]; simp only [alloc.vec.Vec.len_val]; exact fun h => empty (List.eq_nil_of_length_eq_zero h)
    have Dpos : D ≠ 0 := by rw [← dValue]; exact (canonical_zero digits.val cd).not.mpr empty
    set L := digits.val.length with hL
    have Lpos : 1 ≤ L := List.length_pos_of_ne_nil empty
    have Dlow : 10 ^ (L - 1) ≤ D := by rw [← dValue]; exact canonical_low _ cd empty
    have Dhigh : D < 10 ^ L := by rw [← dValue]; exact Rowl.Numbers.value_lt _ cd.1
    set F := fe.val - fs.val with hF
    have Fle : F ≤ 1024 := by omega
    have Lle : L ≤ 1024 := by omega
    have expLe : exponent.val ≤ 100000000 := by rw [expIs]; exact min_le_right _ _
    obtain ⟨fr, frRun, frVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := fe) (y := fs) o3)
    have frIs : fr.val = F := frVal.1
    -- the decimal order, biased
    obtain ⟨order, orderRun, orderIs⟩ : ∃ order : Usize, (if expNeg then do
          let i1 := alloc.vec.Vec.len digits
          let i2 ← floats.ORDER_BIAS + i1
          let i3 ← i2 - fr
          i3 - exponent
        else do
          let i1 := alloc.vec.Vec.len digits
          let i2 ← floats.ORDER_BIAS + i1
          let i3 ← i2 + exponent
          i3 - fr : Result Usize) = .ok order ∧
        (order.val : ℤ) = 268435456 + L + (if expNeg then -(exponent.val : ℤ) else exponent.val) - F := by
      obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := floats.ORDER_BIAS)
        (y := alloc.vec.Vec.len digits) (by rw [order_bias_val]; simp; omega))
      have i2Is : i2.val = 268435456 + L := by rw [i2Val, order_bias_val]; simp [hL]
      cases expNeg
      · obtain ⟨i3, i3Run, i3Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := i2) (y := exponent)
          (by rw [i2Is]; omega))
        obtain ⟨o, oRun, oVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i3) (y := fr)
          (by rw [i3Val, i2Is, frIs]; omega))
        refine ⟨o, by simp [i2Run, i3Run, oRun], ?_⟩
        rw [oVal.1, i3Val, i2Is, frIs]; simp; omega
      · obtain ⟨i3, i3Run, i3Val⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i2) (y := fr)
          (by rw [i2Is, frIs]; omega))
        obtain ⟨o, oRun, oVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := i3) (y := exponent)
          (by rw [i3Val.1, i2Is, frIs]; omega))
        refine ⟨o, by simp [i2Run, i3Run, oRun], ?_⟩
        rw [oVal.1, i3Val.1, i2Is, frIs]; simp; omega
    -- the number and its bounds
    set X : ℤ := if expNeg then -(x0 : ℤ) else x0 with hX
    set val : ℚ := (if negative then -1 else 1) * (D : ℚ) * (10 : ℚ) ^ (X - (F : ℤ)) with hval
    have valNe : val ≠ 0 := by
      rw [hval]
      have : (D : ℚ) ≠ 0 := by exact_mod_cast Dpos
      have tz : (10 : ℚ) ^ (X - (F : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
      cases negative <;> simp [this, tz]
    have absVal : abs val = (D : ℚ) * 10 ^ (X - (F : ℤ)) := by
      rw [hval]; cases negative <;> simp [abs_of_nonneg, abs_mul, zpow_nonneg]
    have signVal : decide (val < 0) = negative := by
      rw [hval]
      have : (0 : ℚ) < (D : ℚ) * 10 ^ (X - (F : ℤ)) := by
        have : (0 : ℚ) < D := by exact_mod_cast Nat.pos_of_ne_zero Dpos
        exact mul_pos this (zpow_pos (by norm_num) _)
      cases negative <;> simp [this, not_lt.mpr this.le]
    obtain ⟨bLow, bHigh⟩ := decimal_bounds D L (X - F) Dlow Dhigh Lpos
    have valueIs : numeralValue double negative (span lexical.val ws.val we.val ++ span lexical.val fs.val fe.val)
        X F = roundBinary (fmt double) val := by
      simp only [numeralValue, ← hD, Dpos, ↓reduceIte, hval]
    rw [valueIs]
    obtain ⟨ov, ovRun, ovVal⟩ := over_spec double
    obtain ⟨un, unRun, unVal⟩ := under_spec double
    have dblBound : (if double then 310 else 40 : ℕ) ≤ 310 := by split <;> omega
    have dblUnder : (if double then 324 else 46 : ℕ) ≤ 324 := by split <;> omega
    by_cases over : ov.val ≤ order.val
    · -- past the greatest value
      have overB : ov ≤ order := by rw [UScalar.le_equiv]; exact over
      refine ⟨.Infinite negative, ?_, trivial, ?_⟩
      · simp only [vRun, wRun, dRun, bind_ok, lenNot, ↓reduceIte, frRun, orderRun, ovRun, overB]
      · have orderBig : (if double then 310 else 40 : ℤ) ≤ (L : ℤ) + X - F := by
          have hov : (ov.val : ℤ) = 268435456 + (if double then 310 else 40 : ℕ) := by rw [ovVal]; push_cast; rfl
          have := expIs
          rcases Nat.lt_or_ge x0 100000000 with sat | sat
          · rw [Nat.min_eq_left sat.le] at this
            cases expNeg <;> cases double <;> simp_all <;> omega
          · rw [Nat.min_eq_right sat] at this
            cases expNeg <;> cases double <;> simp_all <;> omega
        have huge := huge_of_order double (O := (L : ℤ) + X - F) (by rw [absVal]; convert bLow using 2; ring)
          (by convert orderBig using 1)
        rw [roundBinary_huge double valNe huge, signVal]
        rfl
    · have overB : ¬ ov ≤ order := by rw [UScalar.le_equiv]; exact over
      by_cases under : order.val ≤ un.val
      · have underB : order ≤ un := by rw [UScalar.le_equiv]; exact under
        refine ⟨.Finite negative 0#u64 floats.BIAS, ?_, .inl ⟨by simp, bias_val⟩, ?_⟩
        · simp only [vRun, wRun, dRun, bind_ok, lenNot, ↓reduceIte, frRun, orderRun, ovRun, overB, unRun, underB]
        · have orderSmall : (L : ℤ) + X - F ≤ (if double then -324 else -46 : ℤ) := by
            have hun : (un.val : ℤ) = 268435456 - (if double then 324 else 46 : ℕ) := by
              rw [unVal]; push_cast [Nat.cast_sub (show (if double then 324 else 46 : ℕ) ≤ 268435456 by split <;> omega)]
              rfl
            have := expIs
            rcases Nat.lt_or_ge x0 100000000 with sat | sat
            · rw [Nat.min_eq_left sat.le] at this
              cases expNeg <;> cases double <;> simp_all <;> omega
            · rw [Nat.min_eq_right sat] at this
              cases expNeg <;> cases double <;> simp_all <;> omega
          have tiny := tiny_of_order double (O := (L : ℤ) + X - F) (by rw [absVal]; convert bHigh using 2; ring)
            orderSmall
          rw [roundBinary_tiny double valNe tiny, signVal]
          simp [binaryOf]
      · have underB : ¬ order ≤ un := by rw [UScalar.le_equiv]; exact under
        -- within the format: the exponent is not saturated
        have notSat : x0 < 100000000 := by
          by_contra sat
          have sat' : 100000000 ≤ x0 := by omega
          have := expIs
          rw [Nat.min_eq_right sat'] at this
          have hov : (ov.val : ℤ) = 268435456 + (if double then 310 else 40 : ℕ) := by rw [ovVal]; push_cast; rfl
          have hun : (un.val : ℤ) = 268435456 - (if double then 324 else 46 : ℕ) := by
            rw [unVal]; push_cast [Nat.cast_sub (show (if double then 324 else 46 : ℕ) ≤ 268435456 by split <;> omega)]
            rfl
          cases expNeg <;> cases double <;> simp_all <;> omega
        have expEq : exponent.val = x0 := by rw [expIs]; exact Nat.min_eq_left notSat.le
        have orderEq : (order.val : ℤ) = 268435456 + L + X - F := by
          rw [orderIs, hX, expEq]
        have orderLow : 268435456 ≤ order.val + 400 := by
          have : (un.val : ℤ) = 268435456 - (if double then 324 else 46 : ℕ) := by
            rw [unVal]; push_cast [Nat.cast_sub (show (if double then 324 else 46 : ℕ) ≤ 268435456 by split <;> omega)]
            rfl
          omega
        have orderHigh : order.val < 268435456 + 400 := by
          have : (ov.val : ℤ) = 268435456 + (if double then 310 else 40 : ℕ) := by rw [ovVal]; push_cast; rfl
          omega
        obtain ⟨fin, finRun, finLow, finHigh, zeros, stop⟩ := Rowl.Moments.trimmed_end_spec digits 0#usize
          (alloc.vec.Vec.len digits) (by simp) (by simp)
        have finPos : 1 ≤ fin.val := by
          by_contra none
          have fin0 : fin.val = 0 := by omega
          have headZero := zeros (digits.val.head empty) (by
            rw [fin0]
            show digits.val.head empty ∈ (digits.val.take (alloc.vec.Vec.len digits).val).drop 0
            simp [List.head_mem])
          exact cd.2 (by rw [List.head?_eq_some_head empty, headZero])
        obtain ⟨v1, v1Run, v1Val⟩ := Rowl.Moments.copy_span_spec digits 0#usize fin (alloc.vec.Vec.new U8)
          (by simp at finHigh ⊢; omega) (by simp [new_val]; simp at finHigh; omega)
        have v1Is : v1.val = digits.val.take fin.val := by rw [v1Val, new_val]; simp; rfl
        have finLe : fin.val ≤ L := by simpa using finHigh
        have split : digits.val = digits.val.take fin.val ++ digits.val.drop fin.val := (List.take_append_drop _ _).symm
        have dropZeros : ∀ b ∈ digits.val.drop fin.val, b = 48#u8 := by
          intro b mem
          apply zeros b
          show b ∈ (digits.val.take (alloc.vec.Vec.len digits).val).drop fin.val
          simpa using mem
        have dropValue : digitsValue (digits.val.drop fin.val) = 0 :=
          (Rowl.Moments.digitsValue_zero_iff _ (Rowl.Numbers.digits_drop cd.1 _)).mpr dropZeros
        have Dsplit : D = digitsValue v1.val * 10 ^ (L - fin.val) := by
          rw [← dValue, split, Rowl.Numbers.value_append, dropValue, v1Is]; simp; left; omega
        have cv1 : Canonical v1.val := by
          rw [v1Is]
          refine ⟨Rowl.Numbers.digits_take cd.1 _, ?_⟩
          have : digits.val.take fin.val ≠ [] := by simp; constructor <;> omega
          rw [List.head?_take]
          simp only [show fin.val ≠ 0 by omega, ↓reduceIte]
          exact cd.2
        have v1Ne : v1.val ≠ [] := by rw [v1Is]; simp; constructor <;> omega
        have v1Len : v1.val.length = fin.val := by rw [v1Is]; simp; omega
        obtain ⟨b, bRun, bCanon, bValue⟩ := exact_spec v1 order negative double cv1 v1Ne (by omega) orderLow
          orderHigh
        refine ⟨b, ?_, bCanon, ?_⟩
        · simp only [vRun, wRun, dRun, bind_ok, lenNot, ↓reduceIte, frRun, orderRun, ovRun, overB, unRun, underB,
            finRun, v1Run, bRun]
        · rw [bValue]
          congr 1
          have ex : exactValue v1.val order.val = (D : ℚ) * 10 ^ (X - (F : ℤ)) := by
            unfold exactValue
            rw [Dsplit, v1Len, orderEq]
            push_cast
            rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
            congr 2
            push_cast [Nat.cast_sub finLe]
            ring
          rw [ex, hval]
          cases negative <;> simp

/-! ## Reading a lexical form -/

theorem span_cons (bytes : List U8) (start finish : ℕ) (before : start < finish) (fits : finish ≤ bytes.length) :
    span bytes start finish = bytes[start]'(by omega) :: span bytes (start + 1) finish := by
  unfold span
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp

theorem span_empty (bytes : List U8) (start finish : ℕ) (h : finish ≤ start) : span bytes start finish = [] := by
  unfold span; simp; omega

theorem span_length (bytes : List U8) (start finish : ℕ) (fits : finish ≤ bytes.length) :
    (span bytes start finish).length = finish - start := by
  unfold span; simp; omega

theorem small_value_spec (bytes : alloc.vec.Vec U8) (index fin total : Usize)
    (inside : index.val ≤ fin.val) (fits : fin.val ≤ bytes.val.length)
    (dd : Digits (span bytes.val index.val fin.val)) (totalLe : total.val ≤ 1000000009) :
    ∃ r, floats.small_value bytes index fin total = .ok r ∧
      r.val = min (total.val * 10 ^ (fin.val - index.val) + digitsValue (span bytes.val index.val fin.val)) 100000000 := by
  rw [floats.small_value]
  have big : 4294967295 ≤ Usize.max := by scalar_tac
  by_cases before : index.val < fin.val
  · have finLe : fin ≤ alloc.vec.Vec.len bytes := by rw [UScalar.le_equiv]; simpa using fits
    have inside' : index.val < bytes.val.length := by omega
    have spanIs := span_cons bytes.val index.val fin.val before fits
    have dig : Digit bytes.val[index.val] := dd _ (by rw [spanIs]; simp)
    have restDigits : Digits (span bytes.val (index.val + 1) fin.val) := by
      intro b mem; exact dd b (by rw [spanIs]; simp [mem])
    have restLen := span_length bytes.val (index.val + 1) fin.val fits
    have restLt := Rowl.Numbers.value_lt _ restDigits
    rw [restLen] at restLt
    have valueIs : digitsValue (span bytes.val index.val fin.val) =
        (bytes.val[index.val].val - 48) * 10 ^ (fin.val - (index.val + 1)) +
          digitsValue (span bytes.val (index.val + 1) fin.val) := by
      rw [spanIs, Rowl.Numbers.value_cons, restLen]
    have powEq : 10 ^ (fin.val - index.val) = 10 * 10 ^ (fin.val - (index.val + 1)) := by
      rw [← pow_succ']; congr 1; omega
    by_cases under : total.val < 100000000
    · have underB : total < floats.SATURATED := by rw [UScalar.lt_equiv, saturated_val]; exact under
      have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside']
      obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have i1Is : i1.val = index.val + 1 := by simpa using i1Val
      obtain ⟨i2, i2Run, i2Val⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := 10#usize) (y := total)
        (by simp [UScalar.max_USize_eq]; omega))
      have i2Is : i2.val = 10 * total.val := by simpa using i2Val
      obtain ⟨i4, i4Run, i4Val⟩ := WP.spec_imp_exists (U8.sub_spec (x := bytes.val[index.val]) (y := 48#u8)
        (by simpa using dig.1))
      have i4Is : i4.val = bytes.val[index.val].val - 48 := by simpa using i4Val.1
      have castIs : (UScalar.cast .Usize i4).val = i4.val := by simp
      have digLe : bytes.val[index.val].val - 48 ≤ 9 := by have := dig.2; omega
      obtain ⟨i6, i6Run, i6Val⟩ := WP.spec_imp_exists (UScalar.add_spec (x := i2) (y := UScalar.cast .Usize i4)
        (by rw [castIs, i4Is, i2Is]; simp [UScalar.max_USize_eq]; omega))
      have i6Is : i6.val = 10 * total.val + (bytes.val[index.val].val - 48) := by rw [i6Val, castIs, i4Is, i2Is]
      obtain ⟨r, run, value⟩ := small_value_spec bytes i1 fin i6 (by omega) fits (by rw [i1Is]; exact restDigits)
        (by rw [i6Is]; omega)
      refine ⟨r, by simp [before, finLe, underB, i1Run, i2Run, alloc.vec.Vec.index_slice_index, lookup, i4Run, lift,
        i6Run, run], ?_⟩
      rw [value, i6Is, i1Is, valueIs, powEq]
      congr 1
      ring
    · have underB : ¬ total < floats.SATURATED := by rw [UScalar.lt_equiv, saturated_val]; exact under
      refine ⟨floats.SATURATED, by simp [before, finLe, underB], ?_⟩
      rw [saturated_val]
      have : 100000000 ≤ total.val * 10 ^ (fin.val - index.val) := by
        have := Nat.one_le_pow (fin.val - index.val) 10 (by norm_num)
        nlinarith
      omega
  · have same : fin.val ≤ index.val := by omega
    rw [span_empty _ _ _ same, value_nil, show fin.val - index.val = 0 by omega]
    by_cases under : total.val < 100000000
    · have underB : total < floats.SATURATED := by rw [UScalar.lt_equiv, saturated_val]; exact under
      exact ⟨total, by simp [before, underB], by simp; omega⟩
    · have underB : ¬ total < floats.SATURATED := by rw [UScalar.lt_equiv, saturated_val]; exact under
      exact ⟨floats.SATURATED, by simp [before, underB], by rw [saturated_val]; simp; omega⟩
termination_by fin.val - index.val
decreasing_by omega

theorem rest_is_spec (bytes : alloc.vec.Vec U8) (index : Usize) (word : Slice U8) (pos : Usize)
    (exact : bytes.val.length = index.val + word.val.length) (posLe : pos.val ≤ word.val.length) :
    floats.rest_is bytes index word pos =
      .ok (decide (bytes.val.drop (index.val + pos.val) = word.val.drop pos.val)) := by
  rw [floats.rest_is]
  have big : bytes.val.length ≤ Usize.max := by scalar_tac
  by_cases before : pos.val < word.val.length
  · have beforeB : pos < Slice.len word := by rw [UScalar.lt_equiv, Slice.len_val]; exact before
    have inside : index.val + pos.val < bytes.val.length := by omega
    obtain ⟨i1, i1Run, i1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := pos) (by omega))
    have i1Is : i1.val = index.val + pos.val := by simpa using i1Val
    have insideB : i1 < alloc.vec.Vec.len bytes := by rw [UScalar.lt_equiv, i1Is]; simp; omega
    have lookup : bytes.index_usize i1 = .ok bytes.val[index.val + pos.val] := by
      simp [alloc.vec.Vec.index_usize, i1Is, List.getElem?_eq_getElem inside]
    have wordLookup : word.index_usize pos = .ok word.val[pos.val] := by
      have := Slice.index_usize_spec word pos before
      obtain ⟨x, run, value⟩ := WP.spec_imp_exists this
      rw [run, value]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem before]; rfl
    have dropB := List.drop_eq_getElem_cons inside
    have dropW := List.drop_eq_getElem_cons before
    by_cases same : bytes.val[index.val + pos.val] = word.val[pos.val]
    · obtain ⟨a1, a1Run, a1Val⟩ := WP.spec_imp_exists (Usize.add_spec (x := pos) (y := 1#usize) (by simp; omega))
      have a1Is : a1.val = pos.val + 1 := by simpa using a1Val
      have rest := rest_is_spec bytes index word a1 exact (by omega)
      have iff : (bytes.val.drop (index.val + pos.val) = word.val.drop pos.val) ↔
          (bytes.val.drop (index.val + a1.val) = word.val.drop a1.val) := by
        rw [dropB, dropW, same, a1Is, show index.val + (pos.val + 1) = index.val + pos.val + 1 by omega]
        simp only [List.cons.injEq]
        exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
      simp only [beforeB, ↓reduceIte, i1Run, insideB, bind_ok, alloc.vec.Vec.index_slice_index, lookup,
        wordLookup, same, a1Run, rest]
      simp only [iff]
    · have differ : ¬ (bytes.val.drop (index.val + pos.val) = word.val.drop pos.val) := by
        rw [dropB, dropW]; intro h; exact same (List.cons.inj h).1
      simp only [beforeB, ↓reduceIte, i1Run, insideB, bind_ok, alloc.vec.Vec.index_slice_index, lookup,
        wordLookup, same, differ, decide_false]
  · have beforeB : ¬ pos < Slice.len word := by rw [UScalar.lt_equiv, Slice.len_val]; exact before
    simp only [beforeB, ↓reduceIte]
    have e1 : bytes.val.drop (index.val + pos.val) = [] := by simp; omega
    have e2 : word.val.drop pos.val = [] := by simp; omega
    simp [e1, e2]
termination_by word.val.length - pos.val
decreasing_by omega

theorem word_at_spec (bytes : alloc.vec.Vec U8) (index : Usize) (word : Slice U8)
    (inside : index.val ≤ bytes.val.length) :
    floats.word_at bytes index word = .ok (decide (bytes.val.drop index.val = word.val)) := by
  rw [floats.word_at]
  have insideB : index ≤ alloc.vec.Vec.len bytes := by rw [UScalar.le_equiv]; simpa using inside
  obtain ⟨d, dRun, dVal⟩ := WP.spec_imp_exists (Usize.sub_spec (x := alloc.vec.Vec.len bytes) (y := index)
    (by simpa using inside))
  have dIs : d.val = bytes.val.length - index.val := by simpa using dVal.1
  by_cases same : bytes.val.length - index.val = word.val.length
  · have sameB : d = Slice.len word := by rw [UScalar.eq_equiv, dIs, Slice.len_val]; exact same
    have rest := rest_is_spec bytes index word 0#usize (by omega) (by simp)
    simp only [insideB, ↓reduceIte, dRun, bind_ok, sameB, rest]
    simp
  · have sameB : ¬ d = Slice.len word := by rw [UScalar.eq_equiv, dIs, Slice.len_val]; exact same
    simp only [insideB, ↓reduceIte, dRun, bind_ok, sameB]
    have : bytes.val.drop index.val ≠ word.val := by
      intro h; apply same; rw [← h]; simp
    simp [this]

/-- `digits_end` stops right after a run of digits that is followed by a byte
    that is not a digit, or by the end. -/
theorem digits_end_exact (bytes : alloc.vec.Vec U8) (index : Usize) (n : ℕ) (fits : index.val + n ≤ bytes.val.length)
    (run : ∀ i (h : i < bytes.val.length), index.val ≤ i → i < index.val + n → Digit bytes.val[i])
    (stop : ∀ h : index.val + n < bytes.val.length, ¬ Digit bytes.val[index.val + n]) :
    ∃ r, moments.digits_end bytes index = .ok r ∧ r.val = index.val + n := by
  obtain ⟨r, rRun, low, high, digits, rStop⟩ := Rowl.Moments.digits_end_spec bytes index (by omega)
  refine ⟨r, rRun, ?_⟩
  by_contra differ
  rcases Nat.lt_or_gt_of_ne differ with less | more
  · exact rStop (by omega) (run r.val (by omega) low less)
  · exact stop (by omega) (digits (index.val + n) (by omega) (by omega) more)

theorem span_to_end (bytes : List U8) (start : ℕ) : span bytes start bytes.length = bytes.drop start := by
  simp [span]

theorem u8_eq_iff (x y : U8) : x = y ↔ x.val = y.val :=
  ⟨fun h => by rw [h], fun h => UScalar.eq_of_val_eq h⟩

theorem vec_lookup (v : alloc.vec.Vec U8) (i : Usize) (h : i.val < v.val.length) :
    v.index_usize i = .ok (v.val[i.val]'h) := by
  simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]

theorem vec_lookup2 (v : alloc.vec.Vec U8) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) v i = .ok (v.val[i.val]'h) := by
  simp only [alloc.vec.Vec.index_slice_index, vec_lookup v i h]

/-- The digits of an exponent: `digits_end` reaches the end exactly when the
    rest is a nonempty run of digits. -/
theorem exponent_digits (lexical : alloc.vec.Vec U8) (es : Usize) (inside : es.val ≤ lexical.val.length) :
    ∃ ee, moments.digits_end lexical es = .ok ee ∧ es.val ≤ ee.val ∧ ee.val ≤ lexical.val.length ∧
      ((es.val < ee.val ∧ ee.val = lexical.val.length) ↔
        (lexical.val.drop es.val ≠ [] ∧ Digits (lexical.val.drop es.val))) := by
  obtain ⟨ee, run, low, high, digits, stop⟩ := Rowl.Moments.digits_end_spec lexical es inside
  refine ⟨ee, run, low, high, ⟨fun ⟨lt, eq⟩ => ⟨?_, ?_⟩, fun ⟨ne, dd⟩ => ?_⟩⟩
  · simp; omega
  · intro b mem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
    simp only [List.length_drop] at hi
    rw [List.getElem_drop]
    exact digits _ (by omega) (by omega) (by omega)
  · have esLt : es.val < lexical.val.length := by
      by_contra h; apply ne; simp; omega
    by_contra notEnd
    have eeLt : ee.val < lexical.val.length := by
      rcases Nat.lt_or_ge ee.val lexical.val.length with h | h
      · exact h
      · exfalso; apply notEnd; refine ⟨?_, by omega⟩
        by_contra same
        have : ee.val = es.val := by omega
        exact stop (by omega) (by
          have := dd (lexical.val[ee.val]'(by omega)) (by
            rw [List.mem_iff_getElem]
            exact ⟨ee.val - es.val, by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩)
          exact this)
    exact stop eeLt (dd _ (by
      rw [List.mem_iff_getElem]
      exact ⟨ee.val - es.val, by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩))

/-- The digits and exponent of a numeral, read from the positions. -/
noncomputable def positionValue (double negative : Bool) (l : List U8) (ws we fs fe : ℕ) (x : ℤ) : Binary :=
  numeralValue double negative (span l ws we ++ span l fs fe) x (fe - fs)

/-- The end of `numeral`, from the digits on: the exponent. -/
theorem exponent_tail_spec (lexical : alloc.vec.Vec U8) (start whole_end fraction_start fraction_end : Usize)
    (negative double : Bool)
    (o1 : start.val ≤ whole_end.val) (o2 : whole_end.val ≤ fraction_start.val)
    (o3 : fraction_start.val ≤ fraction_end.val) (fits : fraction_end.val ≤ lexical.val.length)
    (short : lexical.val.length < 1024)
    (dw : Digits (span lexical.val start.val whole_end.val))
    (df : Digits (span lexical.val fraction_start.val fraction_end.val)) :
    ∃ r, (do
      let i1 := alloc.vec.Vec.len lexical
      if fraction_end < i1
      then
        let mark ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U8)
            lexical fraction_end
        if (mark = 69#u8) || (mark = 101#u8)
        then
          let sign_at ← fraction_end + 1#usize
          let i2 := alloc.vec.Vec.len lexical
          let signed ←
            if sign_at < i2
            then
              do
              let i3 ←
                alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                  Std.U8) lexical sign_at
              ok ((i3 = 45#u8) || (i3 = 43#u8))
            else ok false
          let i3 := alloc.vec.Vec.len lexical
          let exponent_negative ←
            if sign_at < i3
            then
              do
              let i4 ←
                alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                  Std.U8) lexical sign_at
              ok (i4 = 45#u8)
            else ok false
          let exponent_start ← if signed
                                 then sign_at + 1#usize
                                 else ok sign_at
          let exponent_end ← moments.digits_end lexical exponent_start
          if exponent_start < exponent_end
          then
            let i4 := alloc.vec.Vec.len lexical
            if exponent_end = i4
            then
              let i5 ←
                floats.small_value lexical exponent_start exponent_end 0#usize
              floats.numeral_value lexical start whole_end fraction_start
                fraction_end exponent_negative i5 negative double
            else ok none
          else ok none
        else ok none
      else
        floats.numeral_value lexical start whole_end fraction_start fraction_end
          false 0#usize negative double : Result (Option datatypes.Binary)) = .ok r ∧
      (∀ b, r = some b → CanonicalBinary b ∧ ∃ x, ExponentForm (lexical.val.drop fraction_end.val) x ∧
        binaryOf b = positionValue double negative lexical.val start.val whole_end.val fraction_start.val
          fraction_end.val x) ∧
      (∀ x, ExponentForm (lexical.val.drop fraction_end.val) x → ∃ b, r = some b ∧
        binaryOf b = positionValue double negative lexical.val start.val whole_end.val fraction_start.val
          fraction_end.val x) := by
  have big : 4294967295 ≤ Usize.max := by scalar_tac
  by_cases more : fraction_end.val < lexical.val.length
  · have moreB : fraction_end < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simpa using more
    have lookupMark := vec_lookup2 lexical fraction_end more
    have dropFe := List.drop_eq_getElem_cons more
    by_cases isE : (lexical.val[fraction_end.val]'more) = 69#u8 ∨ (lexical.val[fraction_end.val]'more) = 101#u8
    · obtain ⟨sa, saRun, saVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := fraction_end) (y := 1#usize)
        (by simp; omega))
      have saIs : sa.val = fraction_end.val + 1 := by simpa using saVal
      -- the sign of the exponent, and where its digits start
      obtain ⟨signed, expNeg, es, signedRun, negRun, esRun, esLe, esIs, shape⟩ :
          ∃ (signed expNeg : Bool) (es : Usize),
            (if sa < alloc.vec.Vec.len lexical then do
                let i3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U8) lexical sa
                ok ((i3 = 45#u8) || (i3 = 43#u8))
              else ok false : Result Bool) = .ok signed ∧
            (if sa < alloc.vec.Vec.len lexical then do
                let i4 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U8) lexical sa
                ok (decide (i4 = 45#u8))
              else ok false : Result Bool) = .ok expNeg ∧
            (if signed then sa + 1#usize else ok sa : Result Usize) = .ok es ∧
            es.val ≤ lexical.val.length ∧ es.val = sa.val + (if signed then 1 else 0) ∧
            ∃ sign, SignForm sign expNeg ∧ lexical.val.drop sa.val = sign ++ lexical.val.drop es.val ∧
              (∀ sign' neg' rest', SignForm sign' neg' → lexical.val.drop sa.val = sign' ++ rest' →
                rest' ≠ [] → Digits rest' → sign' = sign ∧ neg' = expNeg ∧ rest' = lexical.val.drop es.val) := by
        by_cases sInside : sa.val < lexical.val.length
        · have lookupS := vec_lookup2 lexical sa sInside
          have dropSa := List.drop_eq_getElem_cons sInside
          by_cases plus : (lexical.val[sa.val]'sInside) = 45#u8 ∨ (lexical.val[sa.val]'sInside) = 43#u8
          · obtain ⟨es, esRun, esVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := sa) (y := 1#usize) (by simp; omega))
            have esIs : es.val = sa.val + 1 := by simpa using esVal
            refine ⟨true, decide ((lexical.val[sa.val]'sInside) = 45#u8), es, ?_, ?_, by simp [esRun], by omega,
              by simp [esIs], [(lexical.val[sa.val]'sInside)], ?_, ?_, ?_⟩
            · simp only [show sa < alloc.vec.Vec.len lexical from by rw [UScalar.lt_equiv]; simpa using sInside,
                ↓reduceIte, lookupS, bind_ok]
              simpa using plus
            · simp only [show sa < alloc.vec.Vec.len lexical from by rw [UScalar.lt_equiv]; simpa using sInside,
                ↓reduceIte, lookupS, bind_ok]
            · rcases plus with h | h
              · right; right; exact ⟨by rw [h], by simp [h]⟩
              · right; left; exact ⟨by rw [h], by simp [h]⟩
            · rw [dropSa, esIs]; rfl
            · intro sign' neg' rest' form split ne dd
              rw [dropSa] at split
              rcases form with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exfalso
                simp only [List.nil_append] at split
                have := dd (lexical.val[sa.val]'sInside) (by rw [← split]; exact List.mem_cons_self ..)
                rcases plus with h | h <;> rw [h] at this <;> simp [Digit] at this
              · simp only [List.singleton_append, List.cons.injEq] at split
                refine ⟨by rw [split.1], ?_, by rw [esIs]; exact split.2.symm⟩
                rw [split.1]; simp
              · simp only [List.singleton_append, List.cons.injEq] at split
                refine ⟨by rw [split.1], ?_, by rw [esIs]; exact split.2.symm⟩
                rw [split.1]; simp
          · have notMinus : ¬ (lexical.val[sa.val]'sInside) = 45#u8 := fun h => plus (.inl h)
            refine ⟨false, false, sa, ?_, ?_, by simp, by omega, by simp, [], .inl ⟨rfl, rfl⟩, by simp, ?_⟩
            · simp only [show sa < alloc.vec.Vec.len lexical from by rw [UScalar.lt_equiv]; simpa using sInside,
                ↓reduceIte, lookupS, bind_ok]
              simpa using plus
            · simp only [show sa < alloc.vec.Vec.len lexical from by rw [UScalar.lt_equiv]; simpa using sInside,
                ↓reduceIte, lookupS, bind_ok]
              simpa using notMinus
            · intro sign' neg' rest' form split ne dd
              rw [dropSa] at split
              rcases form with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · simp only [List.nil_append] at split
                exact ⟨rfl, rfl, by rw [dropSa]; exact split.symm⟩
              · simp only [List.singleton_append, List.cons.injEq] at split
                exact absurd split.1 (fun h => plus (.inr h))
              · simp only [List.singleton_append, List.cons.injEq] at split
                exact absurd split.1 notMinus
        · have notInside : ¬ sa < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simpa using sInside
          refine ⟨false, false, sa, by simp only [notInside, ↓reduceIte], by simp only [notInside, ↓reduceIte],
            by simp, by omega, by simp, [], .inl ⟨rfl, rfl⟩, by simp, ?_⟩
          intro sign' neg' rest' form split ne dd
          have : lexical.val.drop sa.val = [] := by simp; omega
          rw [this] at split
          exact absurd (List.append_eq_nil_iff.mp split.symm).2 ne
      obtain ⟨ee, eeRun, eeLow, eeHigh, eeIff⟩ := exponent_digits lexical es esLe
      obtain ⟨sign, signForm, dropSplit, unique⟩ := shape
      have dropMark : lexical.val.drop fraction_end.val =
          lexical.val[fraction_end.val] :: (sign ++ lexical.val.drop es.val) := by
        rw [dropFe, ← saIs, dropSplit]; rfl
      by_cases good : es.val < ee.val ∧ ee.val = lexical.val.length
      · have goodLt : es < ee := by rw [UScalar.lt_equiv]; exact good.1
        have goodEq : ee = alloc.vec.Vec.len lexical := by rw [UScalar.eq_equiv]; simpa using good.2
        have goodLt2 : es < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simp; omega
        obtain ⟨ne, dd⟩ := eeIff.mp good
        have spanIs : span lexical.val es.val ee.val = lexical.val.drop es.val := by
          rw [good.2, span_to_end]
        obtain ⟨x0, x0Run, x0Val⟩ := small_value_spec lexical es ee 0#usize (by omega) eeHigh
          (by rw [spanIs]; exact dd) (by simp)
        set X0 := digitsValue (lexical.val.drop es.val) with hX0
        have x0Is : x0.val = min X0 100000000 := by rw [x0Val, spanIs]; simp [hX0]
        obtain ⟨b, bRun, bCanon, bValue⟩ := numeral_value_spec lexical start whole_end fraction_start fraction_end
          expNeg x0 X0 negative double o1 o2 o3 fits short dw df x0Is
        have run : (do
          let i1 := alloc.vec.Vec.len lexical
          if fraction_end < i1
          then
            let mark ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U8)
                lexical fraction_end
            if (mark = 69#u8) || (mark = 101#u8)
            then
              let sign_at ← fraction_end + 1#usize
              let i2 := alloc.vec.Vec.len lexical
              let signed ←
                if sign_at < i2
                then
                  do
                  let i3 ←
                    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                      Std.U8) lexical sign_at
                  ok ((i3 = 45#u8) || (i3 = 43#u8))
                else ok false
              let i3 := alloc.vec.Vec.len lexical
              let exponent_negative ←
                if sign_at < i3
                then
                  do
                  let i4 ←
                    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                      Std.U8) lexical sign_at
                  ok (i4 = 45#u8)
                else ok false
              let exponent_start ← if signed
                                     then sign_at + 1#usize
                                     else ok sign_at
              let exponent_end ← moments.digits_end lexical exponent_start
              if exponent_start < exponent_end
              then
                let i4 := alloc.vec.Vec.len lexical
                if exponent_end = i4
                then
                  let i5 ←
                    floats.small_value lexical exponent_start exponent_end 0#usize
                  floats.numeral_value lexical start whole_end fraction_start
                    fraction_end exponent_negative i5 negative double
                else ok none
              else ok none
            else ok none
          else
            floats.numeral_value lexical start whole_end fraction_start fraction_end
              false 0#usize negative double : Result (Option datatypes.Binary)) = .ok (some b) := by
          simp only [moreB, ↓reduceIte, bind_ok, lookupMark, Bool.or_eq_true, decide_eq_true_eq, isE, saRun]
          rw [signedRun]
          simp only [bind_ok]
          rw [negRun]
          simp only [bind_ok]
          rw [esRun]
          simp only [bind_ok, eeRun, goodLt, ↓reduceIte]
          rw [if_pos goodEq]
          simp only [x0Run, bind_ok, bRun]
        refine ⟨some b, run, ?_, ?_⟩
        · intro b' hb'
          simp only [Option.some.injEq] at hb'
          subst hb'
          refine ⟨bCanon, (if expNeg then -1 else 1) * (X0 : ℤ), ?_, ?_⟩
          · right
            refine ⟨lexical.val[fraction_end.val], sign, lexical.val.drop es.val, expNeg, isE, signForm, dd, ne,
              dropMark, rfl⟩
          · rw [bValue]; unfold positionValue; congr 1; cases expNeg <;> simp
        · intro x form
          rcases form with ⟨empty, _⟩ | ⟨mark', sign', digits', neg', isE', signForm', dd', ne', split, xIs⟩
          · rw [dropFe] at empty; cases empty
          · rw [dropFe, List.cons_append, List.cons.injEq] at split
            obtain ⟨same1, same2, same3⟩ := unique sign' neg' digits' signForm' (by rw [saIs]; exact split.2) ne' dd'
            refine ⟨b, rfl, ?_⟩
            rw [bValue, xIs, same2, same3, ← hX0]
            unfold positionValue; congr 1; cases expNeg <;> simp
      · have run : ∀ (tail : Result (Option datatypes.Binary)), (if es < ee then (if ee = alloc.vec.Vec.len lexical
            then tail else ok none) else ok none) = .ok none := by
          intro tail
          by_cases lt : es.val < ee.val
          · have ltB : es < ee := by rw [UScalar.lt_equiv]; exact lt
            have neB : ¬ ee = alloc.vec.Vec.len lexical := by
              rw [UScalar.eq_equiv]; simp; intro h; exact good ⟨lt, h⟩
            simp [ltB, neB]
          · have ltB : ¬ es < ee := by rw [UScalar.lt_equiv]; exact lt
            simp [ltB]
        refine ⟨none, ?_, (fun b hb => by cases hb), ?_⟩
        · simp only [moreB, ↓reduceIte, bind_ok, lookupMark, Bool.or_eq_true, decide_eq_true_eq, isE, saRun]
          rw [signedRun]
          simp only [bind_ok]
          rw [negRun]
          simp only [bind_ok]
          rw [esRun]
          simp only [bind_ok, eeRun]
          exact run _
        · intro x form
          rcases form with ⟨empty, _⟩ | ⟨mark', sign', digits', neg', isE', signForm', dd', ne', split, xIs⟩
          · rw [dropFe] at empty; cases empty
          · rw [dropFe, List.cons_append, List.cons.injEq] at split
            obtain ⟨_, _, same3⟩ := unique sign' neg' digits' signForm' (by rw [saIs]; exact split.2) ne' dd'
            exact absurd (eeIff.mpr ⟨by rw [← same3]; exact ne', by rw [← same3]; exact dd'⟩) good
    · refine ⟨none, ?_, (fun b hb => by cases hb), ?_⟩
      · simp only [moreB, ↓reduceIte, bind_ok, lookupMark, Bool.or_eq_true, decide_eq_true_eq, isE]
      · intro x form
        rcases form with ⟨empty, _⟩ | ⟨mark', sign', digits', neg', isE', signForm', dd', ne', split, xIs⟩
        · rw [dropFe] at empty; cases empty
        · rw [dropFe, List.cons_append, List.cons.injEq] at split
          rw [← split.1] at isE'
          exact absurd isE' isE
  · have moreB : ¬ fraction_end < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simpa using more
    obtain ⟨b, bRun, bCanon, bValue⟩ := numeral_value_spec lexical start whole_end fraction_start fraction_end
      false 0#usize 0 negative double o1 o2 o3 fits short dw df (by simp)
    have dropNil : lexical.val.drop fraction_end.val = [] := by simp; omega
    refine ⟨some b, by simp only [moreB, ↓reduceIte, bRun], ?_, ?_⟩
    · intro b' hb'
      simp only [Option.some.injEq] at hb'
      subst hb'
      exact ⟨bCanon, 0, by rw [dropNil]; exact .inl ⟨rfl, rfl⟩, by rw [bValue]; rfl⟩
    · intro x form
      rw [dropNil] at form
      rcases form with ⟨_, rfl⟩ | ⟨mark', sign', digits', neg', _, _, _, _, split, _⟩
      · exact ⟨b, rfl, by rw [bValue]; rfl⟩
      · cases split

/-- `digits_end` stops after the digits that come first in the rest. -/
theorem digits_end_after (lexical : alloc.vec.Vec U8) (index : Usize) (A B : List U8)
    (inside : index.val ≤ lexical.val.length)
    (split : lexical.val.drop index.val = A ++ B) (dA : Digits A) (stopB : ∀ c rest, B = c :: rest → ¬ Digit c) :
    ∃ r, moments.digits_end lexical index = .ok r ∧ r.val = index.val + A.length := by
  have lenEq : lexical.val.length - index.val = A.length + B.length := by
    have := congrArg List.length split; simp at this; omega
  apply digits_end_exact lexical index A.length (by omega)
  · intro i hi low high
    have : lexical.val[i] = (lexical.val.drop index.val)[i - index.val]'(by simp; omega) := by
      rw [List.getElem_drop]; congr 1; omega
    rw [this]
    have hA : i - index.val < A.length := by omega
    simp only [split]
    rw [List.getElem_append_left hA]
    exact dA _ (List.getElem_mem hA)
  · intro h
    have hB : 0 < B.length := by omega
    obtain ⟨c, rest, rfl⟩ : ∃ c rest, B = c :: rest := by
      cases B with
      | nil => simp at hB
      | cons c rest => exact ⟨c, rest, rfl⟩
    have : lexical.val[index.val + A.length] = (lexical.val.drop index.val)[A.length]'(by simp; omega) := by
      rw [List.getElem_drop]
    rw [this]
    simp only [split]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem_cons_zero]
    exact stopB c rest rfl

theorem span_eq_take_drop (l : List U8) (a b : ℕ) : span l a b = (l.drop a).take (b - a) := by
  unfold span; rw [List.drop_take]

theorem span_append (l : List U8) (a b c : ℕ) (ab : a ≤ b) (bc : b ≤ c) :
    span l a c = span l a b ++ span l b c := by
  rw [span_eq_take_drop, span_eq_take_drop, span_eq_take_drop,
    show c - a = (b - a) + (c - b) by omega, List.take_add, List.drop_drop]
  congr 3; omega

theorem drop_split (l : List U8) (a b : ℕ) (ab : a ≤ b) :
    l.drop a = span l a b ++ l.drop b := by
  rw [span_eq_take_drop]
  conv_lhs => rw [← List.take_append_drop (b - a) (l.drop a)]
  rw [List.drop_drop]; congr 2; omega

theorem span_of_drop (l : List U8) (a : ℕ) (A R : List U8) (split : l.drop a = A ++ R) :
    span l a (a + A.length) = A ∧ l.drop (a + A.length) = R := by
  constructor
  · rw [span_eq_take_drop, split, show a + A.length - a = A.length by omega]; simp
  · rw [← List.drop_drop, split]; simp

/-- Bytes that follow a numeral's digits: an exponent mark or nothing. -/
theorem exponent_head {exponent : List U8} {x : ℤ} (ef : ExponentForm exponent x) :
    ∀ c rest, exponent = c :: rest → ¬ Digit c ∧ c ≠ 46#u8 := by
  intro c rest eq
  rcases ef with ⟨rfl, _⟩ | ⟨mark, sign, digits, neg, isE, _, _, _, split, _⟩
  · cases eq
  · rw [split, List.cons_append, List.cons.injEq] at eq
    rw [← eq.1]
    rcases isE with h | h <;> rw [h] <;> refine ⟨fun d => ?_, by decide⟩ <;> have := d.2 <;> simp at this

/-- `numeral` reads a numeral after its sign: digits, a point and an exponent. -/
theorem numeral_spec (lexical : alloc.vec.Vec U8) (start : Usize) (negative double : Bool)
    (inside : start.val ≤ lexical.val.length) (short : lexical.val.length < 1024) :
    ∃ r, floats.numeral lexical start negative double = .ok r ∧
      (∀ b, r = some b → CanonicalBinary b ∧ ∃ unsigned exponent digits places x,
        lexical.val.drop start.val = unsigned ++ exponent ∧ UnsignedForm unsigned digits places ∧
        ExponentForm exponent x ∧ binaryOf b = numeralValue double negative digits x places) ∧
      (∀ unsigned exponent digits places x, lexical.val.drop start.val = unsigned ++ exponent →
        UnsignedForm unsigned digits places → ExponentForm exponent x →
        ∃ b, r = some b ∧ binaryOf b = numeralValue double negative digits x places) := by
  rw [floats.numeral]
  have big : 4294967295 ≤ Usize.max := by scalar_tac
  obtain ⟨we, weRun, weLow, weHigh, weDigits, weStop⟩ := Rowl.Moments.digits_end_spec lexical start inside
  obtain ⟨point, pointRun, pointIs⟩ : ∃ point : Bool, (if we < alloc.vec.Vec.len lexical then do
        let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) lexical we
        ok (decide (i1 = 46#u8))
      else ok false : Result Bool) = .ok point ∧
      (point = true ↔ ∃ h : we.val < lexical.val.length, (lexical.val[we.val]'h) = 46#u8) := by
    by_cases weIn : we.val < lexical.val.length
    · have weInB : we < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simpa using weIn
      refine ⟨decide ((lexical.val[we.val]'weIn) = 46#u8), ?_, ?_⟩
      · simp only [weInB, ↓reduceIte, vec_lookup2 lexical we weIn, bind_ok]
      · simp [weIn]
    · have weInB : ¬ we < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simpa using weIn
      exact ⟨false, by simp only [weInB, ↓reduceIte], by simp [weIn]⟩
  obtain ⟨fs, fsRun, fsIs⟩ : ∃ fs : Usize, (if point then we + 1#usize else ok we : Result Usize) = .ok fs ∧
      fs.val = we.val + (if point then 1 else 0) := by
    cases point
    · exact ⟨we, by simp, by simp⟩
    · have weIn : we.val < lexical.val.length := (pointIs.mp rfl).1
      obtain ⟨f, fRun, fVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := we) (y := 1#usize) (by simp; omega))
      exact ⟨f, by simp [fRun], by simpa using fVal⟩
  have fsLe : fs.val ≤ lexical.val.length := by
    cases point
    · simp at fsIs; omega
    · have := (pointIs.mp rfl).1; simp at fsIs; omega
  obtain ⟨fe, feRun, feLow, feHigh, feDigits, feStop⟩ := Rowl.Moments.digits_end_spec lexical fs fsLe
  have spanDigits : ∀ a b, (∀ i (hi : i < lexical.val.length), a ≤ i → i < b → Digit lexical.val[i]) →
      b ≤ lexical.val.length → Digits (span lexical.val a b) := by
    intro a b all _ c mem
    rw [span_eq_take_drop] at mem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
    simp only [List.length_take, List.length_drop] at hi
    rw [List.getElem_take, List.getElem_drop]
    exact all _ _ (by omega) (by omega)
  have dw := spanDigits start.val we.val weDigits weHigh
  have df := spanDigits fs.val fe.val feDigits feHigh
  have o2 : we.val ≤ fs.val := by rw [fsIs]; omega
  obtain ⟨r, tailRun, tailSound, tailComplete⟩ := exponent_tail_spec lexical start we fs fe negative double
    weLow o2 feLow feHigh short dw df
  -- without a point, there are no digits after the whole digits
  have noFraction : point = false → fe.val = fs.val := by
    intro np
    have fsWe : fs.val = we.val := by rw [fsIs, np]; simp
    by_contra differ
    have more : fs.val < fe.val := by omega
    have inside' : we.val < lexical.val.length := by omega
    exact weStop inside' (feDigits we.val inside' (by omega) (by omega))
  have uform : start.val < we.val ∨ fs.val < fe.val →
      UnsignedForm (span lexical.val start.val fe.val) (span lexical.val start.val we.val ++ span lexical.val fs.val fe.val)
        (fe.val - fs.val) ∧ lexical.val.drop start.val = span lexical.val start.val fe.val ++ lexical.val.drop fe.val := by
    intro some
    refine ⟨⟨span lexical.val start.val we.val, span lexical.val fs.val fe.val, dw, df, rfl,
      by rw [span_length _ _ _ feHigh], ?_⟩, drop_split _ _ _ (by omega)⟩
    cases hp : point
    · have feFs := noFraction hp
      have fsWe : fs.val = we.val := by rw [fsIs, hp]; simp
      left
      refine ⟨by rw [feFs, fsWe], ?_, span_empty _ _ _ (by omega)⟩
      intro empty
      have := span_length lexical.val start.val we.val weHigh
      rw [empty] at this
      simp at this
      omega
    · obtain ⟨weIn, isPoint⟩ := pointIs.mp hp
      have fsIs' : fs.val = we.val + 1 := by rw [fsIs, hp]; simp
      right
      refine ⟨?_, ?_⟩
      · rw [span_append lexical.val start.val we.val fe.val weLow (by omega),
          span_cons lexical.val we.val fe.val (by omega) feHigh, isPoint, ← fsIs']
      · rcases some with h | h
        · left; intro empty; have := span_length lexical.val start.val we.val weHigh; rw [empty] at this; simp at this; omega
        · right; intro empty; have := span_length lexical.val fs.val fe.val feHigh; rw [empty] at this; simp at this; omega
  -- the positions of a numeral's parts
  have positions : ∀ unsigned exponent digits places x, lexical.val.drop start.val = unsigned ++ exponent →
      UnsignedForm unsigned digits places → ExponentForm exponent x →
      span lexical.val start.val we.val ++ span lexical.val fs.val fe.val = digits ∧ fe.val - fs.val = places ∧
        lexical.val.drop fe.val = exponent ∧ (start.val < we.val ∨ fs.val < fe.val) := by
    intro unsigned exponent digits places x split uf ef
    obtain ⟨whole, fraction, dW, dF, digitsEq, placesEq, shape⟩ := uf
    have stopE := exponent_head ef
    rcases shape with ⟨hu, wholeNe, hf⟩ | ⟨hu, someNe⟩
    · rw [hu] at split
      subst hf
      obtain ⟨r1, r1Run, r1Val⟩ := digits_end_after lexical start whole exponent inside split dW
        (fun c rest h => (stopE c rest h).1)
      have weIs : we.val = start.val + whole.length := by
        rw [weRun] at r1Run; simp only [ok.injEq] at r1Run; rw [r1Run]; exact r1Val
      obtain ⟨spanW, dropW⟩ := span_of_drop lexical.val start.val whole exponent split
      rw [← weIs] at spanW dropW
      have np : point = false := by
        cases hp : point
        · rfl
        · obtain ⟨weIn, isPoint⟩ := pointIs.mp hp
          have := List.drop_eq_getElem_cons weIn
          rw [dropW, isPoint] at this
          exact absurd rfl (stopE _ _ this).2
      have feFs := noFraction np
      have fsWe : fs.val = we.val := by rw [fsIs, np]; simp
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [spanW, span_empty _ _ _ (by omega), digitsEq]
      · rw [placesEq]; simp; omega
      · rw [feFs, fsWe]; exact dropW
      · left
        have : whole.length ≠ 0 := fun h => wholeNe (List.eq_nil_of_length_eq_zero h)
        omega
    · rw [hu] at split
      have split' : lexical.val.drop start.val = whole ++ (46#u8 :: (fraction ++ exponent)) := by
        rw [split]; simp
      obtain ⟨r1, r1Run, r1Val⟩ := digits_end_after lexical start whole _ inside split' dW
        (fun c rest h => by
          simp only [List.cons.injEq] at h
          rw [← h.1]; intro d; have := d.1; simp at this)
      have weIs : we.val = start.val + whole.length := by
        rw [weRun] at r1Run; simp only [ok.injEq] at r1Run; rw [r1Run]; exact r1Val
      obtain ⟨spanW, dropW⟩ := span_of_drop lexical.val start.val whole _ split'
      rw [← weIs] at spanW dropW
      have weIn : we.val < lexical.val.length := by
        by_contra h
        have : lexical.val.drop we.val = [] := by simp; omega
        rw [this] at dropW; cases dropW
      have isPoint : (lexical.val[we.val]'weIn) = 46#u8 := by
        have := List.drop_eq_getElem_cons weIn
        rw [dropW, List.cons.injEq] at this
        exact this.1.symm
      have hp : point = true := pointIs.mpr ⟨weIn, isPoint⟩
      have fsIs' : fs.val = we.val + 1 := by rw [fsIs, hp]; simp
      have dropFs : lexical.val.drop fs.val = fraction ++ exponent := by
        have := List.drop_eq_getElem_cons weIn
        rw [dropW, List.cons.injEq] at this
        rw [fsIs']; exact this.2.symm
      obtain ⟨r2, r2Run, r2Val⟩ := digits_end_after lexical fs fraction exponent fsLe dropFs dF
        (fun c rest h => (stopE c rest h).1)
      have feIs : fe.val = fs.val + fraction.length := by
        rw [feRun] at r2Run; simp only [ok.injEq] at r2Run; rw [r2Run]; exact r2Val
      obtain ⟨spanF, dropF⟩ := span_of_drop lexical.val fs.val fraction exponent dropFs
      rw [← feIs] at spanF dropF
      refine ⟨by rw [spanW, spanF, digitsEq], by rw [placesEq]; omega, dropF, ?_⟩
      rcases someNe with h | h
      · left; have : whole.length ≠ 0 := fun e => h (List.eq_nil_of_length_eq_zero e)
        omega
      · right; have : fraction.length ≠ 0 := fun e => h (List.eq_nil_of_length_eq_zero e)
        omega
  by_cases some : start.val < we.val ∨ fs.val < fe.val
  · obtain ⟨uf, dropIs⟩ := uform some
    refine ⟨r, ?_, ?_, ?_⟩
    · simp only [weRun, bind_ok, pointRun, fsRun, feRun]
      by_cases A : start.val < we.val
      · rw [if_pos (show start < we by rw [UScalar.lt_equiv]; exact A)]
        exact tailRun
      · have B : fs.val < fe.val := by omega
        rw [if_neg (show ¬ start < we by rw [UScalar.lt_equiv]; exact A),
          if_pos (show fs < fe by rw [UScalar.lt_equiv]; exact B)]
        exact tailRun
    · intro b hb
      obtain ⟨canon, x, ef, value⟩ := tailSound b hb
      exact ⟨canon, span lexical.val start.val fe.val, lexical.val.drop fe.val,
        span lexical.val start.val we.val ++ span lexical.val fs.val fe.val, fe.val - fs.val, x, dropIs, uf, ef,
        value⟩
    · intro unsigned exponent digits places x split uf' ef'
      obtain ⟨digitsIs, placesIs, dropIs', _⟩ := positions unsigned exponent digits places x split uf' ef'
      obtain ⟨b, hb, value⟩ := tailComplete x (by rw [dropIs']; exact ef')
      refine ⟨b, hb, ?_⟩
      rw [value, ← digitsIs, ← placesIs]
      rfl
  · have A : ¬ start < we := by rw [UScalar.lt_equiv]; omega
    have B : ¬ fs < fe := by rw [UScalar.lt_equiv]; omega
    refine ⟨none, ?_, (fun b h => by cases h), ?_⟩
    · simp only [weRun, bind_ok, pointRun, fsRun, feRun]
      rw [if_neg A, if_neg B]
    · intro unsigned exponent digits places x split uf' ef'
      exact absurd (positions unsigned exponent digits places x split uf' ef').2.2.2 some


/-! ## The lexical forms -/

/-- An unsigned numeral starts with a digit or the point. -/
theorem unsigned_head {unsigned digits : List U8} {places : ℕ} (uf : UnsignedForm unsigned digits places) :
    ∃ c rest, unsigned = c :: rest ∧ (Digit c ∨ c = 46#u8) := by
  obtain ⟨whole, fraction, dW, _, _, _, shape⟩ := uf
  rcases shape with ⟨hu, ne, _⟩ | ⟨hu, _⟩
  · rw [hu]
    cases whole with
    | nil => exact absurd rfl ne
    | cons c rest => exact ⟨c, rest, rfl, .inl (dW c List.mem_cons_self)⟩
  · rw [hu]
    cases whole with
    | nil => exact ⟨46#u8, fraction, rfl, .inr rfl⟩
    | cons c rest => exact ⟨c, rest ++ 46#u8 :: fraction, rfl, .inl (dW c List.mem_cons_self)⟩

theorem numeralValue_eq (double negative : Bool) (digits : List U8) (x : ℤ) (places : ℕ) :
    let v : ℚ := (if negative then -1 else 1) * (digitsValue digits : ℚ) * (10 : ℚ) ^ (x - places)
    (v = 0 ∧ numeralValue double negative digits x places = .zero negative) ∨
      (v ≠ 0 ∧ numeralValue double negative digits x places = roundBinary (fmt double) v) := by
  intro v
  by_cases zero : digitsValue digits = 0
  · left
    refine ⟨by simp [v, zero], by simp [numeralValue, zero]⟩
  · right
    refine ⟨?_, by simp [numeralValue, zero, v]⟩
    have : (digitsValue digits : ℚ) ≠ 0 := by exact_mod_cast zero
    have tz : (10 : ℚ) ^ (x - places) ≠ 0 := zpow_ne_zero _ (by norm_num)
    cases negative <;> simp [v, this, tz]

theorem inf_slice : ∃ sl, lift (Array.to_slice (Array.make 3#usize [73#u8, 78#u8, 70#u8])) = .ok sl ∧
    sl.val = [73#u8, 78#u8, 70#u8] := ⟨_, rfl, by simp [Array.to_slice, Array.make]⟩

theorem nan_slice : ∃ sl, lift (Array.to_slice (Array.make 3#usize [78#u8, 97#u8, 78#u8])) = .ok sl ∧
    sl.val = [78#u8, 97#u8, 78#u8] := ⟨_, rfl, by simp [Array.to_slice, Array.make]⟩

/-- `binary_value` reads exactly the lexical forms of `xsd:double` (`double`)
    or `xsd:float` below `LIMIT` bytes, into their values, canonically. -/
theorem binary_value_correct (lexical : alloc.vec.Vec U8) (double : Bool) :
    ∃ r, floats.binary_value lexical double = .ok r ∧
      (∀ b, r = some b → CanonicalBinary b ∧ BinaryForm (fmt double) lexical.val (binaryOf b)) ∧
      (lexical.val.length < 1024 → ∀ x, BinaryForm (fmt double) lexical.val x → ∃ b, r = some b ∧ binaryOf b = x) := by
  rw [floats.binary_value]
  by_cases short : lexical.val.length < 1024
  · have shortB : alloc.vec.Vec.len lexical < floats.LIMIT := by rw [UScalar.lt_equiv, limit_val]; simpa using short
    -- the sign
    obtain ⟨negative, signed, negRun, sigRun, negIff, sigIff⟩ : ∃ negative signed : Bool,
        (if 0#usize < alloc.vec.Vec.len lexical then do
            let i2 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) lexical 0#usize
            ok (decide (i2 = 45#u8))
          else ok false : Result Bool) = .ok negative ∧
        (if 0#usize < alloc.vec.Vec.len lexical then do
            let i3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) lexical 0#usize
            ok (decide (i3 = 45#u8) || decide (i3 = 43#u8))
          else ok false : Result Bool) = .ok signed ∧
        (negative = true ↔ ∃ rest, lexical.val = 45#u8 :: rest) ∧
        (signed = true ↔ ∃ c rest, lexical.val = c :: rest ∧ (c = 45#u8 ∨ c = 43#u8)) := by
      cases hl : lexical.val with
      | nil =>
        have notPos : ¬ (0#usize) < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simp [hl]
        exact ⟨false, false, by simp only [notPos, ↓reduceIte], by simp only [notPos, ↓reduceIte], by simp,
          by simp⟩
      | cons c rest =>
        have pos : (0#usize) < alloc.vec.Vec.len lexical := by rw [UScalar.lt_equiv]; simp [hl]
        have inside : (0#usize).val < lexical.val.length := by simp [hl]
        have lookup := vec_lookup2 lexical 0#usize inside
        have first : (lexical.val[(0#usize).val]'inside) = c := by simp [hl]
        refine ⟨decide (c = 45#u8), decide (c = 45#u8) || decide (c = 43#u8), ?_, ?_, ?_, ?_⟩
        · simp only [pos, ↓reduceIte, lookup, bind_ok, first]
        · simp only [pos, ↓reduceIte, lookup, bind_ok, first]
        · simp
        · simp
    obtain ⟨st, stRun, stIs⟩ : ∃ st : Usize, (if signed then ok 1#usize else ok 0#usize : Result Usize) = .ok st ∧
        st.val = if signed then 1 else 0 := by
      cases signed
      · exact ⟨0#usize, by simp, by simp⟩
      · exact ⟨1#usize, by simp, by simp⟩
    have stLe : st.val ≤ lexical.val.length := by
      cases hs : signed
      · rw [stIs, hs]; simp
      · obtain ⟨c, rest, hl, _⟩ := sigIff.mp hs
        rw [stIs, hs, hl]; simp
    -- the sign's form and the rest
    have signForm : ∃ sign, SignForm sign negative ∧ lexical.val = sign ++ lexical.val.drop st.val := by
      cases hs : signed
      · have notNeg : negative = false := by
          cases hn : negative
          · rfl
          · obtain ⟨rest, hl⟩ := negIff.mp hn
            have := sigIff.mpr ⟨45#u8, rest, hl, .inl rfl⟩
            rw [hs] at this; cases this
        refine ⟨[], .inl ⟨rfl, notNeg⟩, ?_⟩
        rw [stIs, hs]; simp
      · obtain ⟨c, rest, hl, plus⟩ := sigIff.mp hs
        refine ⟨[c], ?_, by rw [stIs, hs, hl]; simp⟩
        rcases plus with h | h
        · right; right; refine ⟨by rw [h], ?_⟩
          exact negIff.mpr ⟨rest, by rw [hl, h]⟩
        · right; left; refine ⟨by rw [h], ?_⟩
          cases hn : negative
          · rfl
          · obtain ⟨rest', hl'⟩ := negIff.mp hn
            rw [hl] at hl'
            simp only [List.cons.injEq] at hl'
            rw [h] at hl'; exact absurd hl'.1 (by decide)
    obtain ⟨sign, signForm, lexSplit⟩ := signForm
    obtain ⟨sInf, sInfRun, sInfVal⟩ := inf_slice
    obtain ⟨sNan, sNanRun, sNanVal⟩ := nan_slice
    have infRun := word_at_spec lexical st sInf stLe
    have nanRun := word_at_spec lexical 0#usize sNan (by simp)
    rw [sInfVal] at infRun
    rw [sNanVal] at nanRun
    have nanRun' : floats.word_at lexical 0#usize sNan = .ok (decide (lexical.val = [78#u8, 97#u8, 78#u8])) := by
      rw [nanRun]; simp
    -- the sign that the first byte gives
    have plain : ∀ c rest, lexical.val = c :: rest → c ≠ 45#u8 → c ≠ 43#u8 → signed = false ∧ negative = false := by
      intro c rest hl n45 n43
      constructor
      · cases hs : signed
        · rfl
        · obtain ⟨c', rest', hl', h⟩ := sigIff.mp hs
          rw [hl] at hl'; simp only [List.cons.injEq] at hl'
          rcases h with h | h <;> [exact absurd (hl'.1 ▸ h) n45; exact absurd (hl'.1 ▸ h) n43]
      · cases hn : negative
        · rfl
        · obtain ⟨rest', hl'⟩ := negIff.mp hn
          rw [hl] at hl'; simp only [List.cons.injEq] at hl'
          exact absurd hl'.1 n45
    have plus : ∀ rest, lexical.val = 43#u8 :: rest → signed = true ∧ negative = false := by
      intro rest hl
      refine ⟨sigIff.mpr ⟨43#u8, rest, hl, .inr rfl⟩, ?_⟩
      cases hn : negative
      · rfl
      · obtain ⟨rest', hl'⟩ := negIff.mp hn
        rw [hl] at hl'; simp only [List.cons.injEq] at hl'
        exact absurd hl'.1 (by decide)
    have minus : ∀ rest, lexical.val = 45#u8 :: rest → signed = true ∧ negative = true :=
      fun rest hl => ⟨sigIff.mpr ⟨45#u8, rest, hl, .inl rfl⟩, negIff.mpr ⟨rest, hl⟩⟩
    have dropOne : ∀ c rest, lexical.val = c :: rest → signed = true → lexical.val.drop st.val = rest := by
      intro c rest hl hs; rw [stIs, hs, hl]; simp
    have dropZero : signed = false → lexical.val.drop st.val = lexical.val := by
      intro hs; rw [stIs, hs]; simp
    -- a numeral starts after its sign
    have numeralStart : ∀ sign' negative' unsigned exponent digits places x,
        lexical.val = sign' ++ unsigned ++ exponent → SignForm sign' negative' → UnsignedForm unsigned digits places →
        ExponentForm exponent x →
        negative' = negative ∧ lexical.val.drop st.val = unsigned ++ exponent ∧
          lexical.val.drop st.val ≠ [73#u8, 78#u8, 70#u8] ∧ lexical.val ≠ [78#u8, 97#u8, 78#u8] := by
      intro sign' negative' unsigned exponent digits places x hl sf uf _
      obtain ⟨c, rest, hu, hc⟩ := unsigned_head uf
      have cNot : c ≠ 45#u8 ∧ c ≠ 43#u8 ∧ c ≠ 73#u8 ∧ c ≠ 78#u8 := by
        rcases hc with d | d
        · obtain ⟨lo, hi⟩ := d
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e <;> rw [e] at lo hi <;> simp at lo hi
        · rw [d]; decide
      have notInf : unsigned ++ exponent ≠ [73#u8, 78#u8, 70#u8] := by
        rw [hu]; intro e; simp only [List.cons_append, List.cons.injEq] at e; exact cNot.2.2.1 e.1
      rcases sf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hu] at hl
        simp only [List.nil_append, List.cons_append] at hl
        obtain ⟨hs, hn⟩ := plain _ _ hl cNot.1 cNot.2.1
        refine ⟨hn.symm, ?_, ?_, ?_⟩
        · rw [dropZero hs, hl, hu]; simp
        · rw [dropZero hs, hl, ← List.cons_append, ← hu]; exact notInf
        · rw [hl]; intro e; simp only [List.cons.injEq] at e; exact cNot.2.2.2 e.1
      · simp only [List.singleton_append, List.cons_append, List.append_assoc] at hl
        obtain ⟨hs, hn⟩ := plus _ hl
        refine ⟨hn.symm, ?_, ?_, ?_⟩
        · simp only [dropOne _ _ hl hs, List.nil_append]
        · simp only [dropOne _ _ hl hs, List.nil_append]; exact notInf
        · rw [hl]; intro e; simp at e
      · simp only [List.singleton_append, List.cons_append, List.append_assoc] at hl
        obtain ⟨hs, hn⟩ := minus _ hl
        refine ⟨hn.symm, ?_, ?_, ?_⟩
        · simp only [dropOne _ _ hl hs, List.nil_append]
        · simp only [dropOne _ _ hl hs, List.nil_append]; exact notInf
        · rw [hl]; intro e; simp at e
    obtain ⟨rn, rnRun, rnSound, rnComplete⟩ := numeral_spec lexical st negative double stLe short
    by_cases isInf : lexical.val.drop st.val = [73#u8, 78#u8, 70#u8]
    · have infTrue : decide (lexical.val.drop st.val = [73#u8, 78#u8, 70#u8]) = true := decide_eq_true isInf
      refine ⟨some (.Infinite negative), ?_, ?_, ?_⟩
      · simp only [shortB, ↓reduceIte, negRun, sigRun, stRun, sInfRun, infRun, infTrue, bind_ok]
      · intro b hb
        simp only [Option.some.injEq] at hb
        subst hb
        refine ⟨trivial, ?_⟩
        rw [isInf] at lexSplit
        rcases signForm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inl ⟨.inl (by simpa using lexSplit), rfl⟩
        · exact .inl ⟨.inr (by simpa using lexSplit), rfl⟩
        · exact .inr (.inl ⟨by simpa using lexSplit, rfl⟩)
      · intro _ x form
        rcases form with ⟨shape, rfl⟩ | ⟨shape, rfl⟩ | ⟨shape, rfl⟩ | ⟨negative', v, numeral, _⟩
        · refine ⟨_, rfl, ?_⟩
          rcases shape with h | h
          · rw [(plain _ _ h (by decide) (by decide)).2]; rfl
          · rw [(plus _ h).2]; rfl
        · exact ⟨_, rfl, by rw [(minus _ shape).2]; rfl⟩
        · exfalso
          obtain ⟨hs, _⟩ := plain _ _ shape (by decide) (by decide)
          rw [dropZero hs, shape] at isInf
          simp at isInf
        · exfalso
          obtain ⟨sign', unsigned, exponent, digits, places, x', split, sf, uf, ef, _⟩ := numeral
          exact (numeralStart sign' negative' unsigned exponent digits places x' split sf uf ef).2.2.1 isInf
    · have infFalse : decide (lexical.val.drop st.val = [73#u8, 78#u8, 70#u8]) = false := decide_eq_false isInf
      by_cases isNan : lexical.val = [78#u8, 97#u8, 78#u8]
      · have nanTrue : decide (lexical.val = [78#u8, 97#u8, 78#u8]) = true := decide_eq_true isNan
        refine ⟨some .NotANumber, ?_, ?_, ?_⟩
        · simp only [shortB, ↓reduceIte, negRun, sigRun, stRun, sInfRun, infRun, infFalse, bind_ok,
            Bool.false_eq_true, sNanRun, nanRun', nanTrue]
        · intro b hb
          simp only [Option.some.injEq] at hb
          subst hb
          exact ⟨trivial, .inr (.inr (.inl ⟨isNan, rfl⟩))⟩
        · intro _ x form
          rcases form with ⟨shape, rfl⟩ | ⟨shape, rfl⟩ | ⟨shape, rfl⟩ | ⟨negative', v, numeral, _⟩
          · exfalso; rcases shape with h | h <;> rw [isNan] at h <;> simp at h
          · exfalso; rw [isNan] at shape; simp at shape
          · exact ⟨_, rfl, rfl⟩
          · exfalso
            obtain ⟨sign', unsigned, exponent, digits, places, x', split, sf, uf, ef, _⟩ := numeral
            exact (numeralStart sign' negative' unsigned exponent digits places x' split sf uf ef).2.2.2 isNan
      · have nanFalse : decide (lexical.val = [78#u8, 97#u8, 78#u8]) = false := decide_eq_false isNan
        refine ⟨rn, ?_, ?_, ?_⟩
        · simp only [shortB, ↓reduceIte, negRun, sigRun, stRun, sInfRun, infRun, infFalse, bind_ok,
            Bool.false_eq_true, sNanRun, nanRun', nanFalse, rnRun]
        · intro b hb
          obtain ⟨canon, unsigned, exponent, digits, places, x, split, uf, ef, value⟩ := rnSound b hb
          refine ⟨canon, .inr (.inr (.inr ?_))⟩
          refine ⟨negative, (if negative then -1 else 1) * (digitsValue digits : ℚ) * (10 : ℚ) ^ (x - places),
            ⟨sign, unsigned, exponent, digits, places, x, ?_, signForm, uf, ef, rfl⟩, ?_⟩
          · rw [List.append_assoc, ← split]; exact lexSplit
          · rw [value]; exact numeralValue_eq double negative digits x places
        · intro _ x form
          rcases form with ⟨shape, rfl⟩ | ⟨shape, rfl⟩ | ⟨shape, rfl⟩ | ⟨negative', v, numeral, value⟩
          · exfalso
            rcases shape with h | h
            · obtain ⟨hs, _⟩ := plain _ _ h (by decide) (by decide)
              exact isInf (by rw [dropZero hs, h])
            · obtain ⟨hs, _⟩ := plus _ h
              exact isInf (by rw [dropOne _ _ h hs])
          · exfalso
            obtain ⟨hs, _⟩ := minus _ shape
            exact isInf (by rw [dropOne _ _ shape hs])
          · exact absurd shape isNan
          · obtain ⟨sign', unsigned, exponent, digits, places, x', split, sf, uf, ef, vIs⟩ := numeral
            obtain ⟨sameNeg, dropIs, _, _⟩ := numeralStart sign' negative' unsigned exponent digits places x' split sf uf ef
            obtain ⟨b, hb, bValue⟩ := rnComplete unsigned exponent digits places x' dropIs uf ef
            refine ⟨b, hb, ?_⟩
            rw [bValue, ← sameNeg]
            rcases numeralValue_eq double negative' digits x' places with ⟨v0, n0⟩ | ⟨v1, n1⟩
            · rcases value with ⟨_, rfl⟩ | ⟨vne, _⟩
              · exact n0
              · exact absurd (vIs ▸ v0) vne
            · rcases value with ⟨v0', _⟩ | ⟨_, rfl⟩
              · exact absurd (vIs ▸ v0') v1
              · rw [n1, vIs]
  · have shortB : ¬ alloc.vec.Vec.len lexical < floats.LIMIT := by rw [UScalar.lt_equiv, limit_val]; simpa using short
    exact ⟨none, by simp only [shortB, ↓reduceIte], (fun b h => by cases h), fun h => absurd h short⟩

/-! ## Kernel values and their values -/

/-- The values of the lexical forms are values of the format. -/
theorem binaryForm_valid {double : Bool} {t : List U8} {x : Binary} (form : BinaryForm (fmt double) t x) :
    x.Valid (fmt double) := by
  rcases form with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨negative, v, _, value⟩
  · trivial
  · trivial
  · trivial
  · rcases value with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · trivial
    · exact roundBinary_valid double v

theorem odd_scaled_unique {m1 m2 s1 s2 : ℕ} (o1 : m1 % 2 = 1) (o2 : m2 % 2 = 1)
    (same : (m1 : ℚ) * scale s1 = (m2 : ℚ) * scale s2) : m1 = m2 ∧ s1 = s2 := by
  have key : ∀ {a b : ℕ} {i j : ℕ}, a % 2 = 1 → b % 2 = 1 → i ≤ j → (a : ℚ) * scale i = (b : ℚ) * scale j →
      a = b ∧ i = j := by
    intro a b i j oa ob ij eq
    have eq' : (a : ℚ) = (b : ℚ) * 2 ^ (j - i) := by
      unfold scale at eq
      have : (2 : ℚ) ^ ((j : ℤ) - 2048) = (2 : ℚ) ^ ((i : ℤ) - 2048) * 2 ^ (j - i) := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; push_cast [Nat.cast_sub ij]; ring
      rw [this] at eq
      have pos : (0 : ℚ) < (2 : ℚ) ^ ((i : ℤ) - 2048) := zpow_pos (by norm_num) _
      field_simp at eq
      linarith [eq]
    have natEq : a = b * 2 ^ (j - i) := by exact_mod_cast eq'
    by_cases same : i = j
    · subst same; simp at natEq; exact ⟨natEq, rfl⟩
    · exfalso
      have : 2 ∣ 2 ^ (j - i) := dvd_pow_self 2 (by omega)
      have : 2 ∣ a := by rw [natEq]; exact Dvd.dvd.mul_left this b
      omega
  rcases Nat.le_total s1 s2 with h | h
  · exact key o1 o2 h same
  · obtain ⟨e1, e2⟩ := key o2 o1 h same.symm
    exact ⟨e1.symm, e2.symm⟩

/-- Canonical kernel values of one value are one. -/
theorem binary_canonical_injective {a b : datatypes.Binary} (ca : CanonicalBinary a) (cb : CanonicalBinary b)
    (same : binaryOf a = binaryOf b) : a = b := by
  cases a with
  | Finite n1 m1 s1 =>
    cases b with
    | Finite n2 m2 s2 =>
      simp only [CanonicalBinary] at ca cb
      by_cases z1 : m1.val = 0
      · by_cases z2 : m2.val = 0
        · simp only [binaryOf, z1, z2, ↓reduceIte, Binary.zero.injEq] at same
          have e1 : m1 = m2 := UScalar.eq_of_val_eq (by rw [z1, z2])
          have e2 : s1 = s2 := UScalar.eq_of_val_eq (by
            rcases ca with ⟨_, h1⟩ | h1
            · rcases cb with ⟨_, h2⟩ | h2
              · rw [h1, h2]
              · omega
            · omega)
          rw [same, e1, e2]
        · simp [binaryOf, z1, z2] at same
      · by_cases z2 : m2.val = 0
        · simp [binaryOf, z1, z2] at same
        · simp only [binaryOf, z1, z2, ↓reduceIte, Binary.finite.injEq] at same
          have o1 : m1.val % 2 = 1 := by rcases ca with ⟨h, _⟩ | h <;> omega
          have o2 : m2.val % 2 = 1 := by rcases cb with ⟨h, _⟩ | h <;> omega
          have p1 : (0 : ℚ) < (m1.val : ℚ) * scale s1.val := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero z1)
            (scale_pos _)
          have p2 : (0 : ℚ) < (m2.val : ℚ) * scale s2.val := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero z2)
            (scale_pos _)
          have signs : n1 = n2 := by
            cases n1 <;> cases n2 <;> first | rfl | (simp at same; nlinarith)
          subst signs
          have mags : (m1.val : ℚ) * scale s1.val = (m2.val : ℚ) * scale s2.val := by
            cases n1 <;> simp at same <;> linarith
          obtain ⟨e1, e2⟩ := odd_scaled_unique o1 o2 mags
          rw [UScalar.eq_of_val_eq e1, UScalar.eq_of_val_eq e2]
    | Infinite n2 => simp [binaryOf] at same; split at same <;> simp at same
    | NotANumber => simp [binaryOf] at same; split at same <;> simp at same
  | Infinite n1 =>
    cases b with
    | Finite n2 m2 s2 => simp [binaryOf] at same; split at same <;> simp at same
    | Infinite n2 => simp [binaryOf] at same; rw [same]
    | NotANumber => simp [binaryOf] at same
  | NotANumber =>
    cases b with
    | Finite n2 m2 s2 => simp [binaryOf] at same; split at same <;> simp at same
    | Infinite n2 => simp [binaryOf] at same
    | NotANumber => rfl

/-! ## The lexical forms are unambiguous -/

/-- Whether a byte is an ASCII digit. -/
def isDigitB (c : U8) : Bool := decide (Digit c)

theorem takeWhile_digits {A B : List U8} (dA : Digits A) (stop : ∀ c rest, B = c :: rest → ¬ Digit c) :
    (A ++ B).takeWhile isDigitB = A ∧ (A ++ B).dropWhile isDigitB = B := by
  induction A with
  | nil =>
    cases B with
    | nil => simp
    | cons c rest =>
      have := stop c rest rfl
      simp [isDigitB, this]
  | cons a A ih =>
    have da : Digit a := dA a List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih (fun b m => dA b (List.mem_cons_of_mem _ m))
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, isDigitB, da, decide_true,
      ↓reduceIte]
    exact ⟨congrArg _ h1, h2⟩

theorem not_digit_43 : ¬ Digit 43#u8 := by intro d; have := d.1; simp at this
theorem not_digit_45 : ¬ Digit 45#u8 := by intro d; have := d.1; simp at this
theorem not_digit_46 : ¬ Digit 46#u8 := by intro d; have := d.1; simp at this

theorem cons_ne_of_head {c d : U8} {l m : List U8} (h : c ≠ d) : c :: l ≠ d :: m := fun e => h (List.cons.inj e).1

theorem head_digit {d : List U8} (dd : Digits d) (ne : d ≠ []) : ∃ c t, d = c :: t ∧ Digit c := by
  cases d with
  | nil => exact absurd rfl ne
  | cons c t => exact ⟨c, t, rfl, dd c List.mem_cons_self⟩

/-- An exponent writes one number. -/
theorem exponent_unique {e : List U8} {x1 x2 : ℤ} (f1 : ExponentForm e x1) (f2 : ExponentForm e x2) : x1 = x2 := by
  rcases f1 with ⟨rfl, rfl⟩ | ⟨m1, s1, d1, n1, _, sf1, dd1, ne1, split1, rfl⟩
  · rcases f2 with ⟨_, rfl⟩ | ⟨m2, s2, d2, n2, _, _, _, _, split2, _⟩
    · rfl
    · cases split2
  · rcases f2 with ⟨empty, _⟩ | ⟨m2, s2, d2, n2, _, sf2, dd2, ne2, split2, rfl⟩
    · rw [empty] at split1; cases split1
    · rw [split1, List.cons_append, List.cons_append, List.cons.injEq] at split2
      have rest := split2.2
      obtain ⟨c1, t1, hd1, dc1⟩ := head_digit dd1 ne1
      obtain ⟨c2, t2, hd2, dc2⟩ := head_digit dd2 ne2
      have no1 : c1 ≠ 43#u8 ∧ c1 ≠ 45#u8 := ⟨fun h => not_digit_43 (h ▸ dc1), fun h => not_digit_45 (h ▸ dc1)⟩
      have no2 : c2 ≠ 43#u8 ∧ c2 ≠ 45#u8 := ⟨fun h => not_digit_43 (h ▸ dc2), fun h => not_digit_45 (h ▸ dc2)⟩
      rcases sf1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases sf2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [List.nil_append, List.singleton_append] at rest
      · rw [rest]
      · rw [hd1] at rest; exact absurd (List.cons.inj rest).1 no1.1
      · rw [hd1] at rest; exact absurd (List.cons.inj rest).1 no1.2
      · rw [hd2] at rest; exact absurd (List.cons.inj rest).1.symm no2.1
      · rw [(List.cons.inj rest).2]
      · exact absurd (List.cons.inj rest).1 (by decide)
      · rw [hd2] at rest; exact absurd (List.cons.inj rest).1.symm no2.2
      · exact absurd (List.cons.inj rest).1 (by decide)
      · rw [(List.cons.inj rest).2]

/-- The digits, the places after the point and the exponent of a numeral
    without its sign are determined. -/
theorem unsigned_unique {u1 u2 e1 e2 d1 d2 : List U8} {p1 p2 : ℕ} {x1 x2 : ℤ}
    (same : u1 ++ e1 = u2 ++ e2) (uf1 : UnsignedForm u1 d1 p1) (uf2 : UnsignedForm u2 d2 p2)
    (ef1 : ExponentForm e1 x1) (ef2 : ExponentForm e2 x2) : d1 = d2 ∧ p1 = p2 ∧ e1 = e2 := by
  obtain ⟨w1, f1, dw1, df1, hd1, hp1, sh1⟩ := uf1
  obtain ⟨w2, f2, dw2, df2, hd2, hp2, sh2⟩ := uf2
  subst hd1 hd2 hp1 hp2
  have stop1 := exponent_head ef1
  have stop2 := exponent_head ef2
  have pointStop : ∀ {f e : List U8}, ∀ c rest, (46#u8 :: (f ++ e)) = c :: rest → ¬ Digit c := by
    intro f e c rest h; rw [← (List.cons.inj h).1]; exact not_digit_46
  rcases sh1 with ⟨hu1, _, hf1⟩ | ⟨hu1, _⟩ <;> rcases sh2 with ⟨hu2, _, hf2⟩ | ⟨hu2, _⟩
  · subst hu1 hu2 hf1 hf2
    obtain ⟨a1, b1⟩ := takeWhile_digits dw1 (fun c rest h => (stop1 c rest h).1)
    obtain ⟨a2, b2⟩ := takeWhile_digits dw2 (fun c rest h => (stop2 c rest h).1)
    have w : u1 = u2 := a1.symm.trans (by rw [same]; exact a2)
    have e : e1 = e2 := b1.symm.trans (by rw [same]; exact b2)
    subst w e
    exact ⟨rfl, rfl, rfl⟩
  · subst hu1 hu2 hf1
    obtain ⟨_, b1⟩ := takeWhile_digits dw1 (fun c rest h => (stop1 c rest h).1)
    have b2 := (takeWhile_digits (B := 46#u8 :: (f2 ++ e2)) dw2 pointStop).2
    have h : e1 = 46#u8 :: (f2 ++ e2) := b1.symm.trans (by
      rw [same, List.append_assoc, List.cons_append]; exact b2)
    exact absurd rfl (stop1 _ _ h).2
  · subst hu1 hu2 hf2
    have b1 := (takeWhile_digits (B := 46#u8 :: (f1 ++ e1)) dw1 pointStop).2
    obtain ⟨_, b2⟩ := takeWhile_digits dw2 (fun c rest h => (stop2 c rest h).1)
    have h : e2 = 46#u8 :: (f1 ++ e1) := b2.symm.trans (by
      rw [← same, List.append_assoc, List.cons_append]; exact b1)
    exact absurd rfl (stop2 _ _ h).2
  · subst hu1 hu2
    have t1 := takeWhile_digits (B := 46#u8 :: (f1 ++ e1)) dw1 pointStop
    have t2 := takeWhile_digits (B := 46#u8 :: (f2 ++ e2)) dw2 pointStop
    have same' : w1 ++ 46#u8 :: (f1 ++ e1) = w2 ++ 46#u8 :: (f2 ++ e2) := by
      simpa only [List.append_assoc, List.cons_append] using same
    have ws : w1 = w2 := t1.1.symm.trans (by rw [same']; exact t2.1)
    have rests : f1 ++ e1 = f2 ++ e2 :=
      (List.cons.inj (t1.2.symm.trans (by rw [same']; exact t2.2))).2
    obtain ⟨c1, d1'⟩ := takeWhile_digits df1 (fun c rest h => (stop1 c rest h).1)
    obtain ⟨c2, d2'⟩ := takeWhile_digits df2 (fun c rest h => (stop2 c rest h).1)
    have fs : f1 = f2 := c1.symm.trans (by rw [rests]; exact c2)
    have es : e1 = e2 := d1'.symm.trans (by rw [rests]; exact d2')
    subst ws fs es
    exact ⟨rfl, rfl, rfl⟩

/-- A numeral writes one number, with one sign. -/
theorem numeralForm_unique {t : List U8} {n1 n2 : Bool} {v1 v2 : ℚ} (a : NumeralForm t n1 v1)
    (b : NumeralForm t n2 v2) : n1 = n2 ∧ v1 = v2 := by
  obtain ⟨s1, u1, e1, d1, p1, x1, split1, sf1, uf1, ef1, rfl⟩ := a
  obtain ⟨s2, u2, e2, d2, p2, x2, split2, sf2, uf2, ef2, rfl⟩ := b
  obtain ⟨c1, r1, hu1, hc1⟩ := unsigned_head uf1
  obtain ⟨c2, r2, hu2, hc2⟩ := unsigned_head uf2
  have notSign : ∀ c, (Digit c ∨ c = 46#u8) → c ≠ 43#u8 ∧ c ≠ 45#u8 := by
    intro c h
    rcases h with d | d
    · exact ⟨fun e => not_digit_43 (e ▸ d), fun e => not_digit_45 (e ▸ d)⟩
    · rw [d]; decide
  have no1 := notSign c1 hc1
  have no2 := notSign c2 hc2
  have both : s1 ++ (u1 ++ e1) = s2 ++ (u2 ++ e2) := by
    rw [← List.append_assoc, ← List.append_assoc, ← split1, ← split2]
  have rest : n1 = n2 ∧ u1 ++ e1 = u2 ++ e2 := by
    rw [hu1, hu2] at both
    rcases sf1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases sf2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [List.nil_append, List.singleton_append, List.cons_append] at both
    · exact ⟨rfl, by rw [hu1, hu2]; exact both⟩
    · exact absurd (List.cons.inj both).1 no1.1
    · exact absurd (List.cons.inj both).1 no1.2
    · exact absurd (List.cons.inj both).1.symm no2.1
    · exact ⟨rfl, by rw [hu1, hu2]; exact (List.cons.inj both).2⟩
    · exact absurd (List.cons.inj both).1 (by decide)
    · exact absurd (List.cons.inj both).1.symm no2.2
    · exact absurd (List.cons.inj both).1 (by decide)
    · exact ⟨rfl, by rw [hu1, hu2]; exact (List.cons.inj both).2⟩
  obtain ⟨rfl, same⟩ := rest
  obtain ⟨rfl, rfl, rfl⟩ := unsigned_unique same uf1 uf2 ef1 ef2
  rw [exponent_unique ef1 ef2]
  exact ⟨rfl, rfl⟩

/-- A lexical form of a format has one value. -/
theorem binaryForm_unique {double : Bool} {t : List U8} {a b : Binary} (fa : BinaryForm (fmt double) t a)
    (fb : BinaryForm (fmt double) t b) : a = b := by
  have notNumeral : ∀ n v, NumeralForm t n v → t ≠ [73#u8, 78#u8, 70#u8] ∧ t ≠ [43#u8, 73#u8, 78#u8, 70#u8] ∧
      t ≠ [45#u8, 73#u8, 78#u8, 70#u8] ∧ t ≠ [78#u8, 97#u8, 78#u8] := by
    intro n v form
    obtain ⟨s, u, e, d, p, x, split, sf, uf, _, _⟩ := form
    obtain ⟨c, r, hu, hc⟩ := unsigned_head uf
    have cNot : c ≠ 43#u8 ∧ c ≠ 45#u8 ∧ c ≠ 73#u8 ∧ c ≠ 78#u8 := by
      rcases hc with d | d
      · refine ⟨fun h => not_digit_43 (h ▸ d), fun h => not_digit_45 (h ▸ d), fun h => ?_, fun h => ?_⟩ <;>
          rw [h] at d <;> have := d.2 <;> simp at this
      · rw [d]; decide
    rw [split, hu]
    rcases sf with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      simp only [List.nil_append, List.singleton_append, List.cons_append]
    · exact ⟨cons_ne_of_head cNot.2.2.1, cons_ne_of_head cNot.1, cons_ne_of_head cNot.2.1,
        cons_ne_of_head cNot.2.2.2⟩
    · refine ⟨cons_ne_of_head (by decide), fun h => cNot.2.2.1 (List.cons.inj (List.cons.inj h).2).1,
        cons_ne_of_head (by decide), cons_ne_of_head (by decide)⟩
    · refine ⟨cons_ne_of_head (by decide), cons_ne_of_head (by decide),
        fun h => cNot.2.2.1 (List.cons.inj (List.cons.inj h).2).1, cons_ne_of_head (by decide)⟩
  rcases fa with ⟨ta, rfl⟩ | ⟨ta, rfl⟩ | ⟨ta, rfl⟩ | ⟨na, va, numa, vala⟩ <;>
    rcases fb with ⟨tb, rfl⟩ | ⟨tb, rfl⟩ | ⟨tb, rfl⟩ | ⟨nb, vb, numb, valb⟩
  · rfl
  · exfalso; rcases ta with h | h <;> rw [h] at tb <;> simp at tb
  · exfalso; rcases ta with h | h <;> rw [h] at tb <;> simp at tb
  · exfalso; obtain ⟨n1, n2, _, _⟩ := notNumeral nb vb numb; rcases ta with h | h; exacts [n1 h, n2 h]
  · exfalso; rcases tb with h | h <;> rw [h] at ta <;> simp at ta
  · rfl
  · exfalso; rw [ta] at tb; simp at tb
  · exfalso; exact (notNumeral nb vb numb).2.2.1 ta
  · exfalso; rcases tb with h | h <;> rw [h] at ta <;> simp at ta
  · exfalso; rw [ta] at tb; simp at tb
  · rfl
  · exfalso; exact (notNumeral nb vb numb).2.2.2 ta
  · exfalso; obtain ⟨n1, n2, _, _⟩ := notNumeral na va numa; rcases tb with h | h; exacts [n1 h, n2 h]
  · exfalso; exact (notNumeral na va numa).2.2.1 tb
  · exfalso; exact (notNumeral na va numa).2.2.2 tb
  · obtain ⟨rfl, rfl⟩ := numeralForm_unique numa numb
    rcases vala with ⟨z, rfl⟩ | ⟨nz, rfl⟩ <;> rcases valb with ⟨z', rfl⟩ | ⟨nz', rfl⟩
    · rfl
    · exact absurd z nz'
    · exact absurd z' nz
    · rfl

/-- The lexical forms of the formats are ASCII. -/
theorem binaryForm_ascii {double : Bool} {t : List U8} {b : Binary} (form : BinaryForm (fmt double) t b) :
    ∀ c ∈ t, c.val < 128 := by
  have digitsAscii : ∀ {l : List U8}, Digits l → ∀ c ∈ l, c.val < 128 := fun d c m => by
    have := (d c m).2; omega
  have signAscii : ∀ {s : List U8} {n : Bool}, SignForm s n → ∀ c ∈ s, c.val < 128 := by
    intro s n sf c m
    rcases sf with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp at m <;> subst m <;> decide
  rcases form with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨n, v, numeral, _⟩
  · rcases h with rfl | rfl <;> decide
  · rw [h]; decide
  · rw [h]; decide
  · obtain ⟨s, u, e, d, p, x, rfl, sf, uf, ef, _⟩ := numeral
    obtain ⟨w, f, dw, df, _, _, shape⟩ := uf
    intro c m
    simp only [List.mem_append] at m
    rcases m with (m | m) | m
    · exact signAscii sf c m
    · rcases shape with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact digitsAscii dw c m
      · simp only [List.mem_append, List.mem_cons] at m
        rcases m with m | m | m
        · exact digitsAscii dw c m
        · rw [m]; decide
        · exact digitsAscii df c m
    · rcases ef with ⟨rfl, _⟩ | ⟨mark, sign, digits, neg, isE, sf', dd, _, rfl, _⟩
      · simp at m
      · simp only [List.cons_append, List.mem_cons, List.mem_append] at m
        rcases m with m | m | m
        · rw [m]; rcases isE with h | h <;> rw [h] <;> decide
        · exact signAscii sf' c m
        · exact digitsAscii dd c m

end Rowl.Floats
