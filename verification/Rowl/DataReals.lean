import Rowl.Datatypes
import Mathlib.NumberTheory.Real.Irrational

/-!
Facts about the real line that the models of the data encoding need: between
any two reals lie infinitely many decimals that are no integers, rationals that
are no decimals, and irrational numbers (`levelSet_infinite`), and above or
below any real infinitely many integers. The four levels split the reals by
the numeric datatypes: integers, decimals that are no integers, rationals that
are no decimals, and the rest (`level`).
-/
namespace Rowl.DataReals
open Rowl.Datatypes (RealIn)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- The reals of a level: 0 the integers, 1 the decimals that are no integers,
    2 the rationals that are no decimals, and 3 the irrational numbers. -/
def AtLevel : Nat → ℝ → Prop
  | 0, r => RealIn .Integer r
  | 1, r => RealIn .Decimal r ∧ ¬ RealIn .Integer r
  | 2, r => RealIn .Rational r ∧ ¬ RealIn .Decimal r
  | _, r => ¬ RealIn .Rational r

theorem integer_decimal {r : ℝ} (h : RealIn .Integer r) : RealIn .Decimal r := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, 0, by simp⟩

theorem decimal_rational {r : ℝ} (h : RealIn .Decimal r) : RealIn .Rational r := by
  obtain ⟨z, n, rfl⟩ := h
  exact ⟨(z : ℚ) / 10 ^ n, by push_cast; rfl⟩

/-- Between two reals lies a fraction with a power of a base above one as its
    denominator and a numerator the base does not divide. -/
theorem fraction_between (base : ℕ) (big : 2 ≤ base) {a b : ℝ} (lt : a < b) :
    ∃ (k : ℤ) (n : ℕ), 1 ≤ n ∧ ¬ (base : ℤ) ∣ k ∧ a < (k : ℝ) / base ^ n ∧ (k : ℝ) / base ^ n < b := by
  have gap : 0 < b - a := by linarith
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (3 / (b - a)) (show (1 : ℝ) < base by exact_mod_cast big)
  set n := n0 + 1 with hn
  have powPos : (0 : ℝ) < (base : ℝ) ^ n := by positivity
  have powBig : 3 / (b - a) < (base : ℝ) ^ n := by
    calc 3 / (b - a) < (base : ℝ) ^ n0 := hn0
      _ ≤ (base : ℝ) ^ n := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ base)) (by omega)
  have step : 3 / (base : ℝ) ^ n < b - a := by
    rw [div_lt_iff₀ powPos]
    rw [div_lt_iff₀ gap] at powBig
    linarith
  set k0 := ⌊a * (base : ℝ) ^ n⌋ + 1 with hk0
  have above : a < (k0 : ℝ) / base ^ n := by
    rw [lt_div_iff₀ powPos, hk0]; push_cast; exact Int.lt_floor_add_one _
  have close : (k0 : ℝ) / base ^ n ≤ a + 1 / base ^ n := by
    rw [div_le_iff₀ powPos, add_mul, one_div, inv_mul_cancel₀ powPos.ne', hk0]
    push_cast
    linarith [Int.floor_le (a * (base : ℝ) ^ n)]
  by_cases divides : (base : ℤ) ∣ k0
  · refine ⟨k0 + 1, n, by omega, fun d => ?_, ?_, ?_⟩
    · have : (base : ℤ) ∣ 1 := by simpa using (Int.dvd_add_right divides).mp d
      have := Int.le_of_dvd (by norm_num) this
      omega
    · calc a < (k0 : ℝ) / base ^ n := above
        _ < ((k0 + 1 : ℤ) : ℝ) / base ^ n := by
          apply div_lt_div_of_pos_right _ powPos; push_cast; linarith
    · have : ((k0 + 1 : ℤ) : ℝ) / base ^ n = (k0 : ℝ) / base ^ n + 1 / base ^ n := by push_cast; ring
      rw [this]
      have : 1 / (base : ℝ) ^ n < (b - a) / 2 := by
        have : 1 / (base : ℝ) ^ n = (1 / 3) * (3 / base ^ n) := by ring
        rw [this]; linarith
      linarith
  · refine ⟨k0, n, by omega, divides, above, ?_⟩
    have : 1 / (base : ℝ) ^ n < b - a := by
      have : 1 / (base : ℝ) ^ n = (1 / 3) * (3 / base ^ n) := by ring
      rw [this]; linarith
    linarith

theorem not_integer_of_fraction {k : ℤ} {n : ℕ} (one : 1 ≤ n) (notDiv : ¬ (10 : ℤ) ∣ k) :
    ¬ RealIn .Integer ((k : ℝ) / 10 ^ n) := by
  rintro ⟨z, hz⟩
  have powPos : (0 : ℝ) < 10 ^ n := by positivity
  have : (k : ℝ) = z * 10 ^ n := by rw [div_eq_iff powPos.ne'] at hz; exact hz
  have : k = z * 10 ^ n := by exact_mod_cast this
  apply notDiv
  rw [this]
  exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) z

theorem not_decimal_of_third {k : ℤ} {n : ℕ} (one : 1 ≤ n) (notDiv : ¬ (3 : ℤ) ∣ k) :
    ¬ RealIn .Decimal ((k : ℝ) / 3 ^ n) := by
  rintro ⟨z, m, hz⟩
  have p3 : (0 : ℝ) < 3 ^ n := by positivity
  have p10 : (0 : ℝ) < 10 ^ m := by positivity
  have : (k : ℝ) * 10 ^ m = z * 3 ^ n := by
    field_simp at hz; linarith
  have eq : k * 10 ^ m = z * 3 ^ n := by exact_mod_cast this
  have three : (3 : ℤ) ∣ k * 10 ^ m := by
    rw [eq]; exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) z
  have prime : Prime (3 : ℤ) := Int.prime_three
  rcases prime.dvd_or_dvd three with h | h
  · exact notDiv h
  · have := prime.dvd_of_dvd_pow h
    norm_num at this

/-- Every open interval has a real of each level but the integers. -/
theorem level_between {a b : ℝ} (lt : a < b) (ℓ : Nat) (level : 1 ≤ ℓ) : ∃ r, AtLevel ℓ r ∧ a < r ∧ r < b := by
  match ℓ, level with
  | 1, _ =>
    obtain ⟨k, n, one, notDiv, lo, hi⟩ := fraction_between 10 (by norm_num) lt
    refine ⟨(k : ℝ) / (10 : ℕ) ^ n, ⟨⟨k, n, by push_cast; rfl⟩, ?_⟩, lo, hi⟩
    push_cast
    exact not_integer_of_fraction one (by exact_mod_cast notDiv)
  | 2, _ =>
    obtain ⟨k, n, one, notDiv, lo, hi⟩ := fraction_between 3 (by norm_num) lt
    refine ⟨(k : ℝ) / (3 : ℕ) ^ n, ⟨⟨(k : ℚ) / 3 ^ n, by push_cast; rfl⟩, ?_⟩, lo, hi⟩
    push_cast
    exact not_decimal_of_third one (by exact_mod_cast notDiv)
  | ℓ + 3, _ =>
    obtain ⟨r, irrational, lo, hi⟩ := exists_irrational_btwn lt
    refine ⟨r, ?_, lo, hi⟩
    rintro ⟨q, rfl⟩
    exact irrational ⟨q, rfl⟩

/-- A set of reals that meets every open interval meets each in infinitely
    many points. -/
theorem dense_infinite (S : Set ℝ) (meets : ∀ a b, a < b → ∃ x ∈ S, a < x ∧ x < b) {a b : ℝ} (lt : a < b) :
    (S ∩ Set.Ioo a b).Infinite := by
  intro finite
  obtain ⟨x, xS, lo, hi⟩ := meets a b lt
  have nonempty : (S ∩ Set.Ioo a b).Nonempty := ⟨x, xS, lo, hi⟩
  obtain ⟨m, mIn, mMin⟩ := finite.exists_minimal nonempty
  obtain ⟨y, yS, lo', hi'⟩ := meets a m mIn.2.1
  have yIn : y ∈ S ∩ Set.Ioo a b := ⟨yS, lo', lt_trans hi' mIn.2.2⟩
  exact absurd (mMin yIn (le_of_lt hi')) (not_le.mpr hi')

/-- Every open interval has infinitely many reals of each level but the
    integers. -/
theorem level_infinite {a b : ℝ} (lt : a < b) (ℓ : Nat) (level : 1 ≤ ℓ) :
    ({r | AtLevel ℓ r} ∩ Set.Ioo a b).Infinite :=
  dense_infinite _ (fun a b lt => by
    obtain ⟨r, at_r, lo, hi⟩ := level_between lt ℓ level
    exact ⟨r, at_r, lo, hi⟩) lt

/-- Above any real there are infinitely many integers. -/
theorem integers_above (a : ℝ) : ({r | AtLevel 0 r} ∩ Set.Ioi a).Infinite := by
  intro finite
  obtain ⟨M, bound⟩ := finite.bddAbove
  have big : ((⌈max a M⌉ + 1 : ℤ) : ℝ) ∈ {r | AtLevel 0 r} ∩ Set.Ioi a := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    simp only [Set.mem_Ioi]
    push_cast
    linarith [Int.le_ceil (max a M), le_max_left a M]
  have := bound big
  push_cast at this
  linarith [Int.le_ceil (max a M), le_max_right a M]

/-- Below any real there are infinitely many integers. -/
theorem integers_below (b : ℝ) : ({r | AtLevel 0 r} ∩ Set.Iio b).Infinite := by
  intro finite
  obtain ⟨M, bound⟩ := finite.bddBelow
  have small : ((⌊min b M⌋ - 1 : ℤ) : ℝ) ∈ {r | AtLevel 0 r} ∩ Set.Iio b := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    simp only [Set.mem_Iio]
    push_cast
    linarith [Int.floor_le (min b M), min_le_left b M]
  have := bound small
  push_cast at this
  linarith [Int.floor_le (min b M), min_le_right b M]

end Rowl.DataReals
