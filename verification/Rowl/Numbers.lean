import Rowl.DatatypeMap

/-!
The actual kernel functions of `numbers`: exact arithmetic on natural numbers
written as the ASCII digits of their canonical spelling, most significant first
and without leading zeros (`Canonical`). Comparison, addition, subtraction,
multiplication, division with remainder and the greatest common divisor are
proved to compute exactly what the digits' values (`digitsValue`, the base-ten
reading of the specification) say, for numbers of any length within the
`usize` bounds stated by each theorem.
-/
namespace Rowl.Numbers
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust
open Rowl.DatatypeMap (Digit Digits digitsValue)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- A number's canonical spelling: ASCII digits without a leading zero. -/
def Canonical (digits : List U8) : Prop := Digits digits ∧ digits.head? ≠ some 48#u8

/-- The order of two numbers as the kernel writes it: 0 when the first is
    smaller, 1 when they are equal, 2 when it is greater. -/
def order (a b : Nat) : Nat := if a < b then 0 else if a = b then 1 else 2

/-- The value of the digit `index` places from the right, and 0 beyond the
    digits. -/
def digitAt (digits : List U8) (index : Nat) : Nat :=
  if h : index < digits.length then (digits[digits.length - 1 - index]'(by omega)).val - 48 else 0

/-- The value of the lowest `count` places of the digits. -/
def low (digits : List U8) : Nat → Nat
  | 0 => 0
  | count + 1 => low digits count + digitAt digits count * 10 ^ count

/-- The value of digits written least significant first. -/
def backValue (digits : List U8) : Nat := digitsValue digits.reverse

/-! ### Values of digit lists -/

theorem fold_value (init : Nat) (bytes : List U8) :
    bytes.foldl (fun value byte => 10 * value + (byte.val - 48)) init = init * 10 ^ bytes.length + digitsValue bytes := by
  induction bytes generalizing init with
  | nil => simp [digitsValue]
  | cons head tail ih =>
    simp only [List.foldl_cons, digitsValue, List.length_cons]
    rw [ih, ih (10 * 0 + (head.val - 48))]
    ring

theorem value_nil : digitsValue [] = 0 := rfl

theorem value_cons (head : U8) (tail : List U8) :
    digitsValue (head :: tail) = (head.val - 48) * 10 ^ tail.length + digitsValue tail := by
  rw [digitsValue, List.foldl_cons, fold_value]
  ring

theorem value_append (a b : List U8) : digitsValue (a ++ b) = digitsValue a * 10 ^ b.length + digitsValue b := by
  rw [digitsValue, List.foldl_append, fold_value]
  rfl

theorem value_snoc (a : List U8) (b : U8) : digitsValue (a ++ [b]) = 10 * digitsValue a + (b.val - 48) := by
  rw [value_append, value_cons, value_nil]
  simp; ring

theorem value_lt (bytes : List U8) (digits : Digits bytes) : digitsValue bytes < 10 ^ bytes.length := by
  induction bytes with
  | nil => simp [digitsValue]
  | cons head tail ih =>
    rw [value_cons]
    have d := digits head List.mem_cons_self
    have rest := ih (fun b m => digits b (List.mem_cons_of_mem _ m))
    have small : head.val - 48 ≤ 9 := by have := d.2; omega
    simp only [List.length_cons, pow_succ]
    nlinarith

theorem digits_cons {head : U8} {tail : List U8} : Digits (head :: tail) ↔ Digit head ∧ Digits tail := by
  simp [Digits]

theorem digits_append {a b : List U8} : Digits (a ++ b) ↔ Digits a ∧ Digits b := by
  simp [Digits, or_imp, forall_and]

theorem digits_reverse {a : List U8} : Digits a.reverse ↔ Digits a := by
  simp [Digits]

theorem digits_drop {a : List U8} (d : Digits a) (n : Nat) : Digits (a.drop n) :=
  fun b m => d b (List.mem_of_mem_drop m)

theorem digits_take {a : List U8} (d : Digits a) (n : Nat) : Digits (a.take n) :=
  fun b m => d b (List.mem_of_mem_take m)

/-- Leading zeros do not change the value. -/
theorem value_zeros_append (zeros rest : List U8) (all : ∀ b ∈ zeros, b = 48#u8) :
    digitsValue (zeros ++ rest) = digitsValue rest := by
  induction zeros with
  | nil => rfl
  | cons head tail ih =>
    rw [List.cons_append, value_cons, all head List.mem_cons_self, ih (fun b m => all b (List.mem_cons_of_mem _ m))]
    simp

theorem canonical_low (digits : List U8) (canonical : Canonical digits) (nonempty : digits ≠ []) :
    10 ^ (digits.length - 1) ≤ digitsValue digits := by
  cases digits with
  | nil => exact absurd rfl nonempty
  | cons head tail =>
    rw [value_cons]
    have d := canonical.1 head List.mem_cons_self
    have notZero : head.val ≠ 48 := fun h => canonical.2 (by simp; exact UScalar.eq_of_val_eq (by simpa using h))
    have : 1 ≤ head.val - 48 := by have := d.1; omega
    simp only [List.length_cons, Nat.add_sub_cancel]
    calc 10 ^ tail.length ≤ (head.val - 48) * 10 ^ tail.length := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ _ := Nat.le_add_right _ _

/-- A canonical spelling is zero exactly when it is empty. -/
theorem canonical_zero (digits : List U8) (canonical : Canonical digits) :
    digitsValue digits = 0 ↔ digits = [] := by
  constructor
  · intro zero
    by_contra nonempty
    have := canonical_low digits canonical nonempty
    have : 0 < 10 ^ (digits.length - 1) := by positivity
    omega
  · rintro rfl; rfl

/-- A longer canonical spelling writes a greater number. -/
theorem canonical_shorter (a b : List U8) (ca : Canonical a) (cb : Canonical b) (shorter : a.length < b.length) :
    digitsValue a < digitsValue b := by
  have nonempty : b ≠ [] := by
    intro h; rw [h] at shorter; simp at shorter
  have high := value_lt a ca.1
  have low := canonical_low b cb nonempty
  have : 10 ^ a.length ≤ 10 ^ (b.length - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem digit_eq (a b : U8) (da : Digit a) (db : Digit b) (same : a.val - 48 = b.val - 48) : a = b := by
  have := da.1; have := db.1
  apply UScalar.eq_of_val_eq
  omega

theorem same_length_unique (a b : List U8) (da : Digits a) (db : Digits b) (length : a.length = b.length)
    (value : digitsValue a = digitsValue b) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => simp at length
  | cons x rest ih =>
    cases b with
    | nil => simp at length
    | cons y rest' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at length
      rw [value_cons, value_cons, length] at value
      have restDigits : Digits rest := fun c m => da c (List.mem_cons_of_mem _ m)
      have restDigits' : Digits rest' := fun c m => db c (List.mem_cons_of_mem _ m)
      have small := value_lt rest restDigits
      have small' := value_lt rest' restDigits'
      rw [length] at small
      have pos : 0 < 10 ^ rest'.length := by positivity
      have heads : x.val - 48 = y.val - 48 := by
        have h1 := Nat.add_mul_div_right (digitsValue rest) (x.val - 48) pos
        have h2 := Nat.add_mul_div_right (digitsValue rest') (y.val - 48) pos
        rw [Nat.div_eq_of_lt small] at h1
        rw [Nat.div_eq_of_lt small'] at h2
        have : digitsValue rest + (x.val - 48) * 10 ^ rest'.length =
            digitsValue rest' + (y.val - 48) * 10 ^ rest'.length := by omega
        rw [this] at h1
        omega
      have tails : digitsValue rest = digitsValue rest' := by rw [heads] at value; omega
      rw [digit_eq x y (da x List.mem_cons_self) (db y List.mem_cons_self) heads,
        ih rest' restDigits restDigits' length tails]

/-- Canonical spellings are the same exactly when their numbers are. -/
theorem canonical_unique (a b : List U8) (ca : Canonical a) (cb : Canonical b)
    (value : digitsValue a = digitsValue b) : a = b := by
  apply same_length_unique a b ca.1 cb.1 _ value
  by_contra different
  rcases Nat.lt_or_gt_of_ne different with less | more
  · have := canonical_shorter a b ca cb less; omega
  · have := canonical_shorter b a cb ca more; omega

theorem canonical_nil : Canonical [] := ⟨fun _ m => by simp at m, by simp⟩

/-! ### Digits from the right -/

theorem digitAt_of_lt (l : List U8) (i : Nat) (h : i < l.length) :
    digitAt l i = (l[l.length - 1 - i]'(by omega)).val - 48 := by
  simp [digitAt, h]

theorem digitAt_of_ge (l : List U8) (i : Nat) (h : l.length ≤ i) : digitAt l i = 0 := by
  simp only [digitAt]; split <;> omega

theorem digitAt_le (l : List U8) (d : Digits l) (i : Nat) : digitAt l i ≤ 9 := by
  unfold digitAt
  split
  · rename_i h
    have m : l[l.length - 1 - i]'(by omega) ∈ l := List.getElem_mem _
    have := (d _ m).2
    omega
  · omega

theorem low_drop (l : List U8) (j : Nat) (hj : j ≤ l.length) :
    low l j = digitsValue (l.drop (l.length - j)) := by
  induction j with
  | zero => simp [low, value_nil]
  | succ j ih =>
    rw [low, ih (by omega)]
    have inside : l.length - (j + 1) < l.length := by omega
    rw [List.drop_eq_getElem_cons inside, value_cons, digitAt_of_lt l j (by omega)]
    have e1 : l.length - (j + 1) + 1 = l.length - j := by omega
    have e2 : l.length - 1 - j = l.length - (j + 1) := by omega
    have e3 : (l.drop (l.length - j)).length = j := by simp; omega
    simp only [e1, e2, e3]
    ring

theorem low_full (l : List U8) (j : Nat) (hj : l.length ≤ j) : low l j = digitsValue l := by
  induction j with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | succ j ih =>
    by_cases inside : j < l.length
    · have : j + 1 = l.length := by omega
      rw [this, low_drop l l.length le_rfl]
      simp
    · rw [low, ih (by omega), digitAt_of_ge l j (by omega)]
      simp

theorem low_lt (l : List U8) (d : Digits l) (j : Nat) : low l j < 10 ^ j := by
  induction j with
  | zero => simp [low]
  | succ j ih =>
    rw [low, pow_succ]
    have := digitAt_le l d j
    nlinarith

theorem backValue_nil : backValue [] = 0 := rfl

theorem backValue_snoc (out : List U8) (b : U8) :
    backValue (out ++ [b]) = backValue out + (b.val - 48) * 10 ^ out.length := by
  simp only [backValue, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, value_cons, List.length_reverse]
  ring

/-! ### Scanning -/

theorem digit_value_spec (byte : U8) :
    ∃ d, numbers.digit_value byte = .ok d ∧ d.val = (if Digit byte then byte.val - 48 else 0) := by
  rw [numbers.digit_value]
  by_cases digit : Digit byte
  · have a : (48#u8) ≤ byte := by simp only [UScalar.le_equiv]; simpa using digit.1
    have b : byte ≤ (57#u8) := by simp only [UScalar.le_equiv]; simpa using digit.2
    obtain ⟨d, sub, dValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := byte) (y := 48#u8) (by scalar_tac))
    refine ⟨d, by simp [a, b, sub], by simp [digit, dValue]⟩
  · refine ⟨0#u8, ?_, by simp [digit]⟩
    simp only [Digit, not_and_or, not_le] at digit
    rcases digit with low | high
    · have : ¬ (48#u8) ≤ byte := by simp only [UScalar.le_equiv]; simp; omega
      simp [this]
    · have : ¬ byte ≤ (57#u8) := by simp only [UScalar.le_equiv]; simp; omega
      simp [this]

theorem digit_at_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (index : Usize) :
    ∃ d, numbers.digit_at digits index = .ok d ∧ d.val = digitAt digits.val index.val := by
  rw [numbers.digit_at]
  by_cases inside : index.val < digits.val.length
  · obtain ⟨last, lastRun, lastValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len digits) (y := 1#usize) (by simp; omega))
    have lastIs : last.val = digits.val.length - 1 := by simp at lastValue; omega
    obtain ⟨at', atRun, atValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := last) (y := index) (by scalar_tac))
    have atIs : at'.val = digits.val.length - 1 - index.val := by omega
    have within : at'.val < digits.val.length := by omega
    have lookup : digits.index_usize at' = .ok digits.val[at'.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem within]
    obtain ⟨d, dRun, dValue⟩ := digit_value_spec digits.val[at'.val]
    refine ⟨d, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside, lastRun, atRun, alloc.vec.Vec.index_slice_index, lookup, dRun]
    · have digit := dd _ (List.getElem_mem within)
      rw [dValue, if_pos digit, digitAt_of_lt _ _ inside]
      simp only [atIs]
  · refine ⟨0#u8, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [digitAt_of_ge _ _ (by omega)]; rfl

theorem reverse_into_spec (digits : alloc.vec.Vec U8) («end» : Usize) (out : alloc.vec.Vec U8)
    (fits : «end».val ≤ digits.val.length) (room : out.val.length + «end».val ≤ Usize.max) :
    ∃ v, numbers.reverse_into digits «end» out = .ok v ∧ v.val = out.val ++ (digits.val.take «end».val).reverse := by
  rw [numbers.reverse_into]
  by_cases positive : 0 < «end».val
  · obtain ⟨last, lastRun, lastValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := «end») (y := 1#usize) (by scalar_tac))
    have lastIs : last.val = «end».val - 1 := by simp at lastValue; omega
    have within : last.val < digits.val.length := by omega
    have lookup : digits.index_usize last = .ok digits.val[last.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem within]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out digits.val[last.val] short)
    obtain ⟨v, run, value⟩ := reverse_into_spec digits last pushed (by omega) (by rw [contents]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · have fitsLe : «end» ≤ alloc.vec.Vec.len digits := by simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact fits
      have pos : (0#usize) < «end» := by simp only [UScalar.lt_equiv]; simpa using positive
      simp [pos, fitsLe, UScalar.lt_equiv, short, lastRun, alloc.vec.Vec.index_slice_index, lookup, push, run]
    · have hend : «end».val = last.val + 1 := by omega
      have takeIs : digits.val.take «end».val = digits.val.take last.val ++ [digits.val[last.val]] := by
        rw [hend, List.take_add_one, List.getElem?_eq_getElem within]; rfl
      rw [value, contents, takeIs, List.reverse_append]
      simp
  · have zero : «end».val = 0 := by omega
    refine ⟨out, ?_, by simp [zero]⟩
    have notPos : ¬ (0#usize) < «end» := by simp only [UScalar.lt_equiv]; simpa using zero
    simp [notPos]
termination_by «end».val
decreasing_by omega

theorem first_nonzero_spec (digits : alloc.vec.Vec U8) (index : Usize) (h : index.val ≤ digits.val.length) :
    ∃ r, numbers.first_nonzero digits index = .ok r ∧ index.val ≤ r.val ∧ r.val ≤ digits.val.length ∧
      (∀ i (hi : i < digits.val.length), index.val ≤ i → i < r.val → digits.val[i] = 48#u8) ∧
      ∀ hr : r.val < digits.val.length, digits.val[r.val] ≠ 48#u8 := by
  rw [numbers.first_nonzero]
  by_cases inside : index.val < digits.val.length
  · have lookup : digits.index_usize index = .ok digits.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases zero : digits.val[index.val] = 48#u8
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, low, high, zeros, stop⟩ := first_nonzero_spec digits next (by omega)
      refine ⟨r, ?_, by omega, high, ?_, stop⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, zero, advance, run]
      · intro i hi lowi highi
        by_cases same : i = index.val
        · subst same; exact zero
        · exact zeros i hi (by omega) highi
    · refine ⟨index, ?_, le_rfl, h, fun i _ low high => absurd high (by omega), fun _ => zero⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, zero]
  · refine ⟨alloc.vec.Vec.len digits, by simp [UScalar.lt_equiv, inside], by simp; omega, by simp,
      fun i hi low high => absurd low (by omega), fun hr => by simp at hr⟩
termination_by digits.val.length - index.val
decreasing_by omega

theorem copy_from_spec (digits : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length + (digits.val.length - index.val) ≤ Usize.max) :
    ∃ v, numbers.copy_from digits index out = .ok v ∧ v.val = out.val ++ digits.val.drop index.val := by
  rw [numbers.copy_from]
  by_cases inside : index.val < digits.val.length
  · have lookup : digits.index_usize index = .ok digits.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out digits.val[index.val] short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_from_spec digits next pushed (by rw [contents, nextIndex]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside, short, alloc.vec.Vec.index_slice_index, lookup, push, advance, run]
    · rw [value, contents, nextIndex, List.drop_eq_getElem_cons inside]
      simp
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show digits.val.length ≤ index.val by omega)]
termination_by digits.val.length - index.val
decreasing_by omega

/-- The canonical spelling of a digit vector: its value, without the leading
    zeros. -/
theorem canonical_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) :
    ∃ c, numbers.canonical digits = .ok c ∧ Canonical c.val ∧ digitsValue c.val = digitsValue digits.val ∧
      c.val.length ≤ digits.val.length := by
  rw [numbers.canonical]
  obtain ⟨r, run, _, high, zeros, stop⟩ := first_nonzero_spec digits 0#usize (by simp)
  obtain ⟨c, copy, value⟩ := copy_from_spec digits r (alloc.vec.Vec.new U8) (by simp; scalar_tac)
  have cIs : c.val = digits.val.drop r.val := by rw [value]; rfl
  have allZeros : ∀ b ∈ digits.val.take r.val, b = 48#u8 := by
    intro b member
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem member
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    exact zeros i (by omega) (by simp) (by omega)
  refine ⟨c, by simp [run, copy], ⟨?_, ?_⟩, ?_, by rw [cIs]; simp⟩
  · rw [cIs]; exact digits_drop dd r.val
  · rw [cIs]
    by_cases inside : r.val < digits.val.length
    · rw [List.drop_eq_getElem_cons inside, List.head?_cons]
      intro same
      exact stop inside (Option.some.inj same)
    · simp [List.drop_eq_nil_iff.mpr (show digits.val.length ≤ r.val by omega)]
  · rw [cIs]
    calc digitsValue (digits.val.drop r.val)
        = digitsValue (digits.val.take r.val ++ digits.val.drop r.val) := (value_zeros_append _ _ allZeros).symm
      _ = digitsValue digits.val := by rw [List.take_append_drop]

theorem canonical_reversed_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) :
    ∃ c, numbers.canonical_reversed digits = .ok c ∧ Canonical c.val ∧
      digitsValue c.val = backValue digits.val ∧ c.val.length ≤ digits.val.length := by
  rw [numbers.canonical_reversed]
  obtain ⟨v, run, value⟩ := reverse_into_spec digits (alloc.vec.Vec.len digits) (alloc.vec.Vec.new U8)
    (by simp) (by simp)
  have vIs : v.val = digits.val.reverse := by rw [value]; simp
  obtain ⟨c, crun, cc, cvalue, clen⟩ := canonical_spec v (by rw [vIs]; exact digits_reverse.mpr dd)
  refine ⟨c, by simp [run, crun], cc, by rw [cvalue, vIs]; rfl, by rw [vIs] at clen; simpa using clen⟩

theorem new_val : (alloc.vec.Vec.new U8).val = [] := rfl

/-- A canonical spelling of a number below `10 ^ m` has at most `m` digits. -/
theorem canonical_length_le (l : List U8) (c : Canonical l) (m : Nat) (h : digitsValue l < 10 ^ m) :
    l.length ≤ m := by
  by_contra more
  have nonempty : l ≠ [] := by intro e; subst e; simp at more
  have := canonical_low l c nonempty
  have : 10 ^ m ≤ 10 ^ (l.length - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### Comparison -/

theorem order_lt {a b : Nat} (h : a < b) : order a b = 0 := by simp [order, h]
theorem order_eq {a b : Nat} (h : a = b) : order a b = 1 := by simp [order, h]
theorem order_gt {a b : Nat} (h : b < a) : order a b = 2 := by
  simp only [order]; split_ifs <;> omega

theorem value_cons_lt (x y : U8) (a b : List U8) (dx : Digit x) (dy : Digit y) (da : Digits a)
    (length : a.length = b.length) (less : x.val < y.val) : digitsValue (x :: a) < digitsValue (y :: b) := by
  rw [value_cons, value_cons, ← length]
  have small := value_lt a da
  have : (x.val - 48 + 1) * 10 ^ a.length ≤ (y.val - 48) * 10 ^ a.length :=
    Nat.mul_le_mul_right _ (by have := dx.1; have := dy.1; omega)
  nlinarith

theorem compare_from_spec (left right : alloc.vec.Vec U8) (dl : Digits left.val) (dr : Digits right.val)
    (same : left.val.length = right.val.length) (index : Usize) (h : index.val ≤ left.val.length) :
    ∃ r, numbers.compare_from left right index = .ok r ∧
      r.val = order (digitsValue (left.val.drop index.val)) (digitsValue (right.val.drop index.val)) := by
  rw [numbers.compare_from]
  by_cases inside : index.val < left.val.length
  · have inside' : index.val < right.val.length := by omega
    have lookupL : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have lookupR : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside']
    have dx := dl _ (List.getElem_mem inside)
    have dy := dr _ (List.getElem_mem inside')
    have restL := digits_drop dl (index.val + 1)
    have restR := digits_drop dr (index.val + 1)
    have lengths : (left.val.drop (index.val + 1)).length = (right.val.drop (index.val + 1)).length := by
      simp [same]
    rw [List.drop_eq_getElem_cons inside, List.drop_eq_getElem_cons inside']
    by_cases less : (left.val[index.val]).val < (right.val[index.val]).val
    · refine ⟨0#u8, by simp [UScalar.lt_equiv, inside, inside', alloc.vec.Vec.index_slice_index, lookupL,
        lookupR, less], ?_⟩
      rw [order_lt (value_cons_lt _ _ _ _ dx dy restL lengths less)]; rfl
    · by_cases greater : (right.val[index.val]).val < (left.val[index.val]).val
      · refine ⟨2#u8, by simp [UScalar.lt_equiv, inside, inside', alloc.vec.Vec.index_slice_index, lookupL,
          lookupR, less, greater], ?_⟩
        rw [order_gt (value_cons_lt _ _ _ _ dy dx restR lengths.symm greater)]; rfl
      · have equal : left.val[index.val] = right.val[index.val] := by
          apply UScalar.eq_of_val_eq
          omega
        obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : next.val = index.val + 1 := by simpa using nextValue
        obtain ⟨r, run, value⟩ := compare_from_spec left right dl dr same next (by omega)
        refine ⟨r, by simp [UScalar.lt_equiv, inside, inside', alloc.vec.Vec.index_slice_index, lookupL, lookupR,
          less, greater, advance, run], ?_⟩
        rw [value, nextIndex, value_cons, value_cons, equal, lengths]
        simp only [order]
        split_ifs <;> omega
  · refine ⟨1#u8, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [List.drop_eq_nil_iff.mpr (by omega : left.val.length ≤ index.val),
      List.drop_eq_nil_iff.mpr (by omega : right.val.length ≤ index.val)]
    simp [order, value_nil]
termination_by left.val.length - index.val
decreasing_by omega

/-- The kernel compares canonical numbers exactly. -/
theorem compare_naturals_spec (left right : alloc.vec.Vec U8) (cl : Canonical left.val) (cr : Canonical right.val) :
    ∃ r, numbers.compare_naturals left right = .ok r ∧ r.val = order (digitsValue left.val) (digitsValue right.val) := by
  rw [numbers.compare_naturals]
  by_cases shorter : left.val.length < right.val.length
  · refine ⟨0#u8, by simp [UScalar.lt_equiv, shorter], ?_⟩
    rw [order_lt (canonical_shorter _ _ cl cr shorter)]; rfl
  · by_cases longer : right.val.length < left.val.length
    · refine ⟨2#u8, by simp [UScalar.lt_equiv, shorter, longer], ?_⟩
      rw [order_gt (canonical_shorter _ _ cr cl longer)]; rfl
    · obtain ⟨r, run, value⟩ := compare_from_spec left right cl.1 cr.1 (by omega) 0#usize (by simp)
      exact ⟨r, by simp [UScalar.lt_equiv, shorter, longer, run], by simpa using value⟩

/-! ### Addition -/

theorem within_either_spec (left right : alloc.vec.Vec U8) (index : Usize) :
    numbers.within_either left right index =
      .ok (decide (index.val < left.val.length ∨ index.val < right.val.length)) := by
  simp [numbers.within_either, UScalar.lt_equiv]

theorem add_from_spec (left right : alloc.vec.Vec U8) (dl : Digits left.val) (dr : Digits right.val)
    (small : left.val.length + right.val.length < Usize.max)
    (index : Usize) (carry : U8) (out : alloc.vec.Vec U8)
    (hindex : index.val ≤ max left.val.length right.val.length)
    (hcarry : carry.val ≤ 1) (hlen : out.val.length = index.val) (dout : Digits out.val)
    (inv : backValue out.val + carry.val * 10 ^ index.val = low left.val index.val + low right.val index.val) :
    ∃ v, numbers.add_from left right index carry out = .ok v ∧ Digits v.val ∧
      backValue v.val = digitsValue left.val + digitsValue right.val ∧
      v.val.length ≤ max left.val.length right.val.length + 1 := by
  rw [numbers.add_from]
  by_cases more : index.val < left.val.length ∨ index.val < right.val.length
  · obtain ⟨a, aRun, aValue⟩ := digit_at_spec left dl index
    obtain ⟨b, bRun, bValue⟩ := digit_at_spec right dr index
    have ha := digitAt_le left.val dl index.val
    have hb := digitAt_le right.val dr index.val
    obtain ⟨ab, abRun, abValue⟩ := WP.spec_imp_exists (U8.add_spec (x := a) (y := b) (by scalar_tac))
    obtain ⟨sum, sumRun, sumValue⟩ := WP.spec_imp_exists (U8.add_spec (x := ab) (y := carry) (by scalar_tac))
    have sumIs : sum.val = digitAt left.val index.val + digitAt right.val index.val + carry.val := by
      rw [sumValue, abValue, aValue, bValue]
    have short : out.val.length < Usize.max := by
      have := Nat.le_max_left left.val.length right.val.length
      have := Nat.le_max_right left.val.length right.val.length
      omega
    obtain ⟨m, mRun, mValue⟩ := WP.spec_imp_exists (UScalar.rem_spec sum (y := 10#u8) (by simp))
    obtain ⟨digit, digitRun, digitValue⟩ := WP.spec_imp_exists
      (U8.add_spec (x := 48#u8) (y := m) (by have := Nat.mod_lt sum.val (show 0 < 10 by norm_num); scalar_tac))
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out digit short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨c', cRun, cValue⟩ := UScalar.div_spec sum (y := 10#u8) (by simp)
    have mIs : m.val = sum.val % 10 := by simpa using mValue
    have cIs : c'.val = sum.val / 10 := by simpa using cValue
    have digitIs : digit.val = 48 + sum.val % 10 := by rw [digitValue, mIs]; rfl
    have key : sum.val % 10 + 10 * (sum.val / 10) = sum.val := Nat.mod_add_div _ _
    have invNext : backValue pushed.val + c'.val * 10 ^ next.val =
        low left.val next.val + low right.val next.val := by
      rw [contents, backValue_snoc, nextIndex, low, low, hlen, digitIs, cIs, pow_succ]
      have e : 48 + sum.val % 10 - 48 = sum.val % 10 := by omega
      rw [e]
      have scaled : (sum.val % 10 + 10 * (sum.val / 10)) * 10 ^ index.val =
          (digitAt left.val index.val + digitAt right.val index.val + carry.val) * 10 ^ index.val := by
        rw [key, sumIs]
      nlinarith [scaled, inv]
    obtain ⟨v, run, dv, value, len⟩ := add_from_spec left right dl dr small next c' pushed
      (by
        rw [nextIndex]
        rcases more with h | h
        · exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
        · exact Nat.le_trans (by omega) (Nat.le_max_right _ _))
      (by rw [cIs, sumIs]; omega) (by rw [contents, nextIndex]; simp [hlen])
      (by
        rw [contents]
        refine digits_append.mpr ⟨dout, ?_⟩
        intro x member
        simp only [List.mem_singleton] at member
        subst member
        constructor <;> (rw [digitIs]; have := Nat.mod_lt sum.val (show 0 < 10 by norm_num); omega))
      invNext
    refine ⟨v, ?_, dv, value, len⟩
    simp [within_either_spec, more, aRun, bRun, abRun, sumRun, short, mRun, digitRun, push, advance, cRun, run]
  · have doneL : left.val.length ≤ index.val := by omega
    have doneR : right.val.length ≤ index.val := by omega
    rw [low_full _ _ doneL, low_full _ _ doneR] at inv
    have atMax : index.val = max left.val.length right.val.length := by
      have := Nat.max_le.mpr ⟨doneL, doneR⟩; omega
    by_cases positive : 0 < carry.val
    · have one : carry.val = 1 := by omega
      have short : out.val.length < Usize.max := by
        have := Nat.le_max_left left.val.length right.val.length
        have := Nat.le_max_right left.val.length right.val.length
        omega
      obtain ⟨digit, digitRun, digitValue⟩ := WP.spec_imp_exists
        (U8.add_spec (x := 48#u8) (y := carry) (by scalar_tac))
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out digit short)
      have pos' : (0#u8) < carry := by simp only [UScalar.lt_equiv]; simpa using positive
      refine ⟨pushed, ?_, ?_, ?_, ?_⟩
      · simp [within_either_spec, more, pos', short, digitRun, push]
      · rw [contents]
        refine digits_append.mpr ⟨dout, ?_⟩
        intro x member
        simp only [List.mem_singleton] at member
        subst member
        constructor <;> simp [digitValue, one]
      · rw [contents, backValue_snoc, hlen, ← inv]
        simp [digitValue, one]
      · rw [contents]; simp; omega
    · have zero : carry.val = 0 := by omega
      have notPos : ¬ (0#u8) < carry := by simp only [UScalar.lt_equiv]; simpa using zero
      refine ⟨out, by simp [within_either_spec, more, notPos], dout, by rw [← inv, zero]; simp, by omega⟩
termination_by (max left.val.length right.val.length) - index.val
decreasing_by
  rcases more with h | h
  · have := Nat.le_max_left left.val.length right.val.length; omega
  · have := Nat.le_max_right left.val.length right.val.length; omega

/-- The kernel adds canonical numbers exactly. -/
theorem add_naturals_spec (left right : alloc.vec.Vec U8) (dl : Digits left.val) (dr : Digits right.val)
    (small : left.val.length + right.val.length < Usize.max) :
    ∃ v, numbers.add_naturals left right = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = digitsValue left.val + digitsValue right.val ∧
      v.val.length ≤ max left.val.length right.val.length + 1 := by
  rw [numbers.add_naturals]
  obtain ⟨w, run, dw, value, len⟩ := add_from_spec left right dl dr small 0#usize 0#u8 (alloc.vec.Vec.new U8)
    (by simp) (by simp) (by simp [new_val]) (by simp [new_val, Digits]) (by simp [new_val, backValue_nil, low])
  obtain ⟨c, crun, cc, cvalue, clen⟩ := canonical_reversed_spec w dw
  exact ⟨c, by simp [run, crun], cc, by rw [cvalue, value], by omega⟩

/-! ### Subtraction -/

theorem subtract_from_spec (left right : alloc.vec.Vec U8) (dl : Digits left.val) (dr : Digits right.val)
    (fits : right.val.length ≤ left.val.length) (small : left.val.length < Usize.max)
    (index : Usize) (borrow : U8) (out : alloc.vec.Vec U8)
    (hindex : index.val ≤ left.val.length) (hborrow : borrow.val ≤ 1) (hlen : out.val.length = index.val)
    (dout : Digits out.val)
    (inv : backValue out.val + low right.val index.val = low left.val index.val + borrow.val * 10 ^ index.val) :
    ∃ v, numbers.subtract_from left right index borrow out = .ok v ∧ Digits v.val ∧
      v.val.length = left.val.length ∧
      ∃ b : Nat, b ≤ 1 ∧ backValue v.val + digitsValue right.val = digitsValue left.val + b * 10 ^ left.val.length := by
  rw [numbers.subtract_from]
  by_cases inside : index.val < left.val.length
  · obtain ⟨top, topRun, topValue⟩ := digit_at_spec left dl index
    obtain ⟨r, rRun, rValue⟩ := digit_at_spec right dr index
    have ht := digitAt_le left.val dl index.val
    have hr := digitAt_le right.val dr index.val
    obtain ⟨lowB, lowRun, lowValue⟩ := WP.spec_imp_exists (U8.add_spec (x := r) (y := borrow) (by scalar_tac))
    have lowIs : lowB.val = digitAt right.val index.val + borrow.val := by rw [lowValue, rValue]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    by_cases fitsDigit : lowB ≤ top
    · have fitsVal : lowB.val ≤ top.val := by simpa [UScalar.le_equiv] using fitsDigit
      obtain ⟨d, dRun, dValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := top) (y := lowB) (by scalar_tac))
      obtain ⟨digit, digitRun, digitValue⟩ := WP.spec_imp_exists
        (U8.add_spec (x := 48#u8) (y := d) (by rw [dValue.1]; scalar_tac))
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out digit short)
      have digitIs : digit.val = 48 + (top.val - lowB.val) := by rw [digitValue, dValue.1]; rfl
      obtain ⟨v, run, dv, len, rest⟩ := subtract_from_spec left right dl dr fits small next 0#u8 pushed
        (by omega) (by simp) (by rw [contents, nextIndex]; simp [hlen])
        (by
          rw [contents]
          refine digits_append.mpr ⟨dout, ?_⟩
          intro x member
          simp only [List.mem_singleton] at member
          subst member
          constructor <;> (rw [digitIs]; omega))
        (by
          rw [contents, backValue_snoc, nextIndex, low, low, hlen, digitIs, ← topValue]
          have e : 48 + (top.val - lowB.val) - 48 = top.val - lowB.val := by omega
          rw [e]
          have zeroVal : ((0#u8 : U8).val) = 0 := rfl
          rw [zeroVal, zero_mul, add_zero]
          have h1 : (top.val - lowB.val) * 10 ^ index.val + lowB.val * 10 ^ index.val = top.val * 10 ^ index.val := by
            rw [← add_mul, Nat.sub_add_cancel fitsVal]
          have h2 : lowB.val * 10 ^ index.val =
              digitAt right.val index.val * 10 ^ index.val + borrow.val * 10 ^ index.val := by
            rw [lowIs, add_mul]
          linarith)
      refine ⟨v, ?_, dv, len, rest⟩
      simp [UScalar.lt_equiv, inside, topRun, rRun, lowRun, fitsVal, dRun, short, digitRun, push, advance, run]
    · have overVal : top.val < lowB.val := by simpa [UScalar.le_equiv] using fitsDigit
      obtain ⟨t10, t10Run, t10Value⟩ := WP.spec_imp_exists
        (U8.add_spec (x := top) (y := 10#u8) (by scalar_tac))
      obtain ⟨d, dRun, dValue⟩ := WP.spec_imp_exists
        (U8.sub_spec (x := t10) (y := lowB) (by rw [t10Value]; scalar_tac))
      have dIs : d.val = top.val + 10 - lowB.val := by rw [dValue.1, t10Value]; rfl
      obtain ⟨digit, digitRun, digitValue⟩ := WP.spec_imp_exists
        (U8.add_spec (x := 48#u8) (y := d) (by rw [dIs]; scalar_tac))
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out digit short)
      have digitIs : digit.val = 48 + (top.val + 10 - lowB.val) := by rw [digitValue, dIs]; rfl
      obtain ⟨v, run, dv, len, rest⟩ := subtract_from_spec left right dl dr fits small next 1#u8 pushed
        (by omega) (by simp) (by rw [contents, nextIndex]; simp [hlen])
        (by
          rw [contents]
          refine digits_append.mpr ⟨dout, ?_⟩
          intro x member
          simp only [List.mem_singleton] at member
          subst member
          constructor <;> (rw [digitIs]; omega))
        (by
          rw [contents, backValue_snoc, nextIndex, low, low, hlen, digitIs, ← topValue]
          have e : 48 + (top.val + 10 - lowB.val) - 48 = top.val + 10 - lowB.val := by omega
          rw [e]
          have oneVal : ((1#u8 : U8).val) = 1 := rfl
          rw [oneVal, one_mul, pow_succ]
          have h1 : (top.val + 10 - lowB.val) * 10 ^ index.val + lowB.val * 10 ^ index.val =
              top.val * 10 ^ index.val + 10 ^ index.val * 10 := by
            rw [← add_mul, Nat.sub_add_cancel (by omega)]; ring
          have h2 : lowB.val * 10 ^ index.val =
              digitAt right.val index.val * 10 ^ index.val + borrow.val * 10 ^ index.val := by
            rw [lowIs, add_mul]
          linarith)
      have notFits : ¬ lowB.val ≤ top.val := by omega
      refine ⟨v, ?_, dv, len, rest⟩
      simp [UScalar.lt_equiv, inside, topRun, rRun, lowRun, notFits, t10Run, dRun, short, digitRun, push, advance,
        run]
  · have atEnd : index.val = left.val.length := by omega
    refine ⟨out, by simp [UScalar.lt_equiv, inside], dout, by omega, borrow.val, hborrow, ?_⟩
    rw [low_full _ _ (by omega), low_full _ _ (by omega), atEnd] at inv
    exact inv
termination_by left.val.length - index.val
decreasing_by all_goals omega

/-- The kernel subtracts a canonical number from one at least as large exactly. -/
theorem subtract_naturals_spec (left right : alloc.vec.Vec U8) (cl : Canonical left.val) (cr : Canonical right.val)
    (le : digitsValue right.val ≤ digitsValue left.val) (small : left.val.length < Usize.max) :
    ∃ v, numbers.subtract_naturals left right = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = digitsValue left.val - digitsValue right.val ∧ v.val.length ≤ left.val.length := by
  rw [numbers.subtract_naturals]
  have fits : right.val.length ≤ left.val.length := by
    by_contra longer
    have := canonical_shorter _ _ cl cr (by omega)
    omega
  obtain ⟨w, run, dw, wlen, b, hb, value⟩ := subtract_from_spec left right cl.1 cr.1 fits small 0#usize 0#u8
    (alloc.vec.Vec.new U8) (by simp) (by simp) (by simp [new_val]) (by simp [new_val, Digits])
    (by simp [new_val, backValue_nil, low])
  have below : backValue w.val < 10 ^ left.val.length := by
    have := value_lt w.val.reverse (digits_reverse.mpr dw)
    simpa [backValue, wlen] using this
  have noBorrow : b = 0 := by
    by_contra nonzero
    have : b = 1 := by omega
    subst this
    omega
  subst noBorrow
  obtain ⟨c, crun, cc, cvalue, clen⟩ := canonical_reversed_spec w dw
  exact ⟨c, by simp [run, crun], cc, by rw [cvalue]; omega, by omega⟩

/-! ### Multiplication -/

theorem shifted_spec (digits : alloc.vec.Vec U8) (c : Canonical digits.val) (room : digits.val.length < Usize.max) :
    ∃ v, numbers.shifted digits = .ok v ∧ Canonical v.val ∧ digitsValue v.val = 10 * digitsValue digits.val ∧
      v.val.length ≤ digits.val.length + 1 := by
  rw [numbers.shifted]
  by_cases nonempty : 0 < digits.val.length
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec digits 48#u8 room)
    refine ⟨pushed, by simp [UScalar.lt_equiv, nonempty, room, push], ⟨?_, ?_⟩, ?_, by rw [contents]; simp⟩
    · rw [contents]
      refine digits_append.mpr ⟨c.1, ?_⟩
      intro x member
      simp only [List.mem_singleton] at member
      subst member
      constructor <;> decide
    · rw [contents]
      cases h : digits.val with
      | nil => simp [h] at nonempty
      | cons head tail => simpa [h] using c.2
    · rw [contents, value_snoc]; simp
  · have empty : digits.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨digits, by simp [UScalar.lt_equiv, nonempty], c, by simp [empty, value_nil], by omega⟩

theorem repeated_spec (value : alloc.vec.Vec U8) (cv : Canonical value.val)
    (small : 2 * value.val.length + 2 < Usize.max) (count : U8) (total : alloc.vec.Vec U8)
    (ct : Canonical total.val)
    (bound : digitsValue total.val + count.val * digitsValue value.val < 10 ^ (value.val.length + 1)) :
    ∃ v, numbers.repeated value count total = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = digitsValue total.val + count.val * digitsValue value.val := by
  rw [numbers.repeated]
  by_cases positive : 0 < count.val
  · have totalLen : total.val.length ≤ value.val.length + 1 :=
      canonical_length_le _ ct _ (by have := Nat.zero_le (count.val * digitsValue value.val); omega)
    obtain ⟨sum, sumRun, sc, sumValue, _⟩ := add_naturals_spec total value ct.1 cv.1 (by omega)
    obtain ⟨less, lessRun, lessValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := count) (y := 1#u8) (by scalar_tac))
    have lessIs : less.val = count.val - 1 := lessValue.1
    obtain ⟨v, run, cvv, value'⟩ := repeated_spec value cv small less sum sc
      (by
        rw [sumValue, lessIs]
        have : count.val = (count.val - 1) + 1 := by omega
        rw [this] at bound
        nlinarith [bound])
    have pos' : (0#u8) < count := by simp only [UScalar.lt_equiv]; simpa using positive
    refine ⟨v, by simp [pos', sumRun, lessRun, run], cvv, ?_⟩
    rw [value', sumValue, lessIs]
    have : count.val = (count.val - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  · have zero : count.val = 0 := by omega
    have notPos : ¬ (0#u8) < count := by simp only [UScalar.lt_equiv]; simpa using zero
    exact ⟨total, by simp [notPos], ct, by simp [zero]⟩
termination_by count.val
decreasing_by omega

theorem multiply_from_spec (left right : alloc.vec.Vec U8) (cl : Canonical left.val) (dr : Digits right.val)
    (small : 2 * (left.val.length + right.val.length) + 4 < Usize.max)
    (index : Usize) (total : alloc.vec.Vec U8) (hindex : index.val ≤ right.val.length)
    (ct : Canonical total.val)
    (inv : digitsValue total.val = digitsValue left.val * digitsValue (right.val.take index.val)) :
    ∃ v, numbers.multiply_from left right index total = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = digitsValue left.val * digitsValue right.val := by
  rw [numbers.multiply_from]
  by_cases inside : index.val < right.val.length
  · have lookup : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have digit := dr _ (List.getElem_mem inside)
    obtain ⟨d, dRun, dValue⟩ := digit_value_spec right.val[index.val]
    rw [if_pos digit] at dValue
    have dSmall : d.val ≤ 9 := by have := digit.2; omega
    obtain ⟨part, partRun, pc, partValue⟩ := repeated_spec left cl (by omega) d (alloc.vec.Vec.new U8)
      (by simp [new_val, canonical_nil])
      (by
        simp only [new_val, value_nil, zero_add]
        have := value_lt left.val cl.1
        rw [pow_succ]
        nlinarith)
    have totalLen : total.val.length ≤ left.val.length + index.val := by
      apply canonical_length_le _ ct
      rw [inv, pow_add]
      have h1 := value_lt left.val cl.1
      have h2 := value_lt (right.val.take index.val) (digits_take dr _)
      have : (right.val.take index.val).length = index.val := by simp; omega
      rw [this] at h2
      have : digitsValue left.val * digitsValue (right.val.take index.val) ≤
          digitsValue left.val * 10 ^ index.val := Nat.mul_le_mul_left _ h2.le
      by_cases zero : digitsValue left.val = 0
      · rw [zero]; simp
      · nlinarith
    obtain ⟨sh, shRun, shc, shValue, shLen⟩ := shifted_spec total ct (by omega)
    have partLen : part.val.length ≤ left.val.length + 1 := by
      apply canonical_length_le _ pc
      rw [partValue, new_val, value_nil, zero_add, pow_succ]
      have := value_lt left.val cl.1
      nlinarith
    obtain ⟨next, nextRun, nc, nextValue, _⟩ := add_naturals_spec sh part shc.1 pc.1 (by omega)
    obtain ⟨index', advance, indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val + 1 := by simpa using indexValue
    obtain ⟨v, run, cvv, value⟩ := multiply_from_spec left right cl dr small index' next (by omega) nc
      (by
        rw [nextValue, shValue, partValue, new_val, value_nil, zero_add, inv, nextIndex, List.take_add_one,
          List.getElem?_eq_getElem inside]
        simp only [Option.toList_some]
        rw [value_snoc, dValue]
        ring)
    refine ⟨v, ?_, cvv, value⟩
    simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, dRun, partRun, shRun, nextRun,
      advance, run]
  · have done : right.val.take index.val = right.val := List.take_of_length_le (by omega)
    exact ⟨total, by simp [UScalar.lt_equiv, inside], ct, by rw [inv, done]⟩
termination_by right.val.length - index.val
decreasing_by omega

/-- The kernel multiplies canonical numbers exactly. -/
theorem multiply_naturals_spec (left right : alloc.vec.Vec U8) (cl : Canonical left.val) (dr : Digits right.val)
    (small : 2 * (left.val.length + right.val.length) + 4 < Usize.max) :
    ∃ v, numbers.multiply_naturals left right = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = digitsValue left.val * digitsValue right.val ∧
      v.val.length ≤ left.val.length + right.val.length := by
  rw [numbers.multiply_naturals]
  obtain ⟨v, run, cv, value⟩ := multiply_from_spec left right cl dr small 0#usize (alloc.vec.Vec.new U8)
    (by simp) (by simp [new_val, canonical_nil]) (by simp [new_val, value_nil])
  refine ⟨v, run, cv, value, canonical_length_le _ cv _ ?_⟩
  rw [value, pow_add]
  have h1 := value_lt left.val cl.1
  have h2 := value_lt right.val dr
  by_cases zero : digitsValue left.val = 0
  · rw [zero]; simp
  · nlinarith

/-! ### Division -/

theorem append_digit_spec (digits : alloc.vec.Vec U8) (c : Canonical digits.val) (digit : U8) (d : Digit digit)
    (room : digits.val.length < Usize.max) :
    ∃ v, numbers.append_digit digits digit = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = 10 * digitsValue digits.val + (digit.val - 48) ∧ v.val.length ≤ digits.val.length + 1 := by
  rw [numbers.append_digit]
  by_cases nonempty : 0 < digits.val.length
  · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec digits digit room)
    refine ⟨pushed, by simp [UScalar.lt_equiv, nonempty, room, push], ⟨?_, ?_⟩, ?_, by rw [contents]; simp⟩
    · rw [contents]
      refine digits_append.mpr ⟨c.1, ?_⟩
      intro x member
      simp only [List.mem_singleton] at member
      subst member; exact d
    · rw [contents]
      cases h : digits.val with
      | nil => simp [h] at nonempty
      | cons head tail => simpa [h] using c.2
    · rw [contents, value_snoc]
  · have empty : digits.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    by_cases zero : digit = 48#u8
    · refine ⟨digits, by simp [UScalar.lt_equiv, nonempty, zero], c, ?_, by omega⟩
      rw [empty, zero]; simp [value_nil]
    · obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec digits digit room)
      refine ⟨pushed, by simp [UScalar.lt_equiv, nonempty, zero, room, push], ⟨?_, ?_⟩, ?_, by rw [contents]; simp⟩
      · rw [contents, empty]
        intro x member
        simp only [List.nil_append, List.mem_singleton] at member
        subst member; exact d
      · rw [contents, empty]
        simpa using zero
      · rw [contents, empty, value_snoc]

theorem reduce_spec (divisor : alloc.vec.Vec U8) (cd : Canonical divisor.val) (positive : 0 < digitsValue divisor.val)
    (small : divisor.val.length + 2 < Usize.max) (current : alloc.vec.Vec U8) (cc : Canonical current.val)
    (count : U8) (hcount : count.val ≤ 9)
    (bound : digitsValue current.val < (10 - count.val) * digitsValue divisor.val)
    (hlen : current.val.length ≤ divisor.val.length + 1) :
    ∃ c rest, numbers.reduce divisor current count = .ok (c, rest) ∧ count.val ≤ c.val ∧ c.val ≤ 9 ∧
      Canonical rest.val ∧
      digitsValue current.val = (c.val - count.val) * digitsValue divisor.val + digitsValue rest.val ∧
      digitsValue rest.val < digitsValue divisor.val ∧ rest.val.length ≤ divisor.val.length := by
  rw [numbers.reduce]
  by_cases more : count.val < 9
  · have more' : count < (9#u8) := by simp only [UScalar.lt_equiv]; simpa using more
    obtain ⟨order', orderRun, orderValue⟩ := compare_naturals_spec current divisor cc cd
    by_cases below : digitsValue current.val < digitsValue divisor.val
    · have isZero : order' = 0#u8 := by
        apply UScalar.eq_of_val_eq; rw [orderValue, order_lt below]; rfl
      refine ⟨count, current, by simp [more', orderRun, isZero], le_rfl, by omega, cc, by simp, below, ?_⟩
      by_contra longer
      have := canonical_shorter _ _ cd cc (by omega)
      omega
    · have notZero : order' ≠ 0#u8 := by
        intro h
        have := congrArg UScalar.val h
        rw [orderValue] at this
        simp only [order] at this
        split_ifs at this <;> simp_all
      obtain ⟨rest, restRun, rc, restValue, restLen⟩ := subtract_naturals_spec current divisor cc cd
        (by omega) (by omega)
      obtain ⟨next, nextRun, nextValue⟩ := WP.spec_imp_exists (U8.add_spec (x := count) (y := 1#u8) (by scalar_tac))
      have nextIs : next.val = count.val + 1 := by simpa using nextValue
      obtain ⟨c, rest', run, low, high, rc', value, less, len⟩ := reduce_spec divisor cd positive small rest rc next
        (by omega)
        (by
          rw [restValue, nextIs]
          have : (10 - count.val) * digitsValue divisor.val =
              (10 - (count.val + 1)) * digitsValue divisor.val + digitsValue divisor.val := by
            have : 10 - count.val = (10 - (count.val + 1)) + 1 := by omega
            rw [this]; ring
          omega)
        (by omega)
      refine ⟨c, rest', by simp [more', orderRun, notZero, restRun, nextRun, run], by omega, high, rc', ?_, less, len⟩
      rw [nextIs] at low value
      rw [restValue] at value
      have shift : c.val - count.val = (c.val - (count.val + 1)) + 1 := by omega
      rw [shift]
      have atLeast : digitsValue divisor.val ≤ digitsValue current.val := by omega
      have h := Nat.sub_add_cancel atLeast
      rw [value] at h
      rw [← h]
      ring
  · have nine : count.val = 9 := by omega
    have notMore : ¬ count < (9#u8) := by simp only [UScalar.lt_equiv]; simp; omega
    have below : digitsValue current.val < digitsValue divisor.val := by rw [nine] at bound; simpa using bound
    refine ⟨count, current, by simp [notMore], le_rfl, by omega, cc, by simp, below, ?_⟩
    by_contra longer
    have := canonical_shorter _ _ cd cc (by omega)
    omega
termination_by 9 - count.val
decreasing_by omega

theorem divide_from_spec (dividend divisor : alloc.vec.Vec U8) (dd : Digits dividend.val)
    (cd : Canonical divisor.val) (positive : 0 < digitsValue divisor.val)
    (small : dividend.val.length + divisor.val.length + 4 < Usize.max)
    (index : Usize) (quotient remainder : alloc.vec.Vec U8) (hindex : index.val ≤ dividend.val.length)
    (cq : Canonical quotient.val) (cr : Canonical remainder.val) (qlen : quotient.val.length ≤ index.val)
    (rbound : digitsValue remainder.val < digitsValue divisor.val)
    (inv : digitsValue (dividend.val.take index.val) =
      digitsValue quotient.val * digitsValue divisor.val + digitsValue remainder.val) :
    ∃ q r, numbers.divide_from dividend divisor index quotient remainder = .ok (q, r) ∧ Canonical q.val ∧
      Canonical r.val ∧ digitsValue dividend.val = digitsValue q.val * digitsValue divisor.val + digitsValue r.val ∧
      digitsValue r.val < digitsValue divisor.val ∧ q.val.length ≤ dividend.val.length ∧
      r.val.length ≤ divisor.val.length := by
  rw [numbers.divide_from]
  have rlen : remainder.val.length ≤ divisor.val.length := by
    by_contra longer
    have := canonical_shorter _ _ cd cr (by omega)
    omega
  by_cases inside : index.val < dividend.val.length
  · have lookup : dividend.index_usize index = .ok dividend.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have digit := dd _ (List.getElem_mem inside)
    obtain ⟨current, currentRun, cc, currentValue, currentLen⟩ :=
      append_digit_spec remainder cr dividend.val[index.val] digit (by omega)
    obtain ⟨c, rest, reduceRun, _, high, rc, value, less, restLen⟩ := reduce_spec divisor cd positive (by omega)
      current cc 0#u8 (by simp)
      (by
        rw [currentValue]
        have z : ((0#u8 : U8).val) = 0 := rfl
        rw [z, Nat.sub_zero]
        have := digit.2
        omega)
      (by omega)
    obtain ⟨qd, qdRun, qdValue⟩ := WP.spec_imp_exists (U8.add_spec (x := 48#u8) (y := c) (by scalar_tac))
    have qdIs : qd.val = 48 + c.val := by rw [qdValue]; rfl
    obtain ⟨next, nextRun, nc, nextValue, nextLen⟩ := append_digit_spec quotient cq qd
      (by constructor <;> omega) (by omega)
    obtain ⟨index', advance, indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val + 1 := by simpa using indexValue
    obtain ⟨q, r, run, hq, hr, total, rless, qLen, rLen⟩ := divide_from_spec dividend divisor dd cd positive small
      index' next rest (by omega) nc rc (by omega) less
      (by
        rw [nextIndex, List.take_add_one, List.getElem?_eq_getElem inside]
        simp only [Option.toList_some]
        rw [value_snoc, inv, nextValue, qdIs]
        have z : ((0#u8 : U8).val) = 0 := rfl
        rw [z, Nat.sub_zero] at value
        rw [currentValue] at value
        have e : 48 + c.val - 48 = c.val := by omega
        rw [e]
        nlinarith [value])
    refine ⟨q, r, ?_, hq, hr, total, rless, qLen, rLen⟩
    simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, currentRun, reduceRun, qdRun, nextRun,
      advance, run]
  · have done : dividend.val.take index.val = dividend.val := List.take_of_length_le (by omega)
    rw [done] at inv
    exact ⟨quotient, remainder, by simp [UScalar.lt_equiv, inside], cq, cr, inv, rbound, by omega, rlen⟩
termination_by dividend.val.length - index.val
decreasing_by omega

/-- The kernel divides a number by a positive canonical number exactly, with
    quotient and remainder. -/
theorem divide_naturals_spec (dividend divisor : alloc.vec.Vec U8) (dd : Digits dividend.val)
    (cd : Canonical divisor.val) (positive : 0 < digitsValue divisor.val)
    (small : dividend.val.length + divisor.val.length + 4 < Usize.max) :
    ∃ q r, numbers.divide_naturals dividend divisor = .ok (q, r) ∧ Canonical q.val ∧ Canonical r.val ∧
      digitsValue q.val = digitsValue dividend.val / digitsValue divisor.val ∧
      digitsValue r.val = digitsValue dividend.val % digitsValue divisor.val ∧
      q.val.length ≤ dividend.val.length ∧ r.val.length ≤ divisor.val.length := by
  rw [numbers.divide_naturals]
  obtain ⟨q, r, run, cq, cr, total, less, qLen, rLen⟩ := divide_from_spec dividend divisor dd cd positive small
    0#usize (alloc.vec.Vec.new U8) (alloc.vec.Vec.new U8) (by simp) (by simp [new_val, canonical_nil])
    (by simp [new_val, canonical_nil]) (by simp [new_val]) (by simp [new_val, value_nil]; exact positive)
    (by simp [new_val, value_nil])
  have quot : digitsValue q.val = digitsValue dividend.val / digitsValue divisor.val := by
    rw [total, Nat.add_comm, Nat.add_mul_div_right _ _ positive, Nat.div_eq_of_lt less]; simp
  have remain : digitsValue r.val = digitsValue dividend.val % digitsValue divisor.val := by
    rw [total, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt less]
  exact ⟨q, r, run, cq, cr, quot, remain, qLen, rLen⟩

/-! ### Greatest common divisors -/

theorem gcd_of_spec (left right : alloc.vec.Vec U8) (cl : Canonical left.val) (cr : Canonical right.val)
    (smallL : 2 * left.val.length + 4 < Usize.max) (smallR : 2 * right.val.length + 4 < Usize.max) :
    ∃ g, numbers.gcd_of left right = .ok g ∧ Canonical g.val ∧
      digitsValue g.val = Nat.gcd (digitsValue left.val) (digitsValue right.val) ∧
      g.val.length ≤ max left.val.length right.val.length := by
  rw [numbers.gcd_of]
  by_cases nonempty : 0 < right.val.length
  · have positive : 0 < digitsValue right.val := by
      have := (canonical_zero right.val cr).not.mpr (by intro h; simp [h] at nonempty)
      omega
    obtain ⟨q, rest, divRun, _, rc, _, restValue, _, restLen⟩ := divide_naturals_spec left right cl.1 cr positive
      (by omega)
    have decreasing : digitsValue rest.val < digitsValue right.val := by
      rw [restValue]; exact Nat.mod_lt _ positive
    obtain ⟨g, run, cg, gValue, gLen⟩ := gcd_of_spec right rest cr rc smallR (by omega)
    refine ⟨g, by simp [UScalar.lt_equiv, nonempty, divRun, run], cg, ?_, ?_⟩
    · rw [gValue, restValue, Nat.gcd_comm (digitsValue right.val), ← Nat.gcd_rec, Nat.gcd_comm]
    · have := Nat.le_max_right left.val.length right.val.length
      have := Nat.max_le.mpr ⟨le_rfl, restLen⟩
      omega
  · have empty : right.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨left, by simp [UScalar.lt_equiv, nonempty], cl, by simp [empty, value_nil], Nat.le_max_left _ _⟩
termination_by digitsValue right.val
decreasing_by exact decreasing

/-- The kernel computes greatest common divisors of canonical numbers exactly. -/
theorem gcd_naturals_spec (left right : alloc.vec.Vec U8) (cl : Canonical left.val) (cr : Canonical right.val)
    (smallL : 2 * left.val.length + 4 < Usize.max) (smallR : 2 * right.val.length + 4 < Usize.max) :
    ∃ g, numbers.gcd_naturals left right = .ok g ∧ Canonical g.val ∧
      digitsValue g.val = Nat.gcd (digitsValue left.val) (digitsValue right.val) ∧
      g.val.length ≤ max left.val.length right.val.length := by
  rw [numbers.gcd_naturals]
  obtain ⟨l, lRun, lValue⟩ := copy_from_spec left 0#usize (alloc.vec.Vec.new U8) (by simp)
  obtain ⟨r, rRun, rValue⟩ := copy_from_spec right 0#usize (alloc.vec.Vec.new U8) (by simp)
  have lIs : l.val = left.val := by rw [lValue]; simp [new_val]
  have rIs : r.val = right.val := by rw [rValue]; simp [new_val]
  obtain ⟨g, run, cg, gValue, gLen⟩ := gcd_of_spec l r (by rw [lIs]; exact cl) (by rw [rIs]; exact cr)
    (by rw [lIs]; exact smallL) (by rw [rIs]; exact smallR)
  exact ⟨g, by simp [lRun, rRun, run], cg, by rw [gValue, lIs, rIs], by rw [lIs, rIs] at gLen; exact gLen⟩

/-! ### Powers of ten -/

theorem times_power_spec (digits : alloc.vec.Vec U8) (c : Canonical digits.val) (count : Usize)
    (room : digits.val.length + count.val < Usize.max) :
    ∃ v, numbers.times_power digits count = .ok v ∧ Canonical v.val ∧
      digitsValue v.val = digitsValue digits.val * 10 ^ count.val ∧
      v.val.length ≤ digits.val.length + count.val := by
  rw [numbers.times_power]
  by_cases positive : 0 < count.val
  · obtain ⟨sh, shRun, shc, shValue, shLen⟩ := shifted_spec digits c (by omega)
    obtain ⟨less, lessRun, lessValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := count) (y := 1#usize) (by scalar_tac))
    have lessIs : less.val = count.val - 1 := by simp at lessValue; omega
    obtain ⟨v, run, cv, value, len⟩ := times_power_spec sh shc less (by omega)
    have pos' : (0#usize) < count := by simp only [UScalar.lt_equiv]; simpa using positive
    refine ⟨v, by simp [pos', shRun, lessRun, run], cv, ?_, by omega⟩
    rw [value, shValue, lessIs]
    have : count.val = (count.val - 1) + 1 := by omega
    conv_rhs => rw [this, pow_succ]
    ring
  · have zero : count.val = 0 := by omega
    have notPos : ¬ (0#usize) < count := by simp only [UScalar.lt_equiv]; simpa using zero
    exact ⟨digits, by simp [notPos], c, by simp [zero], by omega⟩
termination_by count.val
decreasing_by omega

theorem ten_power_spec (count : Usize) (room : count.val + 1 < Usize.max) :
    ∃ v, numbers.ten_power count = .ok v ∧ Canonical v.val ∧ digitsValue v.val = 10 ^ count.val ∧
      v.val.length ≤ count.val + 1 := by
  rw [numbers.ten_power]
  obtain ⟨one, oneRun, oneValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 49#u8 (by simp [new_val]; scalar_tac))
  have oneIs : one.val = [49#u8] := by rw [oneValue]; simp [new_val]
  have co : Canonical one.val := by
    rw [oneIs]; refine ⟨?_, by simp⟩
    intro x member; simp only [List.mem_singleton] at member; subst member; constructor <;> decide
  obtain ⟨v, run, cv, value, len⟩ := times_power_spec one co count (by rw [oneIs]; simp; omega)
  refine ⟨v, by simp [oneRun, run], cv, ?_, by rw [oneIs] at len; simp at len; omega⟩
  rw [value, oneIs]
  simp [value_cons, value_nil]

end Rowl.Numbers
