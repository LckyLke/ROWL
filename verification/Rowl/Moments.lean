import Rowl.Numbers

/-!
The actual kernel reading of the lexical forms of `xsd:dateTime` and
`xsd:dateTimeStamp`: `moments.moment_value` returns a value exactly for the
lexical forms of the specification (`MomentForm`, with a time zone for a time
stamp), and that value is the moment that the specification gives the form
(`momentOf`), written canonically (`CanonicalMoment`). On the way, the leap
years and the lengths of the months that the kernel reads from the last digits
of a year are those of the specification (`leap_correct`,
`month_days_correct`), and the day after the end of a day is `nextDate`
(`next_day_correct`).
-/
namespace Rowl.Moments
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.DatatypeMap
open Rowl.Numbers (digitAt low)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

instance digitDecidable (byte : U8) : Decidable (Digit byte) :=
  inferInstanceAs (Decidable (48 ≤ byte.val ∧ byte.val ≤ 57))

/-! ### The moments of kernel values -/

/-- The moment of a kernel moment: the year with its sign, the seconds with
    their fraction, and the time zone offset in minutes. -/
def momentOf (x : datatypes.Moment) : Moment where
  year := (if x.negative then -1 else 1) * (digitsValue x.year.val : ℤ)
  month := x.month.val
  day := x.day.val
  hour := x.hour.val
  minute := x.minute.val
  second := x.second.val + fractionValue x.fraction.val
  zone := x.zone.map fun z => (if z.1 then -1 else 1) * ((60 * z.2.1.val + z.2.2.val : ℕ) : ℤ)

/-- The kernel moments that `moment_value` returns: the year's digits without a
    leading zero, and not negative when zero; the fraction's digits without a
    trailing zero; whole seconds below 60; a time zone whose minutes are below
    60 and that is not west of UTC when it is zero; and a valid moment. -/
def CanonicalMoment (x : datatypes.Moment) : Prop :=
  Rowl.Numbers.Canonical x.year.val ∧ (x.negative = true → x.year.val ≠ []) ∧ Digits x.fraction.val ∧
    x.fraction.val.getLast? ≠ some 48#u8 ∧ x.second.val < 60 ∧
    (∀ w h m, x.zone = some (w, h, m) → m.val < 60 ∧ (w = true → h.val ≠ 0 ∨ m.val ≠ 0)) ∧
    (momentOf x).Valid

/-! ### Bytes -/

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

private theorem new_val : (alloc.vec.Vec.new U8).val = [] := rfl

private theorem eq_43 (b : U8) : b = 43#u8 ↔ b.val = 43 := by rw [UScalar.eq_equiv]; simp
private theorem eq_45 (b : U8) : b = 45#u8 ↔ b.val = 45 := by rw [UScalar.eq_equiv]; simp
private theorem eq_46 (b : U8) : b = 46#u8 ↔ b.val = 46 := by rw [UScalar.eq_equiv]; simp
private theorem eq_48 (b : U8) : b = 48#u8 ↔ b.val = 48 := by rw [UScalar.eq_equiv]; simp
private theorem eq_58 (b : U8) : b = 58#u8 ↔ b.val = 58 := by rw [UScalar.eq_equiv]; simp
private theorem eq_84 (b : U8) : b = 84#u8 ↔ b.val = 84 := by rw [UScalar.eq_equiv]; simp
private theorem eq_90 (b : U8) : b = 90#u8 ↔ b.val = 90 := by rw [UScalar.eq_equiv]; simp

/-- The bytes from `start` up to `finish`. -/
private def seg (bytes : List U8) (start finish : Nat) : List U8 := (bytes.take finish).drop start

private theorem seg_empty (bytes : List U8) (start finish : Nat) (h : finish ≤ start) : seg bytes start finish = [] := by
  simp [seg, List.drop_eq_nil_iff]; omega

private theorem seg_cons (bytes : List U8) (start finish : Nat) (before : start < finish) (fits : finish ≤ bytes.length) :
    seg bytes start finish = bytes[start]'(by omega) :: seg bytes (start + 1) finish := by
  have inside : start < (bytes.take finish).length := by simp; omega
  rw [seg, List.drop_eq_getElem_cons inside]
  simp only [List.getElem_take]
  rfl

private theorem seg_length (bytes : List U8) (start finish : Nat) (fits : finish ≤ bytes.length) :
    (seg bytes start finish).length = finish - start := by
  simp [seg]; omega

private theorem seg_append (bytes : List U8) (a b c : Nat) (ab : a ≤ b) (bc : b ≤ c) (fits : c ≤ bytes.length) :
    seg bytes a c = seg bytes a b ++ seg bytes b c := by
  have split : bytes.take c = bytes.take b ++ (bytes.take c).drop b := by
    conv => lhs; rw [← List.take_append_drop b (bytes.take c)]
    rw [List.take_take, Nat.min_eq_left bc]
  rw [seg, split, List.drop_append_of_le_length (by simp; omega)]
  rfl

private theorem seg_getElem (bytes : List U8) (start finish i : Nat) (h : i < (seg bytes start finish).length) :
    (seg bytes start finish)[i] = bytes[start + i]'(by simp [seg] at h; omega) := by
  simp [seg, List.getElem_drop, List.getElem_take]

private theorem take_seg (bytes : List U8) (start finish : Nat) (le : start ≤ finish) :
    bytes.take finish = bytes.take start ++ seg bytes start finish := by
  rw [seg]
  conv => lhs; rw [← List.take_append_drop start (bytes.take finish)]
  rw [List.take_take, Nat.min_eq_left le]

/-! ### Small kernel functions -/

theorem is_digit_correct (byte : U8) : moments.is_digit byte = .ok (decide (Digit byte)) := by
  rw [moments.is_digit]
  by_cases d : Digit byte
  · have := d.1; have := d.2
    simp [UScalar.le_equiv, d, *]
  · simp only [Digit, not_and_or, not_le] at d
    rcases d with d | d <;> simp [UScalar.le_equiv, Digit, d]

theorem digits_end_spec (bytes : alloc.vec.Vec U8) (index : Usize) (h : index.val ≤ bytes.val.length) :
    ∃ r, moments.digits_end bytes index = .ok r ∧ index.val ≤ r.val ∧ r.val ≤ bytes.val.length ∧
      (∀ i (hi : i < bytes.val.length), index.val ≤ i → i < r.val → Digit bytes.val[i]) ∧
      ∀ hr : r.val < bytes.val.length, ¬ Digit bytes.val[r.val] := by
  rw [moments.digits_end]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases digit : Digit bytes.val[index.val]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, low, high, digits, stop⟩ := digits_end_spec bytes next (by omega)
      refine ⟨r, ?_, by omega, high, ?_, stop⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, is_digit_correct, digit, advance, run]
      · intro i hi lowi highi
        by_cases same : i = index.val
        · subst same; exact digit
        · exact digits i hi (by omega) highi
    · refine ⟨index, ?_, le_rfl, h, fun i _ low high => absurd high (by omega), fun _ => digit⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, is_digit_correct, digit]
  · refine ⟨index, by simp [UScalar.lt_equiv, inside], le_rfl, h, fun i _ low high => absurd high (by omega),
      fun hr => absurd hr inside⟩
termination_by bytes.val.length - index.val
decreasing_by omega

theorem nonzero_start_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (order : index.val ≤ finish.val)
    (fits : finish.val ≤ bytes.val.length) :
    ∃ r, moments.nonzero_start bytes index finish = .ok r ∧ index.val ≤ r.val ∧ r.val ≤ finish.val ∧
      (∀ b ∈ seg bytes.val index.val r.val, b = 48#u8) ∧
      ∀ h : r.val < finish.val, bytes.val[r.val]'(by omega) ≠ 48#u8 := by
  rw [moments.nonzero_start]
  by_cases before : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have fitsLe : finish ≤ alloc.vec.Vec.len bytes := by
      simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact fits
    by_cases zero : bytes.val[index.val] = 48#u8
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, low, high, zeros, stop⟩ := nonzero_start_spec bytes next finish (by omega) fits
      refine ⟨r, ?_, by omega, high, ?_, stop⟩
      · simp [UScalar.lt_equiv, before, fitsLe, alloc.vec.Vec.index_slice_index, lookup, zero, advance, run]
      · rw [seg_cons _ _ _ (by omega) (by omega)]
        intro byte member
        rcases List.mem_cons.mp member with rfl | later
        · exact zero
        · rw [nextIndex] at zeros
          exact zeros byte later
    · refine ⟨index, ?_, le_rfl, by omega, by simp [seg_empty], fun _ => zero⟩
      simp [UScalar.lt_equiv, before, fitsLe, alloc.vec.Vec.index_slice_index, lookup, zero]
  · have same : index.val = finish.val := by omega
    refine ⟨index, ?_, le_rfl, by omega, by simp [seg_empty], fun h => absurd h (by omega)⟩
    simp [UScalar.lt_equiv, before]
termination_by finish.val - index.val
decreasing_by omega

theorem trimmed_end_spec (bytes : alloc.vec.Vec U8) (start finish : Usize)
    (order : start.val ≤ finish.val) (fits : finish.val ≤ bytes.val.length) :
    ∃ r, moments.trimmed_end bytes start finish = .ok r ∧ start.val ≤ r.val ∧ r.val ≤ finish.val ∧
      (∀ b ∈ seg bytes.val r.val finish.val, b = 48#u8) ∧
      ∀ h : start.val < r.val ∧ r.val ≤ finish.val, bytes.val[r.val - 1]'(by omega) ≠ 48#u8 := by
  rw [moments.trimmed_end]
  by_cases before : start.val < finish.val
  · obtain ⟨last, back, lastValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := finish) (y := 1#usize) (by scalar_tac))
    have lastIndex : last.val = finish.val - 1 := by simp at lastValue; omega
    have inside : last.val < bytes.val.length := by omega
    have lookup : bytes.index_usize last = .ok bytes.val[last.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have fitsLe : finish ≤ alloc.vec.Vec.len bytes := by
      simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact fits
    by_cases zero : bytes.val[last.val] = 48#u8
    · obtain ⟨r, run, low, high, zeros, stop⟩ := trimmed_end_spec bytes start last (by omega) (by omega)
      refine ⟨r, ?_, low, by omega, ?_, fun h => stop ⟨h.1, high⟩⟩
      · simp [UScalar.lt_equiv, before, fitsLe, back, alloc.vec.Vec.index_slice_index, lookup, zero, run]
      · rw [seg_append bytes.val r.val last.val finish.val high (by omega) fits]
        intro byte member
        rcases List.mem_append.mp member with early | late
        · exact zeros byte early
        · rw [seg_cons _ _ _ (by omega) fits, seg_empty _ _ _ (by omega)] at late
          simp only [List.mem_singleton] at late
          rw [late]
          simpa [lastIndex] using zero
    · refine ⟨finish, ?_, order, le_rfl, by simp [seg_empty], fun _ => ?_⟩
      · simp [UScalar.lt_equiv, before, fitsLe, back, alloc.vec.Vec.index_slice_index, lookup, zero]
      · simpa [lastIndex] using zero
  · refine ⟨finish, ?_, order, le_rfl, by simp [seg_empty], fun h => absurd h.1 (by omega)⟩
    simp [UScalar.lt_equiv, before]
termination_by finish.val - start.val
decreasing_by omega

theorem copy_span_spec (bytes : alloc.vec.Vec U8) (index finish : Usize) (out : alloc.vec.Vec U8)
    (fits : finish.val ≤ bytes.val.length) (room : out.val.length + (finish.val - index.val) ≤ Usize.max) :
    ∃ v, moments.copy_span bytes index finish out = .ok v ∧ v.val = out.val ++ seg bytes.val index.val finish.val := by
  rw [moments.copy_span]
  by_cases before : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have fitsLe : finish ≤ alloc.vec.Vec.len bytes := by
      simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact fits
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out bytes.val[index.val] short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_span_spec bytes next finish pushed fits
      (by rw [contents, nextIndex]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, before, fitsLe, usize_max_val, short, alloc.vec.Vec.index_slice_index, lookup, push,
        advance, run]
    · rw [value, contents, nextIndex, seg_cons _ _ _ before fits]
      simp
  · refine ⟨out, ?_, ?_⟩
    · simp [UScalar.lt_equiv, before]
    · simp [seg_empty _ _ _ (by omega : finish.val ≤ index.val)]
termination_by finish.val - index.val
decreasing_by omega

/-! ### Two digits -/

/-- The number that two digits at the front of the bytes write. -/
def twoValue : List U8 → Option ℕ
  | a :: b :: _ => if Digit a ∧ Digit b then some (digitsValue [a, b]) else none
  | _ => none

theorem twoValue_pair (a b : U8) (rest : List U8) : twoValue (a :: b :: rest) = twoValue [a, b] := rfl

theorem digitsValue_pair (a b : U8) : digitsValue [a, b] = (a.val - 48) * 10 + (b.val - 48) := by
  rw [Rowl.Numbers.value_cons, Rowl.Numbers.value_cons, Rowl.Numbers.value_nil]
  simp

theorem twoDigits_iff (a b : U8) (n : ℕ) : TwoDigits [a, b] n ↔ twoValue [a, b] = some n := by
  have digits : Digits [a, b] ↔ Digit a ∧ Digit b := by simp [Digits]
  simp only [TwoDigits, twoValue, List.length_cons, List.length_nil, digits, true_and]
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

theorem two_digits_spec (bytes : alloc.vec.Vec U8) (index : Usize) :
    ∃ r, moments.two_digits bytes index = .ok r ∧ r.map (·.val) = twoValue (bytes.val.drop index.val) := by
  rw [moments.two_digits]
  by_cases inside : index.val < bytes.val.length
  · obtain ⟨rest, sub, restValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len bytes) (y := index) (by simp; omega))
    have restIs : rest.val = bytes.val.length - index.val := by have := restValue.1; simpa using this
    by_cases two : 1 < rest.val
    · have second : index.val + 1 < bytes.val.length := by omega
      have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have lookup' : bytes.index_usize next = .ok bytes.val[index.val + 1] := by
        simp [alloc.vec.Vec.index_usize, nextIndex, List.getElem?_eq_getElem second]
      have dropIs : bytes.val.drop index.val = bytes.val[index.val] :: bytes.val[index.val + 1] ::
          bytes.val.drop (index.val + 2) := by
        rw [List.drop_eq_getElem_cons inside, List.drop_eq_getElem_cons second]
      rw [dropIs, twoValue_pair]
      have twoLt : (1#usize) < rest := by simp only [UScalar.lt_equiv]; simpa using two
      by_cases digits : Digit bytes.val[index.val] ∧ Digit bytes.val[index.val + 1]
      · obtain ⟨d0, d1⟩ := digits
        have := d0.1; have := d0.2; have := d1.1; have := d1.2
        obtain ⟨h0, sub0, h0Value⟩ := WP.spec_imp_exists
          (U8.sub_spec (x := bytes.val[index.val]) (y := 48#u8) (by scalar_tac))
        obtain ⟨h1, mul1, h1Value⟩ := WP.spec_imp_exists
          (U8.mul_spec (x := h0) (y := 10#u8) (by scalar_tac))
        obtain ⟨h2, sub2, h2Value⟩ := WP.spec_imp_exists
          (U8.sub_spec (x := bytes.val[index.val + 1]) (y := 48#u8) (by scalar_tac))
        obtain ⟨h3, add3, h3Value⟩ := WP.spec_imp_exists
          (U8.add_spec (x := h1) (y := h2) (by scalar_tac))
        refine ⟨some h3, ?_, ?_⟩
        · simp [UScalar.lt_equiv, inside, sub, two, alloc.vec.Vec.index_slice_index, lookup, advance, lookup',
            is_digit_correct, d0, d1, sub0, mul1, sub2, add3]
        · simp only [Option.map_some, twoValue, d0, d1, and_self, ↓reduceIte, Option.some.injEq]
          rw [digitsValue_pair]
          simp at h0Value h1Value h2Value h3Value
          omega
      · refine ⟨none, ?_, ?_⟩
        · have : ¬ (Digit bytes.val[index.val] ∧ Digit bytes.val[index.val + 1]) := digits
          by_cases d0 : Digit bytes.val[index.val]
          · have d1 : ¬ Digit bytes.val[index.val + 1] := fun d1 => digits ⟨d0, d1⟩
            simp [UScalar.lt_equiv, inside, sub, two, alloc.vec.Vec.index_slice_index, lookup, advance, lookup',
              is_digit_correct, d0, d1]
          · simp [UScalar.lt_equiv, inside, sub, two, alloc.vec.Vec.index_slice_index, lookup, advance, lookup',
              is_digit_correct, d0]
        · simp [twoValue, digits]
    · have notTwo : ¬ (1#usize) < rest := by simp only [UScalar.lt_equiv]; simpa using two
      refine ⟨none, by simp [UScalar.lt_equiv, inside, sub, two], ?_⟩
      have short : (bytes.val.drop index.val).length ≤ 1 := by simp; omega
      match h : bytes.val.drop index.val, short with
      | [], _ => rfl
      | [_], _ => rfl
  · refine ⟨none, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [List.drop_eq_nil_iff.mpr (by omega)]; rfl

/-! ### Years, leap years and the lengths of months -/

theorem digit_at_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (index : Usize) :
    ∃ d, moments.digit_at digits index = .ok d ∧ d.val = digitAt digits.val index.val := by
  rw [moments.digit_at]
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
    have digit := dd _ (List.getElem_mem within)
    have := digit.1; have := digit.2
    obtain ⟨d, sub, dValue⟩ := WP.spec_imp_exists
      (U8.sub_spec (x := digits.val[at'.val]) (y := 48#u8) (by scalar_tac))
    refine ⟨d, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside, lastRun, atRun, alloc.vec.Vec.index_slice_index, lookup, is_digit_correct,
        digit, sub]
    · rw [Rowl.Numbers.digitAt_of_lt _ _ inside]
      simp only [atIs] at dValue ⊢
      simpa using dValue.1
  · refine ⟨0#u8, by simp [UScalar.lt_equiv, inside], ?_⟩
    rw [Rowl.Numbers.digitAt_of_ge _ _ (by omega)]; rfl

theorem pair_at_spec (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (places : Usize)
    (small : places.val < Usize.max) :
    ∃ d, moments.pair_at digits places = .ok d ∧
      d.val = digitAt digits.val (places.val + 1) * 10 + digitAt digits.val places.val := by
  rw [moments.pair_at]
  have below : places < core.num.Usize.MAX := by simp only [UScalar.lt_equiv, usize_max_val]; exact small
  obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := places) (y := 1#usize) (by scalar_tac))
  have nextIs : next.val = places.val + 1 := by simpa using nextValue
  obtain ⟨high, highRun, highValue⟩ := digit_at_spec digits dd next
  obtain ⟨low, lowRun, lowValue⟩ := digit_at_spec digits dd places
  have highSmall := Rowl.Numbers.digitAt_le digits.val dd next.val
  have lowSmall := Rowl.Numbers.digitAt_le digits.val dd places.val
  obtain ⟨tens, mul, tensValue⟩ := WP.spec_imp_exists (U8.mul_spec (x := high) (y := 10#u8) (by scalar_tac))
  obtain ⟨sum, add, sumValue⟩ := WP.spec_imp_exists (U8.add_spec (x := tens) (y := low) (by scalar_tac))
  refine ⟨sum, by simp [below, advance, highRun, lowRun, mul, add], ?_⟩
  simp at tensValue sumValue
  rw [← nextIs]
  omega

/-- The lowest places of a number's digits are its remainder. -/
theorem low_mod (l : List U8) (d : Digits l) (j : Nat) : low l j = digitsValue l % 10 ^ j := by
  by_cases short : l.length ≤ j
  · rw [Rowl.Numbers.low_full l j short, Nat.mod_eq_of_lt]
    calc digitsValue l < 10 ^ l.length := Rowl.Numbers.value_lt l d
      _ ≤ 10 ^ j := Nat.pow_le_pow_right (by norm_num) short
  · rw [Rowl.Numbers.low_drop l j (by omega)]
    have split := congrArg digitsValue (List.take_append_drop (l.length - j) l)
    rw [Rowl.Numbers.value_append] at split
    have dropLength : (l.drop (l.length - j)).length = j := by simp; omega
    rw [dropLength] at split
    have small := Rowl.Numbers.value_lt (l.drop (l.length - j)) (Rowl.Numbers.digits_drop d _)
    rw [dropLength] at small
    rw [← split, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt small]

theorem leapYear_neg (y : ℤ) : leapYear (-y) = leapYear y := by
  have a : ((-y) % 400 = 0) = (y % 400 = 0) := propext (by omega)
  have b : ((-y) % 4 = 0) = (y % 4 = 0) := propext (by omega)
  have c : ((-y) % 100 = 0) = (y % 100 = 0) := propext (by omega)
  simp only [leapYear, ne_eq, a, b, c]

theorem leapYear_natAbs (y : ℤ) : leapYear y = leapYear (y.natAbs : ℤ) := by
  rcases Int.natAbs_eq y with h | h
  · conv => lhs; rw [h]
  · conv => lhs; rw [h, leapYear_neg]

theorem leap_correct (year : alloc.vec.Vec U8) (dy : Digits year.val) :
    moments.leap year = .ok (leapYear (digitsValue year.val : ℤ)) := by
  rw [moments.leap]
  obtain ⟨lowPair, lowRun, lowValue⟩ := pair_at_spec year dy 0#usize (by scalar_tac)
  obtain ⟨highPair, highRun, highValue⟩ := pair_at_spec year dy 2#usize (by scalar_tac)
  have l2 : low year.val 2 = digitAt year.val 0 + digitAt year.val 1 * 10 := by simp [low]
  have l4 : low year.val 4 = digitAt year.val 0 + digitAt year.val 1 * 10 + digitAt year.val 2 * 100 +
      digitAt year.val 3 * 1000 := by simp only [low]; ring
  rw [low_mod year.val dy] at l2 l4
  have lowIs : lowPair.val = digitsValue year.val % 100 := by
    have := lowValue
    simp at this
    norm_num at l2
    omega
  have highIs : highPair.val = digitsValue year.val / 100 % 100 := by
    have := highValue
    simp at this
    norm_num at l2 l4
    omega
  have leapIff : leapYear (digitsValue year.val : ℤ) = true ↔
      (digitsValue year.val % 400 = 0 ∨ (digitsValue year.val % 4 = 0 ∧ digitsValue year.val % 100 ≠ 0)) := by
    simp only [leapYear, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
    omega
  by_cases zero : lowPair.val = 0
  · have lowEq : lowPair = 0#u8 := by rw [UScalar.eq_equiv]; simpa using zero
    obtain ⟨r, mod, rValue⟩ := WP.spec_imp_exists (UScalar.rem_spec highPair (y := 4#u8) (by simp))
    have rIs : r.val = highPair.val % 4 := by simpa using rValue
    simp only [lowRun, lowEq, ↓reduceIte, highRun, mod, bind_ok]
    congr 1
    have z : (0#u8 : U8).val = 0 := by simp
    rw [Bool.eq_iff_iff, leapIff, decide_eq_true_eq, UScalar.eq_equiv, rIs, highIs, z]
    omega
  · have lowNe : ¬ lowPair = 0#u8 := by rw [UScalar.eq_equiv]; simpa using zero
    obtain ⟨r, mod, rValue⟩ := WP.spec_imp_exists (UScalar.rem_spec lowPair (y := 4#u8) (by simp))
    have rIs : r.val = lowPair.val % 4 := by simpa using rValue
    simp only [lowRun, lowNe, ↓reduceIte, mod, bind_ok]
    congr 1
    have z : (0#u8 : U8).val = 0 := by simp
    rw [Bool.eq_iff_iff, leapIff, decide_eq_true_eq, UScalar.eq_equiv, rIs, z]
    omega

theorem month_days_correct (year : alloc.vec.Vec U8) (dy : Digits year.val) (y : ℤ)
    (hy : y.natAbs = digitsValue year.val) (month : U8) :
    ∃ d, moments.month_days year month = .ok d ∧ d.val = daysIn y month.val := by
  have leapIs : leapYear y = leapYear (digitsValue year.val : ℤ) := by rw [leapYear_natAbs, hy]
  rw [moments.month_days]
  by_cases two : month.val = 2
  · have e : month = 2#u8 := by rw [UScalar.eq_equiv]; simpa using two
    by_cases leap : leapYear (digitsValue year.val : ℤ) = true
    · exact ⟨29#u8, by simp [e, leap_correct year dy, leap], by simp [daysIn, two, leapIs, leap]⟩
    · exact ⟨28#u8, by simp [e, leap_correct year dy, leap], by simp [daysIn, two, leapIs, leap]⟩
  · have ne : ¬ month = 2#u8 := by rw [UScalar.eq_equiv]; simpa using two
    have e4 : month = 4#u8 ↔ month.val = 4 := by rw [UScalar.eq_equiv]; simp
    have e6 : month = 6#u8 ↔ month.val = 6 := by rw [UScalar.eq_equiv]; simp
    have e9 : month = 9#u8 ↔ month.val = 9 := by rw [UScalar.eq_equiv]; simp
    have e11 : month = 11#u8 ↔ month.val = 11 := by rw [UScalar.eq_equiv]; simp
    by_cases thirty : month.val = 4 ∨ month.val = 6 ∨ month.val = 9 ∨ month.val = 11
    · refine ⟨30#u8, ?_, by simp [daysIn, two, thirty]⟩
      rcases thirty with h | h | h | h <;> simp [ne, e4, e6, e9, e11, h]
    · refine ⟨31#u8, ?_, by simp [daysIn, two, thirty]⟩
      simp only [not_or] at thirty
      simp [ne, e4, e6, e9, e11, thirty]

theorem daysIn_le (year : ℤ) (month : ℕ) : 28 ≤ daysIn year month ∧ daysIn year month ≤ 31 := by
  unfold daysIn; split_ifs <;> omega

/-! ### The day after a date -/

theorem one_canonical : Rowl.Numbers.Canonical [49#u8] := by
  refine ⟨fun b m => ?_, by simp⟩
  simp at m; subst m; exact ⟨by simp, by simp⟩

theorem next_year_spec (negative : Bool) (year : alloc.vec.Vec U8) (cy : Rowl.Numbers.Canonical year.val)
    (sign : negative = true → year.val ≠ []) (small : year.val.length + 2 < Usize.max) :
    ∃ n y', moments.next_year negative year = .ok (n, y') ∧ Rowl.Numbers.Canonical y'.val ∧
      (n = true → y'.val ≠ []) ∧
      (if n then -1 else 1) * (digitsValue y'.val : ℤ) = (if negative then -1 else 1) * (digitsValue year.val : ℤ) + 1 := by
  rw [moments.next_year]
  obtain ⟨one, oneRun, oneValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 49#u8 (by simp [new_val]; scalar_tac))
  have oneIs : one.val = [49#u8] := by rw [oneValue]; simp [new_val]
  have oneDigits : digitsValue one.val = 1 := by simp [oneIs, Rowl.Numbers.value_cons, Rowl.Numbers.value_nil]
  have oneCanonical : Rowl.Numbers.Canonical one.val := by rw [oneIs]; exact one_canonical
  simp only [oneRun, bind_ok]
  cases negative with
  | true =>
    have nonempty := sign rfl
    have positive : 1 ≤ digitsValue year.val := by
      have := (Rowl.Numbers.canonical_zero year.val cy).not.mpr nonempty; omega
    obtain ⟨rest, run, cr, value, len⟩ := Rowl.Numbers.subtract_naturals_spec year one cy oneCanonical
      (by rw [oneDigits]; exact positive) (by omega)
    refine ⟨decide (0 < rest.val.length), rest, by simp [run], cr, ?_, ?_⟩
    · intro h; simp at h; intro e; rw [e] at h; simp at h
    · simp only [oneDigits] at value
      by_cases empty : rest.val = []
      · have zero : digitsValue rest.val = 0 := by rw [empty]; rfl
        simp [empty, zero]
        omega
      · have : 0 < rest.val.length := List.length_pos_of_ne_nil empty
        simp [this]
        push_cast [value]
        omega
  | false =>
    obtain ⟨sum, run, cs, value, len⟩ := Rowl.Numbers.add_naturals_spec year one cy.1 oneCanonical.1
      (by rw [oneIs]; simp; omega)
    refine ⟨false, sum, by simp [run], cs, by simp, ?_⟩
    simp only [oneDigits] at value
    simp [value]

/-- The facts of a kernel moment that the day after it needs. -/
def DateOk (x : datatypes.Moment) : Prop :=
  Rowl.Numbers.Canonical x.year.val ∧ (x.negative = true → x.year.val ≠ []) ∧ x.year.val.length + 2 < Usize.max ∧
    1 ≤ x.month.val ∧ x.month.val ≤ 12 ∧ 1 ≤ x.day.val ∧ x.day.val ≤ daysIn (momentOf x).year x.month.val

theorem next_day_correct (x : datatypes.Moment) (ok : DateOk x) :
    ∃ x', moments.next_day x = .ok x' ∧ Rowl.Numbers.Canonical x'.year.val ∧ (x'.negative = true → x'.year.val ≠ []) ∧
      ((momentOf x').year, (momentOf x').month, (momentOf x').day) =
        nextDate (momentOf x).year x.month.val x.day.val ∧
      x'.hour.val = 0 ∧ x'.minute = x.minute ∧ x'.second = x.second ∧ x'.fraction = x.fraction ∧ x'.zone = x.zone := by
  obtain ⟨cy, sign, small, m1, m12, d1, dIn⟩ := ok
  have absYear : (momentOf x).year.natAbs = digitsValue x.year.val := by
    simp only [momentOf]; split <;> simp
  rw [moments.next_day]
  obtain ⟨days, daysRun, daysValue⟩ := month_days_correct x.year cy.1 (momentOf x).year absYear x.month
  have daysBound := daysIn_le (momentOf x).year x.month.val
  by_cases before : x.day.val < daysIn (momentOf x).year x.month.val
  · have lt : x.day < days := by simp only [UScalar.lt_equiv]; omega
    obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (U8.add_spec (x := x.day) (y := 1#u8) (by scalar_tac))
    refine ⟨{ x with day := next, hour := 0#u8 }, by simp only [daysRun, bind_ok, lt, ↓reduceIte, add], cy, sign, ?_,
      by simp, rfl, rfl, rfl, rfl⟩
    rw [nextDate, if_pos before]
    simp at nextValue
    simp [momentOf, nextValue]
  · have notLt : ¬ x.day < days := by simp only [UScalar.lt_equiv]; omega
    by_cases early : x.month.val < 12
    · have lt : x.month < 12#u8 := by simp only [UScalar.lt_equiv]; simpa using early
      obtain ⟨next, add, nextValue⟩ := WP.spec_imp_exists (U8.add_spec (x := x.month) (y := 1#u8) (by scalar_tac))
      refine ⟨{ x with month := next, day := 1#u8, hour := 0#u8 },
        by simp only [daysRun, bind_ok, notLt, lt, ↓reduceIte, add], cy, sign, ?_, by simp, rfl, rfl, rfl, rfl⟩
      rw [nextDate, if_neg before, if_pos early]
      simp at nextValue
      simp [momentOf, nextValue]
    · have notLt' : ¬ x.month < 12#u8 := by simp only [UScalar.lt_equiv]; simpa using early
      obtain ⟨n, y', run, cy', sign', value⟩ := next_year_spec x.negative x.year cy sign small
      refine ⟨{ x with negative := n, year := y', month := 1#u8, day := 1#u8, hour := 0#u8 },
        by simp only [daysRun, bind_ok, notLt, notLt', ↓reduceIte, run]; rfl, cy', sign', ?_, by simp, rfl, rfl, rfl,
        rfl⟩
      have this : (momentOf { x with negative := n, year := y', month := 1#u8, day := 1#u8, hour := 0#u8 }).year =
          (momentOf x).year + 1 := by simp only [momentOf]; exact value
      rw [nextDate, if_neg before, if_neg early, this]
      simp [momentOf]

/-! ### Zones -/

/-- A time zone of hours and minutes, when they are within fourteen hours:
    whether it is west of UTC and not zero, its hours and its minutes. -/
def zoneOf (west : Bool) : Option ℕ → Option ℕ → Option (Option (Bool × ℕ × ℕ))
  | some h, some m =>
    if (h ≤ 13 ∧ m ≤ 59) ∨ (h = 14 ∧ m = 0) then some (some (west = true ∧ (h ≠ 0 ∨ m ≠ 0), h, m)) else none
  | _, _ => none

/-- The parts of a time zone that the bytes write: none for no bytes, and for
    `Z` or `(+|-)hh:mm` of at most fourteen hours whether it is west of UTC (and
    not zero), its hours and its minutes. -/
def zoneParts : List U8 → Option (Option (Bool × ℕ × ℕ))
  | [] => some none
  | [z] => if z = 90#u8 then some (some (false, 0, 0)) else none
  | [s, h1, h2, c, m1, m2] =>
    if (s = 43#u8 ∨ s = 45#u8) ∧ c = 58#u8 then zoneOf (decide (s = 45#u8)) (twoValue [h1, h2]) (twoValue [m1, m2])
    else none
  | _ => none

/-- The kernel's parts of a time zone, with natural numbers. -/
def zoneNat (z : Option (Bool × U8 × U8)) : Option (Bool × ℕ × ℕ) := z.map fun p => (p.1, p.2.1.val, p.2.2.val)

theorem zone_parts_spec (west : Bool) (hours minutes : Option U8) :
    ∃ r, moments.zone_parts west hours minutes = .ok r ∧
      r.map zoneNat = zoneOf west (hours.map (·.val)) (minutes.map (·.val)) := by
  unfold moments.zone_parts
  cases hours with
  | none => exact ⟨none, rfl, rfl⟩
  | some h =>
    cases minutes with
    | none => exact ⟨none, rfl, rfl⟩
    | some m =>
      have l13 : h ≤ 13#u8 ↔ h.val ≤ 13 := by simp [UScalar.le_equiv]
      have l59 : m ≤ 59#u8 ↔ m.val ≤ 59 := by simp [UScalar.le_equiv]
      have e14 : h = 14#u8 ↔ h.val = 14 := by rw [UScalar.eq_equiv]; simp
      have e0 : m = 0#u8 ↔ m.val = 0 := by rw [UScalar.eq_equiv]; simp
      have h0 : h = 0#u8 ↔ h.val = 0 := by rw [UScalar.eq_equiv]; simp
      by_cases fits : (h.val ≤ 13 ∧ m.val ≤ 59) ∨ (h.val = 14 ∧ m.val = 0)
      · refine ⟨some (some (west && (h != 0#u8 || m != 0#u8), h, m)), ?_, ?_⟩
        · simp [l13, l59, e14, e0, fits]
        · have hb : (h != 0#u8) = !decide (h.val = 0) := by
            by_cases hz : h.val = 0
            · simp [h0.mpr hz, hz]
            · have hne : h ≠ 0#u8 := fun e => hz (h0.mp e)
              simp [hne, hz]
          have mb : (m != 0#u8) = !decide (m.val = 0) := by
            by_cases mz : m.val = 0
            · simp [e0.mpr mz, mz]
            · have mne : m ≠ 0#u8 := fun e => mz (e0.mp e)
              simp [mne, mz]
          simp [zoneNat, zoneOf, fits, hb, mb]
      · refine ⟨none, ?_, by simp [zoneOf, fits]⟩
        simp only [not_or, not_and_or] at fits
        simp [l13, l59, e14, e0]
        omega

theorem zoneParts_other (l : List U8) (h1 : l.length ≠ 0) (h2 : l.length ≠ 1) (h6 : l.length ≠ 6) :
    zoneParts l = none := by
  match l, h1, h2, h6 with
  | [], h1, _, _ => exact absurd rfl h1
  | [_], _, h2, _ => exact absurd rfl h2
  | [_, _], _, _, _ => rfl
  | [_, _, _], _, _, _ => rfl
  | [_, _, _, _], _, _, _ => rfl
  | [_, _, _, _, _], _, _, _ => rfl
  | [_, _, _, _, _, _], _, _, h6 => exact absurd rfl h6
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, _, _ => rfl

private theorem drop_two (l : List U8) (i : Nat) (h : i + 1 < l.length) :
    l.drop i = l[i] :: l[i + 1] :: l.drop (i + 2) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons h]

theorem zone_value_spec (lexical : alloc.vec.Vec U8) (index : Usize) (h : index.val ≤ lexical.val.length) :
    ∃ r, moments.zone_value lexical index = .ok r ∧ r.map zoneNat = zoneParts (lexical.val.drop index.val) := by
  by_cases inside : index.val < lexical.val.length
  · obtain ⟨rest, sub, restValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len lexical) (y := index) (by simp; omega))
    have restIs : rest.val = lexical.val.length - index.val := by have := restValue.1; simpa using this
    have lookup : lexical.index_usize index = .ok lexical.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have insideLt : index < alloc.vec.Vec.len lexical := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    have dropIs : lexical.val.drop index.val = lexical.val[index.val] :: lexical.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons inside
    have dropLength : (lexical.val.drop (index.val + 1)).length = rest.val - 1 := by simp; omega
    set b := lexical.val[index.val] with hb
    have run0 : moments.zone_value lexical index = (do
        if (decide (b = 90#u8) && decide (rest = 1#usize)) = true then ok (some (some (false, 0#u8, 0#u8)))
        else if ((decide (b = 43#u8) || decide (b = 45#u8)) && decide (rest = 6#usize)) = true then do
          let i3 ← index + 3#usize
          let i4 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) lexical i3
          if i4 = 58#u8 then do
            let i5 ← index + 1#usize
            let o ← moments.two_digits lexical i5
            let i6 ← index + 4#usize
            let o1 ← moments.two_digits lexical i6
            moments.zone_parts (decide (b = 45#u8)) o o1
          else ok none
        else ok none) := by
      rw [moments.zone_value]
      simp only [insideLt, ↓reduceIte, sub, bind_ok, alloc.vec.Vec.index_slice_index, lookup]
      rfl
    rw [run0]
    by_cases zed : b.val = 90 ∧ rest.val = 1
    · have e90 : b = 90#u8 := (eq_90 b).mpr zed.1
      have e1 : rest = 1#usize := by rw [UScalar.eq_equiv]; simpa using zed.2
      refine ⟨some (some (false, 0#u8, 0#u8)), by simp [e90, e1], ?_⟩
      have empty : lexical.val.drop (index.val + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
      rw [dropIs, empty, e90]
      simp [zoneParts, zoneNat]
    · have notZed : ¬ (b = 90#u8 ∧ rest = 1#usize) := by
        rw [eq_90, UScalar.eq_equiv]; simpa using zed
      rw [if_neg (by simpa using notZed)]
      by_cases signed : (b.val = 43 ∨ b.val = 45) ∧ rest.val = 6
      · have e6 : rest = 6#usize := by rw [UScalar.eq_equiv]; simpa using signed.2
        have signB : b = 43#u8 ∨ b = 45#u8 := by rw [eq_43, eq_45]; exact signed.1
        rw [if_pos (by rcases signB with e | e <;> simp [e, e6])]
        have six : index.val + 6 = lexical.val.length := by omega
        obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
        have i3Is : i3.val = index.val + 3 := by simpa using i3Value
        have lookup3 : lexical.index_usize i3 = .ok lexical.val[index.val + 3] := by
          simp [alloc.vec.Vec.index_usize, i3Is,
            List.getElem?_eq_getElem (show index.val + 3 < lexical.val.length by omega)]
        have d1 := drop_two lexical.val (index.val + 1) (by omega)
        have d4 := drop_two lexical.val (index.val + 4) (by omega)
        have d3 : lexical.val.drop (index.val + 3) = lexical.val[index.val + 3] :: lexical.val.drop (index.val + 4) :=
          List.drop_eq_getElem_cons (by omega)
        have dEnd : lexical.val.drop (index.val + 4 + 2) = [] := List.drop_eq_nil_iff.mpr (by omega)
        have bytes : lexical.val.drop index.val = [b, lexical.val[index.val + 1], lexical.val[index.val + 1 + 1],
            lexical.val[index.val + 3], lexical.val[index.val + 4], lexical.val[index.val + 4 + 1]] := by
          apply List.ext_getElem
          · simp; omega
          · intro i h1 h2
            simp only [List.length_drop] at h1
            rw [List.getElem_drop]
            rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
              rfl
        simp only [add3, bind_ok, alloc.vec.Vec.index_slice_index, lookup3]
        by_cases colon : lexical.val[index.val + 3] = 58#u8
        · rw [if_pos colon]
          obtain ⟨i5, add5, i5Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have i5Is : i5.val = index.val + 1 := by simpa using i5Value
          obtain ⟨i6, add6, i6Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 4#usize) (by scalar_tac))
          have i6Is : i6.val = index.val + 4 := by simpa using i6Value
          obtain ⟨hours, hoursRun, hoursValue⟩ := two_digits_spec lexical i5
          obtain ⟨minutes, minutesRun, minutesValue⟩ := two_digits_spec lexical i6
          obtain ⟨r, partsRun, partsValue⟩ := zone_parts_spec (decide (b = 45#u8)) hours minutes
          refine ⟨r, by simp only [add5, bind_ok, hoursRun, add6, minutesRun, partsRun], ?_⟩
          rw [partsValue, hoursValue, minutesValue, i5Is, i6Is, d1, d4]
          simp only [twoValue_pair]
          rw [bytes]
          simp only [zoneParts, colon, and_true]
          rw [if_pos signB]
        · rw [if_neg colon]
          refine ⟨none, rfl, ?_⟩
          rw [bytes]
          simp [zoneParts, colon]
      · rw [if_neg (by
          intro h'
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h'
          rw [eq_43, eq_45, UScalar.eq_equiv] at h'
          exact signed (by simpa using h'))]
        refine ⟨none, rfl, ?_⟩
        rw [dropIs]
        by_cases one : rest.val = 1
        · have empty : lexical.val.drop (index.val + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
          rw [empty]
          have : ¬ b = 90#u8 := fun e => zed ⟨(eq_90 b).mp e, one⟩
          simp [zoneParts, this]
        · by_cases sixLong : rest.val = 6
          · have notSign : ¬ (b = 43#u8 ∨ b = 45#u8) := by
              rw [eq_43, eq_45]; exact fun h' => signed ⟨h', sixLong⟩
            obtain ⟨x1, x2, x3, x4, x5, e⟩ : ∃ x1 x2 x3 x4 x5, lexical.val.drop (index.val + 1) = [x1, x2, x3, x4, x5] := by
              match hl : lexical.val.drop (index.val + 1), dropLength with
              | [x1, x2, x3, x4, x5], _ => exact ⟨x1, x2, x3, x4, x5, rfl⟩
              | [], d => simp at d; omega
              | [_], d => simp at d; omega
              | [_, _], d => simp at d; omega
              | [_, _, _], d => simp at d; omega
              | [_, _, _, _], d => simp at d; omega
              | _ :: _ :: _ :: _ :: _ :: _ :: _, d => simp at d; omega
            rw [e]
            simp [zoneParts, notSign]
          · exact (zoneParts_other _ (by simp) (by simp; omega) (by simp; omega)).symm
  · refine ⟨some none, ?_, ?_⟩
    · rw [moments.zone_value]
      simp [UScalar.lt_equiv, inside]
    · rw [List.drop_eq_nil_iff.mpr (by omega)]; rfl

/-! ### Fractions of a second -/

theorem fraction_end_spec (lexical : alloc.vec.Vec U8) (index : Usize) (h : index.val ≤ lexical.val.length) :
    ∃ r, moments.fraction_end lexical index = .ok r ∧
      (lexical.val[index.val]? ≠ some 46#u8 → r = some index) ∧
      (lexical.val[index.val]? = some 46#u8 →
        ∃ stop : Usize, index.val + 1 ≤ stop.val ∧ stop.val ≤ lexical.val.length ∧
          (∀ i (hi : i < lexical.val.length), index.val + 1 ≤ i → i < stop.val → Digit lexical.val[i]) ∧
          (∀ hs : stop.val < lexical.val.length, ¬ Digit lexical.val[stop.val]) ∧
          r = if index.val + 1 < stop.val then some stop else none) := by
  rw [moments.fraction_end]
  by_cases inside : index.val < lexical.val.length
  · have lookup : lexical.index_usize index = .ok lexical.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have insideLt : index < alloc.vec.Vec.len lexical := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    by_cases dotV : (lexical.val[index.val]'inside).val = 46
    · have dot : lexical.val[index.val]'inside = 46#u8 := (eq_46 _).mpr dotV
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨stop, run, low, high, digits, stopNot⟩ := digits_end_spec lexical next (by omega)
      have isDot : lexical.val[index.val]? = some 46#u8 := by
        rw [List.getElem?_eq_getElem inside]; exact congrArg some dot
      have facts : index.val + 1 ≤ stop.val ∧ stop.val ≤ lexical.val.length ∧
          (∀ i (hi : i < lexical.val.length), index.val + 1 ≤ i → i < stop.val → Digit lexical.val[i]) ∧
          (∀ hs : stop.val < lexical.val.length, ¬ Digit lexical.val[stop.val]) :=
        ⟨by omega, high, fun i hi lo hi' => digits i hi (by omega) hi', stopNot⟩
      by_cases more : next.val < stop.val
      · refine ⟨some stop, ?_, fun h' => absurd isDot h', fun _ => ⟨stop, facts.1, facts.2.1, facts.2.2.1,
          facts.2.2.2, by rw [if_pos (by omega)]⟩⟩
        simp [insideLt, alloc.vec.Vec.index_slice_index, lookup, dot, advance, run, more]
      · refine ⟨none, ?_, fun h' => absurd isDot h', fun _ => ⟨stop, facts.1, facts.2.1, facts.2.2.1,
          facts.2.2.2, by rw [if_neg (by omega)]⟩⟩
        simp [insideLt, alloc.vec.Vec.index_slice_index, lookup, dot, advance, run, more]
    · have notDot : ¬ lexical.val[index.val]'inside = 46#u8 := fun e => dotV ((eq_46 _).mp e)
      refine ⟨some index, ?_, fun _ => rfl, fun h' => absurd ?_ dotV⟩
      · simp [insideLt, alloc.vec.Vec.index_slice_index, lookup, notDot]
      · rw [List.getElem?_eq_getElem inside] at h'
        exact (eq_46 _).mp (Option.some.inj h')
  · refine ⟨some index, ?_, fun _ => rfl, fun h' => ?_⟩
    · simp [UScalar.lt_equiv, inside]
    · rw [List.getElem?_eq_none (by omega)] at h'; cases h'

private theorem seg_last (l : List U8) (a t : Nat) (before : a < t) (fits : t ≤ l.length) :
    (seg l a t).getLast? = some (l[t - 1]'(by omega)) := by
  rw [seg_append l a (t - 1) t (by omega) (by omega) fits, seg_cons l (t - 1) t (by omega) fits,
    seg_empty l (t - 1 + 1) t (by omega)]
  simp

theorem fraction_digits_spec (lexical : alloc.vec.Vec U8) (start stop : Usize) (fits : stop.val ≤ lexical.val.length) :
    ∃ v, moments.fraction_digits lexical start stop = .ok v ∧
      (start.val < stop.val → ∃ zeros, seg lexical.val (start.val + 1) stop.val = v.val ++ zeros ∧
        (∀ b ∈ zeros, b = 48#u8) ∧ v.val.getLast? ≠ some 48#u8) ∧
      (stop.val ≤ start.val → v.val = []) := by
  rw [moments.fraction_digits]
  by_cases before : start.val < stop.val
  · have lt : start < stop := by simp only [UScalar.lt_equiv]; exact before
    have le : stop ≤ alloc.vec.Vec.len lexical := by simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact fits
    obtain ⟨first, add, firstValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := start) (y := 1#usize) (by scalar_tac))
    have firstIs : first.val = start.val + 1 := by simpa using firstValue
    obtain ⟨t, trim, low, high, zeros, last⟩ := trimmed_end_spec lexical first stop (by omega) fits
    obtain ⟨v, copy, value⟩ := copy_span_spec lexical first t (alloc.vec.Vec.new U8) (by omega)
      (by simp [new_val]; scalar_tac)
    refine ⟨v, by simp [lt, le, add, trim, copy], fun _ => ⟨seg lexical.val t.val stop.val, ?_, zeros, ?_⟩,
      fun h' => absurd h' (by omega)⟩
    · rw [value, new_val, List.nil_append, firstIs, ← seg_append lexical.val (start.val + 1) t.val stop.val
        (by omega) high fits]
    · rw [value, new_val, List.nil_append]
      by_cases empty : first.val < t.val
      · rw [seg_last lexical.val first.val t.val empty (by omega)]
        simpa using last ⟨empty, high⟩
      · rw [seg_empty _ _ _ (by omega)]; simp
  · have nlt : ¬ start < stop := by simp only [UScalar.lt_equiv]; exact before
    refine ⟨alloc.vec.Vec.new U8, by simp [nlt], fun h' => absurd h' before, fun _ => new_val⟩

theorem fractionValue_nil : fractionValue [] = 0 := by simp [fractionValue, Rowl.Numbers.value_nil]

theorem digitsValue_zero_iff (ds : List U8) (d : Digits ds) : digitsValue ds = 0 ↔ ∀ b ∈ ds, b = 48#u8 := by
  induction ds with
  | nil => simp [Rowl.Numbers.value_nil]
  | cons x rest ih =>
    rw [Rowl.Numbers.value_cons]
    have dx := d x List.mem_cons_self
    have drest : Digits rest := fun b m => d b (List.mem_cons_of_mem _ m)
    have pos : 0 < 10 ^ rest.length := by positivity
    constructor
    · intro zero
      obtain ⟨hx, hr⟩ := Nat.add_eq_zero_iff.mp zero
      have hx' : x.val - 48 = 0 := by
        rcases Nat.mul_eq_zero.mp hx with h | h
        · exact h
        · omega
      intro b m
      rcases List.mem_cons.mp m with rfl | m'
      · exact (eq_48 b).mpr (by have := dx.1; omega)
      · exact (ih drest).mp hr b m'
    · intro all
      have hx : x.val = 48 := (eq_48 x).mp (all x List.mem_cons_self)
      have hr := (ih drest).mpr (fun b m => all b (List.mem_cons_of_mem _ m))
      simp [hx, hr]

theorem fractionValue_zero_iff (ds : List U8) (d : Digits ds) : fractionValue ds = 0 ↔ ∀ b ∈ ds, b = 48#u8 := by
  rw [← digitsValue_zero_iff ds d, fractionValue]
  constructor
  · intro h
    have : (10 : ℚ) ^ ds.length ≠ 0 := by positivity
    have := (div_eq_zero_iff.mp h).resolve_right this
    exact_mod_cast this
  · intro h; simp [h]

theorem fractionValue_append_zeros (ds zs : List U8) (zeros : ∀ b ∈ zs, b = 48#u8) :
    fractionValue (ds ++ zs) = fractionValue ds := by
  have zv : digitsValue zs = 0 := by
    have := Rowl.Numbers.value_zeros_append zs [] zeros
    simpa [Rowl.Numbers.value_nil] using this
  simp only [fractionValue, Rowl.Numbers.value_append, zv, List.length_append, Nat.add_zero]
  push_cast
  rw [pow_add, mul_comm ((10 : ℚ) ^ ds.length), ← div_div, mul_div_cancel_right₀ _ (by positivity)]

theorem fractionValue_bounds (ds : List U8) (d : Digits ds) : 0 ≤ fractionValue ds ∧ fractionValue ds < 1 := by
  have small := Rowl.Numbers.value_lt ds d
  refine ⟨by unfold fractionValue; positivity, ?_⟩
  unfold fractionValue
  rw [div_lt_one (by positivity)]
  exact_mod_cast small

theorem decimal_second (s : ℕ) (ds : List U8) : IsDecimal ((s : ℚ) + fractionValue ds) := by
  refine ⟨((s * 10 ^ ds.length + digitsValue ds : ℕ) : ℤ), ds.length, ?_⟩
  unfold fractionValue
  push_cast
  rw [add_div, mul_div_cancel_right₀ _ (by positivity)]

/-! ### Dates and times -/

private theorem drop_at (l : List U8) (i : Nat) (h : i < l.length) : l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons h

private theorem drop_six (l : List U8) (i : Nat) (h : i + 6 ≤ l.length) :
    l.drop i = l[i] :: l[i + 1] :: l[i + 2] :: l[i + 3] :: l[i + 4] :: l[i + 5] :: l.drop (i + 6) := by
  rw [drop_at l i (by omega), drop_at l (i + 1) (by omega), drop_at l (i + 1 + 1) (by omega),
    drop_at l (i + 1 + 1 + 1) (by omega), drop_at l (i + 1 + 1 + 1 + 1) (by omega),
    drop_at l (i + 1 + 1 + 1 + 1 + 1) (by omega)]
  rfl

private theorem drop_nine (l : List U8) (i : Nat) (h : i + 9 ≤ l.length) :
    l.drop i = l[i] :: l[i + 1] :: l[i + 2] :: l[i + 3] :: l[i + 4] :: l[i + 5] :: l[i + 6] :: l[i + 7] ::
      l[i + 8] :: l.drop (i + 9) := by
  rw [drop_six l i (by omega), drop_at l (i + 6) (by omega), drop_at l (i + 6 + 1) (by omega),
    drop_at l (i + 6 + 1 + 1) (by omega)]
  rfl

/-- A date of a month and a day, when the day is in the month of the year. -/
def dateOf (year : ℤ) : Option ℕ → Option ℕ → Option (ℕ × ℕ)
  | some m, some d => if 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysIn year m then some (m, d) else none
  | _, _ => none

/-- The date `-MM-DD` at the front of the bytes. -/
def dateValue (year : ℤ) : List U8 → Option (ℕ × ℕ)
  | a :: m1 :: m2 :: b :: d1 :: d2 :: _ =>
    if a = 45#u8 ∧ b = 45#u8 then dateOf year (twoValue [m1, m2]) (twoValue [d1, d2]) else none
  | _ => none

theorem date_at_spec (lexical : alloc.vec.Vec U8) (index : Usize) (year : alloc.vec.Vec U8) (dy : Digits year.val)
    (y : ℤ) (hy : y.natAbs = digitsValue year.val) :
    ∃ r, moments.date_at lexical index year = .ok r ∧
      r.map (fun p => (p.1.val, p.2.val)) = dateValue y (lexical.val.drop index.val) := by
  rw [moments.date_at]
  by_cases enough : index.val + 6 ≤ lexical.val.length
  · have inside : index.val < lexical.val.length := by omega
    have lookup : lexical.index_usize index = .ok lexical.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨rest, sub, restValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len lexical) (y := index) (by simp; omega))
    have restIs : rest.val = lexical.val.length - index.val := by have := restValue.1; simpa using this
    have five : (5#usize) < rest := by simp only [UScalar.lt_equiv]; simp; omega
    have insideLt : index < alloc.vec.Vec.len lexical := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
    have i3Is : i3.val = index.val + 3 := by simpa using i3Value
    have lookup3 : lexical.index_usize i3 = .ok lexical.val[index.val + 3] := by
      simp [alloc.vec.Vec.index_usize, i3Is, List.getElem?_eq_getElem (show index.val + 3 < lexical.val.length by omega)]
    obtain ⟨i1, add1, i1Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have i1Is : i1.val = index.val + 1 := by simpa using i1Value
    obtain ⟨i4, add4, i4Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 4#usize) (by scalar_tac))
    have i4Is : i4.val = index.val + 4 := by simpa using i4Value
    obtain ⟨o, oRun, oValue⟩ := two_digits_spec lexical i1
    obtain ⟨o1, o1Run, o1Value⟩ := two_digits_spec lexical i4
    have two1 : twoValue (lexical.val.drop i1.val) = twoValue [lexical.val[index.val + 1], lexical.val[index.val + 2]] := by
      rw [i1Is, drop_at _ _ (by omega), drop_at _ (index.val + 1 + 1) (by omega)]; rfl
    have two4 : twoValue (lexical.val.drop i4.val) = twoValue [lexical.val[index.val + 4], lexical.val[index.val + 5]] := by
      rw [i4Is, drop_at _ _ (by omega), drop_at _ (index.val + 4 + 1) (by omega)]; rfl
    rw [drop_six _ _ enough]
    simp only [dateValue]
    simp only [insideLt, ↓reduceIte, sub, bind_ok, five, alloc.vec.Vec.index_slice_index, lookup, add3, lookup3]
    by_cases dash : (lexical.val[index.val]'inside).val = 45 ∧ lexical.val[index.val + 3].val = 45
    · have e0 : lexical.val[index.val]'inside = 45#u8 := (eq_45 _).mpr dash.1
      have e3 : lexical.val[index.val + 3] = 45#u8 := (eq_45 _).mpr dash.2
      simp only [e0, e3, eq_self_iff_true, and_self, decide_true, Bool.and_self, ↓reduceIte, add1, bind_ok, oRun]
      rw [two1] at oValue
      rcases o with _ | month
      · refine ⟨none, rfl, ?_⟩
        simp only [Option.map_none] at oValue
        rw [← oValue]; rfl
      · simp only [add4, bind_ok, o1Run]
        rw [two4] at o1Value
        rcases o1 with _ | day
        · refine ⟨none, rfl, ?_⟩
          simp only [Option.map_some, Option.map_none] at oValue o1Value
          rw [← oValue, ← o1Value]; rfl
        · obtain ⟨days, daysRun, daysValue⟩ := month_days_correct year dy y hy month
          simp only [Option.map_some] at oValue o1Value
          rw [← oValue, ← o1Value]
          simp only [daysRun, bind_ok, dateOf]
          by_cases fits : 1 ≤ month.val ∧ month.val ≤ 12 ∧ 1 ≤ day.val ∧ day.val ≤ daysIn y month.val
          · refine ⟨some (month, day), ?_, by simp [fits]⟩
            simp [UScalar.le_equiv, daysValue, fits]
          · refine ⟨none, ?_, by simp [fits]⟩
            have : ¬ (1 ≤ month.val ∧ month.val ≤ 12 ∧ 1 ≤ day.val ∧ day.val ≤ days.val) := by rw [daysValue]; exact fits
            simp only [UScalar.le_equiv]
            simp only [not_and, not_le] at this
            split_ifs with h'
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
              simp at h'
              omega
            · rfl
    · have notDash : ¬ (lexical.val[index.val]'inside = 45#u8 ∧ lexical.val[index.val + 3] = 45#u8) :=
        fun h' => dash ⟨(eq_45 _).mp h'.1, (eq_45 _).mp h'.2⟩
      simp only [if_neg notDash]
      refine ⟨none, ?_, rfl⟩
      by_cases first : lexical.val[index.val]'inside = 45#u8
      · have third : ¬ lexical.val[index.val + 3] = 45#u8 := fun e => notDash ⟨first, e⟩
        simp [first, third]
      · simp [first]
  · refine ⟨none, ?_, ?_⟩
    · by_cases inside : index.val < lexical.val.length
      · obtain ⟨rest, sub, restValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := alloc.vec.Vec.len lexical) (y := index) (by simp; omega))
        have restIs : rest.val = lexical.val.length - index.val := by have := restValue.1; simpa using this
        have notFive : ¬ 5 < rest.val := by omega
        have insideLt : index < alloc.vec.Vec.len lexical := by
          simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
        simp [insideLt, sub, notFive]
      · simp [UScalar.lt_equiv, inside]
    · have short : (lexical.val.drop index.val).length < 6 := by simp; omega
      match hl : lexical.val.drop index.val, short with
      | [], _ => rfl
      | [_], _ => rfl
      | [_, _], _ => rfl
      | [_, _, _], _ => rfl
      | [_, _, _, _], _ => rfl
      | [_, _, _, _, _], _ => rfl

/-- A time of an hour, a minute and whole seconds. -/
def timeOf : Option ℕ → Option ℕ → Option ℕ → Option (ℕ × ℕ × ℕ)
  | some h, some i, some s => some (h, i, s)
  | _, _, _ => none

/-- The time `Thh:mm:ss` at the front of the bytes. -/
def timeValue : List U8 → Option (ℕ × ℕ × ℕ)
  | t :: h1 :: h2 :: c1 :: i1 :: i2 :: c2 :: s1 :: s2 :: _ =>
    if t = 84#u8 ∧ c1 = 58#u8 ∧ c2 = 58#u8 then timeOf (twoValue [h1, h2]) (twoValue [i1, i2]) (twoValue [s1, s2])
    else none
  | _ => none

theorem timeValue_short (l : List U8) (h : l.length < 9) : timeValue l = none := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem time_at_spec (lexical : alloc.vec.Vec U8) (index : Usize) :
    ∃ r, moments.time_at lexical index = .ok r ∧
      r.map (fun p => (p.1.val, p.2.1.val, p.2.2.val)) = timeValue (lexical.val.drop index.val) := by
  rw [moments.time_at]
  by_cases enough : index.val + 9 ≤ lexical.val.length
  · have inside : index.val < lexical.val.length := by omega
    have lookup : lexical.index_usize index = .ok (lexical.val[index.val]'inside) := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨rest, sub, restValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len lexical) (y := index) (by simp; omega))
    have restIs : rest.val = lexical.val.length - index.val := by have := restValue.1; simpa using this
    have eight : (8#usize) < rest := by simp only [UScalar.lt_equiv]; simp; omega
    obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
    have i3Is : i3.val = index.val + 3 := by simpa using i3Value
    have lookup3 : lexical.index_usize i3 = .ok lexical.val[index.val + 3] := by
      simp [alloc.vec.Vec.index_usize, i3Is, List.getElem?_eq_getElem (show index.val + 3 < lexical.val.length by omega)]
    obtain ⟨i6, add6, i6Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 6#usize) (by scalar_tac))
    have i6Is : i6.val = index.val + 6 := by simpa using i6Value
    have lookup6 : lexical.index_usize i6 = .ok lexical.val[index.val + 6] := by
      simp [alloc.vec.Vec.index_usize, i6Is, List.getElem?_eq_getElem (show index.val + 6 < lexical.val.length by omega)]
    obtain ⟨i1, add1, i1Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have i1Is : i1.val = index.val + 1 := by simpa using i1Value
    obtain ⟨i4, add4, i4Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 4#usize) (by scalar_tac))
    have i4Is : i4.val = index.val + 4 := by simpa using i4Value
    obtain ⟨i7, add7, i7Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 7#usize) (by scalar_tac))
    have i7Is : i7.val = index.val + 7 := by simpa using i7Value
    obtain ⟨o, oRun, oValue⟩ := two_digits_spec lexical i1
    obtain ⟨o1, o1Run, o1Value⟩ := two_digits_spec lexical i4
    obtain ⟨o2, o2Run, o2Value⟩ := two_digits_spec lexical i7
    have two1 : twoValue (lexical.val.drop i1.val) = twoValue [lexical.val[index.val + 1], lexical.val[index.val + 2]] := by
      rw [i1Is, drop_at _ _ (by omega), drop_at _ (index.val + 1 + 1) (by omega)]; rfl
    have two4 : twoValue (lexical.val.drop i4.val) = twoValue [lexical.val[index.val + 4], lexical.val[index.val + 5]] := by
      rw [i4Is, drop_at _ _ (by omega), drop_at _ (index.val + 4 + 1) (by omega)]; rfl
    have two7 : twoValue (lexical.val.drop i7.val) = twoValue [lexical.val[index.val + 7], lexical.val[index.val + 8]] := by
      rw [i7Is, drop_at _ _ (by omega), drop_at _ (index.val + 7 + 1) (by omega)]; rfl
    rw [drop_nine _ _ enough]
    simp only [timeValue]
    have insideLt : index < alloc.vec.Vec.len lexical := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
    simp only [insideLt, ↓reduceIte, sub, bind_ok, eight, alloc.vec.Vec.index_slice_index, lookup, add3, lookup3,
      add6, lookup6]
    by_cases marks : (lexical.val[index.val]'inside).val = 84 ∧ lexical.val[index.val + 3].val = 58 ∧
        lexical.val[index.val + 6].val = 58
    · have eT : lexical.val[index.val]'inside = 84#u8 := (eq_84 _).mpr marks.1
      have e3 : lexical.val[index.val + 3] = 58#u8 := (eq_58 _).mpr marks.2.1
      have e6 : lexical.val[index.val + 6] = 58#u8 := (eq_58 _).mpr marks.2.2
      simp only [eT, e3, e6, eq_self_iff_true, and_self, decide_true, Bool.and_self, ↓reduceIte, add1, bind_ok, oRun]
      rw [two1] at oValue
      rcases o with _ | hour
      · refine ⟨none, rfl, ?_⟩
        simp only [Option.map_none] at oValue
        rw [← oValue]; rfl
      · simp only [add4, bind_ok, o1Run]
        rw [two4] at o1Value
        rcases o1 with _ | minute
        · refine ⟨none, rfl, ?_⟩
          simp only [Option.map_some, Option.map_none] at oValue o1Value
          rw [← oValue, ← o1Value]; rfl
        · simp only [add7, bind_ok, o2Run]
          rw [two7] at o2Value
          rcases o2 with _ | second
          · refine ⟨none, rfl, ?_⟩
            simp only [Option.map_some, Option.map_none] at oValue o1Value o2Value
            rw [← oValue, ← o1Value, ← o2Value]; rfl
          · refine ⟨some (hour, minute, second), rfl, ?_⟩
            simp only [Option.map_some] at oValue o1Value o2Value
            rw [← oValue, ← o1Value, ← o2Value]; rfl
    · have notMarks : ¬ (lexical.val[index.val]'inside = 84#u8 ∧ lexical.val[index.val + 3] = 58#u8 ∧
          lexical.val[index.val + 6] = 58#u8) :=
        fun h' => marks ⟨(eq_84 _).mp h'.1, (eq_58 _).mp h'.2.1, (eq_58 _).mp h'.2.2⟩
      simp only [if_neg notMarks]
      refine ⟨none, ?_, rfl⟩
      by_cases f0 : lexical.val[index.val]'inside = 84#u8
      · by_cases f3 : lexical.val[index.val + 3] = 58#u8
        · have f6 : ¬ lexical.val[index.val + 6] = 58#u8 := fun e => notMarks ⟨f0, f3, e⟩
          simp [f0, f3, f6]
        · simp [f0, f3]
      · simp [f0]
  · refine ⟨none, ?_, by rw [timeValue_short _ (by simp; omega)]; rfl⟩
    by_cases inside : index.val < lexical.val.length
    · obtain ⟨rest, sub, restValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := alloc.vec.Vec.len lexical) (y := index) (by simp; omega))
      have restIs : rest.val = lexical.val.length - index.val := by have := restValue.1; simpa using this
      have notEight : ¬ 8 < rest.val := by omega
      have insideLt : index < alloc.vec.Vec.len lexical := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact inside
      simp [insideLt, sub, notEight]
    · simp [UScalar.lt_equiv, inside]

theorem year_shaped_spec (bytes : alloc.vec.Vec U8) (start finish : Usize) :
    ∃ b, moments.year_shaped bytes start finish = .ok b ∧
      (b = true ↔ start.val < finish.val ∧ finish.val ≤ bytes.val.length ∧
        (finish.val - start.val = 4 ∨ (4 < finish.val - start.val ∧ bytes.val[start.val]? ≠ some 48#u8))) := by
  rw [moments.year_shaped]
  by_cases order : start.val < finish.val ∧ finish.val ≤ bytes.val.length
  · have lt : start < finish := by simp only [UScalar.lt_equiv]; exact order.1
    have le : finish ≤ alloc.vec.Vec.len bytes := by simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact order.2
    obtain ⟨width, sub, widthValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := finish) (y := start) (by scalar_tac))
    have widthIs : width.val = finish.val - start.val := by have := widthValue.1; simpa using this
    by_cases four : width.val = 4
    · have e : width = 4#usize := by rw [UScalar.eq_equiv]; simpa using four
      refine ⟨true, by simp [lt, le, sub, e], by simp [order]; omega⟩
    · have ne : ¬ width = 4#usize := by rw [UScalar.eq_equiv]; simpa using four
      by_cases more : 4 < width.val
      · have moreLt : (4#usize) < width := by simp only [UScalar.lt_equiv]; simpa using more
        have inside : start.val < bytes.val.length := by omega
        have lookup : bytes.index_usize start = .ok (bytes.val[start.val]'inside) := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
        refine ⟨!(bytes.val[start.val]'inside == 48#u8), ?_, ?_⟩
        · simp only [lt, le, Bool.and_self, decide_true, ↓reduceIte, sub, bind_ok, ne, moreLt,
            alloc.vec.Vec.index_slice_index, lookup]
          rfl
        · rw [List.getElem?_eq_getElem inside]
          simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
          constructor
          · intro h'; exact ⟨order.1, order.2, .inr ⟨by omega, h'⟩⟩
          · rintro ⟨_, _, h' | ⟨_, h'⟩⟩
            · omega
            · exact h'
      · have notMore : ¬ (4#usize) < width := by simp only [UScalar.lt_equiv]; simpa using more
        refine ⟨false, by simp [lt, le, sub, ne, notMore, more], ?_⟩
        simp only [Bool.false_eq_true, false_iff, not_and, not_or]
        intro _ _
        exact ⟨by omega, fun h' => by omega⟩
  · refine ⟨false, ?_, by simp only [Bool.false_eq_true, false_iff]; exact fun h' => order ⟨h'.1, h'.2.1⟩⟩
    by_cases first : start.val < finish.val
    · have lt : start < finish := by simp only [UScalar.lt_equiv]; exact first
      have notLe : ¬ finish ≤ alloc.vec.Vec.len bytes := by
        simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact fun h' => order ⟨first, h'⟩
      simp [lt, notLe]
    · have notLt : ¬ start < finish := by simp only [UScalar.lt_equiv]; exact first
      simp [notLt]

theorem settled_spec (x : datatypes.Moment) (ok : DateOk x) :
    ∃ r, moments.settled x = .ok r ∧
      (x.hour.val < 24 → r = if x.minute.val < 60 ∧ x.second.val < 60 then some (.Moment x) else none) ∧
      (24 ≤ x.hour.val → x.hour.val = 24 ∧ x.minute.val = 0 ∧ x.second.val = 0 ∧ x.fraction.val = [] →
        ∃ x', moments.next_day x = .ok x' ∧ r = some (.Moment x')) ∧
      (24 ≤ x.hour.val → ¬ (x.hour.val = 24 ∧ x.minute.val = 0 ∧ x.second.val = 0 ∧ x.fraction.val = []) →
        r = none) := by
  rw [moments.settled]
  by_cases early : x.hour.val < 24
  · have lt : x.hour < 24#u8 := by simp only [UScalar.lt_equiv]; simpa using early
    by_cases clock : x.minute.val < 60 ∧ x.second.val < 60
    · have m : x.minute < 60#u8 := by simp only [UScalar.lt_equiv]; simpa using clock.1
      have s' : x.second < 60#u8 := by simp only [UScalar.lt_equiv]; simpa using clock.2
      exact ⟨some (.Moment x), by simp [lt, m, s'], fun _ => by simp [clock], fun h' => absurd h' (by omega),
        fun h' => absurd h' (by omega)⟩
    · refine ⟨none, ?_, fun _ => by simp [clock], fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩
      have : ¬ (x.minute < 60#u8 ∧ x.second < 60#u8) := by
        simp only [UScalar.lt_equiv]; simpa using clock
      by_cases m : x.minute < 60#u8
      · have s' : ¬ x.second < 60#u8 := fun e => this ⟨m, e⟩
        simp [lt, m, s']
      · simp [lt, m]
  · have notLt : ¬ x.hour < 24#u8 := by simp only [UScalar.lt_equiv]; simpa using early
    by_cases end' : x.hour.val = 24 ∧ x.minute.val = 0 ∧ x.second.val = 0 ∧ x.fraction.val = []
    · obtain ⟨x', run, _⟩ := next_day_correct x ok
      have eh : x.hour = 24#u8 := by rw [UScalar.eq_equiv]; simpa using end'.1
      have em : x.minute = 0#u8 := by rw [UScalar.eq_equiv]; simpa using end'.2.1
      have es : x.second = 0#u8 := by rw [UScalar.eq_equiv]; simpa using end'.2.2.1
      have ef : alloc.vec.Vec.len x.fraction = 0#usize := by
        rw [UScalar.eq_equiv]; simp [alloc.vec.Vec.len_val, end'.2.2.2]
      exact ⟨some (.Moment x'), by simp [notLt, eh, em, es, ef, run], fun h' => absurd h' early,
        fun _ _ => ⟨x', run, rfl⟩, fun _ h' => absurd end' h'⟩
    · refine ⟨none, ?_, fun h' => absurd h' early, fun _ h' => absurd h' end', fun _ _ => rfl⟩
      have : ¬ (x.hour = 24#u8 ∧ x.minute = 0#u8 ∧ x.second = 0#u8 ∧ alloc.vec.Vec.len x.fraction = 0#usize) := by
        simp only [UScalar.eq_equiv, alloc.vec.Vec.len_val]; simpa using end'
      by_cases eh : x.hour = 24#u8
      · by_cases em : x.minute = 0#u8
        · by_cases es : x.second = 0#u8
          · have ef : ¬ alloc.vec.Vec.len x.fraction = 0#usize := fun e => this ⟨eh, em, es, e⟩
            simp [notLt, eh, em, es, ef]
          · simp [notLt, eh, em, es]
        · simp [notLt, eh, em]
      · simp [notLt, eh]

/-! ### Reading the bytes after the year -/

/-- The digits of a fraction of a second at the front of the bytes and the bytes
    after them: none without a `.` first, and after a `.` the digits up to the
    first byte that is no digit, which must be at least one. -/
def fractionSplit : List U8 → Option (List U8 × List U8)
  | [] => some ([], [])
  | b :: rest =>
    if b = 46#u8 then
      if rest.takeWhile (fun c => decide (Digit c)) = [] then none
      else some (rest.takeWhile (fun c => decide (Digit c)), rest.dropWhile (fun c => decide (Digit c)))
    else some ([], b :: rest)

/-- The offset in minutes of the parts of a time zone. -/
def zoneMinutes (z : Bool × ℕ × ℕ) : ℤ := (if z.1 then -1 else 1) * ((60 * z.2.1 + z.2.2 : ℕ) : ℤ)

/-- The moment of a date and a time as written, with `24:00:00` and no fraction
    of a second for the first instant of the next day. -/
noncomputable def settle (year : ℤ) (month day hour minute second : ℕ) (fraction : List U8) (zone : Option ℤ) :
    Option Moment :=
  if hour < 24 then
    if minute < 60 ∧ second < 60 then some ⟨year, month, day, hour, minute, second + fractionValue fraction, zone⟩
    else none
  else if hour = 24 ∧ minute = 0 ∧ second = 0 ∧ fractionValue fraction = 0 then
    some ⟨(nextDate year month day).1, (nextDate year month day).2.1, (nextDate year month day).2.2, 0, 0, 0, zone⟩
  else none

/-- The moment that the bytes after a year write, read the way the kernel reads
    them: the date and the time at their places, the fraction of a second, the
    time zone, which a time stamp needs, and the moment they settle to. -/
noncomputable def restRead (stamped : Bool) (year : ℤ) (rest : List U8) : Option Moment :=
  match dateValue year rest, timeValue (rest.drop 6), fractionSplit (rest.drop 15) with
  | some (month, day), some (hour, minute, second), some (fraction, zoneText) =>
    match zoneParts zoneText with
    | some zone =>
      if stamped = true ∧ zone = none then none
      else settle year month day hour minute second fraction (zone.map zoneMinutes)
    | none => none
  | _, _, _ => none

/-- The moment of a kernel value, if it is one. -/
def valueMoment : datatypes.DataValue → Option Moment
  | .Moment x => some (momentOf x)
  | _ => none

/-- The year that `lexical[start..finish]` writes, negative when `negative`. -/
def yearOf (lexical : List U8) (negative : Bool) (start finish : ℕ) : ℤ :=
  (if negative then -1 else 1) * (digitsValue (seg lexical start finish) : ℤ)

/-- What `moment_value` has found of a lexical form before `moment_after`: the
    year `lexical[start..finish]` of digits up to the first byte that is no
    digit, after a `-` when `negative`, of four digits or more without a leading
    zero, and fifteen bytes after it. -/
structure YearRead (lexical : List U8) (negative : Bool) (start finish : ℕ) : Prop where
  start_eq : start = if negative then 1 else 0
  sign : lexical.take start = if negative then [45#u8] else []
  order : start < finish
  room : finish + 15 ≤ lexical.length
  digits : ∀ i (hi : i < lexical.length), start ≤ i → i < finish → Digit lexical[i]
  stop : ∀ h : finish < lexical.length, ¬ Digit lexical[finish]
  shape : finish - start = 4 ∨ (4 < finish - start ∧ lexical[start]? ≠ some 48#u8)

theorem no_zone_spec (zone : Option (Bool × U8 × U8)) : moments.no_zone zone = .ok (decide (zone = none)) := by
  cases zone <;> rfl

private theorem takeWhile_digits (l : List U8) (a b : Nat) (ab : a ≤ b) (fits : b ≤ l.length)
    (digits : ∀ i (hi : i < l.length), a ≤ i → i < b → Digit l[i]) (stop : ∀ h : b < l.length, ¬ Digit l[b]) :
    (l.drop a).takeWhile (fun c => decide (Digit c)) = seg l a b ∧
      (l.drop a).dropWhile (fun c => decide (Digit c)) = l.drop b := by
  induction h : b - a generalizing a with
  | zero =>
    have same : a = b := by omega
    subst same
    rw [seg_empty _ _ _ le_rfl]
    by_cases inside : a < l.length
    · rw [List.drop_eq_getElem_cons inside]
      have nd := stop inside
      simp only [List.takeWhile_cons, List.dropWhile_cons, nd, decide_false, Bool.false_eq_true, ↓reduceIte,
        and_self]
    · rw [List.drop_eq_nil_iff.mpr (by omega)]; simp
  | succ n ih =>
    have inside : a < l.length := by omega
    have d := digits a inside le_rfl (by omega)
    have rest := ih (a + 1) (by omega) (fun i hi lo hi' => digits i hi (by omega) hi') (by omega)
    rw [List.drop_eq_getElem_cons inside, seg_cons _ _ _ (by omega) fits]
    simp only [List.takeWhile_cons, List.dropWhile_cons, d, decide_true, ↓reduceIte]
    exact ⟨by rw [rest.1], rest.2⟩

theorem dateValue_some {year : ℤ} {l : List U8} {m d : ℕ} (h : dateValue year l = some (m, d)) :
    1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysIn year m := by
  match l, h with
  | a :: m1 :: m2 :: b :: d1 :: d2 :: _, h =>
    simp only [dateValue] at h
    split_ifs at h
    generalize twoValue [m1, m2] = x at h
    generalize twoValue [d1, d2] = x' at h
    cases x <;> cases x' <;> simp only [dateOf, reduceCtorEq] at h
    split_ifs at h with fits
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fits

theorem zoneOf_some {west : Bool} {h m : Option ℕ} {w : Bool} {hh mm : ℕ}
    (e : zoneOf west h m = some (some (w, hh, mm))) :
    ((hh ≤ 13 ∧ mm ≤ 59) ∨ (hh = 14 ∧ mm = 0)) ∧ (w = true → hh ≠ 0 ∨ mm ≠ 0) := by
  cases h <;> cases m <;> simp only [zoneOf, reduceCtorEq] at e
  split_ifs at e with fits
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨hw, rfl, rfl⟩ := e
  refine ⟨fits, fun hw' => ?_⟩
  rw [← hw] at hw'
  simp at hw'
  exact hw'.2

theorem zoneParts_some {l : List U8} {w : Bool} {hh mm : ℕ} (e : zoneParts l = some (some (w, hh, mm))) :
    ((hh ≤ 13 ∧ mm ≤ 59) ∨ (hh = 14 ∧ mm = 0)) ∧ (w = true → hh ≠ 0 ∨ mm ≠ 0) := by
  match l, e with
  | [z], e =>
    simp only [zoneParts] at e
    split_ifs at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    simp
  | [s', h1, h2, c, m1, m2], e =>
    simp only [zoneParts] at e
    split_ifs at e
    exact zoneOf_some e

theorem nextDate_valid {year : ℤ} {month day : ℕ} (m1 : 1 ≤ month) (m12 : month ≤ 12) :
    1 ≤ (nextDate year month day).2.1 ∧ (nextDate year month day).2.1 ≤ 12 ∧ 1 ≤ (nextDate year month day).2.2 ∧
      (nextDate year month day).2.2 ≤ daysIn (nextDate year month day).1 (nextDate year month day).2.1 := by
  unfold nextDate
  have := daysIn_le year month
  have := daysIn_le (year + 1) 1
  have := daysIn_le year (month + 1)
  split_ifs <;> simp <;> omega

/-- The digits that the kernel keeps of a fraction of a second have the value of
    all the digits. -/
theorem fraction_read (lexical : alloc.vec.Vec U8) (i3 : Usize) (h : i3.val ≤ lexical.val.length) (f : Option Usize)
    (fNoDot : lexical.val[i3.val]? ≠ some 46#u8 → f = some i3)
    (fDot : lexical.val[i3.val]? = some 46#u8 →
        ∃ stop : Usize, i3.val + 1 ≤ stop.val ∧ stop.val ≤ lexical.val.length ∧
          (∀ i (hi : i < lexical.val.length), i3.val + 1 ≤ i → i < stop.val → Digit lexical.val[i]) ∧
          (∀ hs : stop.val < lexical.val.length, ¬ Digit lexical.val[stop.val]) ∧
          f = if i3.val + 1 < stop.val then some stop else none) :
    (f = none → fractionSplit (lexical.val.drop i3.val) = none) ∧
    ∀ stop, f = some stop → i3.val ≤ stop.val ∧ stop.val ≤ lexical.val.length ∧
      fractionSplit (lexical.val.drop i3.val) =
        some ((if i3.val < stop.val then seg lexical.val (i3.val + 1) stop.val else []), lexical.val.drop stop.val) := by
  by_cases dot : lexical.val[i3.val]? = some 46#u8
  · obtain ⟨stop, low, high, digits, stopNot, fIs⟩ := fDot dot
    have inside : i3.val < lexical.val.length := by
      by_contra out; rw [List.getElem?_eq_none (by omega)] at dot; cases dot
    have atDot : lexical.val[i3.val] = 46#u8 := by
      rw [List.getElem?_eq_getElem inside] at dot; exact Option.some.inj dot
    obtain ⟨tw, dw⟩ := takeWhile_digits lexical.val (i3.val + 1) stop.val low high digits stopNot
    have split : fractionSplit (lexical.val.drop i3.val) =
        if seg lexical.val (i3.val + 1) stop.val = [] then none
        else some (seg lexical.val (i3.val + 1) stop.val, lexical.val.drop stop.val) := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [fractionSplit, atDot, ↓reduceIte, tw, dw]
    by_cases more : i3.val + 1 < stop.val
    · have nonempty : seg lexical.val (i3.val + 1) stop.val ≠ [] := by
        rw [seg_cons _ _ _ more high]; simp
      rw [fIs, if_pos more]
      refine ⟨fun h' => (by cases h'), fun stop' h' => ?_⟩
      cases h'
      refine ⟨by omega, high, ?_⟩
      rw [split, if_neg nonempty, if_pos (by omega)]
    · have empty : seg lexical.val (i3.val + 1) stop.val = [] := seg_empty _ _ _ (by omega)
      rw [fIs, if_neg more]
      refine ⟨fun _ => (by rw [split, if_pos empty]), fun stop' h' => (by cases h')⟩
  · have fIs := fNoDot dot
    subst fIs
    refine ⟨fun h' => (by cases h'), fun stop' h' => ?_⟩
    cases h'
    refine ⟨le_rfl, h, ?_⟩
    rw [if_neg (lt_irrefl _)]
    by_cases inside : i3.val < lexical.val.length
    · rw [List.drop_eq_getElem_cons inside]
      have notDot : ¬ lexical.val[i3.val] = 46#u8 := fun e => dot (by rw [List.getElem?_eq_getElem inside, e])
      simp only [fractionSplit, notDot, ↓reduceIte]
    · rw [List.drop_eq_nil_iff.mpr (by omega)]; rfl

private theorem mem_takeWhile_digit {l : List U8} {c : U8} (m : c ∈ l.takeWhile (fun c => decide (Digit c))) :
    Digit c := by
  induction l with
  | nil => cases m
  | cons a rest ih =>
    simp only [List.takeWhile_cons] at m
    split_ifs at m with h
    · rcases List.mem_cons.mp m with rfl | m'
      · simpa using h
      · exact ih m'
    · cases m

theorem fractionSplit_digits {l F rest : List U8} (h : fractionSplit l = some (F, rest)) : Digits F := by
  match l, h with
  | [], h =>
    simp only [fractionSplit, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; intro b m; cases m
  | b :: tail, h =>
    simp only [fractionSplit] at h
    split_ifs at h with hb hempty
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      intro c m
      exact mem_takeWhile_digit m
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; intro c m; cases m

theorem zone_facts {l : List U8} {zone : Option (Bool × U8 × U8)} (h : zoneParts l = some (zoneNat zone)) :
    (∀ w hh mm, zone = some (w, hh, mm) → mm.val < 60 ∧ (w = true → hh.val ≠ 0 ∨ mm.val ≠ 0)) ∧
    ∀ z, zone.map (fun z => (if z.1 then -1 else 1) * ((60 * z.2.1.val + z.2.2.val : ℕ) : ℤ)) = some z →
      -840 ≤ z ∧ z ≤ 840 := by
  cases zone with
  | none => exact ⟨fun _ _ _ h' => (by cases h'), fun _ h' => (by cases h')⟩
  | some p =>
    obtain ⟨w, hh, mm⟩ := p
    have facts := zoneParts_some (l := l) (w := w) (hh := hh.val) (mm := mm.val) (by rw [h]; rfl)
    refine ⟨fun w' hh' mm' e => ?_, fun z e => ?_⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact ⟨by omega, facts.2⟩
    · simp only [Option.map_some, Option.some.injEq] at e
      subst e
      split <;> omega

theorem zoneNat_minutes (zone : Option (Bool × U8 × U8)) :
    (zoneNat zone).map zoneMinutes =
      zone.map (fun z => (if z.1 then -1 else 1) * ((60 * z.2.1.val + z.2.2.val : ℕ) : ℤ)) := by
  cases zone <;> rfl

theorem moment_after_spec (lexical : alloc.vec.Vec U8) (negative : Bool) (start finish : Usize) (stamped : Bool)
    (read : YearRead lexical.val negative start.val finish.val) (small : lexical.val.length + 2 < Usize.max) :
    ∃ r, moments.moment_after lexical negative start finish stamped = .ok r ∧
      (∀ v, r = some v → ∃ x, v = .Moment x ∧ CanonicalMoment x) ∧
      r.bind valueMoment = restRead stamped (yearOf lexical.val negative start.val finish.val)
        (lexical.val.drop finish.val) := by
  obtain ⟨_, _, order, room, digits, _, _⟩ := read
  rw [moments.moment_after]
  obtain ⟨z, zRun, zLow, zHigh, zZeros, zStop⟩ := nonzero_start_spec lexical start finish (by omega) (by omega)
  obtain ⟨year, yRun, yValue⟩ := copy_span_spec lexical z finish (alloc.vec.Vec.new U8) (by omega)
    (by simp [new_val]; omega)
  have yearIs : year.val = seg lexical.val z.val finish.val := by rw [yValue, new_val, List.nil_append]
  have yearLength : year.val.length ≤ lexical.val.length := by rw [yearIs, seg_length _ _ _ (by omega)]; omega
  have yearDigits : Digits year.val := by
    intro b m
    rw [yearIs] at m
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem m
    have hi' := hi
    rw [seg_length _ _ _ (by omega)] at hi'
    rw [seg_getElem]
    exact digits _ _ (by omega) (by omega)
  have yearCanonical : Rowl.Numbers.Canonical year.val := by
    refine ⟨yearDigits, ?_⟩
    rw [yearIs]
    by_cases before : z.val < finish.val
    · rw [seg_cons _ _ _ before (by omega)]
      simpa using zStop before
    · rw [seg_empty _ _ _ (by omega)]; simp
  have yearValue : digitsValue year.val = digitsValue (seg lexical.val start.val finish.val) := by
    rw [seg_append lexical.val start.val z.val finish.val zLow zHigh (by omega),
      Rowl.Numbers.value_zeros_append _ _ zZeros, yearIs]
  set y := yearOf lexical.val negative start.val finish.val with hyDef
  have hy : y.natAbs = digitsValue year.val := by
    rw [yearValue, hyDef, yearOf]; split <;> simp
  have nonemptyIff : (0#usize < alloc.vec.Vec.len year) ↔ year.val ≠ [] := by
    simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]
    simp [List.length_pos_iff]
  have signYear : (if (negative && decide (0#usize < alloc.vec.Vec.len year)) = true then -1 else 1) *
      (digitsValue year.val : ℤ) = y := by
    rw [hyDef, yearOf, ← yearValue]
    by_cases empty : year.val = []
    · have zero : digitsValue year.val = 0 := by rw [empty]; rfl
      simp [zero]
    · have nonempty : 0#usize < alloc.vec.Vec.len year := nonemptyIff.mpr empty
      simp [nonempty]
  obtain ⟨d, dRun, dValue⟩ := date_at_spec lexical finish year yearDigits y hy
  have drop6 : (lexical.val.drop finish.val).drop 6 = lexical.val.drop (finish.val + 6) := by
    rw [List.drop_drop]
  have drop15 : (lexical.val.drop finish.val).drop 15 = lexical.val.drop (finish.val + 15) := by
    rw [List.drop_drop]
  simp only [zRun, yRun, bind_ok, dRun]
  rcases d with _ | ⟨month, day⟩
  · refine ⟨none, rfl, fun v h' => (by cases h'), ?_⟩
    simp only [Option.map_none] at dValue
    rw [Option.bind_none, restRead, ← dValue]
  · simp only [Option.map_some] at dValue
    have dateFacts := dateValue_some dValue.symm
    obtain ⟨i2, add2, i2Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := finish) (y := 6#usize) (by simp; omega))
    have i2Is : i2.val = finish.val + 6 := by simpa using i2Value
    obtain ⟨t, tRun, tValue⟩ := time_at_spec lexical i2
    rw [i2Is] at tValue
    simp only [add2, bind_ok, tRun]
    rcases t with _ | ⟨hour, minute, second⟩
    · refine ⟨none, rfl, fun v h' => (by cases h'), ?_⟩
      simp only [Option.map_none] at tValue
      rw [Option.bind_none, restRead, ← dValue, drop6, ← tValue]
    · simp only [Option.map_some] at tValue
      obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := finish) (y := 15#usize) (by simp; omega))
      have i3Is : i3.val = finish.val + 15 := by simpa using i3Value
      obtain ⟨f, fRun, fNoDot, fDot⟩ := fraction_end_spec lexical i3 (by omega)
      obtain ⟨fNone, fSome⟩ := fraction_read lexical i3 (by omega) f fNoDot fDot
      rw [i3Is] at fNone fSome
      simp only [add3, bind_ok, fRun]
      rcases f with _ | stop
      · refine ⟨none, rfl, fun v h' => (by cases h'), ?_⟩
        rw [Option.bind_none, restRead, ← dValue, drop6, ← tValue, drop15, fNone rfl]
      · obtain ⟨stopLow, stopHigh, split⟩ := fSome stop rfl
        obtain ⟨zr, zRunZ, zValue⟩ := zone_value_spec lexical stop stopHigh
        simp only [zRunZ, bind_ok]
        rcases zr with _ | zone
        · refine ⟨none, rfl, fun v h' => (by cases h'), ?_⟩
          simp only [Option.map_none] at zValue
          rw [Option.bind_none, restRead, ← dValue, drop6, ← tValue, drop15, split]
          simp only [← zValue]
        · simp only [Option.map_some] at zValue
          simp only [no_zone_spec, bind_ok]
          set F := (if finish.val + 15 < stop.val then seg lexical.val (finish.val + 15 + 1) stop.val else [])
            with hF
          have zoneNone : zoneNat zone = none ↔ zone = none := by cases zone <;> simp [zoneNat]
          have specRest : restRead stamped y (lexical.val.drop finish.val) =
              if stamped = true ∧ zoneNat zone = none then none
              else settle y month.val day.val hour.val minute.val second.val F ((zoneNat zone).map zoneMinutes) := by
            rw [restRead, ← dValue, drop6, ← tValue, drop15, split]
            simp only [← zValue]
          have facts := zone_facts zValue.symm
          by_cases stampedNone : stamped = true ∧ zone = none
          · refine ⟨none, ?_, fun v h' => (by cases h'), ?_⟩
            · obtain ⟨e1, e2⟩ := stampedNone
              subst e1; subst e2
              rfl
            · rw [specRest, if_pos ⟨stampedNone.1, zoneNone.mpr stampedNone.2⟩]; rfl
          · have notBoth : (stamped && decide (zone = none)) = false := by
              cases stamped <;> simp_all
            have notBoth' : ¬ (stamped = true ∧ zoneNat zone = none) := fun h' => stampedNone ⟨h'.1, zoneNone.mp h'.2⟩
            rw [specRest, if_neg notBoth']
            obtain ⟨v, vRun, vTrim, vEmpty⟩ := fraction_digits_spec lexical i3 stop stopHigh
            rw [i3Is] at vTrim vEmpty
            have fDigits : Digits F := fractionSplit_digits split
            have vFacts : Digits v.val ∧ v.val.getLast? ≠ some 48#u8 ∧ fractionValue v.val = fractionValue F := by
              by_cases more : finish.val + 15 < stop.val
              · obtain ⟨zeros, eq, allZeros, last⟩ := vTrim more
                have FIs : F = v.val ++ zeros := by rw [hF, if_pos more, eq]
                rw [FIs] at fDigits ⊢
                exact ⟨fun b m => fDigits b (List.mem_append_left _ m), last,
                  (fractionValue_append_zeros _ _ allZeros).symm⟩
              · have vNil := vEmpty (by omega)
                have FNil : F = [] := by rw [hF, if_neg more]
                rw [vNil, FNil]
                exact ⟨fun b m => (by cases m), (by simp), rfl⟩
            obtain ⟨vDigits, vLast, vValue⟩ := vFacts
            have vNilIff : v.val = [] ↔ fractionValue F = 0 := by
              rw [← vValue, fractionValue_zero_iff _ vDigits]
              constructor
              · intro e b m; rw [e] at m; cases m
              · intro all
                by_contra nonempty
                have lastMem := List.getLast_mem nonempty
                have := all _ lastMem
                exact vLast (by rw [List.getLast?_eq_some_getLast nonempty, this])
            set x : datatypes.Moment := ⟨negative && decide (0#usize < alloc.vec.Vec.len year), year, month, day,
              hour, minute, second, v, zone⟩ with hx
            have xYear : (momentOf x).year = y := by simp only [momentOf, hx]; exact signYear
            have ok : DateOk x := ⟨yearCanonical, fun h' => (by
                simp only [hx, Bool.and_eq_true, decide_eq_true_eq] at h'; exact nonemptyIff.mp h'.2),
              (by simp only [hx]; omega), dateFacts.1, dateFacts.2.1, dateFacts.2.2.1,
              (by rw [xYear]; exact dateFacts.2.2.2)⟩
            obtain ⟨r, sRun, sEarly, sEnd, sNone⟩ := settled_spec x ok
            have fb := fractionValue_bounds v.val vDigits
            have canonicalX : minute.val < 60 ∧ second.val < 60 → hour.val < 24 → CanonicalMoment x := by
              intro clock early
              refine ⟨ok.1, ok.2.1, vDigits, vLast, clock.2, facts.1, dateFacts.1, dateFacts.2.1, dateFacts.2.2.1,
                (by rw [xYear]; exact dateFacts.2.2.2), early, clock.1, ?_, ?_, decimal_second _ _, facts.2⟩
              · show (0 : ℚ) ≤ second.val + fractionValue v.val
                have := fb.1; positivity
              · show (second.val : ℚ) + fractionValue v.val < 60
                have : (second.val : ℚ) ≤ 59 := by exact_mod_cast (by omega : second.val ≤ 59)
                linarith [fb.2]
            obtain ⟨x'', nextRun, nextCanonical, nextSign, nextDateIs, nextHour, nextMinute, nextSecond, nextFraction,
              nextZone⟩ := next_day_correct x ok
            have nextValid : (nextDate y month.val day.val).2.1 = (momentOf x'').month ∧
                (nextDate y month.val day.val).2.2 = (momentOf x'').day ∧
                (nextDate y month.val day.val).1 = (momentOf x'').year := by
              rw [← xYear]
              exact ⟨(congrArg (fun p => p.2.1) nextDateIs).symm, (congrArg (fun p => p.2.2) nextDateIs).symm,
                (congrArg Prod.fst nextDateIs).symm⟩
            have canonicalNext : minute.val = 0 ∧ second.val = 0 ∧ v.val = [] → CanonicalMoment x'' := by
              intro ⟨m0, s0, vNil⟩
              obtain ⟨e1, e2, e3⟩ := nextValid
              have valid := nextDate_valid (year := y) (day := day.val) dateFacts.1 dateFacts.2.1
              rw [e1, e2, e3] at valid
              have fracNil : x''.fraction.val = [] := by rw [nextFraction]; exact vNil
              have secondIs : x''.second.val = 0 := by rw [nextSecond]; exact s0
              have minuteIs : x''.minute.val = 0 := by rw [nextMinute]; exact m0
              have zoneIs : (momentOf x'').zone = (momentOf x).zone := by simp only [momentOf, nextZone]
              refine ⟨nextCanonical, nextSign, ?_, ?_, ?_, ?_, valid.1, valid.2.1, valid.2.2.1, valid.2.2.2, ?_, ?_, ?_,
                ?_, ?_, ?_⟩
              · rw [fracNil]; intro b m; cases m
              · rw [fracNil]; simp
              · omega
              · rw [nextZone]; exact facts.1
              · show x''.hour.val < 24; omega
              · show x''.minute.val < 60; omega
              · show (0 : ℚ) ≤ x''.second.val + fractionValue x''.fraction.val
                rw [fracNil, fractionValue_nil, secondIs]; simp
              · show (x''.second.val : ℚ) + fractionValue x''.fraction.val < 60
                rw [fracNil, fractionValue_nil, secondIs]; norm_num
              · exact decimal_second _ _
              · rw [zoneIs]; exact facts.2
            refine ⟨r, ?_, ?_, ?_⟩
            · simp only [notBoth, Bool.false_eq_true, ↓reduceIte, vRun, bind_ok]
              exact sRun
            · intro w hw
              by_cases early : hour.val < 24
              · have rIs := sEarly early
                by_cases clock : minute.val < 60 ∧ second.val < 60
                · rw [if_pos clock] at rIs
                  rw [rIs] at hw
                  cases hw
                  exact ⟨x, rfl, canonicalX clock early⟩
                · rw [if_neg clock] at rIs; rw [rIs] at hw; cases hw
              · by_cases endDay : hour.val = 24 ∧ minute.val = 0 ∧ second.val = 0 ∧ v.val = []
                · obtain ⟨x', run', rIs⟩ := sEnd (by show 24 ≤ hour.val; omega) endDay
                  have same := Result.ok_injective (nextRun.symm.trans run')
                  subst same
                  rw [rIs] at hw; cases hw
                  exact ⟨x'', rfl, canonicalNext endDay.2⟩
                · rw [sNone (by show 24 ≤ hour.val; omega) endDay] at hw; cases hw
            · unfold settle
              by_cases early : hour.val < 24
              · rw [sEarly early, if_pos early]
                by_cases clock : minute.val < 60 ∧ second.val < 60
                · rw [if_pos clock, if_pos clock, Option.bind_some, valueMoment, ← xYear, ← vValue, zoneNat_minutes]
                  rfl
                · rw [if_neg clock, if_neg clock]; rfl
              · rw [if_neg early]
                by_cases endDay : hour.val = 24 ∧ minute.val = 0 ∧ second.val = 0 ∧ v.val = []
                · obtain ⟨x', run', rIs⟩ := sEnd (by show 24 ≤ hour.val; omega) endDay
                  have same := Result.ok_injective (nextRun.symm.trans run')
                  subst same
                  rw [rIs, if_pos ⟨endDay.1, endDay.2.1, endDay.2.2.1, vNilIff.mp endDay.2.2.2⟩, Option.bind_some,
                    valueMoment]
                  obtain ⟨e1, e2, e3⟩ := nextValid
                  rw [e1, e2, e3, zoneNat_minutes]
                  have fracNil : x''.fraction.val = [] := by rw [nextFraction]; exact endDay.2.2.2
                  simp only [Option.some.injEq]
                  show momentOf x'' = ⟨(momentOf x'').year, (momentOf x'').month, (momentOf x'').day, 0, 0, 0, _⟩
                  simp only [momentOf, nextHour, nextMinute, nextSecond, fracNil, fractionValue_nil, nextZone]
                  simp only [Moment.mk.injEq, true_and, Nat.cast_zero, add_zero]
                  exact ⟨endDay.2.1, (by show ((second.val : ℕ) : ℚ) = 0; exact_mod_cast endDay.2.2.1), rfl⟩
                · rw [sNone (by show 24 ≤ hour.val; omega) endDay, if_neg (fun h' => endDay ⟨h'.1, h'.2.1, h'.2.2.1,
                    vNilIff.mpr h'.2.2.2⟩)]
                  rfl

/-! ### The grammar and the reading -/

theorem dateValue_cases {year : ℤ} {l : List U8} {m d : ℕ} (h : dateValue year l = some (m, d)) :
    ∃ m1 m2 d1 d2 r, l = 45#u8 :: m1 :: m2 :: 45#u8 :: d1 :: d2 :: r ∧ twoValue [m1, m2] = some m ∧
      twoValue [d1, d2] = some d ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysIn year m := by
  match l, h with
  | a :: m1 :: m2 :: b :: d1 :: d2 :: r, h =>
    simp only [dateValue] at h
    split_ifs at h with dashes
    obtain ⟨rfl, rfl⟩ := dashes
    generalize hx : twoValue [m1, m2] = x at h
    generalize hx' : twoValue [d1, d2] = x' at h
    cases x <;> cases x' <;> simp only [dateOf, reduceCtorEq] at h
    split_ifs at h with fits
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m1, m2, d1, d2, r, rfl, hx, hx', fits⟩

theorem timeValue_cases {l : List U8} {h i s : ℕ} (e : timeValue l = some (h, i, s)) :
    ∃ h1 h2 i1 i2 s1 s2 r, l = 84#u8 :: h1 :: h2 :: 58#u8 :: i1 :: i2 :: 58#u8 :: s1 :: s2 :: r ∧
      twoValue [h1, h2] = some h ∧ twoValue [i1, i2] = some i ∧ twoValue [s1, s2] = some s := by
  match l, e with
  | t :: h1 :: h2 :: c1 :: i1 :: i2 :: c2 :: s1 :: s2 :: r, e =>
    simp only [timeValue] at e
    split_ifs at e with marks
    obtain ⟨rfl, rfl, rfl⟩ := marks
    generalize hx : twoValue [h1, h2] = x at e
    generalize hy : twoValue [i1, i2] = y at e
    generalize hz : twoValue [s1, s2] = z at e
    cases x <;> cases y <;> cases z <;> simp only [timeOf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨h1, h2, i1, i2, s1, s2, r, rfl, hx, hy, hz⟩

theorem fractionSplit_eq {l F rest : List U8} (h : fractionSplit l = some (F, rest)) :
    l = (if F = [] then [] else 46#u8 :: F) ++ rest ∧ Digits F := by
  refine ⟨?_, fractionSplit_digits h⟩
  match l, h with
  | [], h =>
    simp only [fractionSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | b :: tail, h =>
    simp only [fractionSplit] at h
    split_ifs at h with hb hempty
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [if_neg hempty, hb]
      simp only [List.cons_append, List.takeWhile_append_dropWhile]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

theorem zoneParts_form {l : List U8} {zt : Option (Bool × ℕ × ℕ)} (h : zoneParts l = some zt) :
    (l = [] ∧ zt = none) ∨ ∃ v, zt = some v ∧ ZoneForm l (zoneMinutes v) := by
  match l, h with
  | [], h =>
    simp only [zoneParts, Option.some.injEq] at h
    exact .inl ⟨rfl, h.symm⟩
  | [z], h =>
    simp only [zoneParts] at h
    split_ifs at h with hz
    simp only [Option.some.injEq] at h
    subst hz; subst h
    exact .inr ⟨_, rfl, .inl ⟨rfl, by simp [zoneMinutes]⟩⟩
  | [s', h1, h2, c, m1, m2], h =>
    simp only [zoneParts] at h
    split_ifs at h with marks
    obtain ⟨sign, rfl⟩ := marks
    generalize hx : twoValue [h1, h2] = x at h
    generalize hy : twoValue [m1, m2] = y at h
    cases x with
    | none => simp [zoneOf] at h
    | some hh =>
      cases y with
      | none => simp [zoneOf] at h
      | some mm =>
        simp only [zoneOf] at h
        split_ifs at h with fits
        simp only [Option.some.injEq] at h
        subst h
        refine .inr ⟨_, rfl, .inr ⟨decide (s' = 45#u8), [h1, h2], [m1, m2], hh, mm, ?_,
          (twoDigits_iff _ _ _).mpr hx, (twoDigits_iff _ _ _).mpr hy, fits, ?_⟩⟩
        · rcases sign with rfl | rfl <;> simp
        · simp only [zoneMinutes]
          by_cases zero : hh = 0 ∧ mm = 0
          · obtain ⟨rfl, rfl⟩ := zero; simp
          · have : hh ≠ 0 ∨ mm ≠ 0 := by omega
            simp [this]

theorem settle_some {year : ℤ} {month day hour minute second : ℕ} {fraction : List U8} {zone : Option ℤ}
    {m : Moment} (h : settle year month day hour minute second fraction zone = some m) :
    (hour < 24 ∧ minute < 60 ∧ second < 60 ∧
        m = ⟨year, month, day, hour, minute, second + fractionValue fraction, zone⟩) ∨
      (hour = 24 ∧ minute = 0 ∧ second = 0 ∧ fractionValue fraction = 0 ∧
        m = ⟨(nextDate year month day).1, (nextDate year month day).2.1, (nextDate year month day).2.2, 0, 0, 0,
          zone⟩) := by
  unfold settle at h
  split_ifs at h with early clock endDay
  · simp only [Option.some.injEq] at h
    exact .inl ⟨early, clock.1, clock.2, h.symm⟩
  · simp only [Option.some.injEq] at h
    exact .inr ⟨endDay.1, endDay.2.1, endDay.2.2.1, endDay.2.2.2, h.symm⟩

private theorem two_list {t : List U8} {n : ℕ} (h : TwoDigits t n) : ∃ a b, t = [a, b] := by
  match t, h.1 with
  | [a, b], _ => exact ⟨a, b, rfl⟩

private theorem takeWhile_digits_append (l1 l2 : List U8) (d : Digits l1)
    (head : ∀ b, l2.head? = some b → ¬ Digit b) :
    (l1 ++ l2).takeWhile (fun c => decide (Digit c)) = l1 ∧ (l1 ++ l2).dropWhile (fun c => decide (Digit c)) = l2 := by
  induction l1 with
  | nil =>
    match l2, head with
    | [], _ => exact ⟨rfl, rfl⟩
    | b :: rest, head =>
      have nd := head b rfl
      simp only [List.nil_append, List.takeWhile_cons, List.dropWhile_cons, nd, decide_false, Bool.false_eq_true,
        ↓reduceIte, and_self]
  | cons a rest ih =>
    have da := d a List.mem_cons_self
    obtain ⟨tw, dw⟩ := ih (fun b m => d b (List.mem_cons_of_mem _ m))
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, da, decide_true, ↓reduceIte, tw, dw,
      and_self]

private theorem u8_ne {a b : U8} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg UScalar.val e)

theorem zoneText_head {l : List U8} (h : l = [] ∨ ∃ z, ZoneForm l z) :
    ∀ b, l.head? = some b → ¬ Digit b ∧ b ≠ 46#u8 := by
  intro b hb
  rcases h with rfl | ⟨z, ⟨rfl, _⟩ | ⟨west, hh, mm, hv, mv, rfl, _⟩⟩
  · cases hb
  · have e : 90#u8 = b := Option.some.inj hb
    subst e
    refine ⟨fun d => ?_, u8_ne (by simp)⟩
    have := d.2; simp at this
  · have e : (if west = true then 45#u8 else 43#u8) = b := Option.some.inj hb
    subst e
    cases west
    · refine ⟨fun d => ?_, u8_ne (by simp)⟩; have := d.1; simp at this
    · refine ⟨fun d => ?_, u8_ne (by simp)⟩; have := d.1; simp at this

theorem fractionSplit_form (fraction zoneText : List U8) (d : Digits fraction)
    (head : ∀ b, zoneText.head? = some b → ¬ Digit b ∧ b ≠ 46#u8) :
    fractionSplit ((if fraction = [] then [] else 46#u8 :: fraction) ++ zoneText) = some (fraction, zoneText) := by
  by_cases empty : fraction = []
  · subst empty
    simp only [↓reduceIte, List.nil_append]
    match zoneText, head with
    | [], _ => rfl
    | b :: rest, head =>
      have := (head b rfl).2
      simp only [fractionSplit, this, ↓reduceIte]
  · obtain ⟨tw, dw⟩ := takeWhile_digits_append fraction zoneText d (fun b hb => (head b hb).1)
    simp only [empty, ↓reduceIte, List.cons_append, fractionSplit, tw, dw]

theorem zoneParts_of_form {l : List U8} {z : ℤ} (h : ZoneForm l z) :
    ∃ v, zoneParts l = some (some v) ∧ zoneMinutes v = z := by
  rcases h with ⟨rfl, rfl⟩ | ⟨west, hh, mm, h, m, rfl, th, tm, fits, rfl⟩
  · exact ⟨(false, 0, 0), rfl, by simp [zoneMinutes]⟩
  · obtain ⟨h1, h2, rfl⟩ := two_list th
    obtain ⟨m1, m2, rfl⟩ := two_list tm
    have hv := (twoDigits_iff _ _ _).mp th
    have mv := (twoDigits_iff _ _ _).mp tm
    refine ⟨(west = true ∧ (h ≠ 0 ∨ m ≠ 0), h, m), ?_, ?_⟩
    · cases west <;> simp [zoneParts, zoneOf, hv, mv, fits]
    · simp only [zoneMinutes]
      by_cases zero : h = 0 ∧ m = 0
      · obtain ⟨rfl, rfl⟩ := zero; simp
      · have : h ≠ 0 ∨ m ≠ 0 := by omega
        cases west <;> simp [this]

theorem momentForm_iff (text : List U8) (m : Moment) :
    MomentForm text m ↔ ∃ (yearText : List U8) (year : ℤ), YearForm yearText year ∧
      text.take yearText.length = yearText ∧ restRead false year (text.drop yearText.length) = some m := by
  constructor
  · rintro ⟨yearText, mm, dd, hh, mi, ss, fraction, zoneText, year, month, day, hour, minute, second, zone, rfl,
      yf, tmm, m1, m12, tdd, d1, dIn, thh, tmi, tss, fd, zoneCase, valueCase⟩
    obtain ⟨a1, a2, rfl⟩ := two_list tmm
    obtain ⟨b1, b2, rfl⟩ := two_list tdd
    obtain ⟨c1, c2, rfl⟩ := two_list thh
    obtain ⟨e1, e2, rfl⟩ := two_list tmi
    obtain ⟨f1, f2, rfl⟩ := two_list tss
    refine ⟨yearText, year, yf, by simp, ?_⟩
    have restEq : (yearText ++ 45#u8 :: [a1, a2] ++ 45#u8 :: [b1, b2] ++ 84#u8 :: [c1, c2] ++ 58#u8 :: [e1, e2] ++
        58#u8 :: [f1, f2] ++ (if fraction = [] then [] else 46#u8 :: fraction) ++ zoneText).drop yearText.length =
        45#u8 :: a1 :: a2 :: 45#u8 :: b1 :: b2 :: 84#u8 :: c1 :: c2 :: 58#u8 :: e1 :: e2 :: 58#u8 :: f1 :: f2 ::
          ((if fraction = [] then [] else 46#u8 :: fraction) ++ zoneText) := by
      simp
    set rest := (yearText ++ 45#u8 :: [a1, a2] ++ 45#u8 :: [b1, b2] ++ 84#u8 :: [c1, c2] ++ 58#u8 :: [e1, e2] ++
        58#u8 :: [f1, f2] ++ (if fraction = [] then [] else 46#u8 :: fraction) ++ zoneText).drop yearText.length
      with hrest
    have ma := (twoDigits_iff _ _ _).mp tmm
    have db := (twoDigits_iff _ _ _).mp tdd
    have hc := (twoDigits_iff _ _ _).mp thh
    have me := (twoDigits_iff _ _ _).mp tmi
    have sf := (twoDigits_iff _ _ _).mp tss
    have hd : dateValue year rest = some (month, day) := by
      rw [restEq]
      simp only [dateValue, eq_self_iff_true, and_self, ↓reduceIte, ma, db, dateOf]
      rw [if_pos ⟨m1, m12, d1, dIn⟩]
    have ht : timeValue (rest.drop 6) = some (hour, minute, second) := by
      rw [restEq]
      simp only [List.drop_succ_cons, List.drop_zero, timeValue, eq_self_iff_true, and_self, ↓reduceIte, hc, me, sf,
        timeOf]
    have hf : fractionSplit (rest.drop 15) = some (fraction, zoneText) := by
      rw [restEq]
      simp only [List.drop_succ_cons, List.drop_zero]
      exact fractionSplit_form fraction zoneText fd (zoneText_head (by
        rcases zoneCase with ⟨e, _⟩ | ⟨z, zf, _⟩
        · exact .inl e
        · exact .inr ⟨z, zf⟩))
    obtain ⟨zt, hz, hzMap⟩ : ∃ zt, zoneParts zoneText = some zt ∧ zt.map zoneMinutes = zone := by
      rcases zoneCase with ⟨rfl, rfl⟩ | ⟨z, zf, rfl⟩
      · exact ⟨none, rfl, rfl⟩
      · obtain ⟨v, hv, mv⟩ := zoneParts_of_form zf
        exact ⟨some v, hv, by rw [Option.map_some, mv]⟩
    have hs : settle year month day hour minute second fraction zone = some m := by
      unfold settle
      rcases valueCase with ⟨early, clock, sec, rfl⟩ | ⟨rfl, rfl, rfl, zero, rfl⟩
      · rw [if_pos early, if_pos ⟨clock, sec⟩]
      · rw [if_neg (by omega), if_pos ⟨rfl, rfl, rfl, zero⟩]
    unfold restRead
    rw [hd, ht, hf]
    simp only []
    rw [hz]
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    rw [hzMap]
    exact hs
  · rintro ⟨yearText, year, yf, pre, read⟩
    have textEq : text = yearText ++ text.drop yearText.length := by
      conv => lhs; rw [← List.take_append_drop yearText.length text]
      rw [pre]
    set rest := text.drop yearText.length with hrest
    unfold restRead at read
    generalize hd : dateValue year rest = dv at read
    generalize ht : timeValue (rest.drop 6) = tv at read
    generalize hf : fractionSplit (rest.drop 15) = fv at read
    rcases dv with _ | ⟨month, day⟩
    · cases read
    rcases tv with _ | ⟨hour, minute, second⟩
    · cases read
    rcases fv with _ | ⟨fraction, zoneText⟩
    · cases read
    simp only [] at read
    generalize hz : zoneParts zoneText = zv at read
    rcases zv with _ | zt
    · cases read
    simp only [Bool.false_eq_true, false_and, ↓reduceIte] at read
    obtain ⟨a1, a2, b1, b2, r1, restIs, ma, db, m1, m12, d1, dIn⟩ := dateValue_cases hd
    have r1Is : rest.drop 6 = r1 := by rw [restIs]; rfl
    rw [r1Is] at ht
    obtain ⟨c1, c2, e1, e2, f1, f2, r2, r1Eq, hc, me, sf⟩ := timeValue_cases ht
    have drop15 : rest.drop 15 = r2 := by simp only [restIs, r1Eq, List.drop_succ_cons, List.drop_zero]
    rw [drop15] at hf
    obtain ⟨r2Eq, fd⟩ := fractionSplit_eq hf
    refine ⟨yearText, [a1, a2], [b1, b2], [c1, c2], [e1, e2], [f1, f2], fraction, zoneText, year, month, day, hour,
      minute, second, zt.map zoneMinutes, ?_, yf, (twoDigits_iff _ _ _).mpr ma, m1, m12, (twoDigits_iff _ _ _).mpr db,
      d1, dIn, (twoDigits_iff _ _ _).mpr hc, (twoDigits_iff _ _ _).mpr me, (twoDigits_iff _ _ _).mpr sf, fd, ?_, ?_⟩
    · rw [textEq, restIs, r1Eq, r2Eq]
      simp
    · rcases zoneParts_form hz with ⟨rfl, rfl⟩ | ⟨v, rfl, zf⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨zoneMinutes v, zf, rfl⟩
    · rcases settle_some read with ⟨early, clock, sec, rfl⟩ | ⟨h24, m0, s0, zero, rfl⟩
      · exact .inl ⟨early, clock, sec, rfl⟩
      · exact .inr ⟨h24, m0, s0, zero, rfl⟩

theorem restRead_shape {stamped : Bool} {year : ℤ} {rest : List U8} {m : Moment}
    (h : restRead stamped year rest = some m) : rest.head? = some 45#u8 ∧ 15 ≤ rest.length := by
  unfold restRead at h
  cases hd : dateValue year rest with
  | none => simp [hd] at h
  | some p =>
    obtain ⟨mo, d⟩ := p
    cases ht : timeValue (rest.drop 6) with
    | none => simp [hd, ht] at h
    | some q =>
      obtain ⟨hh, mi, ss⟩ := q
      obtain ⟨m1, m2, d1, d2, r1, restIs, _⟩ := dateValue_cases hd
      have drop6 : rest.drop 6 = r1 := by rw [restIs]; rfl
      rw [drop6] at ht
      obtain ⟨_, _, _, _, _, _, r2, r1Is, _⟩ := timeValue_cases ht
      subst restIs
      subst r1Is
      exact ⟨rfl, by simp⟩

theorem valueMoment_some {v : datatypes.DataValue} {m : Moment} (h : valueMoment v = some m) :
    ∃ x, v = .Moment x ∧ momentOf x = m := by
  cases v <;> simp only [valueMoment, reduceCtorEq, Option.some.injEq] at h
  exact ⟨_, rfl, h⟩

theorem settle_zone {year : ℤ} {month day hour minute second : ℕ} {fraction : List U8} {zone : Option ℤ}
    {m : Moment} (h : settle year month day hour minute second fraction zone = some m) : m.zone = zone := by
  rcases settle_some h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> rfl

theorem restRead_stamped (year : ℤ) (rest : List U8) (m : Moment) :
    restRead true year rest = some m ↔ restRead false year rest = some m ∧ m.zone ≠ none := by
  unfold restRead
  rcases dateValue year rest with _ | ⟨month, day⟩
  · simp
  rcases timeValue (rest.drop 6) with _ | ⟨hour, minute, second⟩
  · simp
  rcases fractionSplit (rest.drop 15) with _ | ⟨fraction, zoneText⟩
  · simp
  simp only []
  rcases zoneParts zoneText with _ | zone
  · simp
  simp only [true_and, Bool.false_eq_true, false_and, ↓reduceIte]
  by_cases none' : zone = none
  · subst none'
    simp only [↓reduceIte, reduceCtorEq, false_iff, not_and, not_not]
    intro h
    have := settle_zone h
    simpa using this
  · rw [if_neg none']
    constructor
    · intro h
      refine ⟨h, ?_⟩
      rw [settle_zone h]
      cases zone with
      | none => exact absurd rfl none'
      | some z => simp
    · intro h; exact h.1

/-- Every lexical form of `xsd:dateTime` (of `xsd:dateTimeStamp` when
    `stamped`) that `moment_value` returns a value for is one, and the value is
    the canonical kernel moment of its moment; and every lexical form shorter
    than `usize::MAX / 16` gets the value of its moment. -/
theorem moment_value_correct (lexical : alloc.vec.Vec U8) (stamped : Bool) :
    ∃ r, moments.moment_value lexical stamped = .ok r ∧
      (∀ v, r = some v → ∃ x, v = .Moment x ∧ CanonicalMoment x ∧ MomentForm lexical.val (momentOf x) ∧
        (stamped = true → (momentOf x).zone ≠ none)) ∧
      (lexical.val.length < Usize.max / 16 → ∀ m, MomentForm lexical.val m → (stamped = true → m.zone ≠ none) →
        ∃ x, r = some (.Moment x) ∧ momentOf x = m) := by
  rw [moments.moment_value]
  obtain ⟨q, qRun, qValue⟩ := UScalar.div_spec core.num.Usize.MAX (y := 16#usize) (by simp)
  have qIs : q.val = Usize.max / 16 := by rw [qValue]; simp [core.num.Usize.MAX]
  by_cases short : lexical.val.length < Usize.max / 16
  · have shortLt : alloc.vec.Vec.len lexical < q := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, qIs]; exact short
    have small : lexical.val.length + 2 < Usize.max := by
      have : 16 ≤ Usize.max := by scalar_tac
      omega
    set negative := decide (lexical.val.head? = some 45#u8) with hneg
    have negRun : (if 0#usize < alloc.vec.Vec.len lexical then do
          let i3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) lexical 0#usize
          ok (decide (i3 = 45#u8))
        else ok false) = ok negative := by
      by_cases inside : 0 < lexical.val.length
      · have pos : 0#usize < alloc.vec.Vec.len lexical := by
          simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simpa using inside
        have lookup : lexical.index_usize 0#usize = .ok (lexical.val[0]'inside) := by
          simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
        rw [if_pos pos]
        simp only [alloc.vec.Vec.index_slice_index, lookup, bind_ok, hneg]
        congr 1
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem inside]
        simp
      · have notPos : ¬ 0#usize < alloc.vec.Vec.len lexical := by
          simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simpa using inside
        have empty : lexical.val = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [if_neg notPos, hneg]
        exact congrArg ok (decide_eq_false (fun e => by rw [List.head?_eq_none_iff.mpr empty] at e; cases e)).symm
    simp only [qRun, bind_ok, shortLt, ↓reduceIte, negRun]
    have negHead : negative = true ↔ lexical.val.head? = some 45#u8 := by rw [hneg]; simp
    set start : Usize := if negative = true then 1#usize else 0#usize with hstart
    have startRun : (if negative = true then ok 1#usize else ok 0#usize) = (ok start : Result Usize) := by
      rw [hstart]; split <;> rfl
    have startVal : start.val = if negative = true then 1 else 0 := by rw [hstart]; split <;> rfl
    have signTake : lexical.val.take start.val = if negative = true then [45#u8] else [] := by
      rw [startVal]
      by_cases hn : negative = true
      · rw [if_pos hn, if_pos hn]
        have := negHead.mp hn
        cases hl : lexical.val with
        | nil => rw [hl] at this; cases this
        | cons a rest =>
          rw [hl] at this
          have e : a = 45#u8 := Option.some.inj this
          subst e
          rfl
      · rw [if_neg hn, if_neg hn]; rfl
    have startLe : start.val ≤ lexical.val.length := by
      rw [startVal]
      by_cases hn : negative = true
      · rw [if_pos hn]
        have := negHead.mp hn
        cases hl : lexical.val with
        | nil => rw [hl] at this; cases this
        | cons a rest => simp
      · rw [if_neg hn]; omega
    obtain ⟨finish, finishRun, fLow, fHigh, fDigits, fStop⟩ := digits_end_spec lexical start startLe
    obtain ⟨b, bRun, bIff⟩ := year_shaped_spec lexical start finish
    simp only [startRun, bind_ok, finishRun, bRun]
    set y := yearOf lexical.val negative start.val finish.val with hy
    have formFacts : ∀ m, MomentForm lexical.val m → b = true ∧ finish.val + 15 ≤ lexical.val.length ∧
        restRead false y (lexical.val.drop finish.val) = some m := by
      intro m form
      obtain ⟨yt, y', ⟨neg', digits', ytEq, dd, len4, headOk, y'Eq⟩, pre, read⟩ := (momentForm_iff _ _).mp form
      obtain ⟨restHead, restLength⟩ := restRead_shape read
      have textEq : lexical.val = yt ++ lexical.val.drop yt.length := by
        conv => lhs; rw [← List.take_append_drop yt.length lexical.val]
        rw [pre]
      have ytLength : yt.length + 15 ≤ lexical.val.length := by
        have := restLength; simp at this; omega
      have atYt : lexical.val[yt.length]? = some 45#u8 := by
        rw [← restHead, List.head?_drop]
      have signLen : (if neg' = true then [45#u8] else []).length = if neg' = true then 1 else 0 := by
        split <;> rfl
      -- the kernel's sign is the year's sign
      have negSame : negative = neg' := by
        cases neg' with
        | true =>
          apply negHead.mpr
          rw [textEq, ytEq]; rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at ytEq
          rw [Bool.eq_false_iff]
          intro hn
          have h45 := negHead.mp hn
          have nonempty : digits' ≠ [] := by intro e; rw [e] at len4; simp at len4
          obtain ⟨d0, ds, rfl⟩ := List.exists_cons_of_ne_nil nonempty
          rw [textEq, ytEq] at h45
          have e : d0 = 45#u8 := Option.some.inj h45
          have := (dd d0 List.mem_cons_self).1
          rw [e] at this
          simp at this
      have startIs : start.val = if neg' = true then 1 else 0 := by rw [startVal, negSame]
      have ytLen : yt.length = start.val + digits'.length := by
        rw [ytEq, List.length_append, signLen, startIs]
      -- the digits run ends at the year's end
      have finishIs : finish.val = yt.length := by
        have digitAt : ∀ i (hi : i < lexical.val.length), start.val ≤ i → i < yt.length → Digit lexical.val[i] := by
          intro i hi lo hi'
          have : lexical.val[i]? = digits'[i - start.val]? := by
            rw [textEq, List.getElem?_append_left (by omega), ytEq, List.getElem?_append_right (by
              rw [signLen, ← startIs]; omega)]
            rw [signLen, ← startIs]
          rw [List.getElem?_eq_getElem hi] at this
          have inner : i - start.val < digits'.length := by omega
          rw [List.getElem?_eq_getElem inner] at this
          rw [Option.some.inj this]
          exact dd _ (List.getElem_mem _)
        by_contra ne
        rcases Nat.lt_or_gt_of_ne ne with less | more
        · exact fStop (by omega) (digitAt finish.val (by omega) fLow less)
        · have inside : yt.length < lexical.val.length := by omega
          have d := fDigits yt.length inside (by omega) more
          rw [List.getElem?_eq_getElem inside] at atYt
          rw [Option.some.inj atYt] at d
          have := d.1
          simp at this
      have segIs : seg lexical.val start.val finish.val = digits' := by
        rw [seg, finishIs, pre, ytEq, startIs]
        split <;> simp
      refine ⟨bIff.mpr ⟨by omega, by omega, ?_⟩, by omega, ?_⟩
      · rcases Nat.lt_or_eq_of_le len4 with longer | four
        · refine .inr ⟨by omega, ?_⟩
          have nonempty : digits' ≠ [] := by intro e; rw [e] at longer; simp at longer
          rw [show lexical.val[start.val]? = (seg lexical.val start.val finish.val).head? by
            rw [seg, List.head?_drop, List.getElem?_take_of_lt (by omega)], segIs]
          exact headOk longer
        · exact .inl (by omega)
      · rw [hy, yearOf, segIs, negSame, ← y'Eq, finishIs]
        exact read
    by_cases good : b = true ∧ finish.val + 15 ≤ lexical.val.length
    · have read : YearRead lexical.val negative start.val finish.val :=
        ⟨startVal, signTake, ((bIff.mp good.1).1), good.2, fun i hi lo hi' => fDigits i hi lo hi',
          fStop, (bIff.mp good.1).2.2⟩
      obtain ⟨r, run, canonicalR, readR⟩ := moment_after_spec lexical negative start finish stamped read small
      obtain ⟨i4, sub4, i4Value⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := alloc.vec.Vec.len lexical) (y := finish) (by simp; omega))
      have fifteen : 15 ≤ i4.val := by have := i4Value.1; simp at this; omega
      have fifteen' : 15#usize ≤ i4 := by simp only [UScalar.le_equiv]; simpa using fifteen
      refine ⟨r, by simp only [good.1, ↓reduceIte, sub4, bind_ok, fifteen', run], ?_, ?_⟩
      · intro v hv
        obtain ⟨x, rfl, cx⟩ := canonicalR v hv
        have readX : restRead stamped y (lexical.val.drop finish.val) = some (momentOf x) := by
          rw [← readR, hv]; rfl
        have readFalse : restRead false y (lexical.val.drop finish.val) = some (momentOf x) ∧
            (stamped = true → (momentOf x).zone ≠ none) := by
          cases stamped
          · exact ⟨readX, fun h' => (by cases h')⟩
          · obtain ⟨r1, r2⟩ := (restRead_stamped _ _ _).mp readX
            exact ⟨r1, fun _ => r2⟩
        have takeLength : (lexical.val.take finish.val).length = finish.val := by simp; omega
        have yearForm : YearForm (lexical.val.take finish.val) y := by
          refine ⟨negative, seg lexical.val start.val finish.val, ?_, ?_, ?_, ?_, rfl⟩
          · rw [take_seg _ _ _ (by omega), signTake]
          · intro c m
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem m
            have hi' := hi
            rw [seg_length _ _ _ (by omega)] at hi'
            rw [seg_getElem]
            exact fDigits _ _ (by omega) (by omega)
          · rw [seg_length _ _ _ (by omega)]
            rcases (bIff.mp good.1).2.2 with four | ⟨more, _⟩ <;> omega
          · intro longer
            rw [seg_length _ _ _ (by omega)] at longer
            rcases (bIff.mp good.1).2.2 with four | ⟨_, notZero⟩
            · omega
            · rw [seg, List.head?_drop, List.getElem?_take_of_lt (by omega)]
              exact notZero
        refine ⟨x, rfl, cx, (momentForm_iff _ _).mpr ⟨lexical.val.take finish.val, y, yearForm, by rw [takeLength],
          by rw [takeLength]; exact readFalse.1⟩, readFalse.2⟩
      · intro _ m form zoneOk
        obtain ⟨_, _, readM⟩ := formFacts m form
        have readS : restRead stamped y (lexical.val.drop finish.val) = some m := by
          cases stamped
          · exact readM
          · exact (restRead_stamped _ _ _).mpr ⟨readM, zoneOk rfl⟩
        rw [← readR] at readS
        cases r with
        | none => cases readS
        | some v =>
          obtain ⟨x, rfl, mx⟩ := valueMoment_some readS
          exact ⟨x, rfl, mx⟩
    · refine ⟨none, ?_, fun v h' => (by cases h'), fun _ m form _ => ?_⟩
      · by_cases bt : b = true
        · have short15 : ¬ finish.val + 15 ≤ lexical.val.length := fun h' => good ⟨bt, h'⟩
          obtain ⟨i4, sub4, i4Value⟩ := WP.spec_imp_exists
            (Usize.sub_spec (x := alloc.vec.Vec.len lexical) (y := finish) (by simp; omega))
          have notFifteen : ¬ 15 ≤ i4.val := by have := i4Value.1; simp at this; omega
          have notFifteen' : ¬ 15#usize ≤ i4 := by simp only [UScalar.le_equiv]; simpa using notFifteen
          simp only [bt, ↓reduceIte, sub4, bind_ok, notFifteen']
        · simp only [bt, Bool.false_eq_true, ↓reduceIte]
      · obtain ⟨bt, room, _⟩ := formFacts m form
        exact absurd ⟨bt, room⟩ good
  · have notShort : ¬ lexical.val.length < q.val := by rw [qIs]; exact short
    refine ⟨none, by simp [qRun, notShort], fun v h' => (by cases h'), fun h' => absurd h' short⟩

/-- A lexical form writes one moment. -/
theorem momentForm_unique {text : List U8} {m m' : Moment} (h : MomentForm text m) (h' : MomentForm text m') :
    m = m' := by
  obtain ⟨yt, y, ⟨neg, ds, ytEq, dd, len4, _, yEq⟩, pre, read⟩ := (momentForm_iff _ _).mp h
  obtain ⟨yt', y', ⟨neg', ds', ytEq', dd', len4', _, yEq'⟩, pre', read'⟩ := (momentForm_iff _ _).mp h'
  have head := (restRead_shape read).1
  have head' := (restRead_shape read').1
  have signLen : ∀ n : Bool, (if n = true then [45#u8] else []).length = if n = true then 1 else 0 := by
    intro n; split <;> rfl
  -- the year ends at the first byte after its digits, which is `-`
  have boundary : ∀ (a b : List U8) (na nb : Bool) (da db : List U8),
      a = (if na = true then [45#u8] else []) ++ da → b = (if nb = true then [45#u8] else []) ++ db →
      Digits db → 4 ≤ da.length → text.take a.length = a → text.take b.length = b →
      (text.drop a.length).head? = some 45#u8 → ¬ a.length < b.length := by
    intro a b na nb da db aEq bEq ddb la ta tb ha less
    have atA : text[a.length]? = some 45#u8 := by rw [← ha, List.head?_drop]
    have inB : b[a.length]? = some 45#u8 := by
      rw [← tb, List.getElem?_take_of_lt less]; exact atA
    rw [bEq] at inB
    have signB := signLen nb
    have bigger : (if nb = true then [45#u8] else []).length ≤ a.length := by
      have := congrArg List.length aEq; rw [List.length_append] at this
      rw [signB]; split <;> omega
    rw [List.getElem?_append_right bigger] at inB
    obtain ⟨i, hi⟩ : ∃ c, db[a.length - (if nb = true then [45#u8] else []).length]? = some c := ⟨_, inB⟩
    have mem : 45#u8 ∈ db := List.mem_of_getElem? inB
    have := (ddb _ mem).1
    simp at this
  have sameLength : yt.length = yt'.length := by
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with less | more
    · exact boundary yt yt' neg neg' ds ds' ytEq ytEq' dd' len4 pre pre' head less
    · exact boundary yt' yt neg' neg ds' ds ytEq' ytEq dd len4' pre' pre head' more
  have sameText : yt = yt' := by rw [← pre, ← pre', sameLength]
  -- the sign and the digits of one year text
  have signSame : neg = neg' := by
    rw [sameText, ytEq'] at ytEq
    cases neg <;> cases neg'
    · rfl
    · have nonempty : ds ≠ [] := by intro e; rw [e] at len4; simp at len4
      obtain ⟨d0, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append, List.cons.injEq] at ytEq
      have := (dd d0 List.mem_cons_self).1
      rw [← ytEq.1] at this; simp at this
    · have nonempty : ds' ≠ [] := by intro e; rw [e] at len4'; simp at len4'
      obtain ⟨d0, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append, List.cons.injEq] at ytEq
      have := (dd' d0 List.mem_cons_self).1
      rw [ytEq.1] at this; simp at this
    · rfl
  have digitsSame : ds = ds' := by
    rw [sameText, ytEq', signSame] at ytEq
    exact (List.append_cancel_left ytEq).symm
  have yearSame : y = y' := by rw [yEq, yEq', signSame, digitsSame]
  rw [sameLength, yearSame, read'] at read
  exact (Option.some.inj read).symm

/-- The moment of a lexical form is a moment proper. -/
theorem momentForm_valid {text : List U8} {m : Moment} (h : MomentForm text m) : m.Valid := by
  obtain ⟨yearText, mm, dd, hh, mi, ss, fraction, zoneText, year, month, day, hour, minute, second, zone, _,
    _, tmm, m1, m12, tdd, d1, dIn, thh, tmi, tss, fd, zoneCase, valueCase⟩ := h
  have zoneOk : ∀ z, zone = some z → -840 ≤ z ∧ z ≤ 840 := by
    intro z hz
    rcases zoneCase with ⟨_, rfl⟩ | ⟨z', zf, rfl⟩
    · cases hz
    · cases hz
      rcases zf with ⟨_, rfl⟩ | ⟨west, hh', mm', h', mn, _, _, _, fits, rfl⟩
      · omega
      · cases west <;> simp <;> omega
  have fb := fractionValue_bounds fraction fd
  rcases valueCase with ⟨early, clock, sec, rfl⟩ | ⟨rfl, rfl, rfl, zero, rfl⟩
  · refine ⟨m1, m12, d1, dIn, early, clock, by have := fb.1; positivity, ?_, decimal_second _ _, zoneOk⟩
    have : (second : ℚ) ≤ 59 := by exact_mod_cast (by omega : second ≤ 59)
    show (second : ℚ) + fractionValue fraction < 60
    linarith [fb.2]
  · have valid := nextDate_valid (year := year) (day := day) m1 m12
    exact ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2, (by show 0 < 24; omega), (by show 0 < 60; omega),
      le_refl _, (by norm_num), ⟨0, 0, by simp⟩, zoneOk⟩

end Rowl.Moments
