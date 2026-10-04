import Rowl.DatatypeMap
import Rowl.Generated.RowlKernel
import Mathlib.Data.Rat.Floor

/-!
The actual kernel functions of `datatypes`: the kind of a datatype, the value
of a literal and the comparison and classification of values. A value is
returned exactly for a lexical form in the lexical space, it is canonical, and
under every datatype map that is the OWL 2 map on the five datatypes it is the
literal's value; two canonical values are the same value exactly when they
are equal, and a value is in a datatype's value space exactly when the kernel
says so.
-/
namespace Rowl.Datatypes
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (DatatypeMap)
open Rowl.DatatypeMap
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
universe w

/-- The bytes from `start` up to `finish`. -/
def segment (bytes : List U8) (start finish : Nat) : List U8 := (bytes.take finish).drop start

theorem segment_empty (bytes : List U8) (start finish : Nat) (h : finish ≤ start) :
    segment bytes start finish = [] := by
  simp [segment, List.drop_eq_nil_iff]; omega

theorem segment_cons (bytes : List U8) (start finish : Nat) (before : start < finish)
    (fits : finish ≤ bytes.length) :
    segment bytes start finish = bytes[start]'(by omega) :: segment bytes (start + 1) finish := by
  have inside : start < (bytes.take finish).length := by simp; omega
  rw [segment, List.drop_eq_getElem_cons inside]
  simp only [List.getElem_take]
  rfl

theorem segment_length (bytes : List U8) (start finish : Nat) (fits : finish ≤ bytes.length) :
    (segment bytes start finish).length = finish - start := by
  simp [segment]; omega

theorem segment_append (bytes : List U8) (a b c : Nat) (ab : a ≤ b) (bc : b ≤ c) (fits : c ≤ bytes.length) :
    segment bytes a c = segment bytes a b ++ segment bytes b c := by
  have split : bytes.take c = bytes.take b ++ (bytes.take c).drop b := by
    conv => lhs; rw [← List.take_append_drop b (bytes.take c)]
    rw [List.take_take, Nat.min_eq_left bc]
  rw [segment, split, List.drop_append_of_le_length (by simp; omega)]
  rfl

theorem segment_getElem (bytes : List U8) (start finish i : Nat) (h : i < (segment bytes start finish).length) :
    (segment bytes start finish)[i] = bytes[start + i]'(by simp [segment] at h; omega) := by
  simp [segment, List.getElem_drop, List.getElem_take]

theorem segment_whole (bytes : List U8) : segment bytes 0 bytes.length = bytes := by
  simp [segment]

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

theorem new_val : (alloc.vec.Vec.new U8).val = [] := rfl

/-! ### Byte patterns and the kinds of datatypes -/

private theorem equal_total (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    datatypes.equal_from key pattern index = .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [datatypes.equal_from]
  by_cases h : index.val < key.val.length
  · have hr : index.val < pattern.val.length := by omega
    have hkIndex : key.index_usize index = .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hpIndex : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := equal_total key pattern equalLength next
      simp [h, hkIndex, hpIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · simp [h, hkIndex, hpIndex, heads]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have hk : key.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : pattern.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [h, hk, hp]
termination_by key.val.length - index.val
decreasing_by omega

theorem same_pattern_total (key : alloc.vec.Vec U8) (pattern : Slice U8) :
    datatypes.same_pattern key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [datatypes.same_pattern]
  by_cases h : key.val.length = pattern.val.length
  · simpa [h] using equal_total key pattern h 0#usize
  · have unequal : key.val ≠ pattern.val := fun same => h (congrArg List.length same)
    simp [h, unequal]

theorem datatype_eq_iff (a b : Datatype) : a = b ↔ a.iri.spelling.val = b.iri.spelling.val := by
  cases a with | mk ai => cases b with | mk bi => cases ai; cases bi; simp [alloc.vec.Vec.eq_iff]

/-- The datatype of a kind. -/
def typeOf : datatypes.Kind → Datatype
  | .Integer => integerType
  | .Decimal => decimalType
  | .String => stringType
  | .Plain => plainType
  | .Boolean => booleanType

/-- The kind of one of the five datatypes. -/
noncomputable def kindOf (dt : Datatype) : Option datatypes.Kind :=
  open Classical in
  if dt = integerType then some .Integer
  else if dt = decimalType then some .Decimal
  else if dt = stringType then some .String
  else if dt = plainType then some .Plain
  else if dt = booleanType then some .Boolean
  else none

/-- The kernel recognizes exactly the five datatypes by their IRIs. -/
theorem kind_of_correct (dt : Datatype) : datatypes.kind_of dt = .ok (kindOf dt) := by
  rw [datatypes.kind_of, kindOf]
  simp only [datatype_eq_iff dt integerType, datatype_eq_iff dt decimalType, datatype_eq_iff dt stringType,
    datatype_eq_iff dt plainType, datatype_eq_iff dt booleanType]
  by_cases a : dt.iri.spelling.val = integerType.iri.spelling.val <;>
  by_cases b : dt.iri.spelling.val = decimalType.iri.spelling.val <;>
  by_cases c : dt.iri.spelling.val = stringType.iri.spelling.val <;>
  by_cases d : dt.iri.spelling.val = plainType.iri.spelling.val <;>
  by_cases e : dt.iri.spelling.val = booleanType.iri.spelling.val <;>
    simp_all [same_pattern_total, Array.to_slice, Array.make, lift, integerType, decimalType, stringType,
      plainType, booleanType]

theorem kindOf_typeOf (k : datatypes.Kind) : kindOf (typeOf k) = some k := by
  cases k <;> simp [kindOf, typeOf, datatype_eq_iff, integerType, decimalType, stringType, plainType, booleanType]

theorem kindOf_some {dt : Datatype} {k : datatypes.Kind} (h : kindOf dt = some k) : dt = typeOf k := by
  unfold kindOf at h
  split_ifs at h <;> cases h <;> simp_all [typeOf]

/-! ### Scanning bytes -/

theorem is_digit_correct (byte : U8) : datatypes.is_digit byte = .ok (decide (Digit byte)) := by
  rw [datatypes.is_digit]
  by_cases d : Digit byte
  · have := d.1; have := d.2
    simp [UScalar.le_equiv, d, *]
  · simp only [Digit, not_and_or, not_le] at d
    rcases d with d | d <;> simp [UScalar.le_equiv, Digit, d]

theorem digits_from_correct (bytes : alloc.vec.Vec U8) (index finish : Usize)
    (fits : finish.val ≤ bytes.val.length) :
    datatypes.digits_from bytes index finish = .ok (decide (Digits (segment bytes.val index.val finish.val))) := by
  rw [datatypes.digits_from]
  by_cases before : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    rw [segment_cons _ _ _ before fits]
    by_cases digit : Digit bytes.val[index.val]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := digits_from_correct bytes next finish fits
      rw [nextIndex] at rest
      simp [UScalar.lt_equiv, before, inside, alloc.vec.Vec.index_slice_index, lookup, is_digit_correct, digit,
        advance, rest, Digits]
    · simp [UScalar.lt_equiv, before, inside, alloc.vec.Vec.index_slice_index, lookup, is_digit_correct, digit, Digits]
  · simp [UScalar.lt_equiv, before, segment_empty _ _ _ (by omega : finish.val ≤ index.val), Digits]
termination_by finish.val - index.val
decreasing_by omega

/-- Every byte is `0`. -/
def Zeros (bytes : List U8) : Prop := ∀ byte ∈ bytes, byte = 48#u8

theorem skip_zeros_correct (bytes : alloc.vec.Vec U8) (index finish : Usize)
    (order : index.val ≤ finish.val) (fits : finish.val ≤ bytes.val.length) :
    ∃ r, datatypes.skip_zeros bytes index finish = .ok r ∧ index.val ≤ r.val ∧ r.val ≤ finish.val ∧
      Zeros (segment bytes.val index.val r.val) ∧ ∀ h : r.val < finish.val, bytes.val[r.val]'(by omega) ≠ 48#u8 := by
  rw [datatypes.skip_zeros]
  by_cases before : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases zero : bytes.val[index.val] = 48#u8
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, low, high, zeros, stop⟩ := skip_zeros_correct bytes next finish (by omega) fits
      refine ⟨r, ?_, by omega, high, ?_, stop⟩
      · simp [UScalar.lt_equiv, before, inside, alloc.vec.Vec.index_slice_index, lookup, zero, advance, run]
      · rw [segment_cons _ _ _ (by omega) (by omega)]
        intro byte member
        rcases List.mem_cons.mp member with rfl | later
        · exact zero
        · rw [nextIndex] at zeros
          exact zeros byte later
    · refine ⟨index, ?_, le_rfl, by omega, ?_, fun _ => zero⟩
      · simp [UScalar.lt_equiv, before, inside, alloc.vec.Vec.index_slice_index, lookup, zero]
      · simp [segment_empty, Zeros]
  · refine ⟨finish, ?_, order, le_rfl, ?_, fun h => absurd h (lt_irrefl _)⟩
    · simp [UScalar.lt_equiv, before]
    · have same : index.val = finish.val := by omega
      simp [same, segment_empty, Zeros]
termination_by finish.val - index.val
decreasing_by omega

theorem trim_zeros_correct (bytes : alloc.vec.Vec U8) (start finish : Usize)
    (order : start.val ≤ finish.val) (fits : finish.val ≤ bytes.val.length) :
    ∃ r, datatypes.trim_zeros bytes start finish = .ok r ∧ start.val ≤ r.val ∧ r.val ≤ finish.val ∧
      Zeros (segment bytes.val r.val finish.val) ∧
      ∀ h : start.val < r.val ∧ r.val ≤ finish.val, bytes.val[r.val - 1]'(by omega) ≠ 48#u8 := by
  rw [datatypes.trim_zeros]
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
    · obtain ⟨r, run, low, high, zeros, stop⟩ := trim_zeros_correct bytes start last (by omega) (by omega)
      refine ⟨r, ?_, low, by omega, ?_, fun h => stop ⟨h.1, by omega⟩⟩
      · simp [UScalar.lt_equiv, before, fitsLe, back, alloc.vec.Vec.index_slice_index, lookup, zero, run]
      · rw [segment_append bytes.val r.val last.val finish.val high (by omega) fits]
        intro byte member
        rcases List.mem_append.mp member with early | late
        · exact zeros byte early
        · rw [segment_cons _ _ _ (by omega) fits, segment_empty _ _ _ (by omega)] at late
          simp only [List.mem_singleton] at late
          rw [late]
          simpa [lastIndex] using zero
    · refine ⟨finish, ?_, order, le_rfl, by simp [segment_empty, Zeros], fun _ => ?_⟩
      · simp [UScalar.lt_equiv, before, fitsLe, back, alloc.vec.Vec.index_slice_index, lookup, zero]
      · simpa [lastIndex] using zero
  · refine ⟨start, ?_, le_rfl, order, ?_, fun h => absurd h.1 (lt_irrefl _)⟩
    · simp [UScalar.lt_equiv, before]
    · have same : start.val = finish.val := by omega
      simp [same, segment_empty, Zeros]
termination_by finish.val - start.val
decreasing_by omega

theorem copy_range_correct (bytes : alloc.vec.Vec U8) (index finish : Usize) (out : alloc.vec.Vec U8)
    (fits : finish.val ≤ bytes.val.length) (room : out.val.length + (finish.val - index.val) ≤ Usize.max) :
    ∃ v, datatypes.copy_range bytes index finish out = .ok v ∧
      v.val = out.val ++ segment bytes.val index.val finish.val := by
  rw [datatypes.copy_range]
  by_cases before : index.val < finish.val
  · have inside : index.val < bytes.val.length := by omega
    have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out bytes.val[index.val] short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_range_correct bytes next finish pushed fits
      (by rw [contents, nextIndex]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, before, inside, alloc.vec.Vec.index_slice_index, lookup, push, advance, run]
    · rw [value, contents, nextIndex, segment_cons _ _ _ before fits]
      simp
  · refine ⟨out, ?_, ?_⟩
    · simp [UScalar.lt_equiv, before]
    · simp [segment_empty _ _ _ (by omega : finish.val ≤ index.val)]
termination_by finish.val - index.val
decreasing_by omega

theorem find_byte_correct (bytes : alloc.vec.Vec U8) (byte : U8) (index : Usize) :
    ∃ r, datatypes.find_byte bytes byte index = .ok r ∧ r.val ≤ bytes.val.length ∧
      (index.val ≤ bytes.val.length → index.val ≤ r.val) ∧
      (∀ i (h : i < bytes.val.length), index.val ≤ i → i < r.val → bytes.val[i] ≠ byte) ∧
      ∀ h : r.val < bytes.val.length, bytes.val[r.val] = byte := by
  rw [datatypes.find_byte]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases found : bytes.val[index.val] = byte
    · refine ⟨index, ?_, by omega, fun _ => le_rfl, fun i _ low high => absurd high (by omega), fun _ => found⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, found]
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, bound, after, skipped, stop⟩ := find_byte_correct bytes byte next
      refine ⟨r, ?_, bound, fun _ => by have := after (by omega); omega, ?_, stop⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, found, advance, run]
      · intro i h low high
        by_cases same : i = index.val
        · subst same; exact found
        · exact skipped i h (by omega) high
  · refine ⟨alloc.vec.Vec.len bytes, ?_, by simp, fun h => by simp; omega, ?_, fun h => by simp at h⟩
    · simp [UScalar.lt_equiv, inside]
    · intro i h low high
      simp at high; omega
termination_by bytes.val.length - index.val
decreasing_by omega

theorem last_byte_correct (bytes : alloc.vec.Vec U8) (byte : U8) (finish : Usize)
    (fits : finish.val ≤ bytes.val.length) :
    ∃ r, datatypes.last_byte bytes byte finish = .ok r ∧
      ((r.val = bytes.val.length ∧ ∀ i (h : i < bytes.val.length), i < finish.val → bytes.val[i] ≠ byte) ∨
        ∃ h : r.val < finish.val, bytes.val[r.val] = byte ∧
          ∀ i (h : i < bytes.val.length), r.val < i → i < finish.val → bytes.val[i] ≠ byte) := by
  rw [datatypes.last_byte]
  by_cases positive : 0 < finish.val
  · obtain ⟨last, back, lastValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := finish) (y := 1#usize) (by scalar_tac))
    have lastIndex : last.val = finish.val - 1 := by simp at lastValue; omega
    have inside : last.val < bytes.val.length := by omega
    have lookup : bytes.index_usize last = .ok bytes.val[last.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have fitsLe : finish ≤ alloc.vec.Vec.len bytes := by
      simp only [UScalar.le_equiv, alloc.vec.Vec.len_val]; exact fits
    have positive' : (0#usize) < finish := by simp only [UScalar.lt_equiv]; simpa using positive
    by_cases found : bytes.val[last.val] = byte
    · refine ⟨last, ?_, .inr ⟨by omega, found, fun i h low high => by omega⟩⟩
      simp [positive', fitsLe, back, alloc.vec.Vec.index_slice_index, lookup, found]
    · obtain ⟨r, run, cases⟩ := last_byte_correct bytes byte last (by omega)
      refine ⟨r, ?_, ?_⟩
      · simp [positive', fitsLe, back, alloc.vec.Vec.index_slice_index, lookup, found, run]
      · rcases cases with ⟨len, none⟩ | ⟨below, hit, after⟩
        · refine .inl ⟨len, fun i h low => ?_⟩
          by_cases same : i = last.val
          · subst same; exact found
          · exact none i h (by omega)
        · refine .inr ⟨by omega, hit, fun i h low high => ?_⟩
          by_cases same : i = last.val
          · subst same; exact found
          · exact after i h low (by omega)
  · have zero : finish.val = 0 := by omega
    have notPositive : ¬ (0#usize) < finish := by simp only [UScalar.lt_equiv]; simp [zero]
    refine ⟨alloc.vec.Vec.len bytes, by simp [notPositive], .inl ⟨by simp, fun i h low => by omega⟩⟩
termination_by finish.val
decreasing_by omega

/-- The ASCII lower case of a byte, as a number. -/
def lowerValue (byte : U8) : Nat := if 65 ≤ byte.val ∧ byte.val ≤ 90 then byte.val + 32 else byte.val

theorem lower_correct (byte : U8) : ∃ v, datatypes.lower byte = .ok v ∧ v.val = lowerValue byte := by
  rw [datatypes.lower]
  by_cases upper : 65 ≤ byte.val ∧ byte.val ≤ 90
  · have a : (65#u8) ≤ byte := by simp only [UScalar.le_equiv]; simpa using upper.1
    have b : byte ≤ (90#u8) := by simp only [UScalar.le_equiv]; simpa using upper.2
    obtain ⟨sum, add, sumValue⟩ := WP.spec_imp_exists (U8.add_spec (x := byte) (y := 32#u8) (by scalar_tac))
    refine ⟨sum, by simp [a, b, add], by simp [lowerValue, upper, sumValue]⟩
  · refine ⟨byte, ?_, by simp [lowerValue, upper]⟩
    by_cases a : 65 ≤ byte.val
    · have b : ¬ byte.val ≤ 90 := fun b => upper ⟨a, b⟩
      have b' : ¬ byte ≤ (90#u8) := by simp only [UScalar.le_equiv]; simpa using b
      simp [b']
    · have a' : ¬ (65#u8) ≤ byte := by simp only [UScalar.le_equiv]; simpa using a
      simp [a']

theorem lower_from_correct (bytes : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length + (bytes.val.length - index.val) ≤ Usize.max) :
    ∃ v, datatypes.lower_from bytes index out = .ok v ∧
      v.val.map (·.val) = out.val.map (·.val) ++ (bytes.val.drop index.val).map lowerValue := by
  rw [datatypes.lower_from]
  by_cases inside : index.val < bytes.val.length
  · have lookup : bytes.index_usize index = .ok bytes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨lowered, lowerRun, loweredValue⟩ := lower_correct bytes.val[index.val]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out lowered short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := lower_from_correct bytes next pushed (by rw [contents, nextIndex]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, lowerRun, push, advance, run]
    · rw [value, contents, nextIndex, List.drop_eq_getElem_cons inside]
      simp only [List.map_append, List.map_cons, List.map_nil, loweredValue, List.append_assoc, List.singleton_append]
  · refine ⟨out, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside]
    · simp [List.drop_eq_nil_iff.mpr (show bytes.val.length ≤ index.val by omega)]
termination_by bytes.val.length - index.val
decreasing_by omega

theorem xml_text_correct (bytes : alloc.vec.Vec U8) : datatypes.xml_text bytes = .ok (decide (XmlText bytes.val)) := by
  obtain ⟨result, run, _⟩ := Rowl.Unicode.read_text_total_correct bytes
  have valid := Rowl.Unicode.read_text_valid_iff bytes
  rw [datatypes.xml_text, run]
  cases result with
  | Valid scalars =>
    have text : XmlText bytes.val := valid.mp ⟨scalars, run⟩
    simp [text]
  | Invalid error =>
    have text : ¬ XmlText bytes.val := by
      intro accepted
      obtain ⟨scalars, other⟩ := valid.mpr accepted
      cases Result.ok_injective (run.symm.trans other)
    simp [text]

theorem signed_correct (bytes : alloc.vec.Vec U8) :
    datatypes.signed bytes = .ok (decide (bytes.val.head? = some 43#u8 ∨ bytes.val.head? = some 45#u8)) := by
  rw [datatypes.signed]
  cases h : bytes.val with
  | nil =>
    have empty : ¬ (0#usize) < alloc.vec.Vec.len bytes := by simp [UScalar.lt_equiv, h]
    simp [empty]
  | cons head tail =>
    have positive : (0#usize) < alloc.vec.Vec.len bytes := by simp [UScalar.lt_equiv, h]
    have lookup : bytes.index_usize 0#usize = .ok head := by simp [alloc.vec.Vec.index_usize, h]
    by_cases plus : head = 43#u8
    · simp [positive, alloc.vec.Vec.index_slice_index, lookup, plus]
    · by_cases minus : head = 45#u8 <;> simp [positive, alloc.vec.Vec.index_slice_index, lookup, plus, minus]

theorem minus_correct (bytes : alloc.vec.Vec U8) :
    datatypes.minus bytes = .ok (decide (bytes.val.head? = some 45#u8)) := by
  rw [datatypes.minus]
  cases h : bytes.val with
  | nil =>
    have empty : ¬ (0#usize) < alloc.vec.Vec.len bytes := by simp [UScalar.lt_equiv, h]
    simp [empty]
  | cons head tail =>
    have positive : (0#usize) < alloc.vec.Vec.len bytes := by simp [UScalar.lt_equiv, h]
    have lookup : bytes.index_usize 0#usize = .ok head := by simp [alloc.vec.Vec.index_usize, h]
    by_cases minus : head = 45#u8 <;> simp [positive, alloc.vec.Vec.index_slice_index, lookup, minus]

/-! ### Numbers -/

theorem fold_digits (init : Nat) (bytes : List U8) :
    bytes.foldl (fun value byte => 10 * value + (byte.val - 48)) init = init * 10 ^ bytes.length + digitsValue bytes := by
  induction bytes generalizing init with
  | nil => simp [digitsValue]
  | cons head tail ih =>
    simp only [List.foldl_cons, digitsValue, List.length_cons]
    rw [ih, ih (10 * 0 + (head.val - 48))]
    ring

theorem digitsValue_nil : digitsValue [] = 0 := rfl

theorem digitsValue_cons (head : U8) (tail : List U8) :
    digitsValue (head :: tail) = (head.val - 48) * 10 ^ tail.length + digitsValue tail := by
  rw [digitsValue, List.foldl_cons, fold_digits]
  ring

theorem digitsValue_append (a b : List U8) : digitsValue (a ++ b) = digitsValue a * 10 ^ b.length + digitsValue b := by
  rw [digitsValue, List.foldl_append, fold_digits]
  rfl

theorem digitsValue_zeros (zeros : List U8) (all : Zeros zeros) : digitsValue zeros = 0 := by
  induction zeros with
  | nil => rfl
  | cons head tail ih =>
    rw [digitsValue_cons, all head List.mem_cons_self, ih (fun b m => all b (List.mem_cons_of_mem _ m))]
    simp

theorem digitsValue_lt (bytes : List U8) (digits : Digits bytes) : digitsValue bytes < 10 ^ bytes.length := by
  induction bytes with
  | nil => simp [digitsValue]
  | cons head tail ih =>
    rw [digitsValue_cons]
    have d := digits head List.mem_cons_self
    have rest := ih (fun b m => digits b (List.mem_cons_of_mem _ m))
    have small : head.val - 48 ≤ 9 := by have := d.2; omega
    simp only [List.length_cons, pow_succ]
    nlinarith

/-- The number a canonical numeric value writes: its sign, its integer part and
    its fraction. -/
def numberOf (negative : Bool) (whole fraction : List U8) : ℚ :=
  (if negative then -1 else 1) * ((digitsValue whole : ℚ) + (digitsValue fraction : ℚ) / 10 ^ fraction.length)

/-- The digits of a number's integer part without leading zeros and of its
    fraction without trailing zeros, with no sign on zero. -/
def CanonicalNumber (negative : Bool) (whole fraction : List U8) : Prop :=
  Digits whole ∧ Digits fraction ∧ whole.head? ≠ some 48#u8 ∧ fraction.getLast? ≠ some 48#u8 ∧
    (negative = true → whole ≠ [] ∨ fraction ≠ [])

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
      rw [digitsValue_cons, digitsValue_cons, length] at value
      have restDigits : Digits rest := fun c m => da c (List.mem_cons_of_mem _ m)
      have restDigits' : Digits rest' := fun c m => db c (List.mem_cons_of_mem _ m)
      have small := digitsValue_lt rest restDigits
      have small' := digitsValue_lt rest' restDigits'
      rw [length] at small
      have pos : 0 < 10 ^ rest'.length := by positivity
      have heads : x.val - 48 = y.val - 48 := by
        have h1 := Nat.add_mul_div_right (digitsValue rest) (x.val - 48) pos
        have h2 := Nat.add_mul_div_right (digitsValue rest') (y.val - 48) pos
        rw [Nat.div_eq_of_lt small] at h1
        rw [Nat.div_eq_of_lt small'] at h2
        have : digitsValue rest + (x.val - 48) * 10 ^ rest'.length = digitsValue rest' + (y.val - 48) * 10 ^ rest'.length := by
          omega
        rw [this] at h1
        omega
      have tails : digitsValue rest = digitsValue rest' := by rw [heads] at value; omega
      rw [digit_eq x y (da x List.mem_cons_self) (db y List.mem_cons_self) heads, ih rest' restDigits restDigits' length tails]

theorem whole_positive (whole : List U8) (digits : Digits whole) (lead : whole.head? ≠ some 48#u8)
    (nonempty : whole ≠ []) : 10 ^ (whole.length - 1) ≤ digitsValue whole := by
  cases whole with
  | nil => exact absurd rfl nonempty
  | cons head tail =>
    rw [digitsValue_cons]
    have d := digits head List.mem_cons_self
    have notZero : head.val ≠ 48 := fun h => lead (by simp; exact UScalar.eq_of_val_eq (by simpa using h))
    have : 1 ≤ head.val - 48 := by have := d.1; omega
    simp only [List.length_cons, Nat.add_sub_cancel]
    calc 10 ^ tail.length ≤ (head.val - 48) * 10 ^ tail.length := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ _ := Nat.le_add_right _ _

theorem whole_unique (a b : List U8) (da : Digits a) (db : Digits b) (la : a.head? ≠ some 48#u8)
    (lb : b.head? ≠ some 48#u8) (value : digitsValue a = digitsValue b) : a = b := by
  by_cases ea : a = []
  · by_cases eb : b = []
    · rw [ea, eb]
    · have := whole_positive b db lb eb
      rw [ea, digitsValue_nil] at value
      have : 0 < 10 ^ (b.length - 1) := by positivity
      omega
  · by_cases eb : b = []
    · have := whole_positive a da la ea
      rw [eb, digitsValue_nil] at value
      have : 0 < 10 ^ (a.length - 1) := by positivity
      omega
    · apply same_length_unique a b da db _ value
      have lowA := whole_positive a da la ea
      have lowB := whole_positive b db lb eb
      have highA := digitsValue_lt a da
      have highB := digitsValue_lt b db
      have la1 : 1 ≤ a.length := List.length_pos_iff.mpr ea
      have lb1 : 1 ≤ b.length := List.length_pos_iff.mpr eb
      by_contra different
      rcases Nat.lt_or_gt_of_ne different with less | more
      · have : 10 ^ a.length ≤ 10 ^ (b.length - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : 10 ^ b.length ≤ 10 ^ (a.length - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega

theorem fraction_last (fraction : List U8) (digits : Digits fraction) (last : fraction.getLast? ≠ some 48#u8)
    (nonempty : fraction ≠ []) : digitsValue fraction % 10 ≠ 0 := by
  obtain ⟨init, x, rfl⟩ : ∃ init x, fraction = init ++ [x] :=
    ⟨fraction.dropLast, fraction.getLast nonempty, (List.dropLast_append_getLast nonempty).symm⟩
  rw [digitsValue_append, digitsValue_cons, digitsValue_nil]
  have d := digits x (by simp)
  have notZero : x.val ≠ 48 := fun h => last (by simp; exact UScalar.eq_of_val_eq (by simpa using h))
  simp only [List.length_cons, List.length_nil, pow_one, pow_zero, mul_one, add_zero]
  have : 1 ≤ x.val - 48 ∧ x.val - 48 ≤ 9 := by have := d.1; have := d.2; omega
  omega

theorem fraction_unique (a b : List U8) (da : Digits a) (db : Digits b) (la : a.getLast? ≠ some 48#u8)
    (lb : b.getLast? ≠ some 48#u8) (cross : digitsValue a * 10 ^ b.length = digitsValue b * 10 ^ a.length) :
    a = b := by
  by_cases ea : a = []
  · subst ea
    by_cases eb : b = []
    · rw [eb]
    · have := fraction_last b db lb eb
      simp [digitsValue_nil] at cross
      omega
  · by_cases eb : b = []
    · subst eb
      have := fraction_last a da la ea
      simp [digitsValue_nil] at cross
      omega
    · have ra := fraction_last a da la ea
      have rb := fraction_last b db lb eb
      have lengths : a.length = b.length := by
        by_contra different
        rcases Nat.lt_or_gt_of_ne different with less | more
        · have split : 10 ^ b.length = 10 ^ (b.length - a.length) * 10 ^ a.length := by
            rw [← pow_add]; congr 1; omega
          have pos : 0 < 10 ^ a.length := by positivity
          have eq : digitsValue a * 10 ^ (b.length - a.length) = digitsValue b := by
            apply Nat.eq_of_mul_eq_mul_right pos
            calc digitsValue a * 10 ^ (b.length - a.length) * 10 ^ a.length
                = digitsValue a * 10 ^ b.length := by rw [split]; ring
              _ = digitsValue b * 10 ^ a.length := cross
          have ten : 10 ∣ digitsValue b := by
            rw [← eq]
            exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) _
          omega
        · have split : 10 ^ a.length = 10 ^ (a.length - b.length) * 10 ^ b.length := by
            rw [← pow_add]; congr 1; omega
          have pos : 0 < 10 ^ b.length := by positivity
          have eq : digitsValue b * 10 ^ (a.length - b.length) = digitsValue a := by
            apply Nat.eq_of_mul_eq_mul_right pos
            calc digitsValue b * 10 ^ (a.length - b.length) * 10 ^ b.length
                = digitsValue b * 10 ^ a.length := by rw [split]; ring
              _ = digitsValue a * 10 ^ b.length := cross.symm
          have ten : 10 ∣ digitsValue a := by
            rw [← eq]
            exact Dvd.dvd.mul_left (dvd_pow_self 10 (by omega)) _
          omega
      apply same_length_unique a b da db lengths
      rw [lengths] at cross
      exact Nat.eq_of_mul_eq_mul_right (by positivity) cross

/-- The fractional part of a canonical number. -/
theorem fraction_bounds (fraction : List U8) (digits : Digits fraction) :
    0 ≤ (digitsValue fraction : ℚ) / 10 ^ fraction.length ∧ (digitsValue fraction : ℚ) / 10 ^ fraction.length < 1 := by
  have small := digitsValue_lt fraction digits
  have pos : (0 : ℚ) < 10 ^ fraction.length := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one pos]
  exact_mod_cast small

theorem numberOf_zero {negative : Bool} {whole fraction : List U8} (canonical : CanonicalNumber negative whole fraction) :
    numberOf negative whole fraction = 0 ↔ negative = false ∧ whole = [] ∧ fraction = [] := by
  obtain ⟨dw, df, lw, lf, sign⟩ := canonical
  have bounds := fraction_bounds fraction df
  constructor
  · intro zero
    have magnitude : (digitsValue whole : ℚ) + (digitsValue fraction : ℚ) / 10 ^ fraction.length = 0 := by
      unfold numberOf at zero
      split at zero <;> linarith
    have w0 : (digitsValue whole : ℚ) = 0 := by
      have : (0 : ℚ) ≤ digitsValue whole := by positivity
      linarith [bounds.1]
    have f0 : (digitsValue fraction : ℚ) / 10 ^ fraction.length = 0 := by linarith
    have wz : digitsValue whole = 0 := by exact_mod_cast w0
    have fz : digitsValue fraction = 0 := by
      have pos : (10 : ℚ) ^ fraction.length ≠ 0 := by positivity
      rw [div_eq_zero_iff] at f0
      rcases f0 with h | h
      · exact_mod_cast h
      · exact absurd h pos
    have we : whole = [] := by
      by_contra nonempty
      have := whole_positive whole dw lw nonempty
      have : 0 < 10 ^ (whole.length - 1) := by positivity
      omega
    have fe : fraction = [] := by
      by_contra nonempty
      have := fraction_last fraction df lf nonempty
      omega
    refine ⟨?_, we, fe⟩
    cases negative with
    | false => rfl
    | true => rcases sign rfl with h | h <;> contradiction
  · rintro ⟨rfl, rfl, rfl⟩
    simp [numberOf, digitsValue_nil]

theorem numberOf_injective {n1 n2 : Bool} {w1 w2 f1 f2 : List U8}
    (c1 : CanonicalNumber n1 w1 f1) (c2 : CanonicalNumber n2 w2 f2)
    (same : numberOf n1 w1 f1 = numberOf n2 w2 f2) : n1 = n2 ∧ w1 = w2 ∧ f1 = f2 := by
  by_cases zero : numberOf n1 w1 f1 = 0
  · have z1 := (numberOf_zero c1).mp zero
    have z2 := (numberOf_zero c2).mp (same ▸ zero)
    exact ⟨z1.1.trans z2.1.symm, z1.2.1.trans z2.2.1.symm, z1.2.2.trans z2.2.2.symm⟩
  · obtain ⟨dw1, df1, lw1, lf1, _⟩ := c1
    obtain ⟨dw2, df2, lw2, lf2, _⟩ := c2
    have b1 := fraction_bounds f1 df1
    have b2 := fraction_bounds f2 df2
    have q1 : (0 : ℚ) ≤ digitsValue w1 := by positivity
    have q2 : (0 : ℚ) ≤ digitsValue w2 := by positivity
    unfold numberOf at same zero
    have signs : n1 = n2 := by
      cases n1 <;> cases n2
      · rfl
      · exfalso; apply zero; simp at same ⊢; linarith [b1.1, b2.1]
      · exfalso; apply zero; simp at same ⊢; linarith [b1.1, b2.1]
      · rfl
    subst signs
    have magnitudes : (digitsValue w1 : ℚ) + (digitsValue f1 : ℚ) / 10 ^ f1.length =
        (digitsValue w2 : ℚ) + (digitsValue f2 : ℚ) / 10 ^ f2.length := by
      cases n1 <;> simp at same <;> linarith
    have wholes : digitsValue w1 = digitsValue w2 := by
      by_contra different
      rcases Nat.lt_or_gt_of_ne different with less | more
      · have : (digitsValue w1 : ℚ) + 1 ≤ digitsValue w2 := by exact_mod_cast less
        linarith [b1.2, b2.1]
      · have : (digitsValue w2 : ℚ) + 1 ≤ digitsValue w1 := by exact_mod_cast more
        linarith [b2.2, b1.1]
    have fractions : (digitsValue f1 : ℚ) / 10 ^ f1.length = (digitsValue f2 : ℚ) / 10 ^ f2.length := by
      have : (digitsValue w1 : ℚ) = digitsValue w2 := by exact_mod_cast wholes
      linarith
    have cross : digitsValue f1 * 10 ^ f2.length = digitsValue f2 * 10 ^ f1.length := by
      have r1 : (10 : ℚ) ^ f1.length ≠ 0 := by positivity
      have r2 : (10 : ℚ) ^ f2.length ≠ 0 := by positivity
      rw [div_eq_div_iff r1 r2] at fractions
      exact_mod_cast fractions
    exact ⟨rfl, whole_unique w1 w2 dw1 dw2 lw1 lw2 wholes, fraction_unique f1 f2 df1 df2 lf1 lf2 cross⟩

theorem numberOf_decimal (negative : Bool) (whole fraction : List U8) : IsDecimal (numberOf negative whole fraction) := by
  refine ⟨(if negative then -1 else 1) * ((digitsValue whole * 10 ^ fraction.length + digitsValue fraction : ℕ) : ℤ),
    fraction.length, ?_⟩
  have pos : (10 : ℚ) ^ fraction.length ≠ 0 := by positivity
  unfold numberOf
  split <;> push_cast <;> field_simp

theorem numberOf_integer {negative : Bool} {whole fraction : List U8} (canonical : CanonicalNumber negative whole fraction) :
    IsInteger (numberOf negative whole fraction) ↔ fraction = [] := by
  obtain ⟨dw, df, lw, lf, _⟩ := canonical
  constructor
  · intro ⟨z, hz⟩
    by_contra nonempty
    have last := fraction_last fraction df lf nonempty
    have positive : 0 < digitsValue fraction := by
      rcases Nat.eq_zero_or_pos (digitsValue fraction) with h | h
      · rw [h] at last; simp at last
      · exact h
    have b := fraction_bounds fraction df
    have strict : (0 : ℚ) < (digitsValue fraction : ℚ) / 10 ^ fraction.length := by
      have : (0 : ℚ) < digitsValue fraction := by exact_mod_cast positive
      positivity
    set x := (digitsValue fraction : ℚ) / 10 ^ fraction.length
    set W := digitsValue whole
    unfold numberOf at hz
    rw [← show x = (digitsValue fraction : ℚ) / 10 ^ fraction.length from rfl] at hz
    have between : ∀ y : ℤ, (y : ℚ) = (W : ℚ) + x → False := by
      intro y hy
      have lower : (W : ℤ) < y := by
        have : (W : ℚ) < y := by linarith
        exact_mod_cast this
      have upper : y < (W : ℤ) + 1 := by
        have : (y : ℚ) < W + 1 := by linarith [b.2]
        exact_mod_cast this
      omega
    cases negative with
    | false => exact between z (by simp at hz; linarith)
    | true => exact between (-z) (by simp at hz; push_cast; linarith)
  · rintro rfl
    refine ⟨(if negative then -1 else 1) * (digitsValue whole : ℤ), ?_⟩
    unfold numberOf
    split <;> simp [digitsValue_nil]

/-! ### Lexical forms of numbers -/

theorem segment_take (bytes : List U8) (finish : Nat) : segment bytes 0 finish = bytes.take finish := by
  simp [segment]

theorem segment_drop (bytes : List U8) (start : Nat) : segment bytes start bytes.length = bytes.drop start := by
  simp [segment]

theorem digits_append {a b : List U8} : Digits (a ++ b) ↔ Digits a ∧ Digits b := by
  simp [Digits, or_imp, forall_and]

theorem number_from_correct (lexical : alloc.vec.Vec U8) (negative : Bool) (start dot after : Usize)
    (sd : start.val ≤ dot.val) (dl : dot.val ≤ lexical.val.length) (al : after.val ≤ lexical.val.length)
    (dw : Digits (segment lexical.val start.val dot.val))
    (df : Digits (segment lexical.val after.val lexical.val.length)) :
    ∃ n w f, datatypes.number_from lexical negative start dot after = .ok (.Number n w f) ∧
      CanonicalNumber n w.val f.val ∧
      numberOf n w.val f.val = (if negative then -1 else 1) *
        ((digitsValue (segment lexical.val start.val dot.val) : ℚ) +
          (digitsValue (segment lexical.val after.val lexical.val.length) : ℚ) /
            10 ^ (segment lexical.val after.val lexical.val.length).length) := by
  have size := lexical.property
  obtain ⟨first, firstRun, f1, f2, leading, firstStop⟩ := skip_zeros_correct lexical start dot sd dl
  obtain ⟨last, lastRun, l1, l2, trailing, lastStop⟩ :=
    trim_zeros_correct lexical after (alloc.vec.Vec.len lexical) (by simpa using al) (by simp)
  simp only [alloc.vec.Vec.len_val] at l2 trailing lastStop
  replace l2 : last.val ≤ lexical.val.length := by simpa using l2
  replace trailing : Zeros (segment lexical.val last.val lexical.val.length) := by simpa using trailing
  replace lastStop : ∀ h : after.val < last.val ∧ last.val ≤ lexical.val.length,
      lexical.val[last.val - 1]'(by omega) ≠ 48#u8 := fun h => lastStop ⟨h.1, by simpa using h.2⟩
  obtain ⟨integer, integerRun, integerValue⟩ :=
    copy_range_correct lexical first dot (alloc.vec.Vec.new U8) dl (by simp; scalar_tac)
  obtain ⟨fraction, fractionRun, fractionValue⟩ :=
    copy_range_correct lexical after last (alloc.vec.Vec.new U8) (by omega) (by simp; scalar_tac)
  simp only [new_val, List.nil_append] at integerValue fractionValue
  have wholeSplit := segment_append lexical.val start.val first.val dot.val f1 f2 dl
  have fractionSplit := segment_append lexical.val after.val last.val lexical.val.length l1 l2 (le_refl _)
  rw [wholeSplit] at dw
  rw [fractionSplit] at df
  have wholeDigits : Digits (segment lexical.val first.val dot.val) := (digits_append.mp dw).2
  have fractionDigits : Digits (segment lexical.val after.val last.val) := (digits_append.mp df).1
  have lead : (segment lexical.val first.val dot.val).head? ≠ some 48#u8 := by
    by_cases inside : first.val < dot.val
    · rw [segment_cons _ _ _ inside dl]
      simpa using firstStop inside
    · simp [segment_empty _ _ _ (by omega : dot.val ≤ first.val)]
  have tail : (segment lexical.val after.val last.val).getLast? ≠ some 48#u8 := by
    by_cases inside : after.val < last.val
    · have nonempty : segment lexical.val after.val last.val ≠ [] := by
        intro h; have := segment_length lexical.val after.val last.val (by omega); rw [h] at this; simp at this; omega
      rw [List.getLast?_eq_some_getLast nonempty]
      intro same
      simp only [Option.some.injEq] at same
      have position := List.getLast_eq_getElem nonempty
      rw [segment_getElem] at position
      have index : after.val + ((segment lexical.val after.val last.val).length - 1) = last.val - 1 := by
        rw [segment_length _ _ _ (by omega)]; omega
      simp only [index] at position
      exact lastStop ⟨inside, l2⟩ (position ▸ same)
    · simp [segment_empty _ _ _ (by omega : last.val ≤ after.val)]
  set zero := decide (integer.val.length = 0) && decide (fraction.val.length = 0) with zeroIs
  have run : datatypes.number_from lexical negative start dot after =
      .ok (.Number (negative && !zero) integer fraction) := by
    rw [datatypes.number_from]
    simp only [firstRun, alloc.vec.Vec.len_val, lastRun, integerRun, fractionRun, bind_ok]
    cases negative <;> by_cases i0 : integer.val.length = 0 <;> by_cases f0 : fraction.val.length = 0 <;>
      simp [i0, f0, zeroIs, UScalar.eq_equiv]
  refine ⟨negative && !zero, integer, fraction, run, ?_, ?_⟩
  · refine ⟨integerValue ▸ wholeDigits, fractionValue ▸ fractionDigits, integerValue ▸ lead, fractionValue ▸ tail, ?_⟩
    intro sign
    simp only [Bool.and_eq_true, Bool.not_eq_true', zeroIs, Bool.and_eq_false_iff, decide_eq_false_iff_not] at sign
    rcases sign.2 with h | h
    · exact .inl (fun e => h (by rw [e]; rfl))
    · exact .inr (fun e => h (by rw [e]; rfl))
  · rw [integerValue, fractionValue, wholeSplit, fractionSplit, digitsValue_append, digitsValue_zeros _ leading,
      zero_mul, zero_add, digitsValue_append, digitsValue_zeros _ trailing, add_zero, List.length_append]
    have lastZeros : (segment lexical.val last.val lexical.val.length).length = lexical.val.length - last.val :=
      segment_length _ _ _ (le_refl _)
    rw [lastZeros]
    have scale : ((digitsValue (segment lexical.val after.val last.val) * 10 ^ (lexical.val.length - last.val) : ℕ) : ℚ) /
        10 ^ ((segment lexical.val after.val last.val).length + (lexical.val.length - last.val)) =
        (digitsValue (segment lexical.val after.val last.val) : ℚ) / 10 ^ (segment lexical.val after.val last.val).length := by
      push_cast
      rw [pow_add]
      have : (10 : ℚ) ^ (lexical.val.length - last.val) ≠ 0 := by positivity
      field_simp
    rw [scale]
    unfold numberOf
    by_cases isZero : zero = true
    · have i0 : integer.val = [] := by
        simp [zeroIs] at isZero; exact isZero.1
      have f0 : fraction.val = [] := by
        simp [zeroIs] at isZero; exact isZero.2
      rw [← integerValue, ← fractionValue, i0, f0, isZero]
      simp [digitsValue_nil]
    · have notZero : zero = false := by simpa using isZero
      rw [notZero, ← integerValue, ← fractionValue]
      cases negative <;> simp

/-- `text` is a lexical form of the integers, when `whole`, or of the
    decimals, for the number `q`. -/
def NumberForm (whole : Bool) (text : List U8) (q : ℚ) : Prop :=
  if whole then IntegerForm text q else DecimalForm text q

/-- Whether the bytes start with a sign. -/
def SignedText (text : List U8) : Prop := text.head? = some 43#u8 ∨ text.head? = some 45#u8

theorem sign_take (text : List U8) :
    Sign (text.take (if SignedText text then 1 else 0)) ∧
      signValue (text.take (if SignedText text then 1 else 0)) = if text.head? = some 45#u8 then -1 else 1 := by
  cases text with
  | nil => simp [Sign, signValue]
  | cons head tail =>
    by_cases plus : head = 43#u8
    · subst plus; simp [SignedText, Sign, signValue]
    · by_cases minus : head = 45#u8
      · subst minus; simp [SignedText, Sign, signValue]
      · simp [SignedText, plus, minus, Sign, signValue]

private theorem not_dot_of_digit {byte : U8} (d : Digit byte) : byte ≠ 46#u8 := by
  intro h; subst h; simp [Digit] at d

private theorem not_sign_of_digit {byte : U8} (d : Digit byte) : byte ≠ 43#u8 ∧ byte ≠ 45#u8 := by
  constructor <;> (intro h; subst h; simp [Digit] at d)

/-- The shape of a numeric lexical form: a sign, digits and, for a decimal, a
    point followed by digits. -/
theorem number_form_shape (whole : Bool) (text : List U8) (q : ℚ) :
    NumberForm whole text q ↔ ∃ sign w f, Sign sign ∧ Digits w ∧ Digits f ∧
      ((text = sign ++ w ∧ w ≠ [] ∧ f = []) ∨
        (whole = false ∧ text = sign ++ w ++ 46#u8 :: f ∧ (w ≠ [] ∨ f ≠ []))) ∧
      q = signValue sign * ((digitsValue w : ℚ) + (digitsValue f : ℚ) / 10 ^ f.length) := by
  cases whole with
  | true =>
    simp only [NumberForm, ↓reduceIte, IntegerForm]
    constructor
    · rintro ⟨sign, w, hs, hw, ne, rfl, rfl⟩
      exact ⟨sign, w, [], hs, hw, by simp [Digits], .inl ⟨by simp, ne, by simp⟩, by simp [digitsValue_nil]⟩
    · rintro ⟨sign, w, f, hs, hw, hf, shape, rfl⟩
      rcases shape with ⟨rfl, ne, rfl⟩ | ⟨no, _⟩
      · exact ⟨sign, w, hs, hw, ne, rfl, by simp [digitsValue_nil]⟩
      · cases no
  | false =>
    simp only [NumberForm, Bool.false_eq_true, ↓reduceIte, DecimalForm]
    constructor
    · rintro ⟨sign, w, f, hs, hw, hf, shape, rfl⟩
      refine ⟨sign, w, f, hs, hw, hf, ?_, rfl⟩
      rcases shape with h | h
      · exact .inl h
      · exact .inr ⟨by simp, h⟩
    · rintro ⟨sign, w, f, hs, hw, hf, shape, rfl⟩
      refine ⟨sign, w, f, hs, hw, hf, ?_, rfl⟩
      rcases shape with h | ⟨_, h⟩
      · exact .inl h
      · exact .inr h

private theorem segment_after_prefix (a b : List U8) : segment (a ++ b) a.length (a ++ b).length = b := by
  rw [segment_drop]; simp

private theorem segment_middle (a b c : List U8) : segment (a ++ b ++ c) a.length (a.length + b.length) = b := by
  simp [segment, List.take_append, List.drop_append]

/-- The sign is the bytes before `start` when the rest starts with a digit or a point. -/
private theorem start_of_shape (sign rest : List U8) (hs : Sign sign) (ne : rest ≠ [])
    (head : ∀ b, rest.head? = some b → b ≠ 43#u8 ∧ b ≠ 45#u8) :
    (if SignedText (sign ++ rest) then 1 else 0) = sign.length := by
  rcases hs with rfl | rfl | rfl
  · cases rest with
    | nil => exact absurd rfl ne
    | cons b tail =>
      have := head b rfl
      simp [SignedText, this.1, this.2]
  · simp [SignedText]
  · simp [SignedText]

/-- What `number_value` reads of a lexical form: the sign before `start`, the
    first point at or after it at `dot` (the length when there is none), and
    the digits around it. -/
theorem number_form_iff (text : List U8) (whole : Bool) (q : ℚ) (dot : Nat)
    (low : (if SignedText text then 1 else 0) ≤ dot) (high : dot ≤ text.length)
    (before : ∀ i (h : i < text.length), (if SignedText text then 1 else 0) ≤ i → i < dot → text[i] ≠ 46#u8)
    (at_dot : ∀ h : dot < text.length, text[dot] = 46#u8) :
    NumberForm whole text q ↔
      (¬ (whole = true ∧ dot < text.length) ∧
        Digits (segment text (if SignedText text then 1 else 0) dot) ∧
        Digits (segment text (if dot < text.length then dot + 1 else text.length) text.length) ∧
        ¬ (dot = (if SignedText text then 1 else 0) ∧
          (if dot < text.length then dot + 1 else text.length) = text.length) ∧
        q = (if text.head? = some 45#u8 then -1 else 1) *
          ((digitsValue (segment text (if SignedText text then 1 else 0) dot) : ℚ) +
            (digitsValue (segment text (if dot < text.length then dot + 1 else text.length) text.length) : ℚ) /
              10 ^ (segment text (if dot < text.length then dot + 1 else text.length) text.length).length)) := by
  have signs := sign_take text
  generalize hstart : (if SignedText text then 1 else 0) = start at low before signs ⊢
  rw [number_form_shape]
  constructor
  · rintro ⟨sign, w, f, hs, hw, hf, shape, rfl⟩
    rcases shape with ⟨rfl, ne, rfl⟩ | ⟨isDecimal, rfl, ne⟩
    · -- no point
      have startIs : start = sign.length := by
        rw [← hstart]
        apply start_of_shape sign w hs ne
        intro b hb
        cases w with
        | nil => exact absurd rfl ne
        | cons x tail =>
          simp at hb; subst hb
          exact not_sign_of_digit (hw x List.mem_cons_self)
      have dotIs : dot = (sign ++ w).length := by
        by_contra different
        have inside : dot < (sign ++ w).length := by omega
        have atDot := at_dot inside
        have digit : Digit (sign ++ w)[dot] := by
          rw [List.getElem_append_right (by omega)]
          exact hw _ (List.getElem_mem _)
        exact not_dot_of_digit digit atDot
      have takeIs : (sign ++ w).take start = sign := by rw [startIs]; simp
      rw [takeIs] at signs
      subst dotIs
      simp only [lt_irrefl, ↓reduceIte, and_false, not_false_eq_true, true_and]
      rw [startIs, segment_after_prefix, segment_empty _ _ _ (le_refl _)]
      refine ⟨hw, by simp [Digits], ?_, ?_⟩
      · intro h; apply ne; have := h.1; simp at this
        exact this
      · rw [← signs.2]
    · -- a point
      have startIs : start = sign.length := by
        rw [← hstart]
        rw [List.append_assoc]
        apply start_of_shape sign (w ++ 46#u8 :: f) hs (by simp)
        intro b hb
        cases w with
        | nil => simp at hb; subst hb; decide
        | cons x tail =>
          simp at hb; subst hb
          exact not_sign_of_digit (hw x List.mem_cons_self)
      have length : (sign ++ w ++ 46#u8 :: f).length = sign.length + w.length + 1 + f.length := by simp; omega
      have pointAt : (sign ++ w ++ 46#u8 :: f)[sign.length + w.length]'(by rw [length]; omega) = 46#u8 := by
        rw [List.getElem_append_right (by simp)]
        simp
      have dotIs : dot = sign.length + w.length := by
        by_contra different
        rcases Nat.lt_or_gt_of_ne different with less | more
        · have inside : dot < (sign ++ w ++ 46#u8 :: f).length := by rw [length]; omega
          have atDot := at_dot inside
          have digit : Digit (sign ++ w ++ 46#u8 :: f)[dot] := by
            rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
            exact hw _ (List.getElem_mem _)
          exact not_dot_of_digit digit atDot
        · exact before (sign.length + w.length) (by rw [length]; omega) (by omega) more pointAt
      have takeIs : (sign ++ w ++ 46#u8 :: f).take start = sign := by rw [startIs, List.append_assoc]; simp
      rw [takeIs] at signs
      subst dotIs
      have inside : sign.length + w.length < (sign ++ w ++ 46#u8 :: f).length := by rw [length]; omega
      simp only [inside, ↓reduceIte, isDecimal, Bool.false_eq_true, false_and, not_false_eq_true, true_and]
      have wholePart : segment (sign ++ w ++ 46#u8 :: f) start (sign.length + w.length) = w := by
        rw [startIs]; exact segment_middle sign w (46#u8 :: f)
      have fractionPart : segment (sign ++ w ++ 46#u8 :: f) (sign.length + w.length + 1)
          (sign ++ w ++ 46#u8 :: f).length = f := by
        have : sign ++ w ++ 46#u8 :: f = (sign ++ w ++ [46#u8]) ++ f := by simp
        rw [this]
        have prefixLength : (sign ++ w ++ [46#u8]).length = sign.length + w.length + 1 := by simp; omega
        rw [← prefixLength, segment_after_prefix]
      rw [wholePart, fractionPart]
      refine ⟨hw, hf, ?_, ?_⟩
      · rintro ⟨h1, h2⟩
        rcases ne with ne | ne
        · exact ne (List.eq_nil_of_length_eq_zero (by omega))
        · rw [length] at h2; exact ne (List.eq_nil_of_length_eq_zero (by omega))
      · rw [← signs.2]
  · rintro ⟨notWhole, hw, hf, ne, rfl⟩
    have takeSplit : text = text.take start ++ segment text start text.length := by
      rw [segment_drop, List.take_append_drop]
    refine ⟨text.take start, segment text start dot,
      segment text (if dot < text.length then dot + 1 else text.length) text.length,
      signs.1, hw, hf, ?_, by rw [signs.2]⟩
    by_cases point : dot < text.length
    · have isDecimal : whole = false := by
        cases whole with
        | false => rfl
        | true => exact absurd ⟨rfl, point⟩ notWhole
      simp only [point, ↓reduceIte] at hf ne ⊢
      refine .inr ⟨isDecimal, ?_, ?_⟩
      · conv => lhs; rw [takeSplit]
        rw [segment_append text start dot text.length low (by omega) (le_refl _),
          segment_cons text dot text.length point (le_refl _), at_dot point, List.append_assoc]
      · by_contra both
        simp only [not_or, ne_eq, not_not] at both
        apply ne
        constructor
        · have := segment_length text start dot high
          rw [both.1] at this; simp at this; omega
        · have := segment_length text (dot + 1) text.length (le_refl _)
          rw [both.2] at this; simp at this; omega
    · have dotIs : dot = text.length := by omega
      simp only [point, ↓reduceIte] at hf ne ⊢
      refine .inl ⟨by rw [dotIs]; exact takeSplit, ?_, segment_empty _ _ _ (le_refl _)⟩
      intro empty
      apply ne
      refine ⟨?_, by simp⟩
      have := segment_length text start dot high
      rw [empty] at this; simp at this; omega

theorem shaped_correct (lexical : alloc.vec.Vec U8) (whole : Bool) (start dot after : Usize)
    (dotFits : dot.val ≤ lexical.val.length) :
    datatypes.shaped lexical whole start dot after = .ok (decide (¬ (whole = true ∧ dot.val < lexical.val.length) ∧
      Digits (segment lexical.val start.val dot.val) ∧ Digits (segment lexical.val after.val lexical.val.length) ∧
      ¬ (dot.val = start.val ∧ after.val = lexical.val.length))) := by
  rw [datatypes.shaped, digits_from_correct lexical start dot dotFits,
    digits_from_correct lexical after (alloc.vec.Vec.len lexical) (by simp)]
  simp only [alloc.vec.Vec.len_val]
  cases whole <;> by_cases lt : dot.val < lexical.val.length <;>
    by_cases d1 : Digits (segment lexical.val start.val dot.val) <;>
    by_cases d2 : Digits (segment lexical.val after.val lexical.val.length) <;>
    simp [UScalar.lt_equiv, lt, d1, d2] <;>
    by_cases e1 : dot.val = start.val <;> by_cases e2 : after.val = lexical.val.length <;>
    simp [UScalar.eq_equiv, e1, e2]

/-- The kernel's numeric reading is exact: a canonical number, whose value is
    the lexical form's, exactly for the lexical forms of the integers (when
    `whole`) or the decimals; an integer has no fraction. -/
theorem number_value_correct (lexical : alloc.vec.Vec U8) (whole : Bool) :
    ∃ r, datatypes.number_value lexical whole = .ok r ∧
      (∀ v, r = some v → ∃ n w f, v = .Number n w f ∧ CanonicalNumber n w.val f.val ∧
          NumberForm whole lexical.val (numberOf n w.val f.val) ∧ (whole = true → f.val = [])) ∧
      (r = none → ∀ q, ¬ NumberForm whole lexical.val q) := by
  have size := lexical.property
  obtain ⟨start, startRun, startValue⟩ : ∃ start : Usize,
      (if decide (lexical.val.head? = some 43#u8 ∨ lexical.val.head? = some 45#u8) then ok 1#usize
        else ok 0#usize : Result Usize) = ok start ∧
        start.val = if SignedText lexical.val then 1 else 0 := by
    by_cases h : SignedText lexical.val <;> simp [SignedText] at h ⊢ <;> simp [h]
  have startFits : start.val ≤ lexical.val.length := by
    rw [startValue]
    split
    · rename_i h
      rcases h with h | h <;> (cases hl : lexical.val with
        | nil => simp [hl] at h
        | cons _ _ => simp)
    · simp
  obtain ⟨dot, dotRun, dotBound, dotLow, dotBefore, dotAt⟩ := find_byte_correct lexical 46#u8 start
  have dotLow' := dotLow startFits
  obtain ⟨after, afterRun, afterValue⟩ : ∃ after : Usize,
      (if dot < alloc.vec.Vec.len lexical then dot + 1#usize else ok (alloc.vec.Vec.len lexical) : Result Usize) =
        ok after ∧ after.val = if dot.val < lexical.val.length then dot.val + 1 else lexical.val.length := by
    by_cases h : dot.val < lexical.val.length
    · obtain ⟨n, run, v⟩ := WP.spec_imp_exists (Usize.add_spec (x := dot) (y := 1#usize) (by scalar_tac))
      exact ⟨n, by simp [UScalar.lt_equiv, h, run], by simp [h]; simpa using v⟩
    · exact ⟨alloc.vec.Vec.len lexical, by simp [UScalar.lt_equiv, h], by simp [h]⟩
  have afterFits : after.val ≤ lexical.val.length := by rw [afterValue]; split <;> omega
  have form := fun q => number_form_iff lexical.val whole q dot.val (by rw [← startValue]; exact dotLow') dotBound
    (by rw [← startValue]; exact dotBefore) dotAt
  rw [← startValue] at form
  simp only [← afterValue] at form
  rw [datatypes.number_value]
  simp only [signed_correct, bind_ok, startRun, dotRun, afterRun, shaped_correct lexical whole start dot after dotBound]
  by_cases shape : ¬ (whole = true ∧ dot.val < lexical.val.length) ∧
      Digits (segment lexical.val start.val dot.val) ∧ Digits (segment lexical.val after.val lexical.val.length) ∧
      ¬ (dot.val = start.val ∧ after.val = lexical.val.length)
  · obtain ⟨n, w, f, fromRun, canonical, value⟩ := number_from_correct lexical
      (decide (lexical.val.head? = some 45#u8)) start dot after dotLow' dotBound afterFits shape.2.1 shape.2.2.1
    refine ⟨some (.Number n w f), by simp [shape, minus_correct, fromRun], ?_, by simp⟩
    rintro v ⟨⟩
    have hold : NumberForm whole lexical.val (numberOf n w.val f.val) := by
      refine (form _).mpr ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2, ?_⟩
      rw [value]
      by_cases m : lexical.val.head? = some 45#u8 <;> simp [m]
    refine ⟨n, w, f, rfl, canonical, hold, fun isWhole => ?_⟩
    rw [isWhole] at hold
    simp only [NumberForm, ↓reduceIte] at hold
    have integer : IsInteger (numberOf n w.val f.val) := by
      obtain ⟨sign, ws, _, _, _, _, hq⟩ := hold
      refine ⟨(if sign = [45#u8] then -1 else 1) * (digitsValue ws : ℤ), ?_⟩
      rw [hq]; unfold signValue; split <;> simp
    exact (numberOf_integer canonical).mp integer
  · refine ⟨none, by simp only [decide_eq_false shape]; simp, by simp, fun _ q h => shape ?_⟩
    have c := (form q).mp h
    exact ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1⟩

/-! ### Plain literals, strings and truth values -/

/-- A plain literal's lexical form splits uniquely at its last `@`. -/
theorem plain_split_unique {lexical s l s' l' : List U8} (a : PlainSplit lexical s l) (b : PlainSplit lexical s' l') :
    s = s' ∧ l = l' := by
  obtain ⟨ha, na⟩ := a
  obtain ⟨hb, nb⟩ := b
  rcases List.append_eq_append_iff.mp (ha.symm.trans hb) with ⟨extra, hs, rest⟩ | ⟨extra, hs, rest⟩
  · cases extra with
    | nil => simp at hs rest; exact ⟨hs.symm, rest⟩
    | cons x tail =>
      simp only [List.cons_append, List.cons.injEq] at rest
      exact absurd (rest.2 ▸ List.mem_append_right tail List.mem_cons_self) na
  · cases extra with
    | nil => simp at hs rest; exact ⟨hs, rest.symm⟩
    | cons x tail =>
      simp only [List.cons_append, List.cons.injEq] at rest
      exact absurd (rest.2 ▸ List.mem_append_right tail List.mem_cons_self) nb

theorem tagged_value_correct (text tag : alloc.vec.Vec U8) :
    ∃ r, datatypes.tagged_value text tag = .ok r ∧
      (tag.val = [] → r = some (.Text text)) ∧
      (tag.val ≠ [] → LanguageTag tag.val → ∃ m, r = some (.Tagged text m) ∧ Lowered tag.val m.val) ∧
      (tag.val ≠ [] → ¬ LanguageTag tag.val → r = none) := by
  rw [datatypes.tagged_value]
  by_cases empty : tag.val = []
  · have zero : alloc.vec.Vec.len tag = 0#usize := by
      apply UScalar.eq_of_val_eq; simp [empty]
    exact ⟨_, by simp [zero], fun _ => rfl, fun h => absurd empty h, fun h => absurd empty h⟩
  · have notZero : ¬ alloc.vec.Vec.len tag = 0#usize := by
      intro h; apply empty; have := congrArg UScalar.val h; simpa using this
    obtain ⟨accepted, acceptedRun⟩ := Rowl.LangTag.well_formed_total_correct tag
    have acceptance := Rowl.LangTag.well_formed_accepted_iff tag
    cases accepted with
    | true =>
      have isTag : LanguageTag tag.val := acceptance.mp acceptedRun
      obtain ⟨m, lowerRun, lowered⟩ := lower_from_correct tag 0#usize (alloc.vec.Vec.new U8)
        (by simp [new_val])
      refine ⟨some (.Tagged text m), by simp [notZero, acceptedRun, lowerRun], fun h => absurd h empty,
        fun _ _ => ⟨m, rfl, ?_⟩, fun _ no => absurd isTag no⟩
      simp only [new_val, List.map_nil, List.nil_append, List.drop_zero] at lowered
      exact lowered
    | false =>
      have notTag : ¬ LanguageTag tag.val := fun h => by
        have := acceptance.mpr h; rw [acceptedRun] at this; cases Result.ok_injective this
      exact ⟨none, by simp [notZero, acceptedRun], fun h => absurd h empty, fun _ h => absurd h notTag, fun _ _ => rfl⟩

theorem plain_value_correct (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.plain_value lexical = .ok r ∧
      (∀ v, r = some v → ∃ s l, PlainSplit lexical.val s l ∧ XmlText s ∧
        ((l = [] ∧ ∃ t, v = .Text t ∧ t.val = s) ∨
          (LanguageTag l ∧ ∃ t m, v = .Tagged t m ∧ t.val = s ∧ Lowered l m.val))) ∧
      (r = none → ¬ ∃ s l, PlainSplit lexical.val s l ∧ XmlText s ∧ (l = [] ∨ LanguageTag l)) := by
  have size := lexical.property
  rw [datatypes.plain_value]
  obtain ⟨at', atRun, cases⟩ := last_byte_correct lexical 64#u8 (alloc.vec.Vec.len lexical) (by simp)
  simp only [alloc.vec.Vec.len_val] at cases
  rcases cases with ⟨none', absent⟩ | ⟨inside, atByte, after⟩
  · -- no `@`: no split
    refine ⟨none, by simp [atRun, UScalar.lt_equiv, none'], by simp, fun _ ⟨s, l, ⟨split, _⟩, _⟩ => ?_⟩
    have inside : s.length < lexical.val.length := by rw [split]; simp
    have hit : lexical.val[s.length] = 64#u8 := by simp [split]
    exact absent s.length inside (by simpa using inside) hit
  · have inside' : at' < alloc.vec.Vec.len lexical := by simpa [UScalar.lt_equiv] using inside
    have atFits : at'.val ≤ lexical.val.length := by simpa using inside.le
    obtain ⟨text, textRun, textValue⟩ := copy_range_correct lexical 0#usize at' (alloc.vec.Vec.new U8)
      atFits (by simp [new_val]; scalar_tac)
    simp only [new_val, List.nil_append] at textValue
    have splitHere : PlainSplit lexical.val text.val (lexical.val.drop (at'.val + 1)) := by
      refine ⟨?_, ?_⟩
      · rw [textValue, show ((0#usize : Usize).val) = 0 from rfl, segment_take]
        have atLess : at'.val < lexical.val.length := by simpa using inside
        conv => lhs; rw [← List.take_append_drop at'.val lexical.val]
        rw [List.drop_eq_getElem_cons atLess, atByte]
      · intro member
        obtain ⟨i, hi, hv⟩ := List.getElem_of_mem member
        simp only [List.getElem_drop] at hv
        simp only [List.length_drop] at hi
        exact after (at'.val + 1 + i) (by simpa using (show at'.val + 1 + i < lexical.val.length by omega))
          (by omega) (by simpa using (show at'.val + 1 + i < lexical.val.length by omega)) hv
    have unique : ∀ s l, PlainSplit lexical.val s l → s = text.val ∧ l = lexical.val.drop (at'.val + 1) :=
      fun s l split => plain_split_unique split splitHere
    by_cases xml : XmlText text.val
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := at') (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = at'.val + 1 := by simpa using nextValue
      obtain ⟨tag, tagRun, tagValue⟩ := copy_range_correct lexical next (alloc.vec.Vec.len lexical)
        (alloc.vec.Vec.new U8) (by simp) (by simp [new_val]; scalar_tac)
      simp only [new_val, List.nil_append, alloc.vec.Vec.len_val, nextIs] at tagValue
      have tagIs : tag.val = lexical.val.drop (at'.val + 1) := by rw [tagValue, segment_drop]
      obtain ⟨r, taggedRun, onEmpty, onTag, onBad⟩ := tagged_value_correct text tag
      have inside'' : at'.val < lexical.val.length := by simpa using inside
      refine ⟨r, by simp [atRun, UScalar.lt_equiv, inside'', textRun, xml_text_correct, xml, advance, tagRun,
        taggedRun], ?_, ?_⟩
      · intro v hv
        refine ⟨text.val, tag.val, tagIs ▸ splitHere, xml, ?_⟩
        by_cases empty : tag.val = []
        · exact .inl ⟨empty, text, Option.some.inj (hv.symm.trans (onEmpty empty)), rfl⟩
        · by_cases isTag : LanguageTag tag.val
          · obtain ⟨m, hm, lowered⟩ := onTag empty isTag
            exact .inr ⟨isTag, text, m, Option.some.inj (hv.symm.trans hm), rfl, lowered⟩
          · rw [onBad empty isTag] at hv; cases hv
      · intro isNone ⟨s, l, split, xs, kind⟩
        obtain ⟨rfl, rfl⟩ := unique s l split
        rw [← tagIs] at kind
        rcases kind with empty | isTag
        · rw [onEmpty empty] at isNone; cases isNone
        · by_cases empty : tag.val = []
          · rw [onEmpty empty] at isNone; cases isNone
          · obtain ⟨m, hm, _⟩ := onTag empty isTag
            rw [hm] at isNone; cases isNone
    · have inside'' : at'.val < lexical.val.length := by simpa using inside
      refine ⟨none, by simp [atRun, UScalar.lt_equiv, inside'', textRun, xml_text_correct, xml], by simp, ?_⟩
      intro _ ⟨s, l, split, xs, _⟩
      obtain ⟨rfl, _⟩ := unique s l split
      exact xml xs

theorem truth_value_correct (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.truth_value lexical = .ok r ∧
      (∀ v, r = some v → ∃ b, v = .Truth b ∧ TruthForm lexical.val b) ∧
      (r = none → ∀ b, ¬ TruthForm lexical.val b) := by
  rw [datatypes.truth_value]
  by_cases t : lexical.val = [116#u8, 114#u8, 117#u8, 101#u8]
  · exact ⟨some (.Truth true), by simp [same_pattern_total, Array.to_slice, Array.make, lift, t],
      fun v hv => ⟨true, (Option.some.inj hv).symm, .inl ⟨rfl, .inl t⟩⟩, by simp⟩
  · by_cases one : lexical.val = [49#u8]
    · exact ⟨some (.Truth true), by simp [same_pattern_total, Array.to_slice, Array.make, lift, t, one],
        fun v hv => ⟨true, (Option.some.inj hv).symm, .inl ⟨rfl, .inr one⟩⟩, by simp⟩
    · by_cases f : lexical.val = [102#u8, 97#u8, 108#u8, 115#u8, 101#u8]
      · exact ⟨some (.Truth false), by simp [same_pattern_total, Array.to_slice, Array.make, lift, t, one, f],
          fun v hv => ⟨false, (Option.some.inj hv).symm, .inr ⟨rfl, .inl f⟩⟩, by simp⟩
      · by_cases zero : lexical.val = [48#u8]
        · exact ⟨some (.Truth false),
            by simp [same_pattern_total, Array.to_slice, Array.make, lift, t, one, f, zero],
            fun v hv => ⟨false, (Option.some.inj hv).symm, .inr ⟨rfl, .inr zero⟩⟩, by simp⟩
        · refine ⟨none, by simp [same_pattern_total, Array.to_slice, Array.make, lift, t, one, f, zero], by simp, ?_⟩
          intro _ b form
          rcases form with ⟨_, h | h⟩ | ⟨_, h | h⟩ <;> contradiction

/-! ### Values -/

/-- The values that `literal_value` returns: canonical numbers, strings of XML
    characters, such strings with a lower-case well-formed language tag, and
    truth values. -/
def Canonical : datatypes.DataValue → Prop
  | .Number n w f => CanonicalNumber n w.val f.val
  | .Text t => XmlText t.val
  | .Tagged t m => XmlText t.val ∧ TagValue m.val
  | .Truth _ => True

/-- The lexical space of the datatype of a kind. -/
def LexicalForm : datatypes.Kind → List U8 → Prop
  | .Integer, t => ∃ q, IntegerForm t q
  | .Decimal, t => ∃ q, DecimalForm t q
  | .String, t => XmlText t
  | .Plain, t => ∃ s l, PlainSplit t s l ∧ XmlText s ∧ (l = [] ∨ LanguageTag l)
  | .Boolean, t => ∃ b, TruthForm t b

variable {Native : Type w} {D : DatatypeMap Native}

/-- The value of a kernel value in a datatype map that is the OWL 2 map on the
    five datatypes. -/
def valueOf (N : Normative D) : datatypes.DataValue → Native
  | .Number n w f => N.number (numberOf n w.val f.val)
  | .Text t => N.text t.val
  | .Tagged t m => N.tagged t.val m.val
  | .Truth b => N.truth b

theorem normative_lexical (N : Normative D) (k : datatypes.Kind) (t : List U8) :
    D.lexicalSpace (typeOf k) t ↔ LexicalForm k t := by
  cases k
  · exact N.integer_lexical t
  · exact N.decimal_lexical t
  · exact N.string_lexical t
  · exact N.plain_lexical t
  · exact N.boolean_lexical t

theorem normative_supported (N : Normative D) (k : datatypes.Kind) : D.supported (typeOf k) := by
  cases k
  · exact N.integer_supported
  · exact N.decimal_supported
  · exact N.string_supported
  · exact N.plain_supported
  · exact N.boolean_supported

/-- The kernel's reading of a lexical form is exact: a canonical value exactly
    for a lexical form in the lexical space of the kind's datatype, and then,
    under every datatype map that is the OWL 2 map on the five datatypes, the
    lexical form's value. -/
theorem kind_value_correct (k : datatypes.Kind) (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.kind_value k lexical = .ok r ∧
      (∀ v, r = some v → Canonical v ∧ LexicalForm k lexical.val ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
          D.lexicalValue (typeOf k) lexical.val = valueOf N v) ∧
      (r = none → ¬ LexicalForm k lexical.val) := by
  have size := lexical.property
  cases k with
  | Integer =>
    obtain ⟨r, run, some', none'⟩ := number_value_correct lexical true
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn ⟨q, form⟩ => none' hn q form⟩
    obtain ⟨n, w, f, rfl, canonical, form, _⟩ := some' v hv
    exact ⟨canonical, ⟨_, form⟩, fun D N => N.integer_value _ _ form⟩
  | Decimal =>
    obtain ⟨r, run, some', none'⟩ := number_value_correct lexical false
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn ⟨q, form⟩ => none' hn q form⟩
    obtain ⟨n, w, f, rfl, canonical, form, _⟩ := some' v hv
    exact ⟨canonical, ⟨_, form⟩, fun D N => N.decimal_value _ _ form⟩
  | String =>
    by_cases xml : XmlText lexical.val
    · obtain ⟨copy, copyRun, copyValue⟩ := copy_range_correct lexical 0#usize (alloc.vec.Vec.len lexical)
        (alloc.vec.Vec.new U8) (by simp) (by simp [new_val])
      have same : copy.val = lexical.val := by
        rw [copyValue, new_val, List.nil_append, alloc.vec.Vec.len_val, show ((0#usize : Usize).val) = 0 from rfl,
          segment_take]
        simp
      refine ⟨some (.Text copy), by simp [datatypes.kind_value, xml_text_correct, xml, copyRun], ?_, by simp⟩
      rintro v ⟨⟩
      exact ⟨by simp [Canonical, same, xml], xml, fun D N => by simp [valueOf, same, typeOf, N.string_value _ xml]⟩
    · exact ⟨none, by simp [datatypes.kind_value, xml_text_correct, xml], by simp, fun _ => xml⟩
  | Plain =>
    obtain ⟨r, run, some', none'⟩ := plain_value_correct lexical
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, none'⟩
    obtain ⟨s, l, split, xml, cases⟩ := some' v hv
    rcases cases with ⟨rfl, t, rfl, rfl⟩ | ⟨isTag, t, m, rfl, rfl, lowered⟩
    · exact ⟨xml, ⟨_, [], split, xml, .inl rfl⟩, fun D N => N.plain_text _ _ split xml⟩
    · exact ⟨⟨xml, l, isTag, lowered⟩, ⟨_, l, split, xml, .inr isTag⟩,
        fun D N => N.plain_tagged _ _ _ _ split xml isTag lowered⟩
  | Boolean =>
    obtain ⟨r, run, some', none'⟩ := truth_value_correct lexical
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn ⟨b, form⟩ => none' hn b form⟩
    obtain ⟨b, rfl, form⟩ := some' v hv
    exact ⟨trivial, ⟨b, form⟩, fun D N => N.boolean_value _ _ form⟩

/-- A literal has a value exactly when its datatype is one of the five and its
    lexical form is in the lexical space; the value is canonical, and under
    every datatype map that is the OWL 2 map on the five datatypes the literal
    is in the vocabulary's lexical space with that value. -/
theorem literal_value_correct (lt : Literal) :
    ∃ r, datatypes.literal_value lt = .ok r ∧
      (∀ v, r = some v → Canonical v ∧ ∃ k, kindOf lt.datatype = some k ∧ LexicalForm k lt.lexical.val ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
          D.supported lt.datatype ∧ D.lexicalSpace lt.datatype lt.lexical.val ∧
            D.lexicalValue lt.datatype lt.lexical.val = valueOf N v) ∧
      (r = none → kindOf lt.datatype = none ∨
        ∃ k, kindOf lt.datatype = some k ∧ ¬ LexicalForm k lt.lexical.val) := by
  rw [datatypes.literal_value, kind_of_correct]
  cases kind : kindOf lt.datatype with
  | none => exact ⟨none, by simp, by simp, fun _ => .inl rfl⟩
  | some k =>
    have isType := kindOf_some kind
    obtain ⟨r, run, some', none'⟩ := kind_value_correct.{w} k lt.lexical
    refine ⟨r, by simpa using run, fun v hv => ?_, fun hn => .inr ⟨k, rfl, none' hn⟩⟩
    obtain ⟨canonical, form, value⟩ := some' v hv
    refine ⟨canonical, k, rfl, form, fun D N => ?_⟩
    rw [isType]
    exact ⟨normative_supported N k, (normative_lexical N k _).mpr form, value D N⟩

private theorem same_bytes_from_total (left right : alloc.vec.Vec U8)
    (lengths : left.val.length = right.val.length) (index : Usize) :
    datatypes.same_bytes_from left right index =
      .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [datatypes.same_bytes_from]
  by_cases h : index.val < left.val.length
  · have hr : index.val < right.val.length := by omega
    have hl : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hrIndex : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : left.val[index.val] = right.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := same_bytes_from_total left right lengths next
      simp [UScalar.lt_equiv, h, hr, alloc.vec.Vec.index_slice_index, hl, hrIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · simp [UScalar.lt_equiv, h, hr, alloc.vec.Vec.index_slice_index, hl, hrIndex, heads]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have hk : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hp : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [UScalar.lt_equiv, h, hk, hp]
termination_by left.val.length - index.val
decreasing_by omega

theorem same_bytes_correct (left right : alloc.vec.Vec U8) :
    datatypes.same_bytes left right = .ok (decide (left = right)) := by
  have eq : left = right ↔ left.val = right.val := by simp [alloc.vec.Vec.eq_iff]
  rw [datatypes.same_bytes]
  by_cases lengths : left.val.length = right.val.length
  · have lengths' : alloc.vec.Vec.len left = alloc.vec.Vec.len right := UScalar.eq_of_val_eq (by simpa using lengths)
    simp only [lengths', ↓reduceIte, eq]
    simpa using same_bytes_from_total left right lengths 0#usize
  · have unequal : ¬ left.val = right.val := fun same => lengths (congrArg List.length same)
    have lengths' : ¬ alloc.vec.Vec.len left = alloc.vec.Vec.len right := fun same => lengths (by
      simpa using congrArg UScalar.val same)
    simp [lengths', eq, unequal]

/-- The kernel compares values exactly. -/
theorem same_value_correct (left right : datatypes.DataValue) :
    datatypes.same_value left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;> simp [datatypes.same_value, same_bytes_correct] <;>
    split_ifs <;> simp_all [same_bytes_correct]

/-- Membership of a value in the value space of a kind's datatype, as the
    kernel reads it off the value. -/
def InKind : datatypes.DataValue → datatypes.Kind → Prop
  | .Number _ _ f, .Integer => f.val = []
  | .Number _ _ _, .Decimal => True
  | .Text _, .String => True
  | .Text _, .Plain => True
  | .Tagged _ _, .Plain => True
  | .Truth _, .Boolean => True
  | _, _ => False

theorem in_kind_correct (v : datatypes.DataValue) (k : datatypes.Kind) :
    datatypes.in_kind v k = .ok (decide (InKind v k)) := by
  cases v <;> cases k <;> simp [datatypes.in_kind, InKind, UScalar.eq_equiv]

/-- Under every datatype map that is the OWL 2 map on the five datatypes, a
    canonical value is in the value space of a kind's datatype exactly as the
    kernel reads it. -/
theorem normative_in_kind (N : Normative D) {v : datatypes.DataValue} (canonical : Canonical v)
    (k : datatypes.Kind) : InKind v k ↔ D.valueSpace (typeOf k) (valueOf N v) := by
  cases v with
  | Number n w f =>
    have c : CanonicalNumber n w.val f.val := canonical
    cases k <;> simp only [InKind, typeOf, valueOf, N.integer_space, N.decimal_space, N.string_space,
      N.plain_space, N.boolean_space]
    · constructor
      · intro h; exact ⟨_, (numberOf_integer c).mpr h, rfl⟩
      · rintro ⟨q, integer, same⟩
        exact (numberOf_integer c).mp (N.number_injective same ▸ integer)
    · exact ⟨fun _ => ⟨_, numberOf_decimal n w.val f.val, rfl⟩, fun _ => trivial⟩
    · exact ⟨False.elim, fun ⟨s, xs, same⟩ => N.number_text _ s xs same⟩
    · refine ⟨False.elim, ?_⟩
      rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
      · exact N.number_text _ s xs same
      · exact N.number_tagged _ s l xs tl same
    · exact ⟨False.elim, fun ⟨b, same⟩ => N.number_truth _ b same⟩
  | Text t =>
    have xt : XmlText t.val := canonical
    cases k <;> simp only [InKind, typeOf, valueOf, N.integer_space, N.decimal_space, N.string_space,
      N.plain_space, N.boolean_space]
    · exact ⟨False.elim, fun ⟨q, _, same⟩ => N.number_text q _ xt same.symm⟩
    · exact ⟨False.elim, fun ⟨q, _, same⟩ => N.number_text q _ xt same.symm⟩
    · exact ⟨fun _ => ⟨_, xt, rfl⟩, fun _ => trivial⟩
    · exact ⟨fun _ => .inl ⟨_, xt, rfl⟩, fun _ => trivial⟩
    · exact ⟨False.elim, fun ⟨b, same⟩ => N.text_truth _ b xt same⟩
  | Tagged t m =>
    have xt : XmlText t.val := canonical.1
    have tm : TagValue m.val := canonical.2
    cases k <;> simp only [InKind, typeOf, valueOf, N.integer_space, N.decimal_space, N.string_space,
      N.plain_space, N.boolean_space]
    · exact ⟨False.elim, fun ⟨q, _, same⟩ => N.number_tagged q _ _ xt tm same.symm⟩
    · exact ⟨False.elim, fun ⟨q, _, same⟩ => N.number_tagged q _ _ xt tm same.symm⟩
    · exact ⟨False.elim, fun ⟨s, xs, same⟩ => N.text_tagged s _ _ xs xt tm same.symm⟩
    · exact ⟨fun _ => .inr ⟨_, _, xt, tm, rfl⟩, fun _ => trivial⟩
    · exact ⟨False.elim, fun ⟨b, same⟩ => N.tagged_truth _ _ b xt tm same⟩
  | Truth b =>
    cases k <;> simp only [InKind, typeOf, valueOf, N.integer_space, N.decimal_space, N.string_space,
      N.plain_space, N.boolean_space]
    · exact ⟨False.elim, fun ⟨q, _, same⟩ => N.number_truth q b same.symm⟩
    · exact ⟨False.elim, fun ⟨q, _, same⟩ => N.number_truth q b same.symm⟩
    · exact ⟨False.elim, fun ⟨s, xs, same⟩ => N.text_truth s b xs same.symm⟩
    · refine ⟨False.elim, ?_⟩
      rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
      · exact N.text_truth s b xs same.symm
      · exact N.tagged_truth s l b xs tl same.symm
    · exact ⟨fun _ => ⟨b, rfl⟩, fun _ => trivial⟩

private theorem vec_ext {a b : alloc.vec.Vec U8} (h : a.val = b.val) : a = b := by
  simpa [alloc.vec.Vec.eq_iff] using h

/-- Under every datatype map that is the OWL 2 map on the five datatypes,
    distinct canonical values are distinct values. -/
theorem value_injective (N : Normative D) {a b : datatypes.DataValue} (ca : Canonical a) (cb : Canonical b)
    (same : valueOf N a = valueOf N b) : a = b := by
  cases a with
  | Number n w f =>
    cases b with
    | Number n' w' f' =>
      obtain ⟨e1, e2, e3⟩ := numberOf_injective ca cb (N.number_injective same)
      rw [e1, vec_ext e2, vec_ext e3]
    | Text t => exact absurd same (N.number_text _ _ cb)
    | Tagged t m => exact absurd same (N.number_tagged _ _ _ cb.1 cb.2)
    | Truth b => exact absurd same (N.number_truth _ _)
  | Text t =>
    cases b with
    | Number n w f => exact absurd same.symm (N.number_text _ _ ca)
    | Text t' => rw [vec_ext (N.text_injective _ _ ca cb same)]
    | Tagged t' m => exact absurd same (N.text_tagged _ _ _ ca cb.1 cb.2)
    | Truth b => exact absurd same (N.text_truth _ _ ca)
  | Tagged t m =>
    cases b with
    | Number n w f => exact absurd same.symm (N.number_tagged _ _ _ ca.1 ca.2)
    | Text t' => exact absurd same.symm (N.text_tagged _ _ _ cb ca.1 ca.2)
    | Tagged t' m' =>
      obtain ⟨e1, e2⟩ := N.tagged_injective _ _ _ _ ca.1 cb.1 ca.2 cb.2 same
      rw [vec_ext e1, vec_ext e2]
    | Truth b => exact absurd same (N.tagged_truth _ _ _ ca.1 ca.2)
  | Truth x =>
    cases b with
    | Number n w f => exact absurd same.symm (N.number_truth _ _)
    | Text t => exact absurd same.symm (N.text_truth _ _ cb)
    | Tagged t m => exact absurd same.symm (N.tagged_truth _ _ _ cb.1 cb.2)
    | Truth y => rw [N.truth_injective same]

/-! ### The specification has a model

A datatype map on values of five kinds, with every lexical-to-value mapping
chosen by the specification's unique value, is the OWL 2 map on the five
datatypes: `Normative` is not contradictory. -/

private theorem utf8_append {a b : List U8} (ha : Rowl.Owl.Utf8Lexical a) (hb : Rowl.Owl.Utf8Lexical b) :
    Rowl.Owl.Utf8Lexical (a ++ b) := by
  induction ha with
  | empty => simpa using hb
  | ascii x h _ ih => exact .ascii x h ih
  | pair x y h _ ih => exact .pair x y h ih
  | triple x y z h _ ih => exact .triple x y z h ih
  | quad x y z u h _ ih => exact .quad x y z u h ih

private theorem ascii_utf8 (bytes : List U8) (ascii : ∀ b ∈ bytes, b.val < 128) : Rowl.Owl.Utf8Lexical bytes := by
  induction bytes with
  | nil => exact .empty
  | cons head tail ih =>
    exact .ascii head (ascii head List.mem_cons_self) (ih (fun b m => ascii b (List.mem_cons_of_mem _ m)))

private theorem prefix_utf8 (bs : List U8) (offset cp width : Nat)
    (h : Rowl.Unicode.Prefix bs offset = some (cp, width))
    (rest : Rowl.Owl.Utf8Lexical (bs.drop (offset + width))) : Rowl.Owl.Utf8Lexical (bs.drop offset) := by
  unfold Rowl.Unicode.Prefix at h
  cases ha : bs[offset]? with
  | none => simp [ha] at h
  | some a =>
    have inside : offset < bs.length := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨inside, _⟩; exact inside
    have va : bs[offset] = a := by rcases List.getElem?_eq_some_iff.mp ha with ⟨_, v⟩; exact v
    rw [List.drop_eq_getElem_cons inside, va]
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at h
    by_cases one : a.val < 128
    · simp only [one, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2] at rest
      exact .ascii a one rest
    · simp only [one, ↓reduceIte] at h
      by_cases two : a.val < 224
      · simp only [two, ↓reduceIte] at h
        cases hb : bs[offset + 1]? with
        | none => simp [hb] at h
        | some b =>
          simp only [hb, Option.bind_some] at h
          split_ifs at h with pair
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2] at rest
          have inside' : offset + 1 < bs.length := by
            rcases List.getElem?_eq_some_iff.mp hb with ⟨i, _⟩; exact i
          have vb : bs[offset + 1] = b := by rcases List.getElem?_eq_some_iff.mp hb with ⟨_, v⟩; exact v
          rw [List.drop_eq_getElem_cons inside', vb]
          exact .pair a b pair rest
      · simp only [two, ↓reduceIte] at h
        by_cases three : a.val < 240
        · simp only [three, ↓reduceIte] at h
          cases hb : bs[offset + 1]? with
          | none => simp [hb] at h
          | some b =>
            cases hc : bs[offset + 2]? with
            | none => simp [hb, hc] at h
            | some c =>
              simp only [hb, hc, Option.bind_some] at h
              split_ifs at h with triple
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.2] at rest
              have i1 : offset + 1 < bs.length := by rcases List.getElem?_eq_some_iff.mp hb with ⟨i, _⟩; exact i
              have v1 : bs[offset + 1] = b := by rcases List.getElem?_eq_some_iff.mp hb with ⟨_, v⟩; exact v
              have i2 : offset + 2 < bs.length := by rcases List.getElem?_eq_some_iff.mp hc with ⟨i, _⟩; exact i
              have v2 : bs[offset + 2] = c := by rcases List.getElem?_eq_some_iff.mp hc with ⟨_, v⟩; exact v
              rw [List.drop_eq_getElem_cons i1, v1, List.drop_eq_getElem_cons i2, v2]
              exact .triple a b c triple rest
        · simp only [three, ↓reduceIte] at h
          cases hb : bs[offset + 1]? with
          | none => simp [hb] at h
          | some b =>
            cases hc : bs[offset + 2]? with
            | none => simp [hb, hc] at h
            | some c =>
              cases hd : bs[offset + 3]? with
              | none => simp [hb, hc, hd] at h
              | some d =>
                simp only [hb, hc, hd, Option.bind_some] at h
                split_ifs at h with quad
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                rw [← h.2] at rest
                have i1 : offset + 1 < bs.length := by rcases List.getElem?_eq_some_iff.mp hb with ⟨i, _⟩; exact i
                have v1 : bs[offset + 1] = b := by rcases List.getElem?_eq_some_iff.mp hb with ⟨_, v⟩; exact v
                have i2 : offset + 2 < bs.length := by rcases List.getElem?_eq_some_iff.mp hc with ⟨i, _⟩; exact i
                have v2 : bs[offset + 2] = c := by rcases List.getElem?_eq_some_iff.mp hc with ⟨_, v⟩; exact v
                have i3 : offset + 3 < bs.length := by rcases List.getElem?_eq_some_iff.mp hd with ⟨i, _⟩; exact i
                have v3 : bs[offset + 3] = d := by rcases List.getElem?_eq_some_iff.mp hd with ⟨_, v⟩; exact v
                rw [List.drop_eq_getElem_cons i1, v1, List.drop_eq_getElem_cons i2, v2,
                  List.drop_eq_getElem_cons i3, v3]
                exact .quad a b c d quad rest

private theorem text_utf8 {bs : List U8} {offset : Nat} {text : List (Nat × Nat)}
    (h : Rowl.Unicode.TextFrom bs offset text) : Rowl.Owl.Utf8Lexical (bs.drop offset) := by
  induction h with
  | endOfInput => simpa using Rowl.Owl.Utf8Lexical.empty
  | character unit _ _ _ _ ih => exact prefix_utf8 _ _ _ _ unit ih

private theorem from_utf8 {bs : List U8} {offset : Nat} {word : List Nat}
    (h : Rowl.Regular.Utf8From bs offset word) : Rowl.Owl.Utf8Lexical (bs.drop offset) := by
  induction h with
  | endOfInput => simpa using Rowl.Owl.Utf8Lexical.empty
  | character unit _ _ _ ih => exact prefix_utf8 _ _ _ _ unit ih

/-- The first point at or after `start`, or the length. -/
def firstPoint (text : List U8) (start : Nat) : Nat := start + (text.drop start).findIdx (· == 46#u8)

theorem number_form_unique {whole : Bool} {text : List U8} {q q' : ℚ}
    (a : NumberForm whole text q) (b : NumberForm whole text q') : q = q' := by
  have startFits : (if SignedText text then 1 else 0) ≤ text.length := by
    split
    · rename_i h; rcases h with h | h <;> (cases text with
        | nil => simp at h
        | cons _ _ => simp)
    · simp
  set start := if SignedText text then 1 else 0 with hstart
  have high : firstPoint text start ≤ text.length := by
    have := List.findIdx_le_length (xs := text.drop start) (p := (· == 46#u8))
    simp [firstPoint] at this ⊢; omega
  have before : ∀ i (h : i < text.length), start ≤ i → i < firstPoint text start → text[i] ≠ 46#u8 := by
    intro i h low less
    have local' : i - start < (text.drop start).findIdx (· == 46#u8) := by simp [firstPoint] at less; omega
    have := List.not_of_lt_findIdx local'
    simp only [List.getElem_drop, show start + (i - start) = i by omega, beq_iff_eq] at this
    simpa using this
  have at_point : ∀ h : firstPoint text start < text.length, text[firstPoint text start] = 46#u8 := by
    intro h
    have local' : (text.drop start).findIdx (· == 46#u8) < (text.drop start).length := by
      simp [firstPoint] at h ⊢; omega
    have := List.findIdx_getElem (w := local')
    simp only [List.getElem_drop, beq_iff_eq] at this
    simpa [firstPoint] using this
  have low : (if SignedText text then 1 else 0) ≤ firstPoint text start := by
    rw [← hstart]; exact Nat.le_add_right _ _
  have fa := (number_form_iff text whole q (firstPoint text start) low high before at_point).mp a
  have fb := (number_form_iff text whole q' (firstPoint text start) low high before at_point).mp b
  rw [fa.2.2.2.2, fb.2.2.2.2]

/-- The values of the model map. -/
inductive ModelValue where
  | number (q : ℚ)
  | text (s : List U8)
  | tagged (s l : List U8)
  | truth (b : Bool)
  | other

/-- The ASCII lower case of a byte. -/
def lowerByte (byte : U8) : U8 := if 65 ≤ byte.val ∧ byte.val ≤ 90 then ⟨BitVec.ofNat 8 (byte.val + 32)⟩ else byte

theorem lowerByte_val (byte : U8) :
    (lowerByte byte).val = if 65 ≤ byte.val ∧ byte.val ≤ 90 then byte.val + 32 else byte.val := by
  by_cases h : 65 ≤ byte.val ∧ byte.val ≤ 90
  · have : byte.val ≤ 90 := h.2
    rw [if_pos h]
    simp only [lowerByte, if_pos h]
    show (BitVec.ofNat 8 (byte.val + 32)).toNat = byte.val + 32
    rw [BitVec.toNat_ofNat]; omega
  · rw [if_neg h]; simp [lowerByte, h]

theorem lowered_map (bytes : List U8) : Lowered bytes (bytes.map lowerByte) := by
  unfold Lowered
  rw [List.map_map]
  apply List.map_congr_left
  intro byte _
  exact lowerByte_val byte

/-- The value of a lexical form of the datatype of a kind in the model map. -/
noncomputable def modelValue (k : datatypes.Kind) (t : List U8) : ModelValue :=
  match k with
  | .Integer => if h : ∃ q, NumberForm true t q then .number (Classical.choose h) else .other
  | .Decimal => if h : ∃ q, NumberForm false t q then .number (Classical.choose h) else .other
  | .String => .text t
  | .Plain =>
    if h : ∃ p : List U8 × List U8, PlainSplit t p.1 p.2 then
      if (Classical.choose h).2 = [] then .text (Classical.choose h).1
      else .tagged (Classical.choose h).1 ((Classical.choose h).2.map lowerByte)
    else .other
  | .Boolean => if h : ∃ b, TruthForm t b then .truth (Classical.choose h) else .other

/-- The value space of the datatype of a kind in the model map. -/
def ModelSpace : datatypes.Kind → ModelValue → Prop
  | .Integer, x => ∃ q, IsInteger q ∧ x = .number q
  | .Decimal, x => ∃ q, IsDecimal q ∧ x = .number q
  | .String, x => ∃ s, XmlText s ∧ x = .text s
  | .Plain, x => (∃ s, XmlText s ∧ x = .text s) ∨ ∃ s l, XmlText s ∧ TagValue l ∧ x = .tagged s l
  | .Boolean, x => ∃ b, x = .truth b

private theorem integer_of_form {text : List U8} {q : ℚ} (form : NumberForm true text q) : IsInteger q := by
  obtain ⟨sign, w, _, _, _, _, rfl⟩ := form
  refine ⟨(if sign = [45#u8] then -1 else 1) * (digitsValue w : ℤ), ?_⟩
  unfold signValue; split <;> simp

private theorem decimal_of_form {text : List U8} {q : ℚ} (form : NumberForm false text q) : IsDecimal q := by
  obtain ⟨sign, w, f, _, _, _, _, rfl⟩ := form
  refine ⟨(if sign = [45#u8] then -1 else 1) * ((digitsValue w * 10 ^ f.length + digitsValue f : ℕ) : ℤ),
    f.length, ?_⟩
  have pos : (10 : ℚ) ^ f.length ≠ 0 := by positivity
  unfold signValue
  split <;> push_cast <;> field_simp

private theorem ascii_of_digits {bytes : List U8} (d : Digits bytes) : ∀ b ∈ bytes, b.val < 128 := by
  intro b m; have := (d b m).2; omega

private theorem ascii_of_sign {sign : List U8} (s : Sign sign) : ∀ b ∈ sign, b.val < 128 := by
  rcases s with rfl | rfl | rfl <;> simp

private theorem number_utf8 {whole : Bool} {text : List U8} {q : ℚ} (form : NumberForm whole text q) :
    Rowl.Owl.Utf8Lexical text := by
  obtain ⟨sign, w, f, hs, hw, hf, shape, _⟩ := (number_form_shape whole text q).mp form
  apply ascii_utf8
  rcases shape with ⟨rfl, _, _⟩ | ⟨_, rfl, _⟩
  · intro b m
    rcases List.mem_append.mp m with m | m
    · exact ascii_of_sign hs b m
    · exact ascii_of_digits hw b m
  · intro b m
    simp only [List.mem_append, List.mem_cons] at m
    rcases m with (m | m) | m | m
    · exact ascii_of_sign hs b m
    · exact ascii_of_digits hw b m
    · subst m; decide
    · exact ascii_of_digits hf b m

/-- The model map: the five datatypes with the specification's spaces and
    values, no facets, and every other datatype unsupported. -/
noncomputable def modelMap : DatatypeMap ModelValue where
  supported dt := ∃ k, kindOf dt = some k
  lexicalSpace dt t := ∃ k, kindOf dt = some k ∧ LexicalForm k t
  facetSpace _ _ _ := False
  valueSpace dt x := ∃ k, kindOf dt = some k ∧ ModelSpace k x
  lexicalValue dt t := match kindOf dt with
    | some k => modelValue k t
    | none => .other
  facetValue _ _ _ := False
  excludesLiteral := by
    rintro ⟨k, h⟩
    have := kindOf_some h
    cases k <;> simp_all [typeOf, datatype_eq_iff, Rowl.Owl.literalDatatype, integerType, decimalType, stringType,
      plainType, booleanType]
  lexicalUtf8 := by
    rintro dt text ⟨k, kind⟩ ⟨k', kind', form⟩
    rw [kind] at kind'; cases kind'
    cases k with
    | Integer => obtain ⟨q, f⟩ := form; exact number_utf8 (whole := true) f
    | Decimal => obtain ⟨q, f⟩ := form; exact number_utf8 (whole := false) f
    | String => obtain ⟨scalars, f⟩ := form; simpa using text_utf8 f
    | Plain =>
      obtain ⟨s, l, ⟨rfl, _⟩, ⟨scalars, xs⟩, tag⟩ := form
      apply utf8_append (by simpa using text_utf8 xs)
      apply Rowl.Owl.Utf8Lexical.ascii _ (by decide)
      rcases tag with rfl | ⟨word, utf, _⟩
      · exact .empty
      · simpa using from_utf8 utf
    | Boolean =>
      obtain ⟨b, f⟩ := form
      apply ascii_utf8
      rcases f with ⟨_, rfl | rfl⟩ | ⟨_, rfl | rfl⟩ <;> decide
  lexicalInSpace := by
    rintro dt text ⟨k, kind⟩ ⟨k', kind', form⟩
    rw [kind] at kind'; cases kind'
    refine ⟨k, kind, ?_⟩
    simp only [kind]
    cases k with
    | Integer =>
      have h : ∃ q, NumberForm true text q := form
      simp only [modelValue, h, ↓reduceDIte, ModelSpace]
      exact ⟨_, integer_of_form (Classical.choose_spec h), rfl⟩
    | Decimal =>
      have h : ∃ q, NumberForm false text q := form
      simp only [modelValue, h, ↓reduceDIte, ModelSpace]
      exact ⟨_, decimal_of_form (Classical.choose_spec h), rfl⟩
    | String => exact ⟨text, form, rfl⟩
    | Plain =>
      obtain ⟨s, l, split, xs, tag⟩ := form
      have h : ∃ p : List U8 × List U8, PlainSplit text p.1 p.2 := ⟨(s, l), split⟩
      obtain ⟨e1, e2⟩ := plain_split_unique (Classical.choose_spec h) split
      simp only [modelValue, h, ↓reduceDIte, ModelSpace]
      rw [e1, e2]
      split
      · exact .inl ⟨s, xs, rfl⟩
      · rename_i nonempty
        rcases tag with empty | isTag
        · exact absurd empty nonempty
        · exact .inr ⟨s, _, xs, ⟨l, isTag, lowered_map l⟩, rfl⟩
    | Boolean =>
      have h : ∃ b, TruthForm text b := form
      simp only [modelValue, h, ↓reduceDIte, ModelSpace]
      exact ⟨_, rfl⟩
  facetInSpace := by intro _ _ _ _ _ no; exact no.elim

/-- The model map is the OWL 2 map on the five datatypes: the specification
    `Normative` is consistent. -/
noncomputable def modelNormative : Normative modelMap where
  number := .number
  text := .text
  tagged := .tagged
  truth := .truth
  number_injective := fun _ _ h => by cases h; rfl
  text_injective := fun _ _ _ _ h => by cases h; rfl
  tagged_injective := fun _ _ _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl⟩
  truth_injective := fun _ _ h => by cases h; rfl
  number_text := fun _ _ _ h => by cases h
  number_tagged := fun _ _ _ _ _ h => by cases h
  number_truth := fun _ _ h => by cases h
  text_tagged := fun _ _ _ _ _ _ h => by cases h
  text_truth := fun _ _ _ h => by cases h
  tagged_truth := fun _ _ _ _ _ h => by cases h
  integer_supported := ⟨_, kindOf_typeOf .Integer⟩
  decimal_supported := ⟨_, kindOf_typeOf .Decimal⟩
  string_supported := ⟨_, kindOf_typeOf .String⟩
  plain_supported := ⟨_, kindOf_typeOf .Plain⟩
  boolean_supported := ⟨_, kindOf_typeOf .Boolean⟩
  integer_space := fun x => by
    have := kindOf_typeOf .Integer
    simp only [typeOf] at this
    simp [modelMap, this, ModelSpace]
  decimal_space := fun x => by
    have := kindOf_typeOf .Decimal
    simp only [typeOf] at this
    simp [modelMap, this, ModelSpace]
  string_space := fun x => by
    have := kindOf_typeOf .String
    simp only [typeOf] at this
    simp [modelMap, this, ModelSpace]
  plain_space := fun x => by
    have := kindOf_typeOf .Plain
    simp only [typeOf] at this
    simp [modelMap, this, ModelSpace]
  boolean_space := fun x => by
    have := kindOf_typeOf .Boolean
    simp only [typeOf] at this
    simp [modelMap, this, ModelSpace]
  integer_lexical := fun t => by
    have := kindOf_typeOf .Integer
    simp only [typeOf] at this
    simp [modelMap, this, LexicalForm]
  integer_value := fun t q form => by
    have := kindOf_typeOf .Integer
    simp only [typeOf] at this
    have h : ∃ q, NumberForm true t q := ⟨q, form⟩
    simp only [modelMap, this, modelValue, h, ↓reduceDIte]
    rw [number_form_unique (Classical.choose_spec h) form]
  decimal_lexical := fun t => by
    have := kindOf_typeOf .Decimal
    simp only [typeOf] at this
    simp [modelMap, this, LexicalForm]
  decimal_value := fun t q form => by
    have := kindOf_typeOf .Decimal
    simp only [typeOf] at this
    have h : ∃ q, NumberForm false t q := ⟨q, form⟩
    simp only [modelMap, this, modelValue, h, ↓reduceDIte]
    rw [number_form_unique (Classical.choose_spec h) form]
  string_lexical := fun t => by
    have := kindOf_typeOf .String
    simp only [typeOf] at this
    simp [modelMap, this, LexicalForm]
  string_value := fun t _ => by
    have := kindOf_typeOf .String
    simp only [typeOf] at this
    simp [modelMap, this, modelValue]
  plain_lexical := fun t => by
    have := kindOf_typeOf .Plain
    simp only [typeOf] at this
    simp [modelMap, this, LexicalForm]
  plain_text := fun t s split _ => by
    have := kindOf_typeOf .Plain
    simp only [typeOf] at this
    have h : ∃ p : List U8 × List U8, PlainSplit t p.1 p.2 := ⟨(s, []), split⟩
    obtain ⟨e1, e2⟩ := plain_split_unique (Classical.choose_spec h) split
    simp only [modelMap, this, modelValue, h, ↓reduceDIte]
    rw [e1, e2]
    simp
  plain_tagged := fun t s l m split _ isTag lowered => by
    have := kindOf_typeOf .Plain
    simp only [typeOf] at this
    have h : ∃ p : List U8 × List U8, PlainSplit t p.1 p.2 := ⟨(s, l), split⟩
    obtain ⟨e1, e2⟩ := plain_split_unique (Classical.choose_spec h) split
    have nonempty : l ≠ [] := by
      rintro rfl
      obtain ⟨word, utf, member⟩ := isTag
      cases utf with
      | endOfInput => exact Rowl.LangTag.well_formed_nonempty member
      | character _ positive fits _ => simp at fits; omega
    have same : l.map lowerByte = m := by
      apply List.ext_getElem
      · have := congrArg List.length lowered; simp at this ⊢; omega
      · intro i h1 h2
        apply UScalar.eq_of_val_eq
        have hl : i < l.length := by simpa using h1
        have b := congrArg (fun x : List Nat => x[i]?) lowered
        simp only [List.getElem?_map, List.getElem?_eq_getElem hl, List.getElem?_eq_getElem h2, Option.map_some,
          Option.some.injEq] at b
        rw [List.getElem_map, lowerByte_val, b]
    simp only [modelMap, this, modelValue, h, ↓reduceDIte]
    rw [e1, e2, if_neg nonempty, same]
  boolean_lexical := fun t => by
    have := kindOf_typeOf .Boolean
    simp only [typeOf] at this
    simp [modelMap, this, LexicalForm]
  boolean_value := fun t b form => by
    have := kindOf_typeOf .Boolean
    simp only [typeOf] at this
    have h : ∃ b, TruthForm t b := ⟨b, form⟩
    simp only [modelMap, this, modelValue, h, ↓reduceDIte]
    have chosen := Classical.choose_spec h
    rcases form with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      rcases chosen with ⟨e, h1 | h1⟩ | ⟨e, h1 | h1⟩ <;> simp_all

end Rowl.Datatypes
