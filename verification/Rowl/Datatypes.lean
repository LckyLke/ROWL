import Rowl.Strings
import Rowl.FloatOrder
import Mathlib.Data.Rat.Floor

/-!
The actual kernel functions of `datatypes`: the kind of a datatype, the value
of a literal, the order of numbers and the range facets. A value is returned
exactly for a lexical form in the lexical space (an `owl:rational` form only
up to a length the kernel's arithmetic handles), it is canonical, and under
every datatype map that is the OWL 2 map on the datatypes here it is the
literal's value; two canonical values are the same value exactly when they
are equal, a value is in a datatype's value space exactly when the kernel
says so, numbers are ordered exactly, and a range facet holds of a number
exactly when its facet value has the number.
-/
namespace Rowl.Datatypes
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (DatatypeMap)
open Rowl.DatatypeMap
open Rowl.Strings (subtypeOf TextIn)
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

/-- The kinds in the order the kernel tries them. -/
def kindList : List datatypes.Kind :=
  [.Integer, .Decimal, .String, .Plain, .Boolean, .Real, .Rational, .NonNegativeInteger, .NonPositiveInteger,
   .PositiveInteger, .NegativeInteger, .Long, .Int, .Short, .Byte, .UnsignedLong, .UnsignedInt, .UnsignedShort,
   .UnsignedByte, .AnyUri, .HexBinary, .Base64Binary, .NormalizedString, .Token, .Language, .NmToken, .Name,
   .NcName, .DateTime, .DateTimeStamp, .Double, .Float]

/-- The kind at each position of the list. -/
theorem kind_at_eq (i : U8) (h : i.val < 32) :
    datatypes.kind_at i = .ok (kindList.getD i.val .Float) := by
  obtain ⟨⟨⟨n, hn⟩⟩⟩ := i
  have hv : n < 32 := h
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31) with
    e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;>
    subst e <;> rfl

/-- The datatype of a kind. -/
def typeOf : datatypes.Kind → Datatype
  | .Integer => integerType
  | .Decimal => decimalType
  | .String => stringType
  | .Plain => plainType
  | .Boolean => booleanType
  | .Real => realType
  | .Rational => rationalType
  | .NonNegativeInteger => nonNegativeIntegerType
  | .NonPositiveInteger => nonPositiveIntegerType
  | .PositiveInteger => positiveIntegerType
  | .NegativeInteger => negativeIntegerType
  | .Long => longType
  | .Int => intType
  | .Short => shortType
  | .Byte => byteType
  | .UnsignedLong => unsignedLongType
  | .UnsignedInt => unsignedIntType
  | .UnsignedShort => unsignedShortType
  | .UnsignedByte => unsignedByteType
  | .AnyUri => anyUriType
  | .HexBinary => hexBinaryType
  | .Base64Binary => base64BinaryType
  | .NormalizedString => normalizedStringType
  | .Token => tokenType
  | .Language => languageType
  | .NmToken => nmtokenType
  | .Name => nameType
  | .NcName => ncnameType
  | .DateTime => dateTimeType
  | .DateTimeStamp => dateTimeStampType
  | .Double => doubleType
  | .Float => floatType

theorem is_type_correct (iri : alloc.vec.Vec U8) (k : datatypes.Kind) :
    datatypes.is_type iri k = .ok (decide (iri.val = (typeOf k).iri.spelling.val)) := by
  cases k <;> simp [datatypes.is_type, same_pattern_total, Array.to_slice, Array.make, lift, typeOf, integerType,
    decimalType, stringType, plainType, booleanType, realType, rationalType, nonNegativeIntegerType,
    nonPositiveIntegerType, positiveIntegerType, negativeIntegerType, longType, intType, shortType, byteType,
    unsignedLongType, unsignedIntType, unsignedShortType, unsignedByteType, anyUriType, hexBinaryType,
    base64BinaryType, normalizedStringType, tokenType, languageType, nmtokenType, nameType, ncnameType,
    dateTimeType, dateTimeStampType, doubleType, floatType]

/-- Whether the IRI is the spelling of the kind's datatype. -/
def Spelled (iri : List U8) (k : datatypes.Kind) : Bool := decide (iri = (typeOf k).iri.spelling.val)

theorem kind_from_correct (iri : alloc.vec.Vec U8) (i : U8) (h : i.val ≤ 32) :
    datatypes.kind_from iri i = .ok ((kindList.drop i.val).find? (Spelled iri.val)) := by
  rw [datatypes.kind_from]
  by_cases more : i.val < 32
  · have more' : i < (32#u8) := by simp only [UScalar.lt_equiv]; simpa using more
    have split : kindList.drop i.val = kindList.getD i.val .Float :: kindList.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [kindList]; omega), List.getD_eq_getElem]
    rw [split, List.find?_cons, if_pos more', kind_at_eq i more]
    generalize kindList.getD i.val .Float = k
    by_cases found : iri.val = (typeOf k).iri.spelling.val
    · have spelled : Spelled iri.val k = true := by simp [Spelled, found]
      have decided : decide (iri.val = (typeOf k).iri.spelling.val) = true := by simp [found]
      simp only [bind_ok, is_type_correct, decided, ↓reduceIte, spelled]
    · have spelled : Spelled iri.val k = false := by simp [Spelled, found]
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists (U8.add_spec (x := i) (y := 1#u8) (by scalar_tac))
      have nextIs : next.val = i.val + 1 := by simpa using nextValue
      have ih := kind_from_correct iri next (by omega)
      rw [nextIs] at ih
      simp only [bind_ok, is_type_correct, found, decide_false, Bool.false_eq_true, ↓reduceIte, spelled, advance, ih]
  · have done : i.val = 32 := by omega
    have notMore : ¬ i < (32#u8) := by simp only [UScalar.lt_equiv]; simp; omega
    simp [notMore, done, kindList]
termination_by 32 - i.val
decreasing_by omega

/-- The kind of one of the datatypes: the first in the list. -/
noncomputable def kindOf (dt : Datatype) : Option datatypes.Kind := kindList.find? (fun k => decide (dt = typeOf k))

/-- The kernel recognizes exactly the datatypes by their IRIs. -/
theorem kind_of_correct (dt : Datatype) : datatypes.kind_of dt = .ok (kindOf dt) := by
  rw [datatypes.kind_of, kind_from_correct _ _ (by simp)]
  simp only [kindOf, Spelled, datatype_eq_iff]
  rfl

theorem kindOf_typeOf (k : datatypes.Kind) : kindOf (typeOf k) = some k := by
  cases k <;> simp [kindOf, kindList, typeOf, datatype_eq_iff, integerType, decimalType, stringType, plainType,
    booleanType, realType, rationalType, nonNegativeIntegerType, nonPositiveIntegerType, positiveIntegerType,
    negativeIntegerType, longType, intType, shortType, byteType, unsignedLongType, unsignedIntType,
    unsignedShortType, unsignedByteType, anyUriType, hexBinaryType, base64BinaryType, normalizedStringType,
    tokenType, languageType, nmtokenType, nameType, ncnameType, dateTimeType, dateTimeStampType, doubleType,
    floatType]

theorem kindOf_some {dt : Datatype} {k : datatypes.Kind} (h : kindOf dt = some k) : dt = typeOf k := by
  have := List.find?_some h
  simpa using this

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

/-! ### Rational numbers in lowest terms -/

/-- The number a fraction writes: its sign, its numerator and its denominator. -/
def fractionOf (negative : Bool) (numerator denominator : List U8) : ℚ :=
  (if negative then -1 else 1) * ((digitsValue numerator : ℚ) / digitsValue denominator)

/-- A rational number that is not a decimal, written in lowest terms: canonical
    numerator and denominator, the numerator not zero, the denominator positive,
    no common divisor but 1, and the denominator no product of powers of 2 and
    5. -/
def CanonicalFraction (numerator denominator : List U8) : Prop :=
  Rowl.Numbers.Canonical numerator ∧ Rowl.Numbers.Canonical denominator ∧ numerator ≠ [] ∧
    0 < digitsValue denominator ∧ Nat.Coprime (digitsValue numerator) (digitsValue denominator) ∧
    ∀ a b : ℕ, digitsValue denominator ≠ 2 ^ a * 5 ^ b

/-- The divisors of a power of ten are the products of powers of 2 and 5. -/
theorem dvd_ten_power {d m : ℕ} (h : d ∣ 10 ^ m) : ∃ a b, d = 2 ^ a * 5 ^ b := by
  have split : (10 : ℕ) ^ m = 2 ^ m * 5 ^ m := by rw [← mul_pow]; norm_num
  rw [split] at h
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨a, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨b, _, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hz
  exact ⟨a, b, rfl⟩

/-- A canonical fraction writes no decimal number. -/
theorem fraction_not_decimal {negative : Bool} {a b : List U8} (c : CanonicalFraction a b) :
    ¬ IsDecimal (fractionOf negative a b) := by
  rintro ⟨z, m, hz⟩
  obtain ⟨_, _, _, positive, coprime, notPower⟩ := c
  have bq : (digitsValue b : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
  have pq : (10 : ℚ) ^ m ≠ 0 := by positivity
  have key : ((digitsValue a : ℚ) * 10 ^ m) = (((if negative then -z else z : ℤ)) : ℚ) * digitsValue b := by
    unfold fractionOf at hz
    split at hz
    · rw [if_pos (by assumption)]
      field_simp at hz
      push_cast
      linarith
    · rw [if_neg (by assumption)]
      field_simp at hz
      linarith
  have keyZ : (digitsValue a : ℤ) * 10 ^ m = (if negative then -z else z) * digitsValue b := by exact_mod_cast key
  have divides : (digitsValue b : ℤ) ∣ (digitsValue a : ℤ) * 10 ^ m := ⟨_, by rw [keyZ, mul_comm]⟩
  have dividesN : digitsValue b ∣ digitsValue a * 10 ^ m := by exact_mod_cast divides
  have power : digitsValue b ∣ 10 ^ m := (Nat.Coprime.symm coprime).dvd_of_dvd_mul_left dividesN
  obtain ⟨x, y, hxy⟩ := dvd_ten_power power
  exact notPower x y hxy

theorem fractionOf_sign {negative : Bool} {a b : List U8} (c : CanonicalFraction a b) :
    (negative = true → fractionOf negative a b < 0) ∧ (negative = false → 0 < fractionOf negative a b) := by
  obtain ⟨ca, _, nonzero, positive, _, _⟩ := c
  have av : 0 < digitsValue a := by
    have := (Rowl.Numbers.canonical_zero a ca).not.mpr nonzero
    omega
  have quotient : (0 : ℚ) < (digitsValue a : ℚ) / digitsValue b := by
    apply div_pos <;> exact_mod_cast (by assumption)
  constructor
  · intro h; simp [fractionOf, h]; exact quotient
  · intro h; simp [fractionOf, h]; exact quotient

/-- Canonical fractions with the same value are written the same. -/
theorem fractionOf_injective {n1 n2 : Bool} {a1 a2 b1 b2 : List U8}
    (c1 : CanonicalFraction a1 b1) (c2 : CanonicalFraction a2 b2)
    (same : fractionOf n1 a1 b1 = fractionOf n2 a2 b2) : n1 = n2 ∧ a1 = a2 ∧ b1 = b2 := by
  have s1 := fractionOf_sign (negative := n1) c1
  have s2 := fractionOf_sign (negative := n2) c2
  have signs : n1 = n2 := by
    cases n1 <;> cases n2
    · rfl
    · have := s1.2 rfl; have := s2.1 rfl; linarith
    · have := s1.1 rfl; have := s2.2 rfl; linarith
    · rfl
  subst signs
  obtain ⟨ca1, cb1, _, pos1, cop1, _⟩ := c1
  obtain ⟨ca2, cb2, _, pos2, cop2, _⟩ := c2
  have quotients : (digitsValue a1 : ℚ) / digitsValue b1 = (digitsValue a2 : ℚ) / digitsValue b2 := by
    unfold fractionOf at same
    split at same <;> linarith
  have p1 : (digitsValue b1 : ℚ) ≠ 0 := by exact_mod_cast pos1.ne'
  have p2 : (digitsValue b2 : ℚ) ≠ 0 := by exact_mod_cast pos2.ne'
  rw [div_eq_div_iff p1 p2] at quotients
  have cross : digitsValue a1 * digitsValue b2 = digitsValue a2 * digitsValue b1 := by exact_mod_cast quotients
  have d1 : digitsValue b1 ∣ digitsValue b2 := by
    have : digitsValue b1 ∣ digitsValue a1 * digitsValue b2 := ⟨digitsValue a2, by rw [cross, mul_comm]⟩
    exact (Nat.Coprime.symm cop1).dvd_of_dvd_mul_left this
  have d2 : digitsValue b2 ∣ digitsValue b1 := by
    have : digitsValue b2 ∣ digitsValue a2 * digitsValue b1 := ⟨digitsValue a1, by rw [← cross, mul_comm]⟩
    exact (Nat.Coprime.symm cop2).dvd_of_dvd_mul_left this
  have bs : digitsValue b1 = digitsValue b2 := Nat.dvd_antisymm d1 d2
  have nums : digitsValue a1 = digitsValue a2 := by
    rw [bs] at cross
    exact Nat.eq_of_mul_eq_mul_right pos2 cross
  exact ⟨rfl, Rowl.Numbers.canonical_unique _ _ ca1 ca2 nums, Rowl.Numbers.canonical_unique _ _ cb1 cb2 bs⟩

/-- A canonical fraction is no canonical decimal number. -/
theorem fraction_ne_number {negative n : Bool} {a b w f : List U8} (c : CanonicalFraction a b) :
    fractionOf negative a b ≠ numberOf n w f := fun same =>
  fraction_not_decimal c (same ▸ numberOf_decimal n w f)

/-! ### Reading `owl:rational` lexical forms -/

theorem all_digits_correct (bytes : alloc.vec.Vec U8) :
    datatypes.all_digits bytes = .ok (decide (bytes.val ≠ [] ∧ Digits bytes.val)) := by
  rw [datatypes.all_digits, digits_from_correct bytes 0#usize (alloc.vec.Vec.len bytes) (by simp)]
  have whole : segment bytes.val (0#usize : Usize).val (alloc.vec.Vec.len bytes).val = bytes.val := by
    simpa using segment_whole bytes.val
  rw [whole]
  by_cases empty : bytes.val = []
  · simp [UScalar.lt_equiv, empty]
  · have : 0 < bytes.val.length := List.length_pos_iff.mpr empty
    simp [UScalar.lt_equiv, empty, this]

theorem is_one_correct (digits : alloc.vec.Vec U8) :
    datatypes.is_one digits = .ok (decide (digits.val = [49#u8])) := by
  rw [datatypes.is_one]
  by_cases one : digits.val.length = 1
  · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp one
    have lookup : digits.index_usize 0#usize = .ok x := by simp [alloc.vec.Vec.index_usize, hx]
    have lenIs : alloc.vec.Vec.len digits = 1#usize := by apply UScalar.eq_of_val_eq; simpa using one
    simp [lenIs, alloc.vec.Vec.index_slice_index, lookup, hx]
  · have lenIs : alloc.vec.Vec.len digits ≠ 1#usize := by
      intro h; apply one; simpa using congrArg UScalar.val h
    have notOne : digits.val ≠ [49#u8] := fun h => one (by simp [h])
    simp [lenIs, notOne]

theorem zeros_correct (count : Usize) (out : alloc.vec.Vec U8) (room : out.val.length + count.val ≤ Usize.max) :
    ∃ v, datatypes.zeros count out = .ok v ∧ v.val = out.val ++ List.replicate count.val 48#u8 := by
  rw [datatypes.zeros]
  by_cases positive : 0 < count.val
  · have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out 48#u8 short)
    obtain ⟨less, lessRun, lessValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := count) (y := 1#usize) (by scalar_tac))
    have lessIs : less.val = count.val - 1 := by simp at lessValue; omega
    obtain ⟨v, run, value⟩ := zeros_correct less pushed (by rw [contents, lessIs]; simp; omega)
    have pos' : (0#usize) < count := by simp only [UScalar.lt_equiv]; simpa using positive
    refine ⟨v, by simp [pos', short, push, lessRun, run], ?_⟩
    rw [value, contents, lessIs]
    have : count.val = (count.val - 1) + 1 := by omega
    conv_rhs => rw [this, List.replicate_succ]
    simp
  · have zero : count.val = 0 := by omega
    have notPos : ¬ (0#usize) < count := by simp only [UScalar.lt_equiv]; simpa using zero
    exact ⟨out, by simp [notPos], by simp [zero]⟩
termination_by count.val
decreasing_by omega

/-- A decimal number from its digits and the number of its fraction digits. -/
theorem decimal_of_correct (negative : Bool) (digits : alloc.vec.Vec U8) (dd : Digits digits.val) (places : Usize)
    (room : places.val + digits.val.length < Usize.max) :
    ∃ n w f, datatypes.decimal_of negative digits places = .ok (.Number n w f) ∧ CanonicalNumber n w.val f.val ∧
      numberOf n w.val f.val = (if negative then -1 else 1) * ((digitsValue digits.val : ℚ) / 10 ^ places.val) := by
  rw [datatypes.decimal_of]
  by_cases before : places.val < digits.val.length
  · obtain ⟨split, splitRun, splitValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len digits) (y := places) (by simp; omega))
    have splitIs : split.val = digits.val.length - places.val := by simp at splitValue; omega
    obtain ⟨n, w, f, run, canonical, value⟩ := number_from_correct digits negative 0#usize split split
      (by simp) (by omega) (by omega) (by rw [splitIs]; exact fun b m => dd b (by
        simp [segment] at m; exact List.mem_of_mem_take m))
      (by rw [splitIs]; exact fun b m => dd b (by
        simp [segment] at m; exact List.mem_of_mem_drop m))
    refine ⟨n, w, f, by simp [UScalar.lt_equiv, before, splitRun, run], canonical, ?_⟩
    rw [value, splitIs]
    have takeIs : segment digits.val (0#usize : Usize).val (digits.val.length - places.val) =
        digits.val.take (digits.val.length - places.val) := by simp [segment]
    have dropIs : segment digits.val (digits.val.length - places.val) digits.val.length =
        digits.val.drop (digits.val.length - places.val) := segment_drop _ _
    rw [takeIs, dropIs]
    have dropLen : (digits.val.drop (digits.val.length - places.val)).length = places.val := by simp; omega
    rw [dropLen]
    have whole := Rowl.Numbers.value_append (digits.val.take (digits.val.length - places.val))
      (digits.val.drop (digits.val.length - places.val))
    rw [List.take_append_drop, dropLen] at whole
    rw [whole]
    have pos : (10 : ℚ) ^ places.val ≠ 0 := by positivity
    push_cast
    field_simp
  · obtain ⟨gap, gapRun, gapValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := places) (y := alloc.vec.Vec.len digits) (by simp; omega))
    have gapIs : gap.val = places.val - digits.val.length := by simp at gapValue; omega
    obtain ⟨padded, paddedRun, paddedValue⟩ := zeros_correct gap (alloc.vec.Vec.new U8) (by simp; omega)
    obtain ⟨written, writtenRun, writtenValue⟩ := copy_range_correct digits 0#usize (alloc.vec.Vec.len digits)
      padded (by simp) (by rw [paddedValue, gapIs]; simp; omega)
    have writtenIs : written.val = List.replicate (places.val - digits.val.length) 48#u8 ++ digits.val := by
      rw [writtenValue, paddedValue, gapIs]
      simp [new_val, segment_whole]
    have writtenLen : written.val.length = places.val := by rw [writtenIs]; simp; omega
    have writtenDigits : Digits written.val := by
      rw [writtenIs]
      intro b m
      rcases List.mem_append.mp m with z | d
      · rw [(List.mem_replicate.mp z).2]; constructor <;> decide
      · exact dd b d
    obtain ⟨last, lastRun, l1, l2, trailing, lastStop⟩ := trim_zeros_correct written 0#usize
      (alloc.vec.Vec.len written) (by simp) (by simp)
    obtain ⟨fraction, fractionRun, fractionValue⟩ := copy_range_correct written 0#usize last
      (alloc.vec.Vec.new U8) (by simp at l2; omega) (by simp [new_val]; scalar_tac)
    have fractionIs : fraction.val = written.val.take last.val := by
      rw [fractionValue]; simp [new_val, segment]
    let n := negative && decide (0 < fraction.val.length)
    refine ⟨n, alloc.vec.Vec.new U8, fraction, ?_, ?_, ?_⟩
    · have notBefore : ¬ places < alloc.vec.Vec.len digits := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact before
      cases negative <;> simp [notBefore, gapRun, paddedRun, writtenRun, lastRun, fractionRun, n, UScalar.lt_equiv]
    · refine ⟨by simp [new_val, Digits], ?_, by simp [new_val], ?_, ?_⟩
      · rw [fractionIs]; exact fun b m => writtenDigits b (List.mem_of_mem_take m)
      · rw [fractionIs]
        intro h
        have nonempty : 0 < last.val := by
          by_contra zero
          have : last.val = 0 := by omega
          simp [this] at h
        have := lastStop ⟨by simpa using nonempty, l2⟩
        rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by simp at l2; omega),
          List.getElem?_take] at h
        simp only [show last.val - 1 < last.val by omega, ↓reduceIte, List.getElem?_eq_getElem
          (show last.val - 1 < written.val.length by simp at l2; omega), Option.some.injEq] at h
        exact this h
      · intro isNeg
        right
        simp only [n, Bool.and_eq_true, decide_eq_true_eq] at isNeg
        exact List.length_pos_iff.mp isNeg.2
    · have l2' : last.val ≤ written.val.length := by simpa using l2
      have splitW : written.val = written.val.take last.val ++ written.val.drop last.val :=
        (List.take_append_drop _ _).symm
      have dropZeros : ∀ b ∈ written.val.drop last.val, b = 48#u8 := by
        have := trailing
        simp only [segment] at this
        intro b m
        exact this b (by simpa using m)
      have dropValue : digitsValue (written.val.drop last.val) = 0 := by
        have := Rowl.Numbers.value_zeros_append (written.val.drop last.val) [] (by simpa using dropZeros)
        simpa [Rowl.Numbers.value_nil] using this
      have writtenValue' : digitsValue written.val = digitsValue digits.val := by
        rw [writtenIs]
        exact Rowl.Numbers.value_zeros_append _ _ (fun b m => (List.mem_replicate.mp m).2)
      have whole : digitsValue written.val = digitsValue (written.val.take last.val) * 10 ^ (places.val - last.val) := by
        conv_lhs => rw [splitW]
        rw [Rowl.Numbers.value_append, dropValue]
        simp [writtenLen]
      rw [← writtenValue', whole, fractionIs]
      have takeLen : (written.val.take last.val).length = last.val := by simp; omega
      simp only [numberOf, new_val, digitsValue, List.foldl_nil, Nat.cast_zero, zero_add]
      have pos1 : (10 : ℚ) ^ last.val ≠ 0 := by positivity
      have pos2 : (10 : ℚ) ^ places.val ≠ 0 := by positivity
      have split : (10 : ℚ) ^ places.val = 10 ^ (places.val - last.val) * 10 ^ last.val := by
        rw [← pow_add]; congr 1; omega
      rw [takeLen, split]
      by_cases empty : 0 < fraction.val.length
      · have : n = negative := by simp [n, empty]
        rw [this]
        push_cast
        field_simp
      · have zero : fraction.val = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [fractionIs] at zero
        rw [zero]
        simp [n]

/-- Dividing out the factors 2 and 5 of a number. -/
theorem strip_factors_correct (digits : alloc.vec.Vec U8) (cd : Rowl.Numbers.Canonical digits.val) (count : Usize)
    (small : 2 * digits.val.length + 8 < Usize.max)
    (bound : digitsValue digits.val < 2 ^ (Usize.max - 1 - count.val)) (hcount : count.val < Usize.max) :
    ∃ rest places, datatypes.strip_factors digits count = .ok (rest, places) ∧ Rowl.Numbers.Canonical rest.val ∧
      count.val ≤ places.val ∧
      (∃ a b, a + b = places.val - count.val ∧ digitsValue digits.val = digitsValue rest.val * (2 ^ a * 5 ^ b)) ∧
      (0 < digitsValue digits.val → ¬ 2 ∣ digitsValue rest.val ∧ ¬ 5 ∣ digitsValue rest.val) ∧
      rest.val.length ≤ digits.val.length := by
  rw [datatypes.strip_factors]
  have hcount' : count < core.num.Usize.MAX := by
    simp only [UScalar.lt_equiv]; simpa [core.num.Usize.MAX] using hcount
  simp only [hcount', ↓reduceIte]
  rw [datatypes.strip_by]
  obtain ⟨two, twoRun, twoValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 50#u8 (by simp [new_val]; scalar_tac))
  obtain ⟨five, fiveRun, fiveValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 53#u8 (by simp [new_val]; scalar_tac))
  have twoIs : two.val = [50#u8] := by rw [twoValue]; simp [new_val]
  have fiveIs : five.val = [53#u8] := by rw [fiveValue]; simp [new_val]
  have ctwo : Rowl.Numbers.Canonical two.val := by
    rw [twoIs]; refine ⟨fun b m => ?_, by simp⟩
    simp only [List.mem_singleton] at m; subst m; constructor <;> decide
  have cfive : Rowl.Numbers.Canonical five.val := by
    rw [fiveIs]; refine ⟨fun b m => ?_, by simp⟩
    simp only [List.mem_singleton] at m; subst m; constructor <;> decide
  have twoV : digitsValue two.val = 2 := by rw [twoIs]; rfl
  have fiveV : digitsValue five.val = 5 := by rw [fiveIs]; rfl
  obtain ⟨half, rest2, halfRun, ch, c2, halfValue, rest2Value, halfLen, _⟩ :=
    Rowl.Numbers.divide_naturals_spec digits two cd.1 ctwo (by rw [twoV]; norm_num) (by rw [twoIs]; simp; omega)
  obtain ⟨fifth, rest5, fifthRun, cf, c5, fifthValue, rest5Value, fifthLen, _⟩ :=
    Rowl.Numbers.divide_naturals_spec digits five cd.1 cfive (by rw [fiveV]; norm_num) (by rw [fiveIs]; simp; omega)
  rw [twoV] at halfValue rest2Value
  rw [fiveV] at fifthValue rest5Value
  by_cases nonempty : 0 < digits.val.length
  · have positive : 0 < digitsValue digits.val := by
      have := (Rowl.Numbers.canonical_zero digits.val cd).not.mpr (by
        intro h; simp [h] at nonempty)
      omega
    have room : 1 ≤ Usize.max - 1 - count.val := by
      by_contra none
      have : Usize.max - 1 - count.val = 0 := by omega
      rw [this] at bound
      simp at bound
      omega
    have oneVal : (1#usize : Usize).val = 1 := rfl
    obtain ⟨next, nextRun, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := count) (y := 1#usize) (by rw [oneVal]; omega))
    have nextIs : next.val = count.val + 1 := by rw [nextValue, oneVal]
    have pos' : (0#usize) < alloc.vec.Vec.len digits := by simp [UScalar.lt_equiv, nonempty]
    have decreaseHalf : digitsValue half.val < digitsValue digits.val := by rw [halfValue]; omega
    have decreaseFifth : digitsValue fifth.val < digitsValue digits.val := by rw [fifthValue]; omega
    by_cases even : rest2.val.length = 0
    · have rest2Zero : digitsValue digits.val % 2 = 0 := by
        rw [← rest2Value, List.eq_nil_of_length_eq_zero even]; rfl
      have evenLen : alloc.vec.Vec.len rest2 = 0#usize := by apply UScalar.eq_of_val_eq; simpa using even
      obtain ⟨rest, places, run, cr, low, ⟨a, b, sum, value⟩, coprime, len⟩ :=
        strip_factors_correct half ch next (by omega)
          (by
            rw [halfValue, nextIs]
            have : Usize.max - 1 - count.val = (Usize.max - 1 - (count.val + 1)) + 1 := by omega
            rw [this, pow_succ] at bound
            omega)
          (by omega)
      refine ⟨rest, places, by simp [twoRun, fiveRun, halfRun, fifthRun, pos', evenLen, nextRun, run], cr,
        by omega, ⟨a + 1, b, by omega, ?_⟩, fun _ => coprime (by rw [halfValue]; omega), by omega⟩
      have : digitsValue digits.val = 2 * (digitsValue digits.val / 2) := by omega
      rw [this, ← halfValue, value]
      ring
    · have notEven : alloc.vec.Vec.len rest2 ≠ 0#usize := by
        intro h; apply even; simpa using congrArg UScalar.val h
      by_cases byFive : rest5.val.length = 0
      · have rest5Zero : digitsValue digits.val % 5 = 0 := by
          rw [← rest5Value, List.eq_nil_of_length_eq_zero byFive]; rfl
        have fiveLen : alloc.vec.Vec.len rest5 = 0#usize := by apply UScalar.eq_of_val_eq; simpa using byFive
        obtain ⟨rest, places, run, cr, low, ⟨a, b, sum, value⟩, coprime, len⟩ :=
          strip_factors_correct fifth cf next (by omega)
            (by
              rw [fifthValue, nextIs]
              have : Usize.max - 1 - count.val = (Usize.max - 1 - (count.val + 1)) + 1 := by omega
              rw [this, pow_succ] at bound
              omega)
            (by omega)
        refine ⟨rest, places, by simp [twoRun, fiveRun, halfRun, fifthRun, pos', notEven, fiveLen, nextRun, run],
          cr, by omega, ⟨a, b + 1, by omega, ?_⟩, fun _ => coprime (by rw [fifthValue]; omega), by omega⟩
        have : digitsValue digits.val = 5 * (digitsValue digits.val / 5) := by omega
        rw [this, ← fifthValue, value]
        ring
      · have notFive : alloc.vec.Vec.len rest5 ≠ 0#usize := by
          intro h; apply byFive; simpa using congrArg UScalar.val h
        have r2 : digitsValue rest2.val ≠ 0 := fun h =>
          even (by rw [(Rowl.Numbers.canonical_zero _ c2).mp h]; rfl)
        have r5 : digitsValue rest5.val ≠ 0 := fun h =>
          byFive (by rw [(Rowl.Numbers.canonical_zero _ c5).mp h]; rfl)
        refine ⟨digits, count, by simp [twoRun, fiveRun, halfRun, fifthRun, pos', notEven, notFive], cd, le_rfl,
          ⟨0, 0, by simp, by simp⟩, fun _ => ⟨fun h => r2 ?_, fun h => r5 ?_⟩, le_rfl⟩
        · rw [rest2Value]; exact Nat.dvd_iff_mod_eq_zero.mp h
        · rw [rest5Value]; exact Nat.dvd_iff_mod_eq_zero.mp h
  · have notPos : ¬ (0#usize) < alloc.vec.Vec.len digits := by
      simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simpa using nonempty
    have empty : digits.val = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨digits, count, by simp [twoRun, fiveRun, halfRun, fifthRun, notPos], cd, le_rfl,
      ⟨0, 0, by simp, by simp⟩, fun h => by simp [empty, Rowl.Numbers.value_nil] at h, le_rfl⟩
termination_by digitsValue digits.val
decreasing_by all_goals first | exact decreaseHalf | exact decreaseFifth

/-- What a numeric value of the kernel is: a canonical decimal number or a
    canonical fraction, with its rational value. -/
def NumberValue (v : datatypes.DataValue) (q : ℚ) : Prop :=
  (∃ n w f, v = .Number n w f ∧ CanonicalNumber n w.val f.val ∧ numberOf n w.val f.val = q) ∨
  (∃ n a b, v = .Fraction n a b ∧ CanonicalFraction a.val b.val ∧ fractionOf n a.val b.val = q)

theorem ten_power_lt_two (n : ℕ) : 10 ^ n ≤ 2 ^ (4 * n) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by norm_num) n

/-- A quotient of numbers without a common divisor: a decimal number when the
    denominator divides a power of ten, and otherwise a fraction. -/
theorem lowest_value_correct (negative : Bool) (numerator denominator : alloc.vec.Vec U8)
    (cn : Rowl.Numbers.Canonical numerator.val) (cd : Rowl.Numbers.Canonical denominator.val)
    (positive : 0 < digitsValue denominator.val)
    (coprime : Nat.Coprime (digitsValue numerator.val) (digitsValue denominator.val))
    (small : 8 * (numerator.val.length + denominator.val.length) + 16 < Usize.max) :
    ∃ v, datatypes.lowest_value negative numerator denominator = .ok v ∧
      NumberValue v ((if negative then -1 else 1) * ((digitsValue numerator.val : ℚ) / digitsValue denominator.val)) := by
  rw [datatypes.lowest_value]
  obtain ⟨copy, copyRun, copyValue⟩ := copy_range_correct denominator 0#usize (alloc.vec.Vec.len denominator)
    (alloc.vec.Vec.new U8) (by simp) (by simp [new_val])
  have copyIs : copy.val = denominator.val := by rw [copyValue]; simp [new_val, segment_whole]
  have bound : digitsValue copy.val < 2 ^ (Usize.max - 1 - (0#usize : Usize).val) := by
    rw [copyIs]
    have h1 := Rowl.Numbers.value_lt denominator.val cd.1
    have h2 := ten_power_lt_two denominator.val.length
    have h3 : 2 ^ (4 * denominator.val.length) ≤ 2 ^ (Usize.max - 1 - (0#usize : Usize).val) :=
      Nat.pow_le_pow_right (by norm_num) (by simp; omega)
    omega
  obtain ⟨rest, places, stripRun, cr, _, ⟨a, b, sum, factors⟩, odd, restLen⟩ :=
    strip_factors_correct copy (by rw [copyIs]; exact cd) 0#usize (by rw [copyIs]; omega) bound (by simp; scalar_tac)
  rw [copyIs] at factors
  have zeroVal : ((0#usize : Usize).val) = 0 := rfl
  rw [zeroVal, Nat.sub_zero] at sum
  have restPos : 0 < digitsValue rest.val := by
    by_contra zero
    have : digitsValue rest.val = 0 := by omega
    rw [this, zero_mul] at factors
    omega
  have placesBound : places.val < 4 * denominator.val.length + 1 := by
    have h1 := Rowl.Numbers.value_lt denominator.val cd.1
    have h2 := ten_power_lt_two denominator.val.length
    have h3 : 2 ^ places.val ≤ digitsValue denominator.val := by
      rw [factors, ← sum, pow_add]
      have : 2 ^ b ≤ 5 ^ b := Nat.pow_le_pow_left (by norm_num) b
      calc 2 ^ a * 2 ^ b ≤ 1 * (2 ^ a * 5 ^ b) := by rw [one_mul]; exact Nat.mul_le_mul_left _ this
        _ ≤ digitsValue rest.val * (2 ^ a * 5 ^ b) := Nat.mul_le_mul_right _ restPos
    have : 2 ^ places.val < 2 ^ (4 * denominator.val.length) := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
    omega
  by_cases one : rest.val = [49#u8]
  · have restOne : digitsValue rest.val = 1 := by rw [one]; rfl
    rw [restOne, one_mul] at factors
    obtain ⟨scaled, scaledRun, sc, scaledValue, scaledLen⟩ := Rowl.Numbers.times_power_spec numerator cn places
      (by omega)
    have divides : digitsValue denominator.val ∣ digitsValue scaled.val := by
      rw [scaledValue, factors]
      apply Dvd.dvd.mul_left
      rw [show (10 : ℕ) ^ places.val = 2 ^ places.val * 5 ^ places.val by rw [← mul_pow]; norm_num]
      exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (Nat.pow_dvd_pow 5 (by omega))
    obtain ⟨digits, remainder, divRun, cdig, _, digitsValue', _, digitsLen, _⟩ :=
      Rowl.Numbers.divide_naturals_spec scaled denominator sc.1 cd positive (by omega)
    obtain ⟨n, w, f, decRun, canonical, value⟩ := decimal_of_correct negative digits cdig.1 places
      (by have := Nat.le_trans digitsLen scaledLen; omega)
    refine ⟨.Number n w f, by simp [copyRun, stripRun, is_one_correct, one, scaledRun, divRun, decRun],
      .inl ⟨n, w, f, rfl, canonical, ?_⟩⟩
    rw [value, digitsValue']
    have exact : digitsValue scaled.val / digitsValue denominator.val * digitsValue denominator.val =
        digitsValue scaled.val := Nat.div_mul_cancel divides
    have dq : (digitsValue denominator.val : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
    have pq : (10 : ℚ) ^ places.val ≠ 0 := by positivity
    have quotientQ : ((digitsValue scaled.val / digitsValue denominator.val : ℕ) : ℚ) =
        (digitsValue scaled.val : ℚ) / digitsValue denominator.val := by
      rw [eq_div_iff dq]; exact_mod_cast exact
    rw [quotientQ, scaledValue]
    push_cast
    field_simp
  · have notOne : digitsValue rest.val ≠ 1 := by
      intro h
      apply one
      exact Rowl.Numbers.canonical_unique _ _ cr ⟨fun x m => by
        simp only [List.mem_singleton] at m; subst m; constructor <;> decide, by simp⟩ (by rw [h]; rfl)
    have numeratorNonzero : numerator.val ≠ [] := by
      intro empty
      have zero : digitsValue numerator.val = 0 := by rw [empty]; rfl
      rw [zero, Nat.coprime_zero_left] at coprime
      rw [coprime] at factors
      have : digitsValue rest.val = 1 := by
        rcases Nat.eq_zero_or_pos (digitsValue rest.val) with h | h
        · omega
        · have := Nat.eq_one_of_mul_eq_one_right factors.symm; exact this
      exact notOne this
    have notPower : ∀ x y : ℕ, digitsValue denominator.val ≠ 2 ^ x * 5 ^ y := by
      intro x y same
      have dividesRest : digitsValue rest.val ∣ 10 ^ (x + y) := by
        have : digitsValue rest.val ∣ 2 ^ x * 5 ^ y := ⟨2 ^ a * 5 ^ b, by rw [← same, factors]⟩
        apply Nat.dvd_trans this
        rw [show (10 : ℕ) ^ (x + y) = 2 ^ (x + y) * 5 ^ (x + y) by rw [← mul_pow]; norm_num]
        exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) (Nat.pow_dvd_pow 5 (by omega))
      obtain ⟨c, e, hce⟩ := dvd_ten_power dividesRest
      obtain ⟨no2, no5⟩ := odd (by rw [copyIs]; exact positive)
      have c0 : c = 0 := by
        by_contra nz
        exact no2 (by rw [hce]; exact Dvd.dvd.mul_right (dvd_pow_self 2 nz) _)
      have e0 : e = 0 := by
        by_contra nz
        exact no5 (by rw [hce]; exact Dvd.dvd.mul_left (dvd_pow_self 5 nz) _)
      rw [c0, e0] at hce
      exact notOne (by simpa using hce)
    let sign := negative && decide (0 < numerator.val.length)
    have signIs : sign = negative := by
      simp [sign, List.length_pos_iff.mpr numeratorNonzero]
    refine ⟨.Fraction sign numerator denominator, ?_, .inr ⟨sign, numerator, denominator, rfl,
      ⟨cn, cd, numeratorNonzero, positive, coprime, notPower⟩, by rw [signIs]; rfl⟩⟩
    cases negative <;> simp [copyRun, stripRun, is_one_correct, one, sign]

theorem quotient_value_correct (negative : Bool) (numerator denominator : alloc.vec.Vec U8)
    (cn : Rowl.Numbers.Canonical numerator.val) (cd : Rowl.Numbers.Canonical denominator.val)
    (positive : 0 < digitsValue denominator.val)
    (small : 8 * (numerator.val.length + denominator.val.length) + 16 < Usize.max) :
    ∃ v, datatypes.quotient_value negative numerator denominator = .ok v ∧
      NumberValue v ((if negative then -1 else 1) * ((digitsValue numerator.val : ℚ) / digitsValue denominator.val)) := by
  rw [datatypes.quotient_value]
  obtain ⟨common, gcdRun, cg, gValue, gLen⟩ := Rowl.Numbers.gcd_naturals_spec numerator denominator cn cd
    (by omega) (by omega)
  have gPos : 0 < digitsValue common.val := by
    rw [gValue]; exact Nat.gcd_pos_of_pos_right _ positive
  obtain ⟨top, r1, topRun, ct, _, topValue, _, topLen, _⟩ := Rowl.Numbers.divide_naturals_spec numerator common
    cn.1 cg gPos (by have := Nat.max_le.mp (le_refl (max numerator.val.length denominator.val.length)); omega)
  obtain ⟨bottom, r2, bottomRun, cb, _, bottomValue, _, bottomLen, _⟩ := Rowl.Numbers.divide_naturals_spec
    denominator common cd.1 cg gPos
    (by have := Nat.max_le.mp (le_refl (max numerator.val.length denominator.val.length)); omega)
  have dvdN : digitsValue common.val ∣ digitsValue numerator.val := by rw [gValue]; exact Nat.gcd_dvd_left _ _
  have dvdD : digitsValue common.val ∣ digitsValue denominator.val := by rw [gValue]; exact Nat.gcd_dvd_right _ _
  have bottomPos : 0 < digitsValue bottom.val := by
    rw [bottomValue]; exact Nat.div_pos (Nat.le_of_dvd positive dvdD) gPos
  have coprime : Nat.Coprime (digitsValue top.val) (digitsValue bottom.val) := by
    rw [topValue, bottomValue, gValue]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ positive)
  obtain ⟨v, run, value⟩ := lowest_value_correct negative top bottom ct cb bottomPos coprime (by omega)
  refine ⟨v, by simp [gcdRun, topRun, bottomRun, run], ?_⟩
  have same : (digitsValue top.val : ℚ) / digitsValue bottom.val =
      (digitsValue numerator.val : ℚ) / digitsValue denominator.val := by
    obtain ⟨k, hk⟩ := dvdN
    obtain ⟨l, hl⟩ := dvdD
    rw [topValue, bottomValue, hk, hl, Nat.mul_div_cancel_left _ gPos, Nat.mul_div_cancel_left _ gPos]
    have gq : (digitsValue common.val : ℚ) ≠ 0 := by exact_mod_cast gPos.ne'
    push_cast
    field_simp
  rw [same] at value
  exact value

theorem over_value_correct (negative : Bool) (numerator written : alloc.vec.Vec U8)
    (cn : Rowl.Numbers.Canonical numerator.val)
    (small : 8 * (numerator.val.length + written.val.length) + 16 < Usize.max) :
    ∃ r, datatypes.over_value negative numerator written = .ok r ∧
      (∀ v, r = some v → Digits written.val ∧ 0 < digitsValue written.val ∧
        NumberValue v ((if negative then -1 else 1) * ((digitsValue numerator.val : ℚ) / digitsValue written.val))) ∧
      (r = none → ¬ (Digits written.val ∧ 0 < digitsValue written.val)) := by
  rw [datatypes.over_value, all_digits_correct]
  by_cases shape : written.val ≠ [] ∧ Digits written.val
  · obtain ⟨den, denRun, cden, denValue, denLen⟩ := Rowl.Numbers.canonical_spec written shape.2
    by_cases nonzero : 0 < den.val.length
    · have denPos : 0 < digitsValue den.val :=
        Nat.pos_of_ne_zero (fun z => by
          have := (Rowl.Numbers.canonical_zero _ cden).mp z
          simp [this] at nonzero)
      obtain ⟨v, run, value⟩ := quotient_value_correct negative numerator den cn cden denPos (by omega)
      have nonzero' : (0#usize) < alloc.vec.Vec.len den := by simp [UScalar.lt_equiv, nonzero]
      have decided : decide (written.val ≠ [] ∧ Digits written.val) = true := decide_eq_true shape
      refine ⟨some v, by simp only [decided, ↓reduceIte, bind_ok, denRun, nonzero', run], fun v' h => ?_, by simp⟩
      cases h
      refine ⟨shape.2, by rw [← denValue]; exact denPos, ?_⟩
      rw [← denValue]; exact value
    · have notPos : ¬ (0#usize) < alloc.vec.Vec.len den := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; simpa using nonzero
      have decided : decide (written.val ≠ [] ∧ Digits written.val) = true := decide_eq_true shape
      refine ⟨none, by simp only [decided, ↓reduceIte, bind_ok, denRun, notPos], by simp, fun _ ⟨_, pos⟩ => ?_⟩
      have empty : den.val = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [← denValue, empty] at pos
      exact absurd pos (by decide)
  · have decided : decide (written.val ≠ [] ∧ Digits written.val) = false := decide_eq_false shape
    refine ⟨none, by simp only [decided, bind_ok, Bool.false_eq_true, ↓reduceIte], by simp,
      fun _ ⟨digits, pos⟩ => shape ⟨?_, digits⟩⟩
    intro empty; rw [empty] at pos; exact absurd pos (by decide)

theorem short_correct (bytes : alloc.vec.Vec U8) :
    datatypes.short bytes = .ok (decide (bytes.val.length < Usize.max / 16)) := by
  rw [datatypes.short]
  obtain ⟨q, run, value⟩ := UScalar.div_spec core.num.Usize.MAX (y := 16#usize) (by simp)
  have qIs : q.val = Usize.max / 16 := by rw [value]; simp [core.num.Usize.MAX]
  simp [run, UScalar.lt_equiv, qIs]

/-- An integer lexical form has no `/`. -/
theorem no_slash_of_integer {text : List U8} {q : ℚ} (form : IntegerForm text q) : 47#u8 ∉ text := by
  obtain ⟨sign, whole, hs, hw, _, rfl, _⟩ := form
  intro m
  rcases List.mem_append.mp m with s | w
  · rcases hs with rfl | rfl | rfl <;> simp at s
  · have := hw _ w
    simp [Digit] at this

/-- The first `/` of a lexical form `numerator/denominator` is the one after
    the numerator. -/
theorem first_slash {text numerator denominator : List U8} (split : text = numerator ++ 47#u8 :: denominator)
    (clean : 47#u8 ∉ numerator) (r : Nat) (bound : r ≤ text.length)
    (before : ∀ i (h : i < text.length), i < r → text[i] ≠ 47#u8)
    (at_r : ∀ h : r < text.length, text[r] = 47#u8) : r = numerator.length := by
  have hlen : numerator.length < text.length := by rw [split]; simp
  have atSlash : text[numerator.length] = 47#u8 := by simp [split]
  rcases Nat.lt_trichotomy r numerator.length with less | same | more
  · have := at_r (by omega)
    have inside : text[r] = numerator[r] := by simp [split, List.getElem_append_left less]
    rw [inside] at this
    exact absurd (this ▸ List.getElem_mem less) clean
  · exact same
  · exact absurd atSlash (before _ hlen more)

/-- The canonical digits of an integer lexical form are no longer than it. -/
theorem integer_digits_length {text : List U8} {n : Bool} {w f : List U8} (c : CanonicalNumber n w f)
    (form : IntegerForm text (numberOf n w f)) (ff : f = []) :
    w.length ≤ text.length ∧ digitsValue w < 10 ^ text.length := by
  obtain ⟨sign, whole, hs, hw, _, rfl, value⟩ := form
  subst ff
  have absolute : (digitsValue w : ℚ) = digitsValue whole := by
    have := congrArg abs value
    unfold numberOf signValue at this
    split at this <;> split at this <;> simp [abs_of_nonneg] at this <;> exact_mod_cast this
  have natural : digitsValue w = digitsValue whole := by exact_mod_cast absolute
  have below := Rowl.Numbers.value_lt whole hw
  have len := Rowl.Numbers.canonical_length_le w ⟨c.1, c.2.2.1⟩ whole.length (by omega)
  refine ⟨by simp; omega, ?_⟩
  calc digitsValue w < 10 ^ whole.length := by omega
    _ ≤ 10 ^ (sign ++ whole).length := Nat.pow_le_pow_right (by norm_num) (by simp)

/-- The kernel's reading of `owl:rational` lexical forms is exact: a canonical
    number or fraction exactly for a lexical form `numerator/denominator`, of the
    value it writes, unless the form is too long for the kernel's arithmetic. -/
theorem rational_value_correct (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.rational_value lexical = .ok r ∧
      (∀ v, r = some v → ∃ q, RationalForm lexical.val q ∧ NumberValue v q) ∧
      (r = none → (∀ q, ¬ RationalForm lexical.val q) ∨ Usize.max / 16 ≤ lexical.val.length) := by
  rw [datatypes.rational_value, short_correct]
  obtain ⟨slash, slashRun, slashBound, _, slashBefore, slashAt⟩ := find_byte_correct lexical 47#u8 0#usize
  by_cases short : lexical.val.length < Usize.max / 16
  · by_cases found : slash.val < lexical.val.length
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := slash) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = slash.val + 1 := by simpa using nextValue
      obtain ⟨written, writtenRun, writtenValue⟩ := copy_range_correct lexical next (alloc.vec.Vec.len lexical)
        (alloc.vec.Vec.new U8) (by simp) (by have := lexical.property; simp [new_val]; omega)
      have writtenIs : written.val = lexical.val.drop (slash.val + 1) := by
        rw [writtenValue, nextIs]; simp [new_val, segment_drop]
      obtain ⟨num, numRun, numValue⟩ := copy_range_correct lexical 0#usize slash (alloc.vec.Vec.new U8)
        (by omega) (by have := lexical.property; simp [new_val]; omega)
      have numIs : num.val = lexical.val.take slash.val := by rw [numValue]; simp [new_val, segment]
      have splitText : lexical.val = num.val ++ 47#u8 :: written.val := by
        rw [numIs, writtenIs]
        have := slashAt found
        conv_lhs => rw [← List.take_append_drop slash.val lexical.val]
        rw [List.drop_eq_getElem_cons found, this]
      have lengths : num.val.length + written.val.length < lexical.val.length := by
        rw [splitText]; simp
      have found' : slash < alloc.vec.Vec.len lexical := by simp [UScalar.lt_equiv, found]
      have matching : ∀ numerator denominator, lexical.val = numerator ++ 47#u8 :: denominator →
          47#u8 ∉ numerator → num.val = numerator ∧ written.val = denominator := by
        intro numerator denominator hsplit clean
        have at_slash := first_slash hsplit clean slash.val slashBound
          (fun i h low => slashBefore i h (by simp) low) slashAt
        constructor
        · rw [numIs, hsplit, at_slash]; simp
        · rw [writtenIs, hsplit, at_slash]; simp
      obtain ⟨res, numberRun, someCase, noneCase⟩ := number_value_correct num true
      cases res with
      | none =>
        refine ⟨none, by simp [short, slashRun, found, found', advance, writtenRun, numRun, numberRun], by simp, ?_⟩
        intro _
        left
        intro q ⟨numerator, denominator, p, hsplit, hint, _, _, _⟩
        have same := (matching numerator denominator hsplit (no_slash_of_integer hint)).1
        exact noneCase rfl p (by simp only [NumberForm, ↓reduceIte]; rw [same]; exact hint)
      | some v =>
        obtain ⟨n, w, f, rfl, canonical, form, whole⟩ := someCase _ rfl
        have fEmpty := whole rfl
        have intForm : IntegerForm num.val (numberOf n w.val f.val) := form
        have wLen := (integer_digits_length canonical intForm fEmpty).1
        obtain ⟨over, overRun, overSome, overNone⟩ := over_value_correct n w written
          ⟨canonical.1, canonical.2.2.1⟩ (by omega)
        refine ⟨over, by simp [short, slashRun, found, found', advance, writtenRun, numRun, numberRun, overRun], ?_, ?_⟩
        · intro value h
          obtain ⟨digits, positive, number⟩ := overSome value h
          refine ⟨numberOf n w.val f.val / digitsValue written.val,
            ⟨num.val, written.val, numberOf n w.val f.val, splitText, intForm, digits, positive, rfl⟩, ?_⟩
          have numberIs : numberOf n w.val f.val = (if n then -1 else 1) * (digitsValue w.val : ℚ) := by
            simp [numberOf, fEmpty, Rowl.Numbers.value_nil]
          rw [numberIs, mul_div_assoc]
          exact number
        · intro h
          left
          intro q ⟨numerator, denominator, p, hsplit, hint, digits, positive, _⟩
          obtain ⟨_, same⟩ := matching numerator denominator hsplit (no_slash_of_integer hint)
          exact overNone h ⟨same ▸ digits, same ▸ positive⟩
    · have notFound : ¬ slash < alloc.vec.Vec.len lexical := by simp [UScalar.lt_equiv, found]
      refine ⟨none, by simp [short, slashRun, found, notFound], by simp, fun _ => .inl ?_⟩
      intro q ⟨numerator, denominator, p, hsplit, _, _, _, _⟩
      have atEnd : slash.val = lexical.val.length := by omega
      have inside : numerator.length < lexical.val.length := by rw [hsplit]; simp
      exact slashBefore numerator.length inside (by simp) (by omega) (by simp [hsplit])
  · refine ⟨none, by simp [short, slashRun], by simp, fun _ => .inr (by omega)⟩

/-! ### The order of numbers -/

/-- The order of two rationals as the kernel writes it: 0 when the first is
    smaller, 1 when they are equal, 2 when it is greater. -/
def orderOf (a b : ℚ) : Nat := if a < b then 0 else if a = b then 1 else 2

/-- The value of digits after a decimal point. -/
def fracValue (digits : List U8) : ℚ := (digitsValue digits : ℚ) / 10 ^ digits.length

/-- The magnitude of a number: the absolute value it writes. -/
def magnitude : datatypes.DataValue → ℚ
  | .Number _ w f => (digitsValue w.val : ℚ) + fracValue f.val
  | .Fraction _ a b => (digitsValue a.val : ℚ) / digitsValue b.val
  | _ => 0

/-- Whether a value is negative. -/
def negativeOf : datatypes.DataValue → Bool
  | .Number n _ _ => n
  | .Fraction n _ _ => n
  | _ => false

/-- The number a numeric value writes. -/
def numValue : datatypes.DataValue → ℚ
  | .Number n w f => numberOf n w.val f.val
  | .Fraction n a b => fractionOf n a.val b.val
  | _ => 0

/-- A canonical numeric value. -/
def CanonicalNumeric : datatypes.DataValue → Prop
  | .Number n w f => CanonicalNumber n w.val f.val
  | .Fraction _ a b => CanonicalFraction a.val b.val
  | _ => False

/-- Whether a value is a number. -/
def IsNumber : datatypes.DataValue → Prop
  | .Number _ _ _ => True
  | .Fraction _ _ _ => True
  | _ => False

theorem orderOf_lt {a b : ℚ} (h : a < b) : orderOf a b = 0 := by simp [orderOf, h]
theorem orderOf_eq {a b : ℚ} (h : a = b) : orderOf a b = 1 := by simp [orderOf, h]
theorem orderOf_gt {a b : ℚ} (h : b < a) : orderOf a b = 2 := by
  have h1 : ¬ a < b := by linarith
  have h2 : ¬ a = b := by intro e; rw [e] at h; exact lt_irrefl _ h
  simp [orderOf, h1, h2]

theorem orderOf_add (c a b : ℚ) : orderOf (c + a) (c + b) = orderOf a b := by
  have h1 : c + a < c + b ↔ a < b := add_lt_add_iff_left c
  have h2 : c + a = c + b ↔ a = b := add_right_inj c
  simp only [orderOf, h1, h2]

theorem orderOf_neg (a b : ℚ) : orderOf (-a) (-b) = orderOf b a := by
  have h1 : -a < -b ↔ b < a := neg_lt_neg_iff
  have h2 : -a = -b ↔ b = a := by rw [neg_inj, eq_comm]
  simp only [orderOf, h1, h2]

theorem orderOf_shift (k a b : ℚ) : orderOf ((k + a) / 10) ((k + b) / 10) = orderOf a b := by
  have h1 : (k + a) / 10 < (k + b) / 10 ↔ a < b := by constructor <;> intro h <;> linarith
  have h2 : (k + a) / 10 = (k + b) / 10 ↔ a = b := by constructor <;> intro h <;> linarith
  simp only [orderOf, h1, h2]

theorem fracValue_nil : fracValue [] = 0 := by simp [fracValue, digitsValue]

theorem fracValue_cons (x : U8) (r : List U8) :
    fracValue (x :: r) = (((x.val - 48 : ℕ) : ℚ) + fracValue r) / 10 := by
  simp only [fracValue, Rowl.Numbers.value_cons, List.length_cons, pow_succ]
  have : (10 : ℚ) ^ r.length ≠ 0 := by positivity
  push_cast
  field_simp

theorem fracValue_lt_one (l : List U8) (d : Digits l) : fracValue l < 1 := by
  have := Rowl.Numbers.value_lt l d
  unfold fracValue
  rw [div_lt_one (by positivity)]
  exact_mod_cast this

theorem fracValue_nonneg (l : List U8) : 0 ≤ fracValue l := by
  unfold fracValue; positivity

theorem fracValue_pos (l : List U8) (d : Digits l) (ne : l ≠ []) (last : l.getLast? ≠ some 48#u8) :
    0 < fracValue l := by
  have := fraction_last l d last ne
  unfold fracValue
  apply div_pos
  · exact_mod_cast (show 0 < digitsValue l by omega)
  · positivity

theorem noTrailing_drop {l : List U8} (h : l.getLast? ≠ some 48#u8) (n : Nat) :
    (l.drop n).getLast? ≠ some 48#u8 := by
  rw [List.getLast?_drop]
  split
  · simp
  · exact h

theorem compare_places_spec (left right : alloc.vec.Vec U8) (dl : Digits left.val) (dr : Digits right.val)
    (tl : left.val.getLast? ≠ some 48#u8) (tr : right.val.getLast? ≠ some 48#u8) (index : Usize) :
    ∃ c, datatypes.compare_places left right index = .ok c ∧
      c.val = orderOf (fracValue (left.val.drop index.val)) (fracValue (right.val.drop index.val)) := by
  rw [datatypes.compare_places]
  by_cases insideL : index.val < left.val.length
  · by_cases insideR : index.val < right.val.length
    · have lookupL : left.index_usize index = .ok left.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem insideL]
      have lookupR : right.index_usize index = .ok right.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem insideR]
      have dx := dl _ (List.getElem_mem insideL)
      have dy := dr _ (List.getElem_mem insideR)
      have restL := fracValue_lt_one _ (Rowl.Numbers.digits_drop dl (index.val + 1))
      have restR := fracValue_lt_one _ (Rowl.Numbers.digits_drop dr (index.val + 1))
      have nnL := fracValue_nonneg (left.val.drop (index.val + 1))
      have nnR := fracValue_nonneg (right.val.drop (index.val + 1))
      rw [List.drop_eq_getElem_cons insideL, List.drop_eq_getElem_cons insideR, fracValue_cons, fracValue_cons]
      by_cases less : (left.val[index.val]).val < (right.val[index.val]).val
      · refine ⟨0#u8, by simp [UScalar.lt_equiv, insideL, insideR, alloc.vec.Vec.index_slice_index, lookupL,
          lookupR, less], ?_⟩
        rw [orderOf_lt]; · rfl
        have : ((left.val[index.val].val - 48 : ℕ) : ℚ) + 1 ≤ ((right.val[index.val].val - 48 : ℕ) : ℚ) := by
          have := dx.1; have := dy.1
          exact_mod_cast (show left.val[index.val].val - 48 + 1 ≤ right.val[index.val].val - 48 by omega)
        linarith
      · by_cases greater : (right.val[index.val]).val < (left.val[index.val]).val
        · refine ⟨2#u8, by simp [UScalar.lt_equiv, insideL, insideR, alloc.vec.Vec.index_slice_index, lookupL,
            lookupR, less, greater], ?_⟩
          rw [orderOf_gt]; · rfl
          have : ((right.val[index.val].val - 48 : ℕ) : ℚ) + 1 ≤ ((left.val[index.val].val - 48 : ℕ) : ℚ) := by
            have := dx.1; have := dy.1
            exact_mod_cast (show right.val[index.val].val - 48 + 1 ≤ left.val[index.val].val - 48 by omega)
          linarith
        · have equal : left.val[index.val].val = right.val[index.val].val := by omega
          obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          have nextIndex : next.val = index.val + 1 := by simpa using nextValue
          obtain ⟨c, run, value⟩ := compare_places_spec left right dl dr tl tr next
          refine ⟨c, by simp [UScalar.lt_equiv, insideL, insideR, alloc.vec.Vec.index_slice_index, lookupL, lookupR,
            less, greater, advance, run], ?_⟩
          rw [value, nextIndex, equal, orderOf_shift]
    · have drops : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
      refine ⟨2#u8, by simp [UScalar.lt_equiv, insideL, insideR], ?_⟩
      rw [drops, fracValue_nil, orderOf_gt]; · rfl
      exact fracValue_pos _ (Rowl.Numbers.digits_drop dl _) (by simp; omega) (noTrailing_drop tl _)
  · have dropL : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    by_cases insideR : index.val < right.val.length
    · refine ⟨0#u8, by simp [UScalar.lt_equiv, insideL, insideR], ?_⟩
      rw [dropL, fracValue_nil, orderOf_lt]; · rfl
      exact fracValue_pos _ (Rowl.Numbers.digits_drop dr _) (by simp; omega) (noTrailing_drop tr _)
    · have dropR : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
      refine ⟨1#u8, by simp [UScalar.lt_equiv, insideL, insideR], ?_⟩
      rw [dropL, dropR, orderOf_eq rfl]; rfl
termination_by left.val.length - index.val
decreasing_by omega

theorem compare_decimals_spec (lw lf rw rf : alloc.vec.Vec U8) {ln rn : Bool}
    (cl : CanonicalNumber ln lw.val lf.val) (cr : CanonicalNumber rn rw.val rf.val) :
    ∃ c, datatypes.compare_decimals lw lf rw rf = .ok c ∧
      c.val = orderOf ((digitsValue lw.val : ℚ) + fracValue lf.val) ((digitsValue rw.val : ℚ) + fracValue rf.val) := by
  rw [datatypes.compare_decimals]
  obtain ⟨dlw, dlf, llw, llf, _⟩ := cl
  obtain ⟨drw, drf, lrw, lrf, _⟩ := cr
  obtain ⟨o, oRun, oValue⟩ := Rowl.Numbers.compare_naturals_spec lw rw ⟨dlw, llw⟩ ⟨drw, lrw⟩
  have fl := fracValue_lt_one _ dlf
  have fr := fracValue_lt_one _ drf
  have nl := fracValue_nonneg lf.val
  have nr := fracValue_nonneg rf.val
  by_cases same : digitsValue lw.val = digitsValue rw.val
  · have one : o = 1#u8 := by apply UScalar.eq_of_val_eq; rw [oValue, Rowl.Numbers.order_eq same]; rfl
    obtain ⟨c, run, value⟩ := compare_places_spec lf rf dlf drf llf lrf 0#usize
    refine ⟨c, by simp [oRun, one, run], ?_⟩
    have zeroVal : ((0#usize : Usize).val) = 0 := rfl
    rw [value, same, zeroVal, List.drop_zero, List.drop_zero]
    exact (orderOf_add _ _ _).symm
  · by_cases less : digitsValue lw.val < digitsValue rw.val
    · have zero : o = 0#u8 := by apply UScalar.eq_of_val_eq; rw [oValue, Rowl.Numbers.order_lt less]; rfl
      refine ⟨0#u8, by simp [oRun, zero], ?_⟩
      rw [orderOf_lt]; · rfl
      have : (digitsValue lw.val : ℚ) + 1 ≤ digitsValue rw.val := by exact_mod_cast less
      linarith
    · have greater : digitsValue rw.val < digitsValue lw.val := by omega
      have two : o = 2#u8 := by apply UScalar.eq_of_val_eq; rw [oValue, Rowl.Numbers.order_gt greater]; rfl
      refine ⟨2#u8, by simp [oRun, two], ?_⟩
      rw [orderOf_gt]; · rfl
      have : (digitsValue rw.val : ℚ) + 1 ≤ digitsValue lw.val := by exact_mod_cast greater
      linarith

theorem magnitude_number (n : Bool) (w f : alloc.vec.Vec U8) :
    magnitude (.Number n w f) = ((digitsValue (w.val ++ f.val) : ℕ) : ℚ) / 10 ^ f.val.length := by
  simp only [magnitude, fracValue, Rowl.Numbers.value_append]
  have : (10 : ℚ) ^ f.val.length ≠ 0 := by positivity
  push_cast
  field_simp

theorem top_of_number (n : Bool) (w f : alloc.vec.Vec U8) (dw : Digits w.val) (df : Digits f.val)
    (room : w.val.length + f.val.length ≤ Usize.max) :
    ∃ t, datatypes.top_of (.Number n w f) = .ok t ∧ Rowl.Numbers.Canonical t.val ∧
      digitsValue t.val = digitsValue (w.val ++ f.val) ∧ t.val.length ≤ w.val.length + f.val.length := by
  rw [datatypes.top_of]
  obtain ⟨v, vRun, vValue⟩ := copy_range_correct w 0#usize (alloc.vec.Vec.len w) (alloc.vec.Vec.new U8)
    (by simp) (by simp [new_val])
  have vIs : v.val = w.val := by rw [vValue]; simp [new_val, segment_whole]
  obtain ⟨v1, v1Run, v1Value⟩ := copy_range_correct f 0#usize (alloc.vec.Vec.len f) v (by simp)
    (by rw [vIs]; simpa using room)
  have v1Is : v1.val = w.val ++ f.val := by rw [v1Value, vIs]; simp [segment_whole]
  obtain ⟨t, tRun, ct, tValue, tLen⟩ := Rowl.Numbers.canonical_spec v1 (by
    rw [v1Is]; exact Rowl.Numbers.digits_append.mpr ⟨dw, df⟩)
  refine ⟨t, by simp [vRun, v1Run, tRun], ct, by rw [tValue, v1Is], by rw [v1Is] at tLen; simpa using tLen⟩

theorem bottom_of_number (n : Bool) (w f : alloc.vec.Vec U8) (room : f.val.length + 1 < Usize.max) :
    ∃ b, datatypes.bottom_of (.Number n w f) = .ok b ∧ Rowl.Numbers.Canonical b.val ∧
      digitsValue b.val = 10 ^ f.val.length ∧ b.val.length ≤ f.val.length + 1 := by
  rw [datatypes.bottom_of]
  obtain ⟨b, run, cb, value, len⟩ := Rowl.Numbers.ten_power_spec (alloc.vec.Vec.len f) (by simpa using room)
  exact ⟨b, run, cb, by simpa using value, by simpa using len⟩

theorem top_of_fraction (n : Bool) (a b : alloc.vec.Vec U8) :
    ∃ t, datatypes.top_of (.Fraction n a b) = .ok t ∧ t.val = a.val := by
  rw [datatypes.top_of]
  obtain ⟨t, run, value⟩ := copy_range_correct a 0#usize (alloc.vec.Vec.len a) (alloc.vec.Vec.new U8)
    (by simp) (by simp [new_val])
  exact ⟨t, run, by rw [value]; simp [new_val, segment_whole]⟩

theorem bottom_of_fraction (n : Bool) (a b : alloc.vec.Vec U8) :
    ∃ t, datatypes.bottom_of (.Fraction n a b) = .ok t ∧ t.val = b.val := by
  rw [datatypes.bottom_of]
  obtain ⟨t, run, value⟩ := copy_range_correct b 0#usize (alloc.vec.Vec.len b) (alloc.vec.Vec.new U8)
    (by simp) (by simp [new_val])
  exact ⟨t, run, by rw [value]; simp [new_val, segment_whole]⟩

/-- How many digits write a number. -/
def digitWidth : datatypes.DataValue → Nat
  | .Number _ w f => w.val.length + f.val.length
  | .Fraction _ a b => a.val.length + b.val.length
  | _ => 0

/-- The digit vectors whose quotient is a number's magnitude, as the kernel
    computes them. -/
theorem parts_of (v : datatypes.DataValue) (c : CanonicalNumeric v) (small : digitWidth v + 2 < Usize.max) :
    ∃ t b, datatypes.top_of v = .ok t ∧ datatypes.bottom_of v = .ok b ∧ Rowl.Numbers.Canonical t.val ∧
      Rowl.Numbers.Canonical b.val ∧ 0 < digitsValue b.val ∧
      magnitude v = (digitsValue t.val : ℚ) / digitsValue b.val ∧
      t.val.length ≤ digitWidth v ∧ b.val.length ≤ digitWidth v + 1 := by
  cases v with
  | Number n w f =>
    obtain ⟨dw, df, _, _, _⟩ := (c : CanonicalNumber n w.val f.val)
    simp only [digitWidth] at small
    obtain ⟨t, tRun, ct, tValue, tLen⟩ := top_of_number n w f dw df (by omega)
    obtain ⟨b, bRun, cb, bValue, bLen⟩ := bottom_of_number n w f (by omega)
    refine ⟨t, b, tRun, bRun, ct, cb, by rw [bValue]; positivity, ?_, by simp only [digitWidth]; omega,
      by simp only [digitWidth]; omega⟩
    rw [magnitude_number, tValue, bValue]; push_cast; rfl
  | Fraction n a b =>
    obtain ⟨ca, cb, _, positive, _, _⟩ := (c : CanonicalFraction a.val b.val)
    obtain ⟨t, tRun, tValue⟩ := top_of_fraction n a b
    obtain ⟨d, dRun, dValue⟩ := bottom_of_fraction n a b
    refine ⟨t, d, tRun, dRun, by rw [tValue]; exact ca, by rw [dValue]; exact cb, by rw [dValue]; exact positive,
      by simp only [magnitude, tValue, dValue], by simp only [digitWidth, tValue]; omega,
      by simp only [digitWidth, dValue]; omega⟩
  | Text _ => exact absurd c (by simp [CanonicalNumeric])
  | Tagged _ _ => exact absurd c (by simp [CanonicalNumeric])
  | Truth _ => exact absurd c (by simp [CanonicalNumeric])
  | Uri _ => exact absurd c (by simp [CanonicalNumeric])
  | Hex _ => exact absurd c (by simp [CanonicalNumeric])
  | Base64 _ => exact absurd c (by simp [CanonicalNumeric])
  | Moment _ => exact absurd c (by simp [CanonicalNumeric])
  | Double _ => exact absurd c (by simp [CanonicalNumeric])
  | Float _ => exact absurd c (by simp [CanonicalNumeric])

theorem order_cross (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    Rowl.Numbers.order (a * d) (c * b) = orderOf ((a : ℚ) / b) ((c : ℚ) / d) := by
  have bq : (0 : ℚ) < b := by exact_mod_cast hb
  have dq : (0 : ℚ) < d := by exact_mod_cast hd
  have h1 : (a : ℚ) / b < (c : ℚ) / d ↔ a * d < c * b := by
    rw [div_lt_div_iff₀ bq dq]; exact_mod_cast Iff.rfl
  have h2 : (a : ℚ) / b = (c : ℚ) / d ↔ a * d = c * b := by
    rw [div_eq_div_iff bq.ne' dq.ne']; exact_mod_cast Iff.rfl
  simp only [Rowl.Numbers.order, orderOf, h1, h2]

theorem compare_crosswise_spec (l r : datatypes.DataValue) (cl : CanonicalNumeric l) (cr : CanonicalNumeric r)
    (small : 2 * (digitWidth l + digitWidth r) + 8 < Usize.max) :
    ∃ c, datatypes.compare_crosswise l r = .ok c ∧ c.val = orderOf (magnitude l) (magnitude r) := by
  rw [datatypes.compare_crosswise]
  obtain ⟨tl, bl, tlRun, blRun, ctl, cbl, blPos, ml, lenTl, lenBl⟩ := parts_of l cl (by omega)
  obtain ⟨tr, br, trRun, brRun, ctr, cbr, brPos, mr, lenTr, lenBr⟩ := parts_of r cr (by omega)
  obtain ⟨p1, p1Run, cp1, p1Value, _⟩ := Rowl.Numbers.multiply_naturals_spec tl br ctl cbr.1 (by omega)
  obtain ⟨p2, p2Run, cp2, p2Value, _⟩ := Rowl.Numbers.multiply_naturals_spec tr bl ctr cbl.1 (by omega)
  obtain ⟨c, cRun, cValue⟩ := Rowl.Numbers.compare_naturals_spec p1 p2 cp1 cp2
  refine ⟨c, by simp [tlRun, brRun, p1Run, trRun, blRun, p2Run, cRun], ?_⟩
  rw [cValue, p1Value, p2Value, ml, mr, order_cross _ _ _ _ blPos brPos]

theorem compare_magnitudes_spec (l r : datatypes.DataValue) (cl : CanonicalNumeric l) (cr : CanonicalNumeric r)
    (small : (∃ n w f n' w' f', l = .Number n w f ∧ r = .Number n' w' f') ∨
      2 * (digitWidth l + digitWidth r) + 8 < Usize.max) :
    ∃ c, datatypes.compare_magnitudes l r = .ok c ∧ c.val = orderOf (magnitude l) (magnitude r) := by
  cases l with
  | Number n w f =>
    cases r with
    | Number n' w' f' =>
      obtain ⟨c, run, value⟩ := compare_decimals_spec w f w' f' cl cr
      exact ⟨c, by rw [datatypes.compare_magnitudes]; exact run, by rw [value]; rfl⟩
    | Fraction n' a b =>
      have small' : 2 * (digitWidth (.Number n w f) + digitWidth (.Fraction n' a b)) + 8 < Usize.max := by
        rcases small with ⟨_, _, _, _, _, _, _, h⟩ | h
        · cases h
        · exact h
      obtain ⟨c, run, value⟩ := compare_crosswise_spec _ _ cl cr small'
      exact ⟨c, by rw [datatypes.compare_magnitudes]; exact run, value⟩
    | Text _ => exact absurd cr (by simp [CanonicalNumeric])
    | Tagged _ _ => exact absurd cr (by simp [CanonicalNumeric])
    | Truth _ => exact absurd cr (by simp [CanonicalNumeric])
    | Uri _ => exact absurd cr (by simp [CanonicalNumeric])
    | Hex _ => exact absurd cr (by simp [CanonicalNumeric])
    | Base64 _ => exact absurd cr (by simp [CanonicalNumeric])
    | Moment _ => exact absurd cr (by simp [CanonicalNumeric])
    | Double _ => exact absurd cr (by simp [CanonicalNumeric])
    | Float _ => exact absurd cr (by simp [CanonicalNumeric])
  | Fraction n a b =>
    have small' : 2 * (digitWidth (.Fraction n a b) + digitWidth r) + 8 < Usize.max := by
      rcases small with ⟨_, _, _, _, _, _, h, _⟩ | h
      · cases h
      · exact h
    obtain ⟨c, run, value⟩ := compare_crosswise_spec _ _ cl cr small'
    exact ⟨c, by rw [datatypes.compare_magnitudes]; exact run, value⟩
  | Text _ => exact absurd cl (by simp [CanonicalNumeric])
  | Tagged _ _ => exact absurd cl (by simp [CanonicalNumeric])
  | Truth _ => exact absurd cl (by simp [CanonicalNumeric])
  | Uri _ => exact absurd cl (by simp [CanonicalNumeric])
  | Hex _ => exact absurd cl (by simp [CanonicalNumeric])
  | Base64 _ => exact absurd cl (by simp [CanonicalNumeric])
  | Moment _ => exact absurd cl (by simp [CanonicalNumeric])
  | Double _ => exact absurd cl (by simp [CanonicalNumeric])
  | Float _ => exact absurd cl (by simp [CanonicalNumeric])

theorem negative_correct (v : datatypes.DataValue) : datatypes.negative v = .ok (negativeOf v) := by
  cases v <;> rfl

theorem magnitude_nonneg (v : datatypes.DataValue) : 0 ≤ magnitude v := by
  cases v with
  | Number n w f =>
    simp only [magnitude]
    have h1 := fracValue_nonneg f.val
    have h2 : (0 : ℚ) ≤ digitsValue w.val := by positivity
    linarith
  | Fraction n a b => simp only [magnitude]; positivity
  | Text _ => simp [magnitude]
  | Tagged _ _ => simp [magnitude]
  | Truth _ => simp [magnitude]
  | Uri _ => simp [magnitude]
  | Hex _ => simp [magnitude]
  | Base64 _ => simp [magnitude]
  | Moment _ => simp [magnitude]
  | Double _ => simp [magnitude]
  | Float _ => simp [magnitude]

/-- A number is its sign times its magnitude, and a negative number is not zero. -/
theorem numValue_sign (v : datatypes.DataValue) (c : CanonicalNumeric v) :
    numValue v = (if negativeOf v then -1 else 1) * magnitude v ∧ (negativeOf v = true → 0 < magnitude v) := by
  cases v with
  | Number n w f =>
    obtain ⟨dw, df, lw, lf, sign⟩ := (c : CanonicalNumber n w.val f.val)
    refine ⟨by simp [numValue, numberOf, magnitude, fracValue, negativeOf], fun neg => ?_⟩
    simp only [negativeOf] at neg
    rcases sign neg with nw | nf
    · have := Rowl.Numbers.canonical_low w.val ⟨dw, lw⟩ nw
      have : (1 : ℚ) ≤ digitsValue w.val := by exact_mod_cast (show 1 ≤ digitsValue w.val by
        have : 0 < 10 ^ (w.val.length - 1) := by positivity
        omega)
      simp only [magnitude]
      have := fracValue_nonneg f.val
      linarith
    · have := fracValue_pos f.val df nf lf
      simp only [magnitude]
      have : (0 : ℚ) ≤ digitsValue w.val := by positivity
      linarith
  | Fraction n a b =>
    obtain ⟨ca, cb, nonzero, positive, _, _⟩ := (c : CanonicalFraction a.val b.val)
    refine ⟨by simp [numValue, fractionOf, magnitude, negativeOf], fun _ => ?_⟩
    have av : 0 < digitsValue a.val := by
      have := (Rowl.Numbers.canonical_zero a.val ca).not.mpr nonzero
      omega
    simp only [magnitude]
    apply div_pos <;> exact_mod_cast (by assumption)
  | Text _ => exact absurd c (by simp [CanonicalNumeric])
  | Tagged _ _ => exact absurd c (by simp [CanonicalNumeric])
  | Truth _ => exact absurd c (by simp [CanonicalNumeric])
  | Uri _ => exact absurd c (by simp [CanonicalNumeric])
  | Hex _ => exact absurd c (by simp [CanonicalNumeric])
  | Base64 _ => exact absurd c (by simp [CanonicalNumeric])
  | Moment _ => exact absurd c (by simp [CanonicalNumeric])
  | Double _ => exact absurd c (by simp [CanonicalNumeric])
  | Float _ => exact absurd c (by simp [CanonicalNumeric])

/-- The kernel orders canonical numbers exactly. -/
theorem compare_numbers_spec (l r : datatypes.DataValue) (cl : CanonicalNumeric l) (cr : CanonicalNumeric r)
    (small : (∃ n w f n' w' f', l = .Number n w f ∧ r = .Number n' w' f') ∨
      2 * (digitWidth l + digitWidth r) + 8 < Usize.max) :
    ∃ c, datatypes.compare_numbers l r = .ok c ∧ c.val = orderOf (numValue l) (numValue r) := by
  rw [datatypes.compare_numbers, datatypes.sign_rule, negative_correct, negative_correct]
  obtain ⟨vl, pl⟩ := numValue_sign l cl
  obtain ⟨vr, pr⟩ := numValue_sign r cr
  have ml := magnitude_nonneg l
  have mr := magnitude_nonneg r
  cases hl : negativeOf l <;> cases hr : negativeOf r
  · obtain ⟨c, run, value⟩ := compare_magnitudes_spec l r cl cr small
    refine ⟨c, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
      exact run
    · rw [value, vl, vr, hl, hr]; simp
  · refine ⟨2#u8, by simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]; rfl, ?_⟩
    rw [vl, vr, hl, hr]
    have := pr hr
    rw [orderOf_gt (by simp; linarith)]; rfl
  · refine ⟨0#u8, by simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]; rfl, ?_⟩
    rw [vl, vr, hl, hr]
    have := pl hl
    rw [orderOf_lt (by simp; linarith)]; rfl
  · have small' : (∃ n w f n' w' f', r = .Number n w f ∧ l = .Number n' w' f') ∨
        2 * (digitWidth r + digitWidth l) + 8 < Usize.max := by
      rcases small with ⟨n, w, f, n', w', f', a, b⟩ | h
      · exact .inl ⟨n', w', f', n, w, f, b, a⟩
      · exact .inr (by omega)
    obtain ⟨c, run, value⟩ := compare_magnitudes_spec r l cr cl small'
    refine ⟨c, ?_, ?_⟩
    · simp only [↓reduceIte, bind_ok]
      exact run
    · rw [value, vl, vr, hl, hr]
      simp only [↓reduceIte, neg_one_mul]
      exact (orderOf_neg _ _).symm

theorem numeric_correct (v : datatypes.DataValue) : datatypes.numeric v = .ok (decide (IsNumber v)) := by
  cases v <;> simp [datatypes.numeric, IsNumber]

theorem sum_of_spec (first second : Usize) :
    ∃ x, datatypes.sum_of first second = .ok x ∧
      (first.val < Usize.max / 8 → second.val < Usize.max / 8 → x.val = first.val + second.val) ∧
      (x.val < Usize.max / 8 → x.val = first.val + second.val) := by
  rw [datatypes.sum_of]
  obtain ⟨q, qRun, qValue⟩ := UScalar.div_spec core.num.Usize.MAX (y := 8#usize) (by simp)
  have qIs : q.val = Usize.max / 8 := by rw [qValue]; simp [core.num.Usize.MAX]
  by_cases both : first.val < Usize.max / 8 ∧ second.val < Usize.max / 8
  · obtain ⟨s, sRun, sValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := first) (y := second) (by scalar_tac))
    refine ⟨s, by simp [qRun, UScalar.lt_equiv, qIs, both, sRun], fun _ _ => by simpa using sValue,
      fun _ => by simpa using sValue⟩
  · refine ⟨core.num.Usize.MAX, ?_, fun a b => absurd ⟨a, b⟩ both, fun h => ?_⟩
    · by_cases a : first.val < Usize.max / 8
      · have b : ¬ second.val < Usize.max / 8 := fun b => both ⟨a, b⟩
        simp [qRun, UScalar.lt_equiv, qIs, a, b]
      · simp [qRun, UScalar.lt_equiv, qIs, a]
    · simp [core.num.Usize.MAX] at h; omega

theorem width_spec (v : datatypes.DataValue) :
    ∃ x, datatypes.width v = .ok x ∧ (x.val < Usize.max / 8 ↔ digitWidth v < Usize.max / 8) := by
  cases v with
  | Number n w f =>
    obtain ⟨x, run, both, below⟩ := sum_of_spec (alloc.vec.Vec.len w) (alloc.vec.Vec.len f)
    refine ⟨x, by rw [datatypes.width]; exact run, ?_⟩
    simp only [digitWidth]
    simp only [alloc.vec.Vec.len_val] at both below
    constructor
    · intro h; rw [← below h]; exact h
    · intro h; rw [both (by simp; omega) (by simp; omega)]; simpa using h
  | Fraction n a b =>
    obtain ⟨x, run, both, below⟩ := sum_of_spec (alloc.vec.Vec.len a) (alloc.vec.Vec.len b)
    refine ⟨x, by rw [datatypes.width]; exact run, ?_⟩
    simp only [digitWidth]
    simp only [alloc.vec.Vec.len_val] at both below
    constructor
    · intro h; rw [← below h]; exact h
    · intro h; rw [both (by simp; omega) (by simp; omega)]; simpa using h
  | Text _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Tagged _ _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Truth _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Uri _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Hex _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Base64 _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Moment _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Double _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩
  | Float _ => exact ⟨0#usize, by rw [datatypes.width], by simp [digitWidth]⟩

/-- The kernel's comparison of values: the exact order of two canonical
    numbers, and no answer for a value that is no number or for numbers too
    long for the kernel's arithmetic. -/
theorem compare_values_correct (l r : datatypes.DataValue) (cl : IsNumber l → CanonicalNumeric l)
    (cr : IsNumber r → CanonicalNumeric r) :
    ∃ res, datatypes.compare_values l r = .ok res ∧
      (res = none → ¬ IsNumber l ∨ ¬ IsNumber r ∨ Usize.max / 8 ≤ digitWidth l ∨ Usize.max / 8 ≤ digitWidth r) ∧
      ∀ c, res = some c → IsNumber l ∧ IsNumber r ∧ c.val = orderOf (numValue l) (numValue r) := by
  rw [datatypes.compare_values, numeric_correct, numeric_correct]
  by_cases nl : IsNumber l
  · by_cases nr : IsNumber r
    · obtain ⟨xl, xlRun, xl'⟩ := width_spec l
      obtain ⟨xr, xrRun, xr'⟩ := width_spec r
      obtain ⟨q, qRun, qValue⟩ := UScalar.div_spec core.num.Usize.MAX (y := 8#usize) (by simp)
      have qIs : q.val = Usize.max / 8 := by rw [qValue]; simp [core.num.Usize.MAX]
      by_cases wl : digitWidth l < Usize.max / 8
      · by_cases wr : digitWidth r < Usize.max / 8
        · have lt1 : xl.val < q.val := by rw [qIs]; exact xl'.mpr wl
          have lt2 : xr.val < q.val := by rw [qIs]; exact xr'.mpr wr
          obtain ⟨c, run, value⟩ := compare_numbers_spec l r (cl nl) (cr nr) (.inr (by
            have : 32 ≤ Usize.max := by scalar_tac
            omega))
          refine ⟨some c, by simp [nl, nr, xlRun, xrRun, qRun, lt1, lt2, run, UScalar.lt_equiv], by simp,
            fun c' h => ?_⟩
          cases h
          exact ⟨nl, nr, value⟩
        · have lt1 : xl.val < q.val := by rw [qIs]; exact xl'.mpr wl
          have notLt : ¬ xr.val < q.val := by rw [qIs]; exact fun h => wr (xr'.mp h)
          exact ⟨none, by simp [nl, nr, xlRun, xrRun, qRun, lt1, notLt, UScalar.lt_equiv],
            fun _ => .inr (.inr (.inr (by omega))), by simp⟩
      · have notLt : ¬ xl.val < q.val := by rw [qIs]; exact fun h => wl (xl'.mp h)
        exact ⟨none, by simp [nl, nr, xlRun, qRun, notLt, UScalar.lt_equiv], fun _ => .inr (.inr (.inl (by omega))),
          by simp⟩
    · exact ⟨none, by simp [nl, nr], fun _ => .inr (.inl nr), by simp⟩
  · exact ⟨none, by simp [nl], fun _ => .inl nl, by simp⟩

/-! ### The integer subtypes -/

/-- The least value of an integer subtype. -/
def lowerOf : datatypes.Kind → Option ℤ
  | .NonNegativeInteger => some 0
  | .PositiveInteger => some 1
  | .Long => some (-9223372036854775808)
  | .Int => some (-2147483648)
  | .Short => some (-32768)
  | .Byte => some (-128)
  | .UnsignedLong => some 0
  | .UnsignedInt => some 0
  | .UnsignedShort => some 0
  | .UnsignedByte => some 0
  | _ => none

/-- The greatest value of an integer subtype. -/
def upperOf : datatypes.Kind → Option ℤ
  | .NonPositiveInteger => some 0
  | .NegativeInteger => some (-1)
  | .Long => some 9223372036854775807
  | .Int => some 2147483647
  | .Short => some 32767
  | .Byte => some 127
  | .UnsignedLong => some 18446744073709551615
  | .UnsignedInt => some 4294967295
  | .UnsignedShort => some 65535
  | .UnsignedByte => some 255
  | _ => none

/-- The integer subtypes of `xsd:integer`. -/
def IsSubtype : datatypes.Kind → Prop
  | .Integer | .Decimal | .String | .Plain | .Boolean | .Real | .Rational | .AnyUri | .HexBinary | .Base64Binary
  | .NormalizedString | .Token | .Language | .NmToken | .Name | .NcName | .DateTime | .DateTimeStamp | .Double
  | .Float => False
  | _ => True

/-- Whether a number, an integer when `whole`, is in the value space of a
    kind's datatype. -/
def NumberIn (k : datatypes.Kind) (whole : Prop) (q : ℚ) : Prop :=
  match k with
  | .Integer => whole
  | .Decimal => True
  | .String => False
  | .Plain => False
  | .Boolean => False
  | .Real => True
  | .Rational => True
  | .AnyUri => False
  | .HexBinary => False
  | .Base64Binary => False
  | .NormalizedString => False
  | .Token => False
  | .Language => False
  | .NmToken => False
  | .Name => False
  | .NcName => False
  | .DateTime => False
  | .DateTimeStamp => False
  | .Double => False
  | .Float => False
  | k => whole ∧ (∀ l, lowerOf k = some l → (l : ℚ) ≤ q) ∧ (∀ u, upperOf k = some u → q ≤ (u : ℚ))

/-- The subtypes are those of the specification with their bounds. -/
theorem subtype_listed (k : datatypes.Kind) (h : IsSubtype k) :
    (typeOf k, lowerOf k, upperOf k) ∈ integerSubtypes := by
  cases k <;> simp_all [IsSubtype, typeOf, lowerOf, upperOf, integerSubtypes]

theorem listed_subtype (s : Datatype × Option ℤ × Option ℤ) (h : s ∈ integerSubtypes) :
    ∃ k, IsSubtype k ∧ s = (typeOf k, lowerOf k, upperOf k) := by
  simp only [integerSubtypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.NonNegativeInteger, trivial, rfl⟩
  · exact ⟨.NonPositiveInteger, trivial, rfl⟩
  · exact ⟨.PositiveInteger, trivial, rfl⟩
  · exact ⟨.NegativeInteger, trivial, rfl⟩
  · exact ⟨.Long, trivial, rfl⟩
  · exact ⟨.Int, trivial, rfl⟩
  · exact ⟨.Short, trivial, rfl⟩
  · exact ⟨.Byte, trivial, rfl⟩
  · exact ⟨.UnsignedLong, trivial, rfl⟩
  · exact ⟨.UnsignedInt, trivial, rfl⟩
  · exact ⟨.UnsignedShort, trivial, rfl⟩
  · exact ⟨.UnsignedByte, trivial, rfl⟩

theorem pattern_copy_correct (pattern : Slice U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length + (pattern.val.length - index.val) ≤ Usize.max) :
    ∃ v, datatypes.pattern_copy pattern index out = .ok v ∧ v.val = out.val ++ pattern.val.drop index.val := by
  rw [datatypes.pattern_copy]
  by_cases inside : index.val < pattern.val.length
  · have lookup : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem inside]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out pattern.val[index.val] short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := pattern_copy_correct pattern next pushed (by rw [contents, nextIndex]; simp; omega)
    refine ⟨v, by simp [UScalar.lt_equiv, inside, short, lookup, push, advance, run], ?_⟩
    rw [value, contents, nextIndex, List.drop_eq_getElem_cons inside]
    simp
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show pattern.val.length ≤ index.val by omega)]
termination_by pattern.val.length - index.val
decreasing_by omega

/-- A bound as the kernel writes it: a canonical integer of the given value. -/
def BoundValue (v : datatypes.DataValue) (z : ℤ) : Prop :=
  ∃ n w f, v = .Number n w f ∧ CanonicalNumber n w.val f.val ∧ numberOf n w.val f.val = z

theorem positive_number_value (digits : Slice U8) (d : Digits digits.val) (lead : digits.val.head? ≠ some 48#u8) :
    ∃ v, datatypes.positive_number digits = .ok v ∧ BoundValue v (digitsValue digits.val) := by
  rw [datatypes.positive_number]
  obtain ⟨c, run, value⟩ := pattern_copy_correct digits 0#usize (alloc.vec.Vec.new U8) (by simp [new_val])
  have cIs : c.val = digits.val := by rw [value]; simp [new_val]
  refine ⟨_, by simp [run], false, c, alloc.vec.Vec.new U8, rfl, ⟨by rw [cIs]; exact d, by simp [new_val, Digits],
    by rw [cIs]; exact lead, by simp [new_val], by simp⟩, ?_⟩
  simp [numberOf, cIs, new_val, digitsValue_nil]

theorem negative_number_value (digits : Slice U8) (d : Digits digits.val) (lead : digits.val.head? ≠ some 48#u8)
    (nonempty : digits.val ≠ []) :
    ∃ v, datatypes.negative_number digits = .ok v ∧ BoundValue v (-(digitsValue digits.val : ℤ)) := by
  rw [datatypes.negative_number]
  obtain ⟨c, run, value⟩ := pattern_copy_correct digits 0#usize (alloc.vec.Vec.new U8) (by simp [new_val])
  have cIs : c.val = digits.val := by rw [value]; simp [new_val]
  refine ⟨_, by simp [run], true, c, alloc.vec.Vec.new U8, rfl, ⟨by rw [cIs]; exact d, by simp [new_val, Digits],
    by rw [cIs]; exact lead, by simp [new_val], fun _ => .inl (by rw [cIs]; exact nonempty)⟩, ?_⟩
  simp [numberOf, cIs, new_val, digitsValue_nil]

theorem lower_bound_correct (k : datatypes.Kind) :
    ∃ r, datatypes.lower_bound k = .ok r ∧ (r = none ↔ lowerOf k = none) ∧
      ∀ v, r = some v → ∃ l, lowerOf k = some l ∧ BoundValue v l := by
  cases k with
  | Integer => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | AnyUri => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | HexBinary => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Base64Binary => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Decimal => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | String => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Plain => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Boolean => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Real => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Rational => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | NormalizedString => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Token => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Language => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | NmToken => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Name => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | NcName => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | DateTime => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | DateTimeStamp => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Double => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Float => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | NonNegativeInteger =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Std.Array.empty U8).to_slice
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | NonPositiveInteger => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | PositiveInteger =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 1#usize [49#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | NegativeInteger => exact ⟨none, by simp [datatypes.lower_bound], by simp [lowerOf], by simp⟩
  | Long =>
    obtain ⟨v, run, bound⟩ := negative_number_value (Array.to_slice (Array.make 19#usize [57#u8, 50#u8, 50#u8, 51#u8, 51#u8, 55#u8, 50#u8, 48#u8, 51#u8, 54#u8, 56#u8, 53#u8, 52#u8, 55#u8, 55#u8, 53#u8, 56#u8, 48#u8, 56#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, digitsValue]
  | Int =>
    obtain ⟨v, run, bound⟩ := negative_number_value (Array.to_slice (Array.make 10#usize [50#u8, 49#u8, 52#u8, 55#u8, 52#u8, 56#u8, 51#u8, 54#u8, 52#u8, 56#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, digitsValue]
  | Short =>
    obtain ⟨v, run, bound⟩ := negative_number_value (Array.to_slice (Array.make 5#usize [51#u8, 50#u8, 55#u8, 54#u8, 56#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, digitsValue]
  | Byte =>
    obtain ⟨v, run, bound⟩ := negative_number_value (Array.to_slice (Array.make 3#usize [49#u8, 50#u8, 56#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, digitsValue]
  | UnsignedLong =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Std.Array.empty U8).to_slice
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | UnsignedInt =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Std.Array.empty U8).to_slice
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | UnsignedShort =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Std.Array.empty U8).to_slice
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | UnsignedByte =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Std.Array.empty U8).to_slice
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.lower_bound, lift, run], by simp [lowerOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]

theorem upper_bound_correct (k : datatypes.Kind) :
    ∃ r, datatypes.upper_bound k = .ok r ∧ (r = none ↔ upperOf k = none) ∧
      ∀ v, r = some v → ∃ u, upperOf k = some u ∧ BoundValue v u := by
  cases k with
  | Integer => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | AnyUri => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | HexBinary => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Base64Binary => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Decimal => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | String => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Plain => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Boolean => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Real => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Rational => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | NormalizedString => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Token => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Language => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | NmToken => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Name => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | NcName => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | DateTime => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | DateTimeStamp => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Double => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | Float => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | NonNegativeInteger => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | NonPositiveInteger =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Std.Array.empty U8).to_slice
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | PositiveInteger => exact ⟨none, by simp [datatypes.upper_bound], by simp [upperOf], by simp⟩
  | NegativeInteger =>
    obtain ⟨v, run, bound⟩ := negative_number_value (Array.to_slice (Array.make 1#usize [49#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, digitsValue]
  | Long =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 19#usize [57#u8, 50#u8, 50#u8, 51#u8, 51#u8, 55#u8, 50#u8, 48#u8, 51#u8, 54#u8, 56#u8, 53#u8, 52#u8, 55#u8, 55#u8, 53#u8, 56#u8, 48#u8, 55#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | Int =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 10#usize [50#u8, 49#u8, 52#u8, 55#u8, 52#u8, 56#u8, 51#u8, 54#u8, 52#u8, 55#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | Short =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 5#usize [51#u8, 50#u8, 55#u8, 54#u8, 55#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | Byte =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 3#usize [49#u8, 50#u8, 55#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | UnsignedLong =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 20#usize [49#u8, 56#u8, 52#u8, 52#u8, 54#u8, 55#u8, 52#u8, 52#u8, 48#u8, 55#u8, 51#u8, 55#u8, 48#u8, 57#u8, 53#u8, 53#u8, 49#u8, 54#u8, 49#u8, 53#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | UnsignedInt =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 10#usize [52#u8, 50#u8, 57#u8, 52#u8, 57#u8, 54#u8, 55#u8, 50#u8, 57#u8, 53#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | UnsignedShort =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 5#usize [54#u8, 53#u8, 53#u8, 51#u8, 53#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]
  | UnsignedByte =>
    obtain ⟨v, run, bound⟩ := positive_number_value (Array.to_slice (Array.make 3#usize [50#u8, 53#u8, 53#u8]))
      (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit]) (by simp [Array.to_slice, Array.make, Std.Array.empty, Digits, Digit])
    refine ⟨some v, by simp [datatypes.upper_bound, lift, run], by simp [upperOf], fun v' h => ⟨_, rfl, ?_⟩⟩
    cases h
    convert bound using 2
    simp [Array.to_slice, Array.make, Std.Array.empty, digitsValue]

theorem bound_number {v : datatypes.DataValue} {z : ℤ} (h : BoundValue v z) :
    CanonicalNumeric v ∧ numValue v = z ∧ ∃ n w f, v = .Number n w f := by
  obtain ⟨n, w, f, rfl, c, value⟩ := h
  exact ⟨c, value, n, w, f, rfl⟩

theorem above_lower_correct (n : Bool) (w f : alloc.vec.Vec U8) (c : CanonicalNumber n w.val f.val)
    (k : datatypes.Kind) :
    datatypes.above_lower (.Number n w f) k =
      .ok (decide (∀ l, lowerOf k = some l → (l : ℚ) ≤ numberOf n w.val f.val)) := by
  rw [datatypes.above_lower]
  obtain ⟨r, run, isNone, isSome⟩ := lower_bound_correct k
  cases r with
  | none =>
    have : lowerOf k = none := isNone.mp rfl
    simp [run, this]
  | some bound =>
    obtain ⟨l, hl, bv⟩ := isSome bound rfl
    obtain ⟨cb, vb, n', w', f', rfl⟩ := bound_number bv
    obtain ⟨o, oRun, oValue⟩ := compare_numbers_spec (.Number n w f) (.Number n' w' f') c cb
      (.inl ⟨n, w, f, n', w', f', rfl, rfl⟩)
    simp only [numValue] at oValue vb
    rw [vb] at oValue
    have key : (o != 0#u8) = decide ((l : ℚ) ≤ numberOf n w.val f.val) := by
      by_cases below : numberOf n w.val f.val < l
      · have : o = 0#u8 := by apply UScalar.eq_of_val_eq; rw [oValue, orderOf_lt below]; rfl
        simp [this, not_le.mpr below]
      · have notZero : orderOf (numberOf n w.val f.val) (l : ℚ) ≠ 0 := by
          unfold orderOf
          split_ifs <;> simp_all
        have : o ≠ 0#u8 := fun h => notZero (by rw [← oValue, h]; rfl)
        simp [this, not_lt.mp below]
    simp [run, oRun, key, hl]

theorem below_upper_correct (n : Bool) (w f : alloc.vec.Vec U8) (c : CanonicalNumber n w.val f.val)
    (k : datatypes.Kind) :
    datatypes.below_upper (.Number n w f) k =
      .ok (decide (∀ u, upperOf k = some u → numberOf n w.val f.val ≤ (u : ℚ))) := by
  rw [datatypes.below_upper]
  obtain ⟨r, run, isNone, isSome⟩ := upper_bound_correct k
  cases r with
  | none =>
    have : upperOf k = none := isNone.mp rfl
    simp [run, this]
  | some bound =>
    obtain ⟨u, hu, bv⟩ := isSome bound rfl
    obtain ⟨cb, vb, n', w', f', rfl⟩ := bound_number bv
    obtain ⟨o, oRun, oValue⟩ := compare_numbers_spec (.Number n w f) (.Number n' w' f') c cb
      (.inl ⟨n, w, f, n', w', f', rfl, rfl⟩)
    simp only [numValue] at oValue vb
    rw [vb] at oValue
    have key : (o != 2#u8) = decide (numberOf n w.val f.val ≤ (u : ℚ)) := by
      by_cases above : (u : ℚ) < numberOf n w.val f.val
      · have : o = 2#u8 := by apply UScalar.eq_of_val_eq; rw [oValue, orderOf_gt above]; rfl
        simp [this, not_le.mpr above]
      · have notTwo : orderOf (numberOf n w.val f.val) (u : ℚ) ≠ 2 := by
          unfold orderOf
          split_ifs with h1 h2
          · decide
          · decide
          · exact absurd (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)) above
        have : o ≠ 2#u8 := fun h => notTwo (by rw [← oValue, h]; rfl)
        simp [this, not_lt.mp above]
    simp [run, oRun, key, hu]

theorem number_in_kind_correct (n : Bool) (w f : alloc.vec.Vec U8) (c : CanonicalNumber n w.val f.val)
    (whole : Bool) (k : datatypes.Kind) :
    datatypes.number_in_kind (.Number n w f) whole k =
      .ok (decide (NumberIn k (whole = true) (numberOf n w.val f.val))) := by
  cases k <;> simp [datatypes.number_in_kind, NumberIn, above_lower_correct n w f c,
    below_upper_correct n w f c, Bool.and_eq_true, decide_eq_true_eq, and_assoc, Bool.and_assoc]

/-- The value of an integer lexical form of an integer subtype within its
    bounds. -/
theorem bounded_value_correct (k : datatypes.Kind) (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.bounded_value k lexical = .ok r ∧
      (∀ v, r = some v → ∃ n w f, v = .Number n w f ∧ CanonicalNumber n w.val f.val ∧ f.val = [] ∧
        IntegerForm lexical.val (numberOf n w.val f.val) ∧ NumberIn k True (numberOf n w.val f.val)) ∧
      (r = none → ∀ q, IntegerForm lexical.val q → ¬ NumberIn k True q) := by
  rw [datatypes.bounded_value]
  obtain ⟨r, run, someCase, noneCase⟩ := number_value_correct lexical true
  cases r with
  | none =>
    refine ⟨none, by simp [run], by simp, fun _ q form _ => noneCase rfl q form⟩
  | some v =>
    obtain ⟨n, w, f, rfl, c, form, whole⟩ := someCase _ rfl
    have fEmpty := whole rfl
    have form' : IntegerForm lexical.val (numberOf n w.val f.val) := form
    by_cases inside : NumberIn k True (numberOf n w.val f.val)
    · refine ⟨some (.Number n w f), by simp [run, number_in_kind_correct n w f c, inside], fun v h => ?_, by simp⟩
      cases h
      exact ⟨n, w, f, rfl, c, fEmpty, form', inside⟩
    · refine ⟨none, by simp [run, number_in_kind_correct n w f c, inside], by simp, fun _ q formQ => ?_⟩
      rw [number_form_unique (whole := true) formQ form]
      exact inside

/-! ### Values -/

/-- The values that `literal_value` returns: canonical numbers and fractions,
    strings of XML characters, such strings with a lower-case well-formed
    language tag, truth values, IRIs, octets and canonical moments. -/
def Canonical : datatypes.DataValue → Prop
  | .Number n w f => CanonicalNumber n w.val f.val
  | .Fraction _ a b => CanonicalFraction a.val b.val
  | .Text t => XmlText t.val
  | .Tagged t m => XmlText t.val ∧ TagValue m.val
  | .Truth _ => True
  | .Uri t => XmlText t.val
  | .Hex _ => True
  | .Base64 _ => True
  | .Moment x => Rowl.Moments.CanonicalMoment x
  | .Double b => Rowl.Floats.CanonicalBinary b ∧ (Rowl.Floats.binaryOf b).Valid doubleFormat
  | .Float b => Rowl.Floats.CanonicalBinary b ∧ (Rowl.Floats.binaryOf b).Valid floatFormat

/-- The lexical space of the datatype of a kind. -/
def LexicalForm : datatypes.Kind → List U8 → Prop
  | .Integer, t => ∃ q, IntegerForm t q
  | .Decimal, t => ∃ q, DecimalForm t q
  | .String, t => XmlText t
  | .Plain, t => ∃ s l, PlainSplit t s l ∧ XmlText s ∧ (l = [] ∨ LanguageTag l)
  | .Boolean, t => ∃ b, TruthForm t b
  | .Real, _ => False
  | .Rational, t => ∃ q, RationalForm t q
  | .AnyUri, t => XmlText t
  | .HexBinary, t => ∃ o, HexForm t o
  | .Base64Binary, t => ∃ o, Base64Form t o
  | .NormalizedString, t => StringSubtype.normalized.Form t
  | .Token, t => StringSubtype.token.Form t
  | .Language, t => StringSubtype.language.Form t
  | .NmToken, t => StringSubtype.nmtoken.Form t
  | .Name, t => StringSubtype.name.Form t
  | .NcName, t => StringSubtype.ncname.Form t
  | .DateTime, t => ∃ m, MomentForm t m
  | .DateTimeStamp, t => ∃ m, MomentForm t m ∧ m.zone ≠ none
  | .Double, t => ∃ b, BinaryForm doubleFormat t b
  | .Float, t => ∃ b, BinaryForm floatFormat t b
  | k, t => ∃ z : ℤ, Bounded (lowerOf k) (upperOf k) z ∧ IntegerForm t (z : ℚ)

/-- The numeric datatypes. -/
def IsNumeric : datatypes.Kind → Prop
  | .String | .Plain | .Boolean | .AnyUri | .HexBinary | .Base64Binary | .NormalizedString | .Token | .Language
  | .NmToken | .Name | .NcName | .DateTime | .DateTimeStamp | .Double | .Float => False
  | _ => True

theorem subtypeOf_type {k : datatypes.Kind} {s : StringSubtype} (h : subtypeOf k = some s) :
    typeOf k = s.datatype := by
  cases k <;> simp [subtypeOf] at h <;> subst h <;> rfl

/-- The kind of a subtype of `xsd:string`. -/
def subtypeKind : StringSubtype → datatypes.Kind
  | .normalized => .NormalizedString
  | .token => .Token
  | .language => .Language
  | .nmtoken => .NmToken
  | .name => .Name
  | .ncname => .NcName

theorem typeOf_subtypeKind (s : StringSubtype) : typeOf (subtypeKind s) = s.datatype := by cases s <;> rfl

theorem subtypeOf_subtypeKind (s : StringSubtype) : subtypeOf (subtypeKind s) = some s := by cases s <;> rfl

/-- The real numbers of the value space of a numeric kind's datatype. -/
def RealIn (k : datatypes.Kind) (r : ℝ) : Prop :=
  match k with
  | .Integer => ∃ z : ℤ, r = z
  | .Decimal => ∃ (z : ℤ) (n : ℕ), r = (z : ℝ) / 10 ^ n
  | .String => False
  | .Plain => False
  | .Boolean => False
  | .Real => True
  | .Rational => ∃ q : ℚ, r = q
  | .AnyUri => False
  | .HexBinary => False
  | .Base64Binary => False
  | .NormalizedString => False
  | .Token => False
  | .Language => False
  | .NmToken => False
  | .Name => False
  | .NcName => False
  | .DateTime => False
  | .DateTimeStamp => False
  | .Double => False
  | .Float => False
  | k => ∃ z : ℤ, Bounded (lowerOf k) (upperOf k) z ∧ r = z

variable {Native : Type w} {D : DatatypeMap Native}

/-- The value of a kernel value in a datatype map that is the OWL 2 map on the
    datatypes here. -/
noncomputable def valueOf (N : Normative D) : datatypes.DataValue → Native
  | .Number n w f => N.number (numberOf n w.val f.val)
  | .Fraction n a b => N.number (fractionOf n a.val b.val)
  | .Text t => N.text t.val
  | .Tagged t m => N.tagged t.val m.val
  | .Truth b => N.truth b
  | .Uri t => N.coded (.uri t.val)
  | .Hex o => N.coded (.hex o.val)
  | .Base64 o => N.coded (.base64 o.val)
  | .Moment x => N.moment (Rowl.Moments.momentOf x)
  | .Double b => N.double (Rowl.Floats.binaryOf b)
  | .Float b => N.float (Rowl.Floats.binaryOf b)

theorem real_rat (N : Normative D) (q : ℚ) : N.number q = N.real q := (N.real_number q).symm

theorem real_int (N : Normative D) (z : ℤ) : N.number (z : ℚ) = N.real z := by
  rw [real_rat]; simp

/-- Every numeric value space is the image of a set of reals. -/
theorem numeric_space (N : Normative D) (k : datatypes.Kind) (numeric : IsNumeric k) (x : Native) :
    D.valueSpace (typeOf k) x ↔ ∃ r, x = N.real r ∧ RealIn k r := by
  have subtype : ∀ k, IsSubtype k → (D.valueSpace (typeOf k) x ↔ ∃ r, x = N.real r ∧
      ∃ z : ℤ, Bounded (lowerOf k) (upperOf k) z ∧ r = z) := by
    intro k sub
    rw [N.subtype_space _ (subtype_listed k sub)]
    constructor
    · rintro ⟨z, bounded, rfl⟩; exact ⟨z, real_int N z, z, bounded, rfl⟩
    · rintro ⟨r, rfl, z, bounded, rfl⟩; exact ⟨z, bounded, (real_int N z).symm⟩
  cases k with
  | Integer =>
    simp only [typeOf, N.integer_space, RealIn]
    constructor
    · rintro ⟨q, ⟨z, rfl⟩, rfl⟩; exact ⟨z, real_int N z, z, rfl⟩
    · rintro ⟨r, rfl, z, rfl⟩; exact ⟨z, ⟨z, rfl⟩, (real_int N z).symm⟩
  | Decimal =>
    simp only [typeOf, N.decimal_space, RealIn]
    constructor
    · rintro ⟨q, ⟨z, n, rfl⟩, rfl⟩
      exact ⟨_, real_rat N _, z, n, by push_cast; rfl⟩
    · rintro ⟨r, rfl, z, n, rfl⟩
      refine ⟨(z : ℚ) / 10 ^ n, ⟨z, n, rfl⟩, ?_⟩
      rw [real_rat]; push_cast; rfl
  | String => exact absurd numeric (by simp [IsNumeric])
  | Plain => exact absurd numeric (by simp [IsNumeric])
  | Boolean => exact absurd numeric (by simp [IsNumeric])
  | AnyUri => exact absurd numeric (by simp [IsNumeric])
  | HexBinary => exact absurd numeric (by simp [IsNumeric])
  | Base64Binary => exact absurd numeric (by simp [IsNumeric])
  | NormalizedString => exact absurd numeric (by simp [IsNumeric])
  | Token => exact absurd numeric (by simp [IsNumeric])
  | Language => exact absurd numeric (by simp [IsNumeric])
  | NmToken => exact absurd numeric (by simp [IsNumeric])
  | Name => exact absurd numeric (by simp [IsNumeric])
  | NcName => exact absurd numeric (by simp [IsNumeric])
  | DateTime => exact absurd numeric (by simp [IsNumeric])
  | DateTimeStamp => exact absurd numeric (by simp [IsNumeric])
  | Double => exact absurd numeric (by simp [IsNumeric])
  | Float => exact absurd numeric (by simp [IsNumeric])
  | Real => simp only [typeOf, N.real_space, RealIn, and_true]
  | Rational =>
    simp only [typeOf, N.rational_space, RealIn]
    constructor
    · rintro ⟨q, rfl⟩; exact ⟨q, real_rat N q, q, rfl⟩
    · rintro ⟨r, rfl, q, rfl⟩; exact ⟨q, (real_rat N q).symm⟩
  | NonNegativeInteger => exact subtype _ trivial
  | NonPositiveInteger => exact subtype _ trivial
  | PositiveInteger => exact subtype _ trivial
  | NegativeInteger => exact subtype _ trivial
  | Long => exact subtype _ trivial
  | Int => exact subtype _ trivial
  | Short => exact subtype _ trivial
  | Byte => exact subtype _ trivial
  | UnsignedLong => exact subtype _ trivial
  | UnsignedInt => exact subtype _ trivial
  | UnsignedShort => exact subtype _ trivial
  | UnsignedByte => exact subtype _ trivial

theorem normative_lexical (N : Normative D) (k : datatypes.Kind) (t : List U8) :
    D.lexicalSpace (typeOf k) t ↔ LexicalForm k t := by
  have subtype : ∀ k, IsSubtype k → (D.lexicalSpace (typeOf k) t ↔
      ∃ z : ℤ, Bounded (lowerOf k) (upperOf k) z ∧ IntegerForm t (z : ℚ)) :=
    fun k sub => N.subtype_lexical _ (subtype_listed k sub) t
  cases k with
  | Integer => exact N.integer_lexical t
  | Decimal => exact N.decimal_lexical t
  | String => exact N.string_lexical t
  | Plain => exact N.plain_lexical t
  | Boolean => exact N.boolean_lexical t
  | Real => simp only [LexicalForm, iff_false]; exact N.real_lexical t
  | Rational => exact N.rational_lexical t
  | AnyUri => exact N.uri_lexical t
  | HexBinary => exact N.hex_lexical t
  | Base64Binary => exact N.base64_lexical t
  | NormalizedString => exact N.string_subtype_lexical .normalized t
  | Token => exact N.string_subtype_lexical .token t
  | Language => exact N.string_subtype_lexical .language t
  | NmToken => exact N.string_subtype_lexical .nmtoken t
  | Name => exact N.string_subtype_lexical .«name» t
  | NcName => exact N.string_subtype_lexical .ncname t
  | DateTime => exact N.datetime_lexical t
  | DateTimeStamp => exact N.stamp_lexical t
  | Double => exact N.double_lexical t
  | Float => exact N.float_lexical t
  | NonNegativeInteger => exact subtype _ trivial
  | NonPositiveInteger => exact subtype _ trivial
  | PositiveInteger => exact subtype _ trivial
  | NegativeInteger => exact subtype _ trivial
  | Long => exact subtype _ trivial
  | Int => exact subtype _ trivial
  | Short => exact subtype _ trivial
  | Byte => exact subtype _ trivial
  | UnsignedLong => exact subtype _ trivial
  | UnsignedInt => exact subtype _ trivial
  | UnsignedShort => exact subtype _ trivial
  | UnsignedByte => exact subtype _ trivial

theorem normative_supported (N : Normative D) (k : datatypes.Kind) : D.supported (typeOf k) := by
  have subtype : ∀ k, IsSubtype k → D.supported (typeOf k) :=
    fun k sub => N.subtype_supported _ (subtype_listed k sub)
  cases k with
  | Integer => exact N.integer_supported
  | Decimal => exact N.decimal_supported
  | String => exact N.string_supported
  | Plain => exact N.plain_supported
  | Boolean => exact N.boolean_supported
  | Real => exact N.real_supported
  | Rational => exact N.rational_supported
  | AnyUri => exact N.uri_supported
  | HexBinary => exact N.hex_supported
  | Base64Binary => exact N.base64_supported
  | NormalizedString => exact N.string_subtype_supported .normalized
  | Token => exact N.string_subtype_supported .token
  | Language => exact N.string_subtype_supported .language
  | NmToken => exact N.string_subtype_supported .nmtoken
  | Name => exact N.string_subtype_supported .«name»
  | NcName => exact N.string_subtype_supported .ncname
  | DateTime => exact N.datetime_supported
  | DateTimeStamp => exact N.stamp_supported
  | Double => exact N.double_supported
  | Float => exact N.float_supported
  | _ => exact subtype _ trivial

theorem number_value_canonical {v : datatypes.DataValue} {q : ℚ} (h : NumberValue v q) : Canonical v := by
  rcases h with ⟨n, w, f, rfl, c, rfl⟩ | ⟨n, a, b, rfl, c, rfl⟩
  · exact c
  · exact c

theorem number_value_of (N : Normative D) {v : datatypes.DataValue} {q : ℚ} (h : NumberValue v q) :
    valueOf N v = N.number q := by
  rcases h with ⟨n, w, f, rfl, c, rfl⟩ | ⟨n, a, b, rfl, c, rfl⟩ <;> rfl

theorem lexical_subtype (k : datatypes.Kind) (sub : IsSubtype k) (t : List U8) :
    LexicalForm k t ↔ ∃ z : ℤ, Bounded (lowerOf k) (upperOf k) z ∧ IntegerForm t (z : ℚ) := by
  cases k <;> simp_all [IsSubtype, LexicalForm]

theorem numberIn_subtype (k : datatypes.Kind) (sub : IsSubtype k) (whole : Prop) (q : ℚ) :
    NumberIn k whole q ↔ whole ∧ (∀ l, lowerOf k = some l → (l : ℚ) ≤ q) ∧ (∀ u, upperOf k = some u → q ≤ (u : ℚ)) := by
  cases k <;> simp_all [IsSubtype, NumberIn]

theorem bounded_iff (k : datatypes.Kind) (z : ℤ) :
    Bounded (lowerOf k) (upperOf k) z ↔
      (∀ l, lowerOf k = some l → (l : ℚ) ≤ z) ∧ (∀ u, upperOf k = some u → (z : ℚ) ≤ u) := by
  simp only [Bounded]
  constructor
  · rintro ⟨low, high⟩
    exact ⟨fun l hl => by exact_mod_cast low l hl, fun u hu => by exact_mod_cast high u hu⟩
  · rintro ⟨low, high⟩
    exact ⟨fun l hl => by exact_mod_cast low l hl, fun u hu => by exact_mod_cast high u hu⟩

/-- The integer of a canonical number without fraction digits. -/
theorem whole_integer {n : Bool} {w f : List U8} (c : CanonicalNumber n w f) (empty : f = []) :
    ∃ z : ℤ, numberOf n w f = z := by
  obtain ⟨z, hz⟩ := (numberOf_integer c).mpr empty
  exact ⟨z, hz⟩

/-! ### IRIs and octets -/

/-- The kernel's value of a hexadecimal digit. -/
theorem hex_digit_correct (byte : U8) :
    ∃ r, datatypes.hex_digit byte = .ok r ∧ r.map (·.val) = hexDigitValue byte := by
  rw [datatypes.hex_digit]
  by_cases h1 : 48 ≤ byte.val ∧ byte.val ≤ 57
  · have := h1.1; have := h1.2
    obtain ⟨d, sub, dValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := byte) (y := 48#u8) (by scalar_tac))
    exact ⟨some d, by simp [UScalar.le_equiv, *], by simp [hexDigitValue, h1, dValue]⟩
  by_cases h2 : 65 ≤ byte.val ∧ byte.val ≤ 70
  · have := h2.1; have := h2.2
    have n1 : ¬ byte.val ≤ 57 := by omega
    obtain ⟨d, sub, dValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := byte) (y := 55#u8) (by scalar_tac))
    exact ⟨some d, by simp [UScalar.le_equiv, *], by simp [hexDigitValue, h1, h2, dValue]⟩
  by_cases h3 : 97 ≤ byte.val ∧ byte.val ≤ 102
  · have := h3.1; have := h3.2
    have n1 : ¬ byte.val ≤ 57 := by omega
    have n2 : ¬ byte.val ≤ 70 := by omega
    obtain ⟨d, sub, dValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := byte) (y := 87#u8) (by scalar_tac))
    exact ⟨some d, by simp [UScalar.le_equiv, *], by simp [hexDigitValue, h1, h2, h3, dValue]⟩
  refine ⟨none, ?_, by simp [hexDigitValue, h1, h2, h3]⟩
  rcases (by omega : byte.val < 48 ∨ (57 < byte.val ∧ byte.val < 65) ∨ (70 < byte.val ∧ byte.val < 97) ∨
      102 < byte.val) with r | ⟨r1, r2⟩ | ⟨r1, r2⟩ | r
  · have : ¬ 48 ≤ byte.val := by omega
    have : ¬ 65 ≤ byte.val := by omega
    have : ¬ 97 ≤ byte.val := by omega
    simp [UScalar.le_equiv, *]
  · have : ¬ byte.val ≤ 57 := by omega
    have : ¬ 65 ≤ byte.val := by omega
    have : ¬ 97 ≤ byte.val := by omega
    simp [UScalar.le_equiv, *]
  · have : ¬ byte.val ≤ 57 := by omega
    have : ¬ byte.val ≤ 70 := by omega
    have : ¬ 97 ≤ byte.val := by omega
    simp [UScalar.le_equiv, *]
  · have : ¬ byte.val ≤ 57 := by omega
    have : ¬ byte.val ≤ 70 := by omega
    have : ¬ byte.val ≤ 102 := by omega
    simp [UScalar.le_equiv, *]

private theorem hex_digit_small {byte : U8} {d : Nat} (h : hexDigitValue byte = some d) : d < 16 := by
  unfold hexDigitValue at h
  split_ifs at h <;> simp at h <;> omega

private theorem push_octet_spec (out : alloc.vec.Vec U8) (octet : U8) (room : out.val.length < Usize.max) :
    ∃ v, datatypes.push_octet out octet = .ok (some v) ∧ v.val = out.val ++ [octet] := by
  obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out octet room)
  exact ⟨pushed, by simp [datatypes.push_octet, alloc.vec.Vec.len_val, usize_max_val, room, push], contents⟩

/-- A hexadecimal lexical form has one value. -/
theorem hex_form_unique : ∀ {t o o' : List U8}, HexForm t o → HexForm t o' → o = o'
  | [], _, _, h, h' => by simp only [HexForm] at h h'; rw [h, h']
  | [_], _, _, h, _ => by simp [HexForm] at h
  | _ :: _ :: _, _, _, h, h' => by
    obtain ⟨x, y, octet, o1, hx, hy, rfl, hv, hr⟩ := h
    obtain ⟨x', y', octet', o1', hx', hy', rfl, hv', hr'⟩ := h'
    rw [hx] at hx'; rw [hy] at hy'
    simp only [Option.some.injEq] at hx' hy'
    subst hx' hy'
    rw [hex_form_unique hr hr', UScalar.eq_of_val_eq (hv.trans hv'.symm)]

/-- The kernel reads exactly the hexadecimal lexical forms, each to its octets. -/
theorem hex_from_correct (lexical : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length ≤ index.val) :
    ∃ r, datatypes.hex_from lexical index out = .ok r ∧
      (∀ v, r = some v → ∃ o, v.val = out.val ++ o ∧ HexForm (lexical.val.drop index.val) o) ∧
      (r = none → ∀ o, ¬ HexForm (lexical.val.drop index.val) o) := by
  have size := lexical.property
  rw [datatypes.hex_from]
  by_cases more : index.val < lexical.val.length
  · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = index.val + 1 := by simpa using nextValue
    have lookup1 : lexical.index_usize index = .ok lexical.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    by_cases pair : next.val < lexical.val.length
    · have pair' : index.val + 1 < lexical.val.length := by omega
      have lookup2 : lexical.index_usize next = .ok lexical.val[index.val + 1] := by
        simp [alloc.vec.Vec.index_usize, nextIs, List.getElem?_eq_getElem pair']
      have split : lexical.val.drop index.val =
          lexical.val[index.val] :: lexical.val[index.val + 1] :: lexical.val.drop (index.val + 2) := by
        rw [List.drop_eq_getElem_cons more, List.drop_eq_getElem_cons pair']
      obtain ⟨r1, run1, value1⟩ := hex_digit_correct lexical.val[index.val]
      cases r1 with
      | none =>
        refine ⟨none, by simp [UScalar.lt_equiv, more, advance, nextIs, pair', lookup1, run1], by simp,
          fun _ o form => ?_⟩
        rw [split] at form
        obtain ⟨x, _, _, _, hx, _⟩ := form
        rw [hx] at value1
        simp at value1
      | some high =>
        obtain ⟨r2, run2, value2⟩ := hex_digit_correct lexical.val[index.val + 1]
        cases r2 with
        | none =>
          refine ⟨none, by simp [UScalar.lt_equiv, more, advance, nextIs, pair', lookup1, lookup2, run1, run2],
            by simp, fun _ o form => ?_⟩
          rw [split] at form
          obtain ⟨_, y, _, _, _, hy, _⟩ := form
          rw [hy] at value2
          simp at value2
        | some low =>
          have hv : hexDigitValue lexical.val[index.val] = some high.val := by simpa using value1.symm
          have lv : hexDigitValue lexical.val[index.val + 1] = some low.val := by simpa using value2.symm
          have hs := hex_digit_small hv
          have ls := hex_digit_small lv
          obtain ⟨m, mul, mValue⟩ := WP.spec_imp_exists
            (UScalar.mul_spec (x := high) (y := 16#u8) (by scalar_tac))
          have mIs : m.val = high.val * 16 := by simpa using mValue
          obtain ⟨s, add, sValue⟩ := WP.spec_imp_exists (U8.add_spec (x := m) (y := low) (by scalar_tac))
          have sIs : s.val = 16 * high.val + low.val := by rw [sValue, mIs]; ring
          have roomOut : out.val.length < Usize.max := by omega
          obtain ⟨pushed, push, contents⟩ := push_octet_spec out s roomOut
          obtain ⟨after, advance2, afterValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 2#usize) (by scalar_tac))
          have afterIs : after.val = index.val + 2 := by simpa using afterValue
          obtain ⟨r, run, someCase, noneCase⟩ := hex_from_correct lexical after pushed
            (by rw [contents, afterIs]; simp; omega)
          rw [afterIs] at someCase noneCase
          refine ⟨r, by simp [UScalar.lt_equiv, more, advance, nextIs, pair', lookup1, lookup2, run1, run2, mul,
            add, push, advance2, run], fun v hv' => ?_, fun hn o form => ?_⟩
          · obtain ⟨o, hvo, form⟩ := someCase v hv'
            refine ⟨s :: o, by rw [hvo, contents]; simp, ?_⟩
            rw [split]
            exact ⟨high.val, low.val, s, o, hv, lv, rfl, sIs, form⟩
          · rw [split] at form
            obtain ⟨_, _, _, o', _, _, _, _, rest⟩ := form
            exact noneCase hn o' rest
    · have single : lexical.val.drop index.val = [lexical.val[index.val]] := by
        rw [List.drop_eq_getElem_cons more, List.drop_eq_nil_of_le (by omega)]
      refine ⟨none, by simp [UScalar.lt_equiv, more, advance, pair], by simp, fun _ o form => ?_⟩
      rw [single] at form
      simp [HexForm] at form
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun v hv => ⟨[], by cases hv; simp, ?_⟩, by simp⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [HexForm]
termination_by lexical.val.length - index.val
decreasing_by omega

/-- The kernel's value of a character of the Base64 alphabet. -/
theorem sextet_correct (byte : U8) :
    ∃ r, datatypes.sextet byte = .ok r ∧ r.map (·.val) = base64Value byte := by
  rw [datatypes.sextet]
  by_cases h1 : 65 ≤ byte.val ∧ byte.val ≤ 90
  · have := h1.1; have := h1.2
    obtain ⟨d, sub, dValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := byte) (y := 65#u8) (by scalar_tac))
    exact ⟨some d, by simp [UScalar.le_equiv, *], by simp [base64Value, h1, dValue]⟩
  by_cases h2 : 97 ≤ byte.val ∧ byte.val ≤ 122
  · have := h2.1; have := h2.2
    have n1 : ¬ byte.val ≤ 90 := by omega
    obtain ⟨d, sub, dValue⟩ := WP.spec_imp_exists (U8.sub_spec (x := byte) (y := 71#u8) (by scalar_tac))
    exact ⟨some d, by simp [UScalar.le_equiv, *], by simp [base64Value, h1, h2, dValue]⟩
  by_cases h3 : 48 ≤ byte.val ∧ byte.val ≤ 57
  · have := h3.1; have := h3.2
    have n1 : ¬ 65 ≤ byte.val := by omega
    have n2 : ¬ 97 ≤ byte.val := by omega
    obtain ⟨d, add, dValue⟩ := WP.spec_imp_exists (U8.add_spec (x := byte) (y := 4#u8) (by scalar_tac))
    exact ⟨some d, by simp [UScalar.le_equiv, *], by simp [base64Value, h1, h2, h3, dValue]⟩
  have n1 : ¬ (65 ≤ byte.val ∧ byte.val ≤ 90) := h1
  by_cases h4 : byte.val = 43
  · have e : byte = 43#u8 := UScalar.eq_of_val_eq (by simpa using h4)
    subst e
    exact ⟨some 62#u8, by simp [UScalar.le_equiv], by simp [base64Value]⟩
  by_cases h5 : byte.val = 47
  · have e : byte = 47#u8 := UScalar.eq_of_val_eq (by simpa using h5)
    subst e
    exact ⟨some 63#u8, by simp [UScalar.le_equiv], by simp [base64Value]⟩
  have n4 : byte ≠ 43#u8 := fun e => h4 (by rw [e]; rfl)
  have n5 : byte ≠ 47#u8 := fun e => h5 (by rw [e]; rfl)
  refine ⟨none, ?_, by simp [base64Value, h1, h2, h3, h4, h5]⟩
  rcases (by omega : byte.val < 48 ∨ (57 < byte.val ∧ byte.val < 65) ∨ (90 < byte.val ∧ byte.val < 97) ∨
      122 < byte.val) with r | ⟨r1, r2⟩ | ⟨r1, r2⟩ | r
  · have : ¬ 65 ≤ byte.val := by omega
    have : ¬ 97 ≤ byte.val := by omega
    have : ¬ 48 ≤ byte.val := by omega
    simp [UScalar.le_equiv, *]
  · have : ¬ 65 ≤ byte.val := by omega
    have : ¬ 97 ≤ byte.val := by omega
    have : ¬ byte.val ≤ 57 := by omega
    simp [UScalar.le_equiv, *]
  · have : ¬ byte.val ≤ 90 := by omega
    have : ¬ 97 ≤ byte.val := by omega
    have : ¬ byte.val ≤ 57 := by omega
    simp [UScalar.le_equiv, *]
  · have : ¬ byte.val ≤ 90 := by omega
    have : ¬ byte.val ≤ 122 := by omega
    have : ¬ byte.val ≤ 57 := by omega
    simp [UScalar.le_equiv, *]

private theorem sextet_small {byte : U8} {d : Nat} (h : base64Value byte = some d) : d < 64 := by
  unfold base64Value at h
  split_ifs at h <;> simp at h <;> omega

private theorem space_no_sextet : base64Value 32#u8 = none := by decide
private theorem pad_no_sextet : base64Value 61#u8 = none := by decide

/-- The characters of Base64 groups are no spaces. -/
theorem base64_chars_spaceless : ∀ {chars o : List U8}, Base64Chars chars o → (32#u8) ∉ chars
  | [], _, _ => by simp
  | a :: b :: c :: d :: rest, o, h => by
    obtain ⟨va, vb, ha, hb, cases⟩ := h
    have na : a ≠ 32#u8 := fun e => by rw [e, space_no_sextet] at ha; cases ha
    have nb : b ≠ 32#u8 := fun e => by rw [e, space_no_sextet] at hb; cases hb
    rcases cases with ⟨vc, vd, _, _, _, _, hc, hd, _, _, _, _, rest'⟩ | ⟨vc, _, _, rfl, hc, rfl, _⟩ |
        ⟨_, rfl, rfl, rfl, _⟩
    · have nc : c ≠ 32#u8 := fun e => by rw [e, space_no_sextet] at hc; cases hc
      have nd : d ≠ 32#u8 := fun e => by rw [e, space_no_sextet] at hd; cases hd
      have := base64_chars_spaceless rest'
      simp only [List.mem_cons, not_or]
      exact ⟨na.symm, nb.symm, nc.symm, nd.symm, this⟩
    · have nc : c ≠ 32#u8 := fun e => by rw [e, space_no_sextet] at hc; cases hc
      simp only [List.mem_cons, not_or, List.not_mem_nil]
      exact ⟨na.symm, nb.symm, nc.symm, by decide, not_false⟩
    · simp only [List.mem_cons, not_or, List.not_mem_nil]
      exact ⟨na.symm, nb.symm, by decide, by decide, not_false⟩
  | [_], _, h => by simp [Base64Chars] at h
  | [_, _], _, h => by simp [Base64Chars] at h
  | [_, _, _], _, h => by simp [Base64Chars] at h

/-- Base64 groups have one value. -/
theorem base64_chars_unique : ∀ {chars o o' : List U8}, Base64Chars chars o → Base64Chars chars o' → o = o'
  | [], _, _, h, h' => by simp only [Base64Chars] at h h'; rw [h, h']
  | a :: b :: c :: d :: rest, o, o', h, h' => by
    obtain ⟨va, vb, ha, hb, cases⟩ := h
    obtain ⟨va', vb', ha', hb', cases'⟩ := h'
    rw [ha] at ha'; rw [hb] at hb'
    simp only [Option.some.injEq] at ha' hb'
    subst ha' hb'
    rcases cases with ⟨vc, vd, x, y, z, o1, hc, hd, rfl, hx, hy, hz, r1⟩ |
        ⟨vc, x, y, rfl, hc, rfl, _, rfl, hx, hy⟩ | ⟨x, rfl, rfl, rfl, _, rfl, hx⟩ <;>
      rcases cases' with ⟨vc', vd', x', y', z', o1', hc', hd', rfl, hx', hy', hz', r1'⟩ |
        ⟨vc', x', y', hrest', hc', hd', _, rfl, hx', hy'⟩ | ⟨x', hrest', hcpad', hdpad', _, rfl, hx'⟩
    · rw [hc] at hc'; rw [hd] at hd'
      simp only [Option.some.injEq] at hc' hd'
      subst hc' hd'
      rw [base64_chars_unique r1 r1', UScalar.eq_of_val_eq (hx.trans hx'.symm),
        UScalar.eq_of_val_eq (hy.trans hy'.symm), UScalar.eq_of_val_eq (hz.trans hz'.symm)]
    · rw [hd', pad_no_sextet] at hd; cases hd
    · rw [hcpad', pad_no_sextet] at hc; cases hc
    · rw [pad_no_sextet] at hd'; cases hd'
    · rw [hc] at hc'
      simp only [Option.some.injEq] at hc'
      subst hc'
      rw [UScalar.eq_of_val_eq (hx.trans hx'.symm), UScalar.eq_of_val_eq (hy.trans hy'.symm)]
    · rw [hcpad', pad_no_sextet] at hc; cases hc
    · rw [pad_no_sextet] at hc'; cases hc'
    · rw [pad_no_sextet] at hc'; cases hc'
    · rw [UScalar.eq_of_val_eq (hx.trans hx'.symm)]
  | [_], _, _, h, _ => by simp [Base64Chars] at h
  | [_, _], _, _, h, _ => by simp [Base64Chars] at h
  | [_, _, _], _, _, h, _ => by simp [Base64Chars] at h

/-- The first character of a spaced text is its first byte. -/
private theorem spaced_head {text : List U8} {c : U8} {cs : List U8} (h : Spaced text (c :: cs)) :
    ∃ rest, text = c :: rest := by
  cases cs with
  | nil => exact ⟨[], by simpa [Spaced] using h⟩
  | cons d ds =>
    obtain ⟨rest, shape, _⟩ := h
    rcases shape with rfl | rfl
    · exact ⟨rest, rfl⟩
    · exact ⟨32#u8 :: rest, rfl⟩

private theorem spaced_nil {chars : List U8} (h : Spaced [] chars) : chars = [] := by
  cases chars with
  | nil => rfl
  | cons c cs =>
    obtain ⟨rest, e⟩ := spaced_head h
    cases e

/-- The characters of a spaced text without spaces among them are unique. -/
theorem spaced_unique : ∀ {text c1 c2 : List U8}, Spaced text c1 → Spaced text c2 → (32#u8) ∉ c1 →
    (32#u8) ∉ c2 → c1 = c2
  | text, [], c2, h1, h2, _, _ => by
    simp only [Spaced] at h1
    subst h1
    exact (spaced_nil h2).symm
  | text, [c], [], h1, h2, _, _ => by
    simp only [Spaced] at h1 h2
    rw [h1] at h2
    cases h2
  | text, [c], [d], h1, h2, _, _ => by
    simp only [Spaced] at h1 h2
    rw [h1] at h2
    simp only [List.cons.injEq, and_true] at h2
    rw [h2]
  | text, [c], d :: e :: es, h1, h2, _, n2 => by
    simp only [Spaced] at h1
    subst h1
    obtain ⟨rest, shape, inner⟩ := h2
    rcases shape with e1 | e1
    · simp only [List.cons.injEq] at e1
      obtain ⟨_, rfl⟩ := e1
      exact absurd (spaced_nil inner) (by simp)
    · simp at e1
  | text, c :: d :: cs, [], h1, h2, _, _ => by
    simp only [Spaced] at h2
    subst h2
    obtain ⟨rest, e⟩ := spaced_head h1
    cases e
  | text, c :: d :: cs, [e], h1, h2, n1, _ => by
    simp only [Spaced] at h2
    subst h2
    obtain ⟨rest, shape, inner⟩ := h1
    rcases shape with e1 | e1
    · simp only [List.cons.injEq] at e1
      obtain ⟨_, rfl⟩ := e1
      exact absurd (spaced_nil inner) (by simp)
    · simp at e1
  | text, c :: d :: cs, c' :: d' :: cs', h1, h2, n1, n2 => by
    obtain ⟨r1, shape1, inner1⟩ := h1
    obtain ⟨r2, shape2, inner2⟩ := h2
    have nd : d ≠ 32#u8 := fun e => n1 (by rw [e]; simp)
    have nd' : d' ≠ 32#u8 := fun e => n2 (by rw [e]; simp)
    have tail1 : (32#u8) ∉ d :: cs := fun m => n1 (List.mem_cons_of_mem _ m)
    have tail2 : (32#u8) ∉ d' :: cs' := fun m => n2 (List.mem_cons_of_mem _ m)
    rcases shape1 with rfl | rfl <;> rcases shape2 with e2 | e2 <;> simp only [List.cons.injEq] at e2
    · obtain ⟨rfl, rfl⟩ := e2
      rw [spaced_unique inner1 inner2 tail1 tail2]
    · obtain ⟨rfl, rfl⟩ := e2
      obtain ⟨rest, e⟩ := spaced_head inner1
      simp only [List.cons.injEq] at e
      exact absurd e.1.symm nd
    · obtain ⟨rfl, e2'⟩ := e2
      obtain ⟨rest, e⟩ := spaced_head inner2
      rw [e] at e2'
      simp only [List.cons.injEq] at e2'
      exact absurd e2'.1.symm nd'
    · obtain ⟨rfl, _, rfl⟩ := e2
      rw [spaced_unique inner1 inner2 tail1 tail2]

/-- A Base64 lexical form has one value. -/
theorem base64_form_unique {text o o' : List U8} (h : Base64Form text o) (h' : Base64Form text o') : o = o' := by
  obtain ⟨c1, s1, b1⟩ := h
  obtain ⟨c2, s2, b2⟩ := h'
  rw [spaced_unique s1 s2 (base64_chars_spaceless b1) (base64_chars_spaceless b2)] at b1
  exact base64_chars_unique b1 b2

private theorem spaced_space {text chars : List U8} (h : Spaced (32#u8 :: text) chars) (n : (32#u8) ∉ chars) :
    False := by
  cases chars with
  | nil => simp [Spaced] at h
  | cons c cs =>
    obtain ⟨rest, e⟩ := spaced_head h
    simp only [List.cons.injEq] at e
    exact n (by rw [← e.1]; simp)

/-- The kernel removes exactly the spaces of the Base64 grammar: one after a
    character, never first, last or twice. -/
theorem unspaced_correct (lexical : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length ≤ index.val) :
    ∃ r, datatypes.unspaced lexical index out = .ok r ∧
      (∀ v, r = some v → ∃ chars, v.val = out.val ++ chars ∧ Spaced (lexical.val.drop index.val) chars ∧
        (32#u8) ∉ chars) ∧
      (r = none → ∀ chars, (32#u8) ∉ chars → ¬ Spaced (lexical.val.drop index.val) chars) := by
  have size := lexical.property
  rw [datatypes.unspaced]
  by_cases more : index.val < lexical.val.length
  · have lookup : lexical.index_usize index = .ok lexical.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
    have split := List.drop_eq_getElem_cons more
    by_cases space : lexical.val[index.val] = 32#u8
    · refine ⟨none, by simp [UScalar.lt_equiv, more, lookup, space], by simp, fun _ chars n form => ?_⟩
      rw [split, space] at form
      exact spaced_space form n
    · have roomOut : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := push_octet_spec out lexical.val[index.val] roomOut
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIs : next.val = index.val + 1 := by simpa using nextValue
      by_cases pair : index.val + 1 < lexical.val.length
      · have lookup2 : lexical.index_usize next = .ok lexical.val[index.val + 1] := by
          simp [alloc.vec.Vec.index_usize, nextIs, List.getElem?_eq_getElem pair]
        have split2 : lexical.val.drop (index.val + 1) =
            lexical.val[index.val + 1] :: lexical.val.drop (index.val + 2) :=
          List.drop_eq_getElem_cons pair
        by_cases space2 : lexical.val[index.val + 1] = 32#u8
        · obtain ⟨after, advance2, afterValue⟩ := WP.spec_imp_exists
            (Usize.add_spec (x := index) (y := 2#usize) (by scalar_tac))
          have afterIs : after.val = index.val + 2 := by simpa using afterValue
          by_cases third : index.val + 2 < lexical.val.length
          · obtain ⟨r, run, someCase, noneCase⟩ := unspaced_correct lexical after pushed
              (by rw [contents, afterIs]; simp; omega)
            rw [afterIs] at someCase noneCase
            have nonempty : lexical.val.drop (index.val + 2) ≠ [] := by
              intro e; have := List.drop_eq_nil_iff.mp e; omega
            refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, space, push, advance, nextIs, pair, lookup2,
              space2, advance2, afterIs, third, run], fun v hv => ?_, fun hn chars n form => ?_⟩
            · obtain ⟨chars, hvc, spaced, n⟩ := someCase v hv
              cases chars with
              | nil => exact absurd (by simpa [Spaced] using spaced) nonempty
              | cons d ds =>
                refine ⟨lexical.val[index.val] :: d :: ds, by rw [hvc, contents]; simp, ?_, ?_⟩
                · rw [split, split2, space2]
                  exact ⟨_, .inr rfl, spaced⟩
                · simp only [List.mem_cons, not_or]
                  exact ⟨fun e => space e.symm, by simpa using n⟩
            · rw [split, split2, space2] at form
              cases chars with
              | nil => simp [Spaced] at form
              | cons c cs =>
                cases cs with
                | nil => simp [Spaced] at form
                | cons d ds =>
                  obtain ⟨rest, shape, inner⟩ := form
                  have tail : (32#u8) ∉ d :: ds := fun m => n (List.mem_cons_of_mem _ m)
                  rcases shape with e | e <;> simp only [List.cons.injEq] at e
                  · obtain ⟨_, rfl⟩ := e
                    exact spaced_space inner tail
                  · obtain ⟨_, _, rfl⟩ := e
                    exact noneCase hn _ tail inner
          · refine ⟨none, by simp [UScalar.lt_equiv, more, lookup, space, push, advance, nextIs, pair, lookup2,
              space2, advance2, afterIs, third], by simp, fun _ chars n form => ?_⟩
            have empty : lexical.val.drop (index.val + 2) = [] := List.drop_eq_nil_of_le (by omega)
            rw [split, split2, space2, empty] at form
            cases chars with
            | nil => simp [Spaced] at form
            | cons c cs =>
              cases cs with
              | nil => simp [Spaced] at form
              | cons d ds =>
                obtain ⟨rest, shape, inner⟩ := form
                have tail : (32#u8) ∉ d :: ds := fun m => n (List.mem_cons_of_mem _ m)
                rcases shape with e | e <;> simp only [List.cons.injEq] at e
                · obtain ⟨_, rfl⟩ := e
                  exact spaced_space inner tail
                · obtain ⟨_, _, rfl⟩ := e
                  exact absurd (spaced_nil inner) (by simp)
        · obtain ⟨r, run, someCase, noneCase⟩ := unspaced_correct lexical next pushed
            (by rw [contents, nextIs]; simp; omega)
          rw [nextIs] at someCase noneCase
          have nonempty : lexical.val.drop (index.val + 1) ≠ [] := by
            intro e; have := List.drop_eq_nil_iff.mp e; omega
          refine ⟨r, by simp [UScalar.lt_equiv, more, lookup, space, push, advance, nextIs, pair, lookup2, space2,
            run], fun v hv => ?_, fun hn chars n form => ?_⟩
          · obtain ⟨chars, hvc, spaced, n⟩ := someCase v hv
            cases chars with
            | nil => exact absurd (by simpa [Spaced] using spaced) nonempty
            | cons d ds =>
              refine ⟨lexical.val[index.val] :: d :: ds, by rw [hvc, contents]; simp, ?_, ?_⟩
              · rw [split]
                exact ⟨_, .inl rfl, spaced⟩
              · simp only [List.mem_cons, not_or]
                exact ⟨fun e => space e.symm, by simpa using n⟩
          · rw [split] at form
            cases chars with
            | nil => (simp [Spaced] at form; omega)
            | cons c cs =>
              cases cs with
              | nil =>
                simp only [Spaced, List.cons.injEq] at form
                exact nonempty form.2
              | cons d ds =>
                obtain ⟨rest, shape, inner⟩ := form
                have tail : (32#u8) ∉ d :: ds := fun m => n (List.mem_cons_of_mem _ m)
                rcases shape with e | e <;> simp only [List.cons.injEq] at e
                · obtain ⟨_, rfl⟩ := e
                  exact noneCase hn _ tail inner
                · obtain ⟨_, e2⟩ := e
                  rw [split2] at e2
                  simp only [List.cons.injEq] at e2
                  exact space2 e2.1
      · have last : lexical.val.drop (index.val + 1) = [] := List.drop_eq_nil_of_le (by omega)
        refine ⟨some pushed, by simp [UScalar.lt_equiv, more, lookup, space, push, advance, nextIs, pair],
          fun v hv => ⟨[lexical.val[index.val]], by cases hv; rw [contents], ?_, ?_⟩, by simp⟩
        · rw [split, last]; rfl
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact fun e => space e.symm
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun v hv => ⟨[], by cases hv; simp, ?_, by simp⟩, by simp⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
termination_by lexical.val.length - index.val
decreasing_by all_goals omega

private theorem u8_mul {x : U8} {k : U8} (bound : x.val * k.val ≤ 255) :
    ∃ y : U8, (x * k : Result U8) = .ok y ∧ y.val = x.val * k.val := by
  obtain ⟨y, run, value⟩ := WP.spec_imp_exists (UScalar.mul_spec (x := x) (y := k) (by scalar_tac))
  exact ⟨y, run, by simpa using value⟩

private theorem u8_add {x y : U8} (bound : x.val + y.val ≤ 255) :
    ∃ z : U8, (x + y : Result U8) = .ok z ∧ z.val = x.val + y.val := by
  obtain ⟨z, run, value⟩ := WP.spec_imp_exists (U8.add_spec (x := x) (y := y) (by scalar_tac))
  exact ⟨z, run, by simpa using value⟩

private theorem u8_div {x : U8} {k : U8} (nonzero : k.val ≠ 0) :
    ∃ y : U8, (x / k : Result U8) = .ok y ∧ y.val = x.val / k.val := by
  obtain ⟨y, run, value⟩ := WP.spec_imp_exists (U8.div_spec (x := x) (y := k) nonzero)
  exact ⟨y, run, by simpa using value⟩

private theorem u8_rem {x : U8} {k : U8} (nonzero : k.val ≠ 0) :
    ∃ y : U8, (x % k : Result U8) = .ok y ∧ y.val = x.val % k.val := by
  obtain ⟨y, run, value⟩ := WP.spec_imp_exists (U8.rem_spec (x := x) (y := k) nonzero)
  exact ⟨y, run, by simpa using value⟩

private theorem padded_one_correct (chars : alloc.vec.Vec U8) (index : Usize) (a b : U8) (out : alloc.vec.Vec U8)
    (more : index.val + 3 < chars.val.length) (va : a.val < 64) (vb : b.val < 64)
    (room : out.val.length < Usize.max) :
    ∃ r, datatypes.padded_one chars index a b out = .ok r ∧
      (∀ v, r = some v → ∃ x : U8, v.val = out.val ++ [x] ∧ chars.val[index.val + 3] = 61#u8 ∧
        index.val + 4 = chars.val.length ∧ b.val % 16 = 0 ∧ x.val = a.val * 4 + b.val / 16) ∧
      (r = none → ¬ (chars.val[index.val + 3] = 61#u8 ∧ index.val + 4 = chars.val.length ∧ b.val % 16 = 0)) := by
  have size := chars.property
  rw [datatypes.padded_one]
  obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
  have i3Is : i3.val = index.val + 3 := by simpa using i3Value
  have lookup : chars.index_usize i3 = .ok chars.val[index.val + 3] := by
    simp [alloc.vec.Vec.index_usize, i3Is, List.getElem?_eq_getElem more]
  by_cases pad : chars.val[index.val + 3] = 61#u8
  · obtain ⟨i4, add4, i4Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 4#usize) (by scalar_tac))
    have i4Is : i4.val = index.val + 4 := by simpa using i4Value
    by_cases ends : index.val + 4 = chars.val.length
    · have endsU : i4 = alloc.vec.Vec.len chars := UScalar.eq_of_val_eq (by simp [i4Is, ends])
      obtain ⟨m, mRun, mValue⟩ := u8_rem (x := b) (k := 16#u8) (by simp)
      by_cases zero : b.val % 16 = 0
      · have mZero : m = 0#u8 := UScalar.eq_of_val_eq (by simp [mValue, zero])
        obtain ⟨i, iRun, iValue⟩ := u8_mul (x := a) (k := 4#u8) (by simp; omega)
        obtain ⟨j, jRun, jValue⟩ := u8_div (x := b) (k := 16#u8) (by simp)
        obtain ⟨x, xRun, xValue⟩ := u8_add (x := i) (y := j) (by simp [iValue, jValue]; omega)
        obtain ⟨v, push, contents⟩ := push_octet_spec out x room
        refine ⟨some v, by simp [alloc.vec.Vec.index_slice_index, add3, lookup, pad, add4, endsU, mRun, mZero, iRun,
          jRun, xRun, push], fun v' hv => ?_, by simp⟩
        cases hv
        exact ⟨x, contents, pad, ends, zero, by rw [xValue, iValue, jValue]; simp⟩
      · have mNonzero : m ≠ 0#u8 := fun e => zero (by
          have := congrArg UScalar.val e; simp [mValue] at this; omega)
        exact ⟨none, by simp [alloc.vec.Vec.index_slice_index, add3, lookup, pad, add4, endsU, mRun, mNonzero],
          by simp, fun _ ⟨_, _, z⟩ => zero z⟩
    · have notEnds : i4 ≠ alloc.vec.Vec.len chars := fun e => ends (by
        have := congrArg UScalar.val e; simp [i4Is] at this; omega)
      exact ⟨none, by simp [alloc.vec.Vec.index_slice_index, add3, lookup, pad, add4, notEnds], by simp,
        fun _ ⟨_, e, _⟩ => ends e⟩
  · exact ⟨none, by simp [alloc.vec.Vec.index_slice_index, add3, lookup, pad], by simp, fun _ ⟨p, _⟩ => pad p⟩

private theorem padded_two_correct (chars : alloc.vec.Vec U8) (index : Usize) (a b c : U8)
    (out : alloc.vec.Vec U8) (va : a.val < 64) (vb : b.val < 64) (vc : c.val < 64)
    (room : out.val.length + 1 < Usize.max) (fits : index.val + 4 ≤ Usize.max) :
    ∃ r, datatypes.padded_two chars index a b c out = .ok r ∧
      (∀ v, r = some v → ∃ x y : U8, v.val = out.val ++ [x, y] ∧ index.val + 4 = chars.val.length ∧
        c.val % 4 = 0 ∧ x.val = a.val * 4 + b.val / 16 ∧ y.val = b.val % 16 * 16 + c.val / 4) ∧
      (r = none → ¬ (index.val + 4 = chars.val.length ∧ c.val % 4 = 0)) := by
  rw [datatypes.padded_two]
  obtain ⟨i4, add4, i4Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 4#usize) (by scalar_tac))
  have i4Is : i4.val = index.val + 4 := by simpa using i4Value
  by_cases ends : index.val + 4 = chars.val.length
  · have endsU : i4 = alloc.vec.Vec.len chars := UScalar.eq_of_val_eq (by simp [i4Is, ends])
    obtain ⟨m, mRun, mValue⟩ := u8_rem (x := c) (k := 4#u8) (by simp)
    by_cases zero : c.val % 4 = 0
    · have mZero : m = 0#u8 := UScalar.eq_of_val_eq (by simp [mValue, zero])
      obtain ⟨i, iRun, iValue⟩ := u8_mul (x := a) (k := 4#u8) (by simp; omega)
      obtain ⟨j, jRun, jValue⟩ := u8_div (x := b) (k := 16#u8) (by simp)
      obtain ⟨x, xRun, xValue⟩ := u8_add (x := i) (y := j) (by simp [iValue, jValue]; omega)
      obtain ⟨v1, push1, contents1⟩ := push_octet_spec out x (by omega)
      obtain ⟨p, pRun, pValue⟩ := u8_rem (x := b) (k := 16#u8) (by simp)
      have pSmall : p.val < 16 := by rw [pValue]; simp; omega
      obtain ⟨q, qRun, qValue⟩ := u8_mul (x := p) (k := 16#u8) (by simp; omega)
      obtain ⟨k, kRun, kValue⟩ := u8_div (x := c) (k := 4#u8) (by simp)
      obtain ⟨y, yRun, yValue⟩ := u8_add (x := q) (y := k) (by simp [qValue, kValue]; omega)
      obtain ⟨v2, push2, contents2⟩ := push_octet_spec v1 y (by rw [contents1]; simp; omega)
      refine ⟨some v2, by simp [add4, endsU, mRun, mZero, iRun, jRun, xRun, push1, pRun, qRun, kRun, yRun, push2],
        fun v' hv => ?_, by simp⟩
      cases hv
      exact ⟨x, y, by rw [contents2, contents1]; simp, ends, zero, by rw [xValue, iValue, jValue]; simp,
        by rw [yValue, qValue, kValue, pValue]; simp⟩
    · have mNonzero : m ≠ 0#u8 := fun e => zero (by
        have := congrArg UScalar.val e; simp [mValue] at this; omega)
      exact ⟨none, by simp [add4, endsU, mRun, mNonzero], by simp, fun _ ⟨_, z⟩ => zero z⟩
  · have notEnds : i4 ≠ alloc.vec.Vec.len chars := fun e => ends (by
      have := congrArg UScalar.val e; simp [i4Is] at this; omega)
    exact ⟨none, by simp [add4, notEnds], by simp, fun _ ⟨e, _⟩ => ends e⟩

private theorem full_group_correct (out : alloc.vec.Vec U8) (a b c d : U8) (va : a.val < 64) (vb : b.val < 64)
    (vc : c.val < 64) (vd : d.val < 64) (room : out.val.length + 2 < Usize.max) :
    ∃ v, datatypes.full_group out a b c d = .ok (some v) ∧ ∃ x y z : U8, v.val = out.val ++ [x, y, z] ∧
      x.val = a.val * 4 + b.val / 16 ∧ y.val = b.val % 16 * 16 + c.val / 4 ∧ z.val = c.val % 4 * 64 + d.val := by
  rw [datatypes.full_group]
  obtain ⟨i, iRun, iValue⟩ := u8_mul (x := a) (k := 4#u8) (by simp; omega)
  obtain ⟨j, jRun, jValue⟩ := u8_div (x := b) (k := 16#u8) (by simp)
  obtain ⟨x, xRun, xValue⟩ := u8_add (x := i) (y := j) (by simp [iValue, jValue]; omega)
  obtain ⟨v1, push1, contents1⟩ := push_octet_spec out x (by omega)
  obtain ⟨p, pRun, pValue⟩ := u8_rem (x := b) (k := 16#u8) (by simp)
  have pSmall : p.val < 16 := by rw [pValue]; simp; omega
  obtain ⟨q, qRun, qValue⟩ := u8_mul (x := p) (k := 16#u8) (by simp; omega)
  obtain ⟨k, kRun, kValue⟩ := u8_div (x := c) (k := 4#u8) (by simp)
  obtain ⟨y, yRun, yValue⟩ := u8_add (x := q) (y := k) (by simp [qValue, kValue]; omega)
  obtain ⟨v2, push2, contents2⟩ := push_octet_spec v1 y (by rw [contents1]; simp; omega)
  obtain ⟨e, eRun, eValue⟩ := u8_rem (x := c) (k := 4#u8) (by simp)
  have eSmall : e.val < 4 := by rw [eValue]; simp; omega
  obtain ⟨f, fRun, fValue⟩ := u8_mul (x := e) (k := 64#u8) (by simp; omega)
  obtain ⟨z, zRun, zValue⟩ := u8_add (x := f) (y := d) (by simp [fValue]; omega)
  obtain ⟨v3, push3, contents3⟩ := push_octet_spec v2 z (by rw [contents2, contents1]; simp; omega)
  refine ⟨v3, by simp [iRun, jRun, xRun, push1, pRun, qRun, kRun, yRun, push2, eRun, fRun, zRun, push3], x, y, z,
    by rw [contents3, contents2, contents1]; simp, by rw [xValue, iValue, jValue]; simp,
    by rw [yValue, qValue, kValue, pValue]; simp, by rw [zValue, fValue, eValue]; simp⟩

private theorem base64_short (l o : List U8) (pos : 0 < l.length) (short : l.length < 4) : ¬ Base64Chars l o := by
  match l with
  | [] => simp at pos
  | [_] => simp [Base64Chars]
  | [_, _] => simp [Base64Chars]
  | [_, _, _] => simp [Base64Chars]
  | _ :: _ :: _ :: _ :: _ => exact absurd short (by simp only [List.length_cons]; omega)

/-- The kernel reads exactly the Base64 groups without spaces, each to its
    octets. -/
theorem base64_from_correct (chars : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length ≤ index.val) :
    ∃ r, datatypes.base64_from chars index out = .ok r ∧
      (∀ v, r = some v → ∃ o, v.val = out.val ++ o ∧ Base64Chars (chars.val.drop index.val) o) ∧
      (r = none → ∀ o, ¬ Base64Chars (chars.val.drop index.val) o) := by
  have size := chars.property
  rw [datatypes.base64_from]
  by_cases more : index.val < chars.val.length
  · obtain ⟨left, sub, leftValue⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len chars) (y := index) (by simp; omega))
    have leftIs : left.val = chars.val.length - index.val := by
      have := leftValue
      simp only [alloc.vec.Vec.len_val] at this
      exact this.1
    by_cases group : index.val + 3 < chars.val.length
    · have three : 3 < left.val := by rw [leftIs]; omega
      have h1 : index.val + 1 < chars.val.length := by omega
      have h2 : index.val + 2 < chars.val.length := by omega
      have split : chars.val.drop index.val = chars.val[index.val] :: chars.val[index.val + 1] ::
          chars.val[index.val + 2] :: chars.val[index.val + 3] :: chars.val.drop (index.val + 4) := by
        rw [List.drop_eq_getElem_cons more, List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2,
          List.drop_eq_getElem_cons group]
      have l0 : chars.index_usize index = .ok chars.val[index.val] := by
        simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem more]
      obtain ⟨i1, add1, i1Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have i1Is : i1.val = index.val + 1 := by simpa using i1Value
      have l1 : chars.index_usize i1 = .ok chars.val[index.val + 1] := by
        simp [alloc.vec.Vec.index_usize, i1Is, List.getElem?_eq_getElem h1]
      obtain ⟨i2, add2, i2Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 2#usize) (by scalar_tac))
      have i2Is : i2.val = index.val + 2 := by simpa using i2Value
      have l2 : chars.index_usize i2 = .ok chars.val[index.val + 2] := by
        simp [alloc.vec.Vec.index_usize, i2Is, List.getElem?_eq_getElem h2]
      obtain ⟨i3, add3, i3Value⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 3#usize) (by scalar_tac))
      have i3Is : i3.val = index.val + 3 := by simpa using i3Value
      have l3 : chars.index_usize i3 = .ok chars.val[index.val + 3] := by
        simp [alloc.vec.Vec.index_usize, i3Is, List.getElem?_eq_getElem group]
      obtain ⟨r1, run1, value1⟩ := sextet_correct chars.val[index.val]
      cases r1 with
      | none =>
        refine ⟨none, by simp [UScalar.lt_equiv, more, sub, three, l0, run1], by simp, fun _ o form => ?_⟩
        rw [split] at form
        obtain ⟨va, _, ha, _⟩ := form
        rw [ha] at value1
        simp at value1
      | some a =>
        have va : base64Value chars.val[index.val] = some a.val := by simpa using value1.symm
        have aSmall := sextet_small va
        obtain ⟨r2, run2, value2⟩ := sextet_correct chars.val[index.val + 1]
        cases r2 with
        | none =>
          refine ⟨none, by simp [UScalar.lt_equiv, more, sub, three, l0, run1, add1, l1, run2], by simp,
            fun _ o form => ?_⟩
          rw [split] at form
          obtain ⟨_, vb, _, hb, _⟩ := form
          rw [hb] at value2
          simp at value2
        | some b =>
          have vb : base64Value chars.val[index.val + 1] = some b.val := by simpa using value2.symm
          have bSmall := sextet_small vb
          by_cases pad2 : chars.val[index.val + 2] = 61#u8
          · obtain ⟨r, run, someCase, noneCase⟩ :=
              padded_one_correct chars index a b out group aSmall bSmall (by omega)
            refine ⟨r, by simp [UScalar.lt_equiv, more, sub, three, l0, run1, add1, l1, run2, add2, l2, pad2, run],
              fun v hv => ?_, fun hn o form => ?_⟩
            · obtain ⟨x, hvx, pad3, ends, zero, xv⟩ := someCase v hv
              refine ⟨[x], hvx, ?_⟩
              rw [split, List.drop_eq_nil_of_le (by omega)]
              exact ⟨a.val, b.val, va, vb, .inr (.inr ⟨x, rfl, pad2, pad3, zero, rfl, xv⟩)⟩
            · rw [split] at form
              obtain ⟨va', vb', ha, hb, cases⟩ := form
              rw [va] at ha; rw [vb] at hb
              simp only [Option.some.injEq] at ha hb
              subst ha hb
              rcases cases with ⟨vc, _, _, _, _, _, hc, _⟩ | ⟨vc, _, _, _, hc, _⟩ | ⟨x, restNil, _, pad3, zero, _⟩
              · rw [pad2, pad_no_sextet] at hc; cases hc
              · rw [pad2, pad_no_sextet] at hc; cases hc
              · have ends : index.val + 4 = chars.val.length := by
                  have := List.drop_eq_nil_iff.mp restNil; omega
                exact noneCase hn ⟨pad3, ends, zero⟩
          · obtain ⟨r3, run3, value3⟩ := sextet_correct chars.val[index.val + 2]
            cases r3 with
            | none =>
              refine ⟨none, by simp [UScalar.lt_equiv, more, sub, three, l0, run1, add1, l1, run2, add2, l2, pad2,
                run3], by simp, fun _ o form => ?_⟩
              rw [split] at form
              obtain ⟨_, _, _, _, cases⟩ := form
              rcases cases with ⟨vc, _, _, _, _, _, hc, _⟩ | ⟨vc, _, _, _, hc, _⟩ | ⟨_, _, pad, _⟩
              · rw [hc] at value3; simp at value3
              · rw [hc] at value3; simp at value3
              · exact pad2 pad
            | some c =>
              have vc : base64Value chars.val[index.val + 2] = some c.val := by simpa using value3.symm
              have cSmall := sextet_small vc
              by_cases pad3 : chars.val[index.val + 3] = 61#u8
              · obtain ⟨r, run, someCase, noneCase⟩ :=
                  padded_two_correct chars index a b c out aSmall bSmall cSmall (by omega) (by omega)
                refine ⟨r, by simp [UScalar.lt_equiv, more, sub, three, l0, run1, add1, l1, run2, add2, l2, pad2,
                  run3, add3, l3, pad3, run], fun v hv => ?_, fun hn o form => ?_⟩
                · obtain ⟨x, y, hvxy, ends, zero, xv, yv⟩ := someCase v hv
                  refine ⟨[x, y], hvxy, ?_⟩
                  rw [split, List.drop_eq_nil_of_le (by omega)]
                  exact ⟨a.val, b.val, va, vb, .inr (.inl ⟨c.val, x, y, rfl, vc, pad3, zero, rfl, xv, yv⟩)⟩
                · rw [split] at form
                  obtain ⟨va', vb', ha, hb, cases⟩ := form
                  rw [va] at ha; rw [vb] at hb
                  simp only [Option.some.injEq] at ha hb
                  subst ha hb
                  rcases cases with ⟨vc', vd, _, _, _, _, _, hd, _⟩ | ⟨vc', _, _, restNil, hc, _, zero, _⟩ |
                      ⟨_, _, pad, _⟩
                  · rw [pad3, pad_no_sextet] at hd; cases hd
                  · rw [vc] at hc
                    simp only [Option.some.injEq] at hc
                    subst hc
                    have ends : index.val + 4 = chars.val.length := by
                      have := List.drop_eq_nil_iff.mp restNil; omega
                    exact noneCase hn ⟨ends, zero⟩
                  · exact pad2 pad
              · obtain ⟨r4, run4, value4⟩ := sextet_correct chars.val[index.val + 3]
                cases r4 with
                | none =>
                  refine ⟨none, by simp [UScalar.lt_equiv, more, sub, three, l0, run1, add1, l1, run2, add2, l2, pad2,
                    run3, add3, l3, pad3, run4], by simp, fun _ o form => ?_⟩
                  rw [split] at form
                  obtain ⟨_, _, _, _, cases⟩ := form
                  rcases cases with ⟨_, vd, _, _, _, _, _, hd, _⟩ | ⟨_, _, _, _, _, pad, _⟩ | ⟨_, _, _, pad, _⟩
                  · rw [hd] at value4; simp at value4
                  · exact pad3 pad
                  · exact pad3 pad
                | some d =>
                  have vd : base64Value chars.val[index.val + 3] = some d.val := by simpa using value4.symm
                  have dSmall := sextet_small vd
                  obtain ⟨v1, full, x, y, z, contents, xv, yv, zv⟩ :=
                    full_group_correct out a b c d aSmall bSmall cSmall dSmall (by omega)
                  obtain ⟨i4, add4, i4Value⟩ := WP.spec_imp_exists
                    (Usize.add_spec (x := index) (y := 4#usize) (by scalar_tac))
                  have i4Is : i4.val = index.val + 4 := by simpa using i4Value
                  obtain ⟨r, run, someCase, noneCase⟩ := base64_from_correct chars i4 v1
                    (by rw [contents, i4Is]; simp; omega)
                  rw [i4Is] at someCase noneCase
                  refine ⟨r, by simp [UScalar.lt_equiv, more, sub, three, l0, run1, add1, l1, run2, add2, l2, pad2,
                    run3, add3, l3, pad3, run4, full, add4, run], fun v hv => ?_, fun hn o form => ?_⟩
                  · obtain ⟨o, hvo, rest⟩ := someCase v hv
                    refine ⟨x :: y :: z :: o, by rw [hvo, contents]; simp, ?_⟩
                    rw [split]
                    exact ⟨a.val, b.val, va, vb, .inl ⟨c.val, d.val, x, y, z, o, vc, vd, rfl, xv, yv, zv, rest⟩⟩
                  · rw [split] at form
                    obtain ⟨_, _, _, _, cases⟩ := form
                    rcases cases with ⟨_, _, _, _, _, o', _, _, _, _, _, _, rest⟩ | ⟨_, _, _, _, _, pad, _⟩ |
                        ⟨_, _, _, pad, _⟩
                    · exact noneCase hn o' rest
                    · exact pad3 pad
                    · exact pad3 pad
    · have notThree : ¬ 3 < left.val := by rw [leftIs]; omega
      refine ⟨none, by simp [UScalar.lt_equiv, more, sub, notThree], by simp, fun _ o form => ?_⟩
      exact base64_short _ o (by simp; omega) (by simp; omega) form
  · refine ⟨some out, by simp [UScalar.lt_equiv, more], fun v hv => ⟨[], by cases hv; simp, ?_⟩, by simp⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [Base64Chars]
termination_by chars.val.length - index.val
decreasing_by omega

/-- The kernel reads exactly the lexical forms of `xsd:base64Binary`, each to
    its octets. -/
theorem base64_value_correct (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.base64_value lexical = .ok r ∧
      (∀ v, r = some v → Base64Form lexical.val v.val) ∧ (r = none → ∀ o, ¬ Base64Form lexical.val o) := by
  rw [datatypes.base64_value]
  obtain ⟨r1, run1, someCase1, noneCase1⟩ := unspaced_correct lexical 0#usize (alloc.vec.Vec.new U8) (by simp)
  simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at someCase1 noneCase1
  cases r1 with
  | none =>
    refine ⟨none, by simp [run1], by simp, fun _ o ⟨chars, spaced, groups⟩ => ?_⟩
    exact noneCase1 rfl chars (base64_chars_spaceless groups) spaced
  | some chars =>
    obtain ⟨cs, hcs, spaced, spaceless⟩ := someCase1 chars rfl
    rw [new_val, List.nil_append] at hcs
    obtain ⟨r2, run2, someCase2, noneCase2⟩ := base64_from_correct chars 0#usize (alloc.vec.Vec.new U8) (by simp)
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at someCase2 noneCase2
    refine ⟨r2, by simp [run1, run2], fun v hv => ?_, fun hn o ⟨chars', spaced', groups⟩ => ?_⟩
    · obtain ⟨o, hvo, groups⟩ := someCase2 v hv
      rw [new_val, List.nil_append] at hvo
      exact ⟨chars.val, by rw [hcs]; exact spaced, by rw [hvo]; exact groups⟩
    · rw [← hcs] at spaced
      have same := spaced_unique spaced' spaced (base64_chars_spaceless groups) (by rw [hcs]; exact spaceless)
      rw [same] at groups
      exact noneCase2 hn o groups

/-- The kernel's value of a string or of a literal of a subtype of
    `xsd:string`: the string itself, exactly when it is XML text in the kind. -/
theorem string_value_correct (k : datatypes.Kind) (lexical : alloc.vec.Vec U8) :
    datatypes.string_value k lexical =
      .ok (if XmlText lexical.val ∧ TextIn k lexical.val then some (.Text lexical) else none) := by
  rw [datatypes.string_value, xml_text_correct]
  by_cases xml : XmlText lexical.val
  · rw [Rowl.Strings.text_in_kind_correct lexical xml k]
    by_cases inK : TextIn k lexical.val
    · obtain ⟨copy, copyRun, copyValue⟩ := copy_range_correct lexical 0#usize (alloc.vec.Vec.len lexical)
        (alloc.vec.Vec.new U8) (by simp) (by simp [new_val])
      have same : copy = lexical := by
        have h : copy.val = lexical.val := by
          rw [copyValue, new_val, List.nil_append, alloc.vec.Vec.len_val, show ((0#usize : Usize).val) = 0 from rfl,
            segment_take]
          simp
        simpa [alloc.vec.Vec.eq_iff] using h
      simp [xml, inK, copyRun, same]
    · simp [xml, inK]
  · simp [xml]

/-- A literal of a subtype of `xsd:string` has the string of its lexical form
    as value, exactly when the form is in the subtype. -/
theorem subtype_value_correct {k : datatypes.Kind} {s : StringSubtype} (hs : subtypeOf k = some s)
    (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.string_value k lexical = .ok r ∧
      (∀ v, r = some v → Canonical v ∧ LexicalForm k lexical.val ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
          D.lexicalValue (typeOf k) lexical.val = valueOf N v) ∧
      (r = none → ¬ LexicalForm k lexical.val) := by
  have form : LexicalForm k lexical.val ↔ s.Form lexical.val := by
    cases k <;> simp [subtypeOf] at hs <;> subst hs <;> rfl
  have inK : TextIn k lexical.val ↔ s.Form lexical.val := by
    have : k ≠ .String ∧ k ≠ .Plain := by cases k <;> simp [subtypeOf] at hs ⊢
    simp [TextIn, hs, this.1, this.2]
  rw [string_value_correct]
  by_cases f : s.Form lexical.val
  · have xml := Rowl.Strings.form_xml f
    refine ⟨some (.Text lexical), by simp [xml, inK.mpr f], ?_, by simp⟩
    rintro v ⟨⟩
    exact ⟨xml, form.mpr f, fun D N => by rw [subtypeOf_type hs, N.string_subtype_value s _ f]; rfl⟩
  · exact ⟨none, by simp [inK, f], by simp, fun _ h => f (form.mp h)⟩

/-- The kernel's reading of a lexical form is exact: a canonical value exactly
    for a lexical form in the lexical space of the kind's datatype, except an
    `owl:rational` form too long for the kernel's arithmetic, and then, under
    every datatype map that is the OWL 2 map on the datatypes here, the lexical
    form's value. -/
theorem kind_value_correct (k : datatypes.Kind) (lexical : alloc.vec.Vec U8) :
    ∃ r, datatypes.kind_value k lexical = .ok r ∧
      (∀ v, r = some v → Canonical v ∧ LexicalForm k lexical.val ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
          D.lexicalValue (typeOf k) lexical.val = valueOf N v) ∧
      (r = none → ¬ LexicalForm k lexical.val ∨
        ((k = .Rational ∨ k = .DateTime ∨ k = .DateTimeStamp) ∧ Usize.max / 16 ≤ lexical.val.length) ∨
        ((k = .Double ∨ k = .Float) ∧ 1024 ≤ lexical.val.length)) := by
  have size := lexical.property
  have subtype : IsSubtype k → ∃ r, datatypes.bounded_value k lexical = .ok r ∧
      (∀ v, r = some v → Canonical v ∧ LexicalForm k lexical.val ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
          D.lexicalValue (typeOf k) lexical.val = valueOf N v) ∧
      (r = none → ¬ LexicalForm k lexical.val ∨
        ((k = .Rational ∨ k = .DateTime ∨ k = .DateTimeStamp) ∧ Usize.max / 16 ≤ lexical.val.length) ∨
        ((k = .Double ∨ k = .Float) ∧ 1024 ≤ lexical.val.length)) := by
    intro sub
    obtain ⟨r, run, someCase, noneCase⟩ := bounded_value_correct k lexical
    refine ⟨r, run, fun v hv => ?_, fun hn => .inl ?_⟩
    · obtain ⟨n, w, f, rfl, c, fEmpty, form, inside⟩ := someCase v hv
      obtain ⟨z, hz⟩ := whole_integer c fEmpty
      have bounded : Bounded (lowerOf k) (upperOf k) z := by
        rw [numberIn_subtype k sub, hz] at inside
        exact (bounded_iff k z).mpr inside.2
      refine ⟨c, (lexical_subtype k sub _).mpr ⟨z, bounded, hz ▸ form⟩, fun D N => ?_⟩
      rw [N.subtype_value _ (subtype_listed k sub) _ z bounded (hz ▸ form)]
      simp only [valueOf, hz]
    · intro lexicalForm
      obtain ⟨z, bounded, form⟩ := (lexical_subtype k sub _).mp lexicalForm
      apply noneCase hn z form
      rw [numberIn_subtype k sub]
      exact ⟨trivial, (bounded_iff k z).mp bounded⟩
  cases k with
  | Integer =>
    obtain ⟨r, run, some', none'⟩ := number_value_correct lexical true
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn => .inl fun ⟨q, form⟩ => none' hn q form⟩
    obtain ⟨n, w, f, rfl, canonical, form, _⟩ := some' v hv
    exact ⟨canonical, ⟨_, form⟩, fun D N => N.integer_value _ _ form⟩
  | Decimal =>
    obtain ⟨r, run, some', none'⟩ := number_value_correct lexical false
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn => .inl fun ⟨q, form⟩ => none' hn q form⟩
    obtain ⟨n, w, f, rfl, canonical, form, _⟩ := some' v hv
    exact ⟨canonical, ⟨_, form⟩, fun D N => N.decimal_value _ _ form⟩
  | String =>
    by_cases xml : XmlText lexical.val
    · refine ⟨some (.Text lexical), by simp [datatypes.kind_value, string_value_correct, xml, TextIn], ?_, by simp⟩
      rintro v ⟨⟩
      exact ⟨xml, xml, fun D N => by simp [valueOf, typeOf, N.string_value _ xml]⟩
    · exact ⟨none, by simp [datatypes.kind_value, string_value_correct, xml], by simp, fun _ => .inl xml⟩
  | Plain =>
    obtain ⟨r, run, some', none'⟩ := plain_value_correct lexical
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn => .inl (none' hn)⟩
    obtain ⟨s, l, split, xml, cases⟩ := some' v hv
    rcases cases with ⟨rfl, t, rfl, rfl⟩ | ⟨isTag, t, m, rfl, rfl, lowered⟩
    · exact ⟨xml, ⟨_, [], split, xml, .inl rfl⟩, fun D N => N.plain_text _ _ split xml⟩
    · exact ⟨⟨xml, l, isTag, lowered⟩, ⟨_, l, split, xml, .inr isTag⟩,
        fun D N => N.plain_tagged _ _ _ _ split xml isTag lowered⟩
  | Boolean =>
    obtain ⟨r, run, some', none'⟩ := truth_value_correct lexical
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn => .inl fun ⟨b, form⟩ => none' hn b form⟩
    obtain ⟨b, rfl, form⟩ := some' v hv
    exact ⟨trivial, ⟨b, form⟩, fun D N => N.boolean_value _ _ form⟩
  | Real => exact ⟨none, by rw [datatypes.kind_value], by simp, fun _ => .inl (by simp [LexicalForm])⟩
  | Rational =>
    obtain ⟨r, run, some', none'⟩ := rational_value_correct lexical
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn => ?_⟩
    · obtain ⟨q, form, value⟩ := some' v hv
      exact ⟨number_value_canonical value, ⟨q, form⟩, fun D N => by
        show D.lexicalValue rationalType lexical.val = valueOf N v
        rw [N.rational_value _ _ form, number_value_of N value]⟩
    · rcases none' hn with no | long
      · exact .inl fun ⟨q, form⟩ => no q form
      · exact .inr (.inl ⟨.inl rfl, long⟩)
  | NonNegativeInteger => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | NonPositiveInteger => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | PositiveInteger => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | NegativeInteger => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | Long => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | Int => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | Short => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | Byte => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | UnsignedLong => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | UnsignedInt => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | UnsignedShort => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | UnsignedByte => obtain ⟨r, run, facts⟩ := subtype trivial; exact ⟨r, by rw [datatypes.kind_value]; exact run, facts⟩
  | AnyUri =>
    by_cases xml : XmlText lexical.val
    · obtain ⟨copy, copyRun, copyValue⟩ := copy_range_correct lexical 0#usize (alloc.vec.Vec.len lexical)
        (alloc.vec.Vec.new U8) (by simp) (by simp [new_val])
      have same : copy.val = lexical.val := by
        rw [copyValue, new_val, List.nil_append, alloc.vec.Vec.len_val, show ((0#usize : Usize).val) = 0 from rfl,
          segment_take]
        simp
      refine ⟨some (.Uri copy), by simp [datatypes.kind_value, xml_text_correct, xml, copyRun], ?_, by simp⟩
      rintro v ⟨⟩
      exact ⟨by simp [Canonical, same, xml], xml, fun D N => by simp [valueOf, same, typeOf, N.uri_value _ xml]⟩
    · exact ⟨none, by simp [datatypes.kind_value, xml_text_correct, xml], by simp, fun _ => .inl xml⟩
  | HexBinary =>
    obtain ⟨r, run, someCase, noneCase⟩ := hex_from_correct lexical 0#usize (alloc.vec.Vec.new U8) (by simp)
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero] at someCase noneCase
    cases r with
    | none =>
      exact ⟨none, by simp [datatypes.kind_value, run], by simp, fun _ => .inl fun ⟨o, form⟩ => noneCase rfl o form⟩
    | some octets =>
      obtain ⟨o, ho, form⟩ := someCase octets rfl
      rw [new_val, List.nil_append] at ho
      refine ⟨some (.Hex octets), by simp [datatypes.kind_value, run], ?_, by simp⟩
      rintro v ⟨⟩
      exact ⟨trivial, ⟨_, form⟩, fun D N => by simp [valueOf, typeOf, ho, N.hex_value _ _ form]⟩
  | Base64Binary =>
    obtain ⟨r, run, someCase, noneCase⟩ := base64_value_correct lexical
    cases r with
    | none =>
      exact ⟨none, by simp [datatypes.kind_value, run], by simp, fun _ => .inl fun ⟨o, form⟩ => noneCase rfl o form⟩
    | some octets =>
      have form := someCase octets rfl
      refine ⟨some (.Base64 octets), by simp [datatypes.kind_value, run], ?_, by simp⟩
      rintro v ⟨⟩
      exact ⟨trivial, ⟨_, form⟩, fun D N => by simp [valueOf, typeOf, N.base64_value _ _ form]⟩
  | NormalizedString =>
    obtain ⟨r, run, someCase, noneCase⟩ := subtype_value_correct (k := .NormalizedString) (s := .normalized) rfl lexical
    exact ⟨r, by rw [datatypes.kind_value]; exact run, someCase, fun hn => .inl (noneCase hn)⟩
  | Token =>
    obtain ⟨r, run, someCase, noneCase⟩ := subtype_value_correct (k := .Token) (s := .token) rfl lexical
    exact ⟨r, by rw [datatypes.kind_value]; exact run, someCase, fun hn => .inl (noneCase hn)⟩
  | Language =>
    obtain ⟨r, run, someCase, noneCase⟩ := subtype_value_correct (k := .Language) (s := .language) rfl lexical
    exact ⟨r, by rw [datatypes.kind_value]; exact run, someCase, fun hn => .inl (noneCase hn)⟩
  | NmToken =>
    obtain ⟨r, run, someCase, noneCase⟩ := subtype_value_correct (k := .NmToken) (s := .nmtoken) rfl lexical
    exact ⟨r, by rw [datatypes.kind_value]; exact run, someCase, fun hn => .inl (noneCase hn)⟩
  | Name =>
    obtain ⟨r, run, someCase, noneCase⟩ := subtype_value_correct (k := .Name) (s := .«name») rfl lexical
    exact ⟨r, by rw [datatypes.kind_value]; exact run, someCase, fun hn => .inl (noneCase hn)⟩
  | NcName =>
    obtain ⟨r, run, someCase, noneCase⟩ := subtype_value_correct (k := .NcName) (s := .ncname) rfl lexical
    exact ⟨r, by rw [datatypes.kind_value]; exact run, someCase, fun hn => .inl (noneCase hn)⟩
  | DateTime =>
    obtain ⟨r, run, someCase, completeCase⟩ := Rowl.Moments.moment_value_correct lexical false
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn => ?_⟩
    · obtain ⟨x, rfl, cx, form, _⟩ := someCase v hv
      exact ⟨cx, ⟨_, form⟩, fun D N => by simp only [typeOf, valueOf]; exact N.datetime_value _ _ form⟩
    · by_cases long : lexical.val.length < Usize.max / 16
      · refine .inl fun ⟨m, form⟩ => ?_
        obtain ⟨x, hx, _⟩ := completeCase long m form (fun h => (by cases h))
        rw [hn] at hx; cases hx
      · exact .inr (.inl ⟨.inr (.inl rfl), by omega⟩)
  | DateTimeStamp =>
    obtain ⟨r, run, someCase, completeCase⟩ := Rowl.Moments.moment_value_correct lexical true
    refine ⟨r, by rw [datatypes.kind_value]; exact run, fun v hv => ?_, fun hn => ?_⟩
    · obtain ⟨x, rfl, cx, form, zone⟩ := someCase v hv
      exact ⟨cx, ⟨_, form, zone rfl⟩, fun D N => by
        simp only [typeOf, valueOf]; exact N.stamp_value _ _ form (zone rfl)⟩
    · by_cases long : lexical.val.length < Usize.max / 16
      · refine .inl fun ⟨m, form, zone⟩ => ?_
        obtain ⟨x, hx, _⟩ := completeCase long m form (fun _ => zone)
        rw [hn] at hx; cases hx
      · exact .inr (.inl ⟨.inr (.inr rfl), by omega⟩)
  | Double =>
    obtain ⟨r, run, someCase, completeCase⟩ := Rowl.Floats.binary_value_correct lexical true
    cases r with
    | none =>
      refine ⟨none, by simp [datatypes.kind_value, run], by simp, fun _ => ?_⟩
      by_cases long : lexical.val.length < 1024
      · exact .inl fun ⟨b, form⟩ => by obtain ⟨_, h, _⟩ := completeCase long b form; cases h
      · exact .inr (.inr ⟨.inl rfl, by omega⟩)
    | some b =>
      obtain ⟨canon, form⟩ := someCase b rfl
      refine ⟨some (.Double b), by simp [datatypes.kind_value, run], ?_, by simp⟩
      rintro v ⟨⟩
      exact ⟨⟨canon, Rowl.Floats.binaryForm_valid form⟩, ⟨_, form⟩, fun D N => by
        simp only [typeOf, valueOf]; exact N.double_value _ _ form⟩
  | Float =>
    obtain ⟨r, run, someCase, completeCase⟩ := Rowl.Floats.binary_value_correct lexical false
    cases r with
    | none =>
      refine ⟨none, by simp [datatypes.kind_value, run], by simp, fun _ => ?_⟩
      by_cases long : lexical.val.length < 1024
      · exact .inl fun ⟨b, form⟩ => by obtain ⟨_, h, _⟩ := completeCase long b form; cases h
      · exact .inr (.inr ⟨.inr rfl, by omega⟩)
    | some b =>
      obtain ⟨canon, form⟩ := someCase b rfl
      refine ⟨some (.Float b), by simp [datatypes.kind_value, run], ?_, by simp⟩
      rintro v ⟨⟩
      exact ⟨⟨canon, Rowl.Floats.binaryForm_valid form⟩, ⟨_, form⟩, fun D N => by
        simp only [typeOf, valueOf]; exact N.float_value _ _ form⟩

/-- A literal has a value exactly when its datatype is one of the datatypes and
    its lexical form is in the lexical space, except an `owl:rational` form too
    long for the kernel's arithmetic; the value is canonical, and under every
    datatype map that is the OWL 2 map on the datatypes here the literal is in
    the vocabulary's lexical space with that value. -/
theorem literal_value_correct (lt : Literal) :
    ∃ r, datatypes.literal_value lt = .ok r ∧
      (∀ v, r = some v → Canonical v ∧ ∃ k, kindOf lt.datatype = some k ∧ LexicalForm k lt.lexical.val ∧
        ∀ {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
          D.supported lt.datatype ∧ D.lexicalSpace lt.datatype lt.lexical.val ∧
            D.lexicalValue lt.datatype lt.lexical.val = valueOf N v) ∧
      (r = none → kindOf lt.datatype = none ∨
        ∃ k, kindOf lt.datatype = some k ∧
          (¬ LexicalForm k lt.lexical.val ∨
            ((k = .Rational ∨ k = .DateTime ∨ k = .DateTimeStamp) ∧ Usize.max / 16 ≤ lt.lexical.val.length) ∨
            ((k = .Double ∨ k = .Float) ∧ 1024 ≤ lt.lexical.val.length))) := by
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

theorem same_zone_correct (left right : Option (Bool × U8 × U8)) :
    datatypes.same_zone left right = .ok (decide (left = right)) := by
  rcases left with _ | ⟨w, h, m⟩ <;> rcases right with _ | ⟨w', h', m'⟩ <;> simp [datatypes.same_zone, Bool.and_assoc]

theorem same_moment_correct (left right : datatypes.Moment) :
    datatypes.same_moment left right = .ok (decide (left = right)) := by
  rw [datatypes.same_moment]
  simp only [same_bytes_correct, same_zone_correct, bind_ok]
  congr 1
  obtain ⟨n, y, mo, d, h, mi, se, f, z⟩ := left
  obtain ⟨n', y', mo', d', h', mi', se', f', z'⟩ := right
  simp only [datatypes.Moment.mk.injEq, alloc.vec.Vec.eq_iff, Bool.and_eq_true, decide_eq_true_eq,
    Bool.decide_and]
  by_cases a1 : n = n' <;> by_cases a2 : y.val = y'.val <;> by_cases a3 : mo = mo' <;> by_cases a4 : d = d' <;>
    by_cases a5 : h = h' <;> by_cases a6 : mi = mi' <;> by_cases a7 : se = se' <;> by_cases a8 : f.val = f'.val <;>
    by_cases a9 : z = z' <;> simp [a1, a2, a3, a4, a5, a6, a7, a8, a9]

theorem same_binary_correct (left right : datatypes.Binary) :
    datatypes.same_binary left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;> simp [datatypes.same_binary, Bool.and_assoc]

/-- The kernel compares values exactly. -/
theorem same_value_correct (left right : datatypes.DataValue) :
    datatypes.same_value left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;>
    simp [datatypes.same_value, same_bytes_correct, same_moment_correct, same_binary_correct] <;>
    split_ifs <;> simp_all [same_bytes_correct]

/-- Membership of a value in the value space of a kind's datatype, as the
    kernel reads it off the value. -/
def InKind : datatypes.DataValue → datatypes.Kind → Prop
  | .Number n w f, k => NumberIn k (f.val = []) (numberOf n w.val f.val)
  | .Fraction _ _ _, k => k = .Real ∨ k = .Rational
  | .Text t, k => TextIn k t.val
  | .Tagged _ _, k => k = .Plain
  | .Truth _, k => k = .Boolean
  | .Uri _, k => k = .AnyUri
  | .Hex _, k => k = .HexBinary
  | .Base64 _, k => k = .Base64Binary
  | .Moment x, k => k = .DateTime ∨ (k = .DateTimeStamp ∧ x.zone ≠ none)
  | .Double _, k => k = .Double
  | .Float _, k => k = .Float

theorem in_kind_correct (v : datatypes.DataValue) (canonical : Canonical v) (k : datatypes.Kind) :
    datatypes.in_kind v k = .ok (decide (InKind v k)) := by
  cases v with
  | Number n w f =>
    rw [datatypes.in_kind, number_in_kind_correct n w f canonical]
    have : (alloc.vec.Vec.len f = 0#usize) = (f.val = []) := by
      apply propext; constructor
      · intro h; exact List.eq_nil_of_length_eq_zero (by simpa using congrArg UScalar.val h)
      · intro h; apply UScalar.eq_of_val_eq; simp [h]
    simp [InKind, this]
  | Fraction n a b => cases k <;> simp [datatypes.in_kind, InKind]
  | Text t => rw [datatypes.in_kind, Rowl.Strings.text_in_kind_correct t canonical k]; rfl
  | Tagged t m => cases k <;> simp [datatypes.in_kind, InKind]
  | Truth b => cases k <;> simp [datatypes.in_kind, InKind]
  | Uri t => cases k <;> simp [datatypes.in_kind, InKind]
  | Hex o => cases k <;> simp [datatypes.in_kind, InKind]
  | Base64 o => cases k <;> simp [datatypes.in_kind, InKind]
  | Moment x => rcases hz : x.zone with _ | z <;> cases k <;> simp [datatypes.in_kind, InKind, hz]
  | Double b => cases k <;> simp [datatypes.in_kind, InKind]
  | Float b => cases k <;> simp [datatypes.in_kind, InKind]

/-- The reals of a numeric kind's value space that are canonical decimal
    numbers are those the kernel reads off them. -/
theorem number_realIn {n : Bool} {w f : List U8} (c : CanonicalNumber n w f) (k : datatypes.Kind)
    (numeric : IsNumeric k) : RealIn k (numberOf n w f : ℝ) ↔ NumberIn k (f = []) (numberOf n w f) := by
  have integer : (∃ z : ℤ, (numberOf n w f : ℝ) = z) ↔ f = [] := by
    rw [← numberOf_integer c]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z, by exact_mod_cast hz⟩
    · rintro ⟨z, hz⟩; exact ⟨z, by rw [hz]; simp⟩
  have subtype : IsSubtype k → (RealIn k (numberOf n w f : ℝ) ↔ NumberIn k (f = []) (numberOf n w f)) := by
    intro sub
    rw [numberIn_subtype k sub]
    have real : RealIn k (numberOf n w f : ℝ) ↔ ∃ z : ℤ, Bounded (lowerOf k) (upperOf k) z ∧
        (numberOf n w f : ℝ) = z := by
      cases k <;> simp_all [IsSubtype, RealIn]
    rw [real]
    constructor
    · rintro ⟨z, bounded, hz⟩
      have hq : numberOf n w f = z := by exact_mod_cast hz
      refine ⟨integer.mp ⟨z, hz⟩, ?_⟩
      rw [hq]; exact (bounded_iff k z).mp bounded
    · rintro ⟨empty, low, high⟩
      obtain ⟨z, hz⟩ := integer.mpr empty
      have hq : numberOf n w f = z := by exact_mod_cast hz
      rw [hq] at low high
      exact ⟨z, (bounded_iff k z).mpr ⟨low, high⟩, hz⟩
  cases k with
  | Integer => simp only [RealIn, NumberIn]; exact integer
  | Decimal =>
    simp only [RealIn, NumberIn, iff_true]
    obtain ⟨z, m, hz⟩ := numberOf_decimal n w f
    exact ⟨z, m, by rw [hz]; push_cast; rfl⟩
  | String => exact absurd numeric (by simp [IsNumeric])
  | Plain => exact absurd numeric (by simp [IsNumeric])
  | Boolean => exact absurd numeric (by simp [IsNumeric])
  | Real => simp [RealIn, NumberIn]
  | Rational => simp only [RealIn, NumberIn, iff_true]; exact ⟨_, rfl⟩
  | AnyUri => exact absurd numeric (by simp [IsNumeric])
  | HexBinary => exact absurd numeric (by simp [IsNumeric])
  | Base64Binary => exact absurd numeric (by simp [IsNumeric])
  | NormalizedString => exact absurd numeric (by simp [IsNumeric])
  | Token => exact absurd numeric (by simp [IsNumeric])
  | Language => exact absurd numeric (by simp [IsNumeric])
  | NmToken => exact absurd numeric (by simp [IsNumeric])
  | Name => exact absurd numeric (by simp [IsNumeric])
  | NcName => exact absurd numeric (by simp [IsNumeric])
  | DateTime => exact absurd numeric (by simp [IsNumeric])
  | DateTimeStamp => exact absurd numeric (by simp [IsNumeric])
  | Double => exact absurd numeric (by simp [IsNumeric])
  | Float => exact absurd numeric (by simp [IsNumeric])
  | _ => exact subtype trivial

theorem fraction_realIn {n : Bool} {a b : List U8} (c : CanonicalFraction a b) (k : datatypes.Kind)
    (numeric : IsNumeric k) : RealIn k (fractionOf n a b : ℝ) ↔ k = .Real ∨ k = .Rational := by
  have noDecimal := fraction_not_decimal (negative := n) c
  have notInteger : ¬ ∃ z : ℤ, (fractionOf n a b : ℝ) = z := by
    rintro ⟨z, hz⟩
    have hq : fractionOf n a b = z := by exact_mod_cast hz
    exact noDecimal ⟨z, 0, by rw [hq]; simp⟩
  have subtype : IsSubtype k → ¬ RealIn k (fractionOf n a b : ℝ) := by
    intro sub inside
    have real : RealIn k (fractionOf n a b : ℝ) → ∃ z : ℤ, (fractionOf n a b : ℝ) = z := by
      cases k <;> simp_all [IsSubtype, RealIn]
    exact notInteger (real inside)
  cases k with
  | Integer => simp only [RealIn, reduceCtorEq, or_self, iff_false]; exact notInteger
  | Decimal =>
    simp only [RealIn, reduceCtorEq, or_self, iff_false, not_exists]
    intro z m hz
    apply noDecimal
    refine ⟨z, m, ?_⟩
    have : ((fractionOf n a b : ℚ) : ℝ) = (((z : ℚ) / 10 ^ m : ℚ) : ℝ) := by rw [hz]; push_cast; rfl
    exact_mod_cast this
  | String => exact absurd numeric (by simp [IsNumeric])
  | Plain => exact absurd numeric (by simp [IsNumeric])
  | Boolean => exact absurd numeric (by simp [IsNumeric])
  | Real => simp [RealIn]
  | Rational => simp only [RealIn, true_or, or_true, iff_true]; exact ⟨_, rfl⟩
  | AnyUri => exact absurd numeric (by simp [IsNumeric])
  | HexBinary => exact absurd numeric (by simp [IsNumeric])
  | Base64Binary => exact absurd numeric (by simp [IsNumeric])
  | NormalizedString => exact absurd numeric (by simp [IsNumeric])
  | Token => exact absurd numeric (by simp [IsNumeric])
  | Language => exact absurd numeric (by simp [IsNumeric])
  | NmToken => exact absurd numeric (by simp [IsNumeric])
  | Name => exact absurd numeric (by simp [IsNumeric])
  | NcName => exact absurd numeric (by simp [IsNumeric])
  | DateTime => exact absurd numeric (by simp [IsNumeric])
  | DateTimeStamp => exact absurd numeric (by simp [IsNumeric])
  | Double => exact absurd numeric (by simp [IsNumeric])
  | Float => exact absurd numeric (by simp [IsNumeric])
  | _ => simp only [reduceCtorEq, or_self, iff_false]; exact subtype trivial

/-- A number is no value of an IRI or of octets. -/
private theorem number_coded (N : Normative D) (q : ℚ) (a : Coded) (valid : a.Valid) : N.number q ≠ N.coded a :=
  fun e => N.real_coded q a valid (by rw [← real_rat]; exact e)

/-- The value space of a subtype of `xsd:string`: the strings of its forms. -/
theorem subtype_space_iff (N : Normative D) {k : datatypes.Kind} {s : StringSubtype} (hs : subtypeOf k = some s)
    (x : Native) : D.valueSpace (typeOf k) x ↔ ∃ t, s.Form t ∧ x = N.text t := by
  rw [subtypeOf_type hs]; exact N.string_subtype_space s x

/-- Under every datatype map that is the OWL 2 map on the datatypes here, a
    canonical value is in the value space of a kind's datatype exactly as the
    kernel reads it. -/
theorem normative_in_kind (N : Normative D) {v : datatypes.DataValue} (canonical : Canonical v)
    (k : datatypes.Kind) : InKind v k ↔ D.valueSpace (typeOf k) (valueOf N v) := by
  by_cases numeric : IsNumeric k
  · rw [numeric_space N k numeric]
    cases v with
    | Number n w f =>
      have c : CanonicalNumber n w.val f.val := canonical
      simp only [InKind, valueOf, real_rat]
      rw [← number_realIn c k numeric]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨r, same, h⟩; rw [N.real_injective same]; exact h
    | Fraction n a b =>
      have c : CanonicalFraction a.val b.val := canonical
      simp only [InKind, valueOf, real_rat]
      rw [← fraction_realIn (n := n) c k numeric]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨r, same, h⟩; rw [N.real_injective same]; exact h
    | Text t =>
      have xt : XmlText t.val := canonical
      simp only [InKind, valueOf]
      constructor
      · intro h
        exfalso
        rcases h with rfl | rfl | ⟨s, hs, _⟩
        · simp [IsNumeric] at numeric
        · simp [IsNumeric] at numeric
        · cases k <;> simp [subtypeOf] at hs <;> simp [IsNumeric] at numeric
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_text r _ xt)
    | Tagged t m =>
      have xt : XmlText t.val := canonical.1
      have tm : TagValue m.val := canonical.2
      simp only [InKind, valueOf]
      constructor
      · rintro rfl; exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_tagged r _ _ xt tm)
    | Truth b =>
      simp only [InKind, valueOf]
      constructor
      · rintro rfl; exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_truth r b)
    | Uri t =>
      have xt : XmlText t.val := canonical
      simp only [InKind, valueOf]
      constructor
      · rintro rfl; exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_coded r _ xt)
    | Hex o =>
      simp only [InKind, valueOf]
      constructor
      · rintro rfl; exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_coded r (.hex o.val) trivial)
    | Base64 o =>
      simp only [InKind, valueOf]
      constructor
      · rintro rfl; exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_coded r (.base64 o.val) trivial)
    | Moment x =>
      have valid : (Rowl.Moments.momentOf x).Valid := (canonical : Rowl.Moments.CanonicalMoment x).2.2.2.2.2.2
      simp only [InKind, valueOf]
      constructor
      · rintro (rfl | ⟨rfl, _⟩) <;> exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_moment r _ valid)
    | Double b =>
      have valid : (Rowl.Floats.binaryOf b).Valid doubleFormat := canonical.2
      simp only [InKind, valueOf]
      constructor
      · rintro rfl; exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_double r _ valid)
    | Float b =>
      have valid : (Rowl.Floats.binaryOf b).Valid floatFormat := canonical.2
      simp only [InKind, valueOf]
      constructor
      · rintro rfl; exact absurd numeric (by simp [IsNumeric])
      · rintro ⟨r, same, _⟩; exact absurd same.symm (N.real_float r _ valid)
  · by_cases sub : ∃ s, subtypeOf k = some s
    · obtain ⟨s, hs⟩ := sub
      rw [subtype_space_iff N hs]
      have others : k ≠ .String ∧ k ≠ .Plain ∧ k ≠ .Real ∧ k ≠ .Rational ∧ k ≠ .Boolean ∧ k ≠ .AnyUri ∧
          k ≠ .HexBinary ∧ k ≠ .Base64Binary ∧ k ≠ .DateTime ∧ k ≠ .DateTimeStamp ∧ k ≠ .Double ∧ k ≠ .Float ∧
          ∀ (w : Prop) q, ¬ NumberIn k w q := by
        cases k <;> simp [subtypeOf, NumberIn] at hs ⊢
      obtain ⟨nS, nP, nR, nQ, nB, nU, nH, n64, nD, nDS, nDb, nFl, nN⟩ := others
      have xmlOf : ∀ {t}, s.Form t → XmlText t := fun f => Rowl.Strings.form_xml f
      cases v with
      | Number n w f =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h (nN _ _), fun ⟨t, f', same⟩ => absurd same (N.number_text _ _ (xmlOf f'))⟩
      | Fraction n a b =>
        simp only [InKind, valueOf]
        exact ⟨fun h => by rcases h with h | h <;> contradiction,
          fun ⟨t, f', same⟩ => absurd same (N.number_text _ _ (xmlOf f'))⟩
      | Text t =>
        have xt : XmlText t.val := canonical
        simp only [InKind, TextIn, valueOf, hs, nS, nP, false_or, Option.some.injEq, exists_eq_left']
        constructor
        · intro f'; exact ⟨_, f', rfl⟩
        · rintro ⟨t', f', same⟩; rw [N.text_injective _ _ xt (xmlOf f') same]; exact f'
      | Tagged t m =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h nP,
          fun ⟨t', f', same⟩ => absurd same.symm (N.text_tagged _ _ _ (xmlOf f') canonical.1 canonical.2)⟩
      | Truth b =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h nB, fun ⟨t', f', same⟩ => absurd same.symm (N.text_truth _ b (xmlOf f'))⟩
      | Uri t =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h nU,
          fun ⟨t', f', same⟩ => absurd same.symm (N.text_coded _ (.uri t.val) (xmlOf f') canonical)⟩
      | Hex o =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h nH,
          fun ⟨t', f', same⟩ => absurd same.symm (N.text_coded _ (.hex o.val) (xmlOf f') trivial)⟩
      | Base64 o =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h n64,
          fun ⟨t', f', same⟩ => absurd same.symm (N.text_coded _ (.base64 o.val) (xmlOf f') trivial)⟩
      | Moment x =>
        have valid : (Rowl.Moments.momentOf x).Valid := (canonical : Rowl.Moments.CanonicalMoment x).2.2.2.2.2.2
        simp only [InKind, valueOf]
        exact ⟨fun h => by rcases h with h | ⟨h, _⟩; exacts [absurd h nD, absurd h nDS],
          fun ⟨t', f', same⟩ => absurd same.symm (N.text_moment _ _ (xmlOf f') valid)⟩
      | Double b =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h nDb,
          fun ⟨t', f', same⟩ => absurd same.symm (N.text_double _ _ (xmlOf f') canonical.2)⟩
      | Float b =>
        simp only [InKind, valueOf]
        exact ⟨fun h => absurd h nFl,
          fun ⟨t', f', same⟩ => absurd same.symm (N.text_float _ _ (xmlOf f') canonical.2)⟩
    have numberNot : ∀ q, ¬ D.valueSpace (typeOf k) (N.number q) := by
      intro q
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [typeOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space, N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space, not_exists, not_and, not_or]
      · exact fun s xs e => N.number_text q s xs e
      · exact ⟨fun s xs e => N.number_text q s xs e, fun s l xs tl e => N.number_tagged q s l xs tl e⟩
      · exact fun b e => N.number_truth q b e
      · exact fun s xs e => number_coded N q (.uri s) xs e
      · exact fun o e => number_coded N q (.hex o) trivial e
      · exact fun o e => number_coded N q (.base64 o) trivial e
      · exact fun m valid e => N.real_moment q m valid ((real_rat N q).symm.trans e)
      · exact fun m valid _ e => N.real_moment q m valid ((real_rat N q).symm.trans e)
      · exact fun b valid e => N.real_double q b valid ((real_rat N q).symm.trans e)
      · exact fun b valid e => N.real_float q b valid ((real_rat N q).symm.trans e)
    cases v with
    | Number n w f =>
      simp only [InKind, valueOf]
      refine ⟨fun h => ?_, fun h => absurd h (numberNot _)⟩
      cases k <;> simp_all [IsNumeric, NumberIn, subtypeOf]
    | Fraction n a b =>
      simp only [InKind, valueOf]
      refine ⟨fun h => ?_, fun h => absurd h (numberNot _)⟩
      rcases h with rfl | rfl <;> exact absurd trivial numeric
    | Text t =>
      have xt : XmlText t.val := canonical
      have classic : TextIn k t.val ↔ k = .String ∨ k = .Plain := by
        simp only [TextIn]
        constructor
        · rintro (h | h | ⟨s, hs, _⟩)
          exacts [.inl h, .inr h, absurd ⟨s, hs⟩ sub]
        · rintro (h | h)
          exacts [.inl h, .inr (.inl h)]
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, classic, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space, N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · exact ⟨fun _ => ⟨_, xt, rfl⟩, fun _ => by simp⟩
      · exact ⟨fun _ => .inl ⟨_, xt, rfl⟩, fun _ => by simp⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, same⟩ => absurd same (N.text_truth _ b xt)⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same (N.text_coded _ (.uri s) xt xs)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same (N.text_coded _ (.hex o) xt trivial)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same (N.text_coded _ (.base64 o) xt trivial)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, same⟩ => absurd same (N.text_moment _ m xt mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, _, same⟩ => absurd same (N.text_moment _ m xt mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.text_double _ b xt bv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.text_float _ b xt bv)⟩
    | Tagged t m =>
      have xt : XmlText t.val := canonical.1
      have tm : TagValue m.val := canonical.2
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space, N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.text_tagged s _ _ xs xt tm)⟩
      · exact ⟨fun _ => .inr ⟨_, _, xt, tm, rfl⟩, fun _ => by simp⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, same⟩ => absurd same (N.tagged_truth _ _ b xt tm)⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same (N.tagged_coded _ _ (.uri s) xt tm xs)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same (N.tagged_coded _ _ (.hex o) xt tm trivial)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨o, same⟩ => absurd same (N.tagged_coded _ _ (.base64 o) xt tm trivial)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, same⟩ => absurd same (N.tagged_moment _ _ m xt tm mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, _, same⟩ => absurd same (N.tagged_moment _ _ m xt tm mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.tagged_double _ _ b xt tm bv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.tagged_float _ _ b xt tm bv)⟩
    | Truth b =>
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space, N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.text_truth s b xs)⟩
      · refine ⟨fun h => by simp at h, ?_⟩
        rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
        · exact absurd same.symm (N.text_truth s b xs)
        · exact absurd same.symm (N.tagged_truth s l b xs tl)
      · exact ⟨fun _ => ⟨b, rfl⟩, fun _ => by simp⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same (N.truth_coded _ (.uri s) xs)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same (N.truth_coded _ (.hex o) trivial)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same (N.truth_coded _ (.base64 o) trivial)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, same⟩ => absurd same (N.truth_moment _ m mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, _, same⟩ => absurd same (N.truth_moment _ m mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨a, av, same⟩ => absurd same (N.truth_double _ a av)⟩
      · refine ⟨fun h => by simp at h, fun ⟨a, av, same⟩ => absurd same (N.truth_float _ a av)⟩
    | Uri t =>
      have xt : XmlText t.val := canonical
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space, N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.text_coded s (.uri t.val) xs xt)⟩
      · refine ⟨fun h => by simp at h, ?_⟩
        rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
        · exact absurd same.symm (N.text_coded s (.uri t.val) xs xt)
        · exact absurd same.symm (N.tagged_coded s l (.uri t.val) xs tl xt)
      · refine ⟨fun h => by simp at h, fun ⟨b, same⟩ => absurd same.symm (N.truth_coded b (.uri t.val) xt)⟩
      · exact ⟨fun _ => ⟨_, xt, rfl⟩, fun _ => trivial⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => ?_⟩
        have := N.coded_injective (.uri t.val) (.hex o) xt trivial same
        cases this
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => ?_⟩
        have := N.coded_injective (.uri t.val) (.base64 o) xt trivial same
        cases this
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, same⟩ => absurd same (N.coded_moment (.uri t.val) m xt mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, _, same⟩ => absurd same (N.coded_moment (.uri t.val) m xt mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.coded_double (.uri t.val) b xt bv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.coded_float (.uri t.val) b xt bv)⟩
    | Hex o =>
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space, N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.text_coded s (.hex o.val) xs trivial)⟩
      · refine ⟨fun h => by simp at h, ?_⟩
        rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
        · exact absurd same.symm (N.text_coded s (.hex o.val) xs trivial)
        · exact absurd same.symm (N.tagged_coded s l (.hex o.val) xs tl trivial)
      · refine ⟨fun h => by simp at h, fun ⟨b, same⟩ => absurd same.symm (N.truth_coded b (.hex o.val) trivial)⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => ?_⟩
        have := N.coded_injective (.hex o.val) (.uri s) trivial xs same
        cases this
      · exact ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
      · refine ⟨fun h => by simp at h, fun ⟨o', same⟩ => ?_⟩
        have := N.coded_injective (.hex o.val) (.base64 o') trivial trivial same
        cases this
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, same⟩ => absurd same (N.coded_moment (.hex o.val) m trivial mv)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨m, mv, _, same⟩ => absurd same (N.coded_moment (.hex o.val) m trivial mv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.coded_double (.hex o.val) b trivial bv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.coded_float (.hex o.val) b trivial bv)⟩
    | Base64 o =>
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space, N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h,
          fun ⟨s, xs, same⟩ => absurd same.symm (N.text_coded s (.base64 o.val) xs trivial)⟩
      · refine ⟨fun h => by simp at h, ?_⟩
        rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
        · exact absurd same.symm (N.text_coded s (.base64 o.val) xs trivial)
        · exact absurd same.symm (N.tagged_coded s l (.base64 o.val) xs tl trivial)
      · refine ⟨fun h => by simp at h,
          fun ⟨b, same⟩ => absurd same.symm (N.truth_coded b (.base64 o.val) trivial)⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => ?_⟩
        have := N.coded_injective (.base64 o.val) (.uri s) trivial xs same
        cases this
      · refine ⟨fun h => by simp at h, fun ⟨o', same⟩ => ?_⟩
        have := N.coded_injective (.base64 o.val) (.hex o') trivial trivial same
        cases this
      · exact ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨m, mv, same⟩ => absurd same (N.coded_moment (.base64 o.val) m trivial mv)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨m, mv, _, same⟩ => absurd same (N.coded_moment (.base64 o.val) m trivial mv)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨b, bv, same⟩ => absurd same (N.coded_double (.base64 o.val) b trivial bv)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨b, bv, same⟩ => absurd same (N.coded_float (.base64 o.val) b trivial bv)⟩
    | Moment x =>
      have cx : Rowl.Moments.CanonicalMoment x := canonical
      have valid : (Rowl.Moments.momentOf x).Valid := cx.2.2.2.2.2.2
      have zoneIff : (Rowl.Moments.momentOf x).zone ≠ none ↔ x.zone ≠ none := by
        simp [Rowl.Moments.momentOf]
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space,
          N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.text_moment s _ xs valid)⟩
      · refine ⟨fun h => by simp at h, ?_⟩
        rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
        · exact absurd same.symm (N.text_moment s _ xs valid)
        · exact absurd same.symm (N.tagged_moment s l _ xs tl valid)
      · refine ⟨fun h => by simp at h, fun ⟨b, same⟩ => absurd same.symm (N.truth_moment b _ valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.coded_moment (.uri s) _ xs valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same.symm (N.coded_moment (.hex o) _ trivial valid)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨o, same⟩ => absurd same.symm (N.coded_moment (.base64 o) _ trivial valid)⟩
      · exact ⟨fun _ => ⟨_, valid, rfl⟩, fun _ => .inl trivial⟩
      · constructor
        · rintro (h | ⟨_, z⟩)
          · cases h
          · exact ⟨_, valid, zoneIff.mpr z, rfl⟩
        · rintro ⟨m, mv, mz, same⟩
          have e := N.moment_injective _ _ valid mv same
          rw [← e] at mz
          exact .inr ⟨trivial, zoneIff.mp mz⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.moment_double _ b valid bv)⟩
      · refine ⟨fun h => by simp at h, fun ⟨b, bv, same⟩ => absurd same (N.moment_float _ b valid bv)⟩
    | Double b =>
      have valid : (Rowl.Floats.binaryOf b).Valid doubleFormat := canonical.2
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space,
          N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.text_double s _ xs valid)⟩
      · refine ⟨fun h => by simp at h, ?_⟩
        rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
        · exact absurd same.symm (N.text_double s _ xs valid)
        · exact absurd same.symm (N.tagged_double s l _ xs tl valid)
      · refine ⟨fun h => by simp at h, fun ⟨a, same⟩ => absurd same.symm (N.truth_double a _ valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.coded_double (.uri s) _ xs valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same.symm (N.coded_double (.hex o) _ trivial valid)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨o, same⟩ => absurd same.symm (N.coded_double (.base64 o) _ trivial valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, same⟩ => absurd same.symm (N.moment_double m _ mv valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, _, same⟩ => absurd same.symm (N.moment_double m _ mv valid)⟩
      · exact ⟨fun _ => ⟨_, valid, rfl⟩, fun _ => trivial⟩
      · refine ⟨fun h => by simp at h, fun ⟨a, av, same⟩ => absurd same (N.double_float _ _ valid av)⟩
    | Float b =>
      have valid : (Rowl.Floats.binaryOf b).Valid floatFormat := canonical.2
      cases k <;> simp only [IsNumeric, not_true_eq_false, not_false_eq_true] at numeric <;>
        (try simp only [subtypeOf, Option.some.injEq, exists_eq', not_true_eq_false] at sub) <;>
        simp only [InKind, typeOf, valueOf, N.string_space, N.plain_space, N.boolean_space, N.uri_space, N.hex_space,
          N.base64_space, N.datetime_space, N.stamp_space, N.double_space, N.float_space]
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.text_float s _ xs valid)⟩
      · refine ⟨fun h => by simp at h, ?_⟩
        rintro (⟨s, xs, same⟩ | ⟨s, l, xs, tl, same⟩)
        · exact absurd same.symm (N.text_float s _ xs valid)
        · exact absurd same.symm (N.tagged_float s l _ xs tl valid)
      · refine ⟨fun h => by simp at h, fun ⟨a, same⟩ => absurd same.symm (N.truth_float a _ valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨s, xs, same⟩ => absurd same.symm (N.coded_float (.uri s) _ xs valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨o, same⟩ => absurd same.symm (N.coded_float (.hex o) _ trivial valid)⟩
      · refine ⟨fun h => by simp at h,
          fun ⟨o, same⟩ => absurd same.symm (N.coded_float (.base64 o) _ trivial valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, same⟩ => absurd same.symm (N.moment_float m _ mv valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨m, mv, _, same⟩ => absurd same.symm (N.moment_float m _ mv valid)⟩
      · refine ⟨fun h => by simp at h, fun ⟨a, av, same⟩ => absurd same.symm (N.double_float _ _ av valid)⟩
      · exact ⟨fun _ => ⟨_, valid, rfl⟩, fun _ => trivial⟩

private theorem vec_ext {a b : alloc.vec.Vec U8} (h : a.val = b.val) : a = b := by
  simpa [alloc.vec.Vec.eq_iff] using h

/-- Canonical kernel moments of one moment are one. -/
theorem moment_canonical_injective {x y : datatypes.Moment} (cx : Rowl.Moments.CanonicalMoment x)
    (cy : Rowl.Moments.CanonicalMoment y) (same : Rowl.Moments.momentOf x = Rowl.Moments.momentOf y) : x = y := by
  obtain ⟨xYear, xSign, xFd, xFl, xS, xZone, _⟩ := cx
  obtain ⟨yYear, ySign, yFd, yFl, yS, yZone, _⟩ := cy
  simp only [Rowl.Moments.momentOf, Moment.mk.injEq] at same
  obtain ⟨eYear, eMonth, eDay, eHour, eMinute, eSecond, eZone⟩ := same
  have years : x.negative = y.negative ∧ x.year = y.year := by
    have zx := Rowl.Numbers.canonical_zero x.year.val xYear
    have zy := Rowl.Numbers.canonical_zero y.year.val yYear
    cases hx : x.negative <;> cases hy : y.negative <;> simp only [hx, hy, Bool.false_eq_true, ↓reduceIte,
      one_mul, neg_mul, neg_inj, Nat.cast_inj] at eYear xSign ySign
    · exact ⟨rfl, vec_ext (Rowl.Numbers.canonical_unique _ _ xYear yYear eYear)⟩
    · have : digitsValue y.year.val = 0 := by omega
      exact absurd (zy.mp this) (ySign trivial)
    · have : digitsValue x.year.val = 0 := by omega
      exact absurd (zx.mp this) (xSign trivial)
    · exact ⟨rfl, vec_ext (Rowl.Numbers.canonical_unique _ _ xYear yYear eYear)⟩
  have fx := fraction_bounds x.fraction.val xFd
  have fy := fraction_bounds y.fraction.val yFd
  simp only [fractionValue] at eSecond
  have seconds : x.second.val = y.second.val := by
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with less | more
    · have : (x.second.val : ℚ) + 1 ≤ y.second.val := by exact_mod_cast less
      linarith [fx.2, fy.1]
    · have : (y.second.val : ℚ) + 1 ≤ x.second.val := by exact_mod_cast more
      linarith [fx.1, fy.2]
  have fractions : x.fraction = y.fraction := by
    rw [seconds] at eSecond
    have e : (digitsValue x.fraction.val : ℚ) / 10 ^ x.fraction.val.length =
        (digitsValue y.fraction.val : ℚ) / 10 ^ y.fraction.val.length := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at e
    apply vec_ext
    apply fraction_unique _ _ xFd yFd xFl yFl
    exact_mod_cast e
  have zones : x.zone = y.zone := by
    rcases hx : x.zone with _ | ⟨w, h, m⟩ <;> rcases hy : y.zone with _ | ⟨w', h', m'⟩
    · rfl
    · rw [hx, hy] at eZone; simp at eZone
    · rw [hx, hy] at eZone; simp at eZone
    · rw [hx, hy] at eZone
      simp only [Option.map_some, Option.some.injEq] at eZone
      obtain ⟨m60, wnz⟩ := xZone w h m hx
      obtain ⟨m60', wnz'⟩ := yZone w' h' m' hy
      have parts : w = w' ∧ h.val = h'.val ∧ m.val = m'.val := by
        cases w <;> cases w' <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, true_and,
          forall_const, IsEmpty.forall_iff, false_implies] at eZone wnz wnz' ⊢ <;> omega
      obtain ⟨rfl, eh, em⟩ := parts
      rw [UScalar.eq_of_val_eq eh, UScalar.eq_of_val_eq em]
  obtain ⟨n, yr, mo, d, hr, mi, se, fr, z⟩ := x
  obtain ⟨n', yr', mo', d', hr', mi', se', fr', z'⟩ := y
  simp only at years fractions zones seconds eMonth eDay eHour eMinute
  obtain ⟨rfl, rfl⟩ := years
  subst fractions zones
  rw [UScalar.eq_of_val_eq eMonth, UScalar.eq_of_val_eq eDay, UScalar.eq_of_val_eq eHour,
    UScalar.eq_of_val_eq eMinute, UScalar.eq_of_val_eq seconds]

/-- Under every datatype map that is the OWL 2 map on the datatypes here,
    distinct canonical values are distinct values. -/
theorem value_injective (N : Normative D) {a b : datatypes.DataValue} (ca : Canonical a) (cb : Canonical b)
    (same : valueOf N a = valueOf N b) : a = b := by
  have momentValid : ∀ {x : datatypes.Moment}, Canonical (.Moment x) → (Rowl.Moments.momentOf x).Valid :=
    fun c => (c : Rowl.Moments.CanonicalMoment _).2.2.2.2.2.2
  have doubleValid : ∀ {x : datatypes.Binary}, Canonical (.Double x) → (Rowl.Floats.binaryOf x).Valid doubleFormat :=
    fun c => c.2
  have floatValid : ∀ {x : datatypes.Binary}, Canonical (.Float x) → (Rowl.Floats.binaryOf x).Valid floatFormat :=
    fun c => c.2
  cases a with
  | Number n w f =>
    cases b with
    | Number n' w' f' =>
      obtain ⟨e1, e2, e3⟩ := numberOf_injective ca cb (N.number_injective same)
      rw [e1, vec_ext e2, vec_ext e3]
    | Fraction n' a' b' =>
      exact absurd (N.number_injective same).symm (fraction_ne_number (negative := n') cb)
    | Text t => exact absurd same (N.number_text _ _ cb)
    | Tagged t m => exact absurd same (N.number_tagged _ _ _ cb.1 cb.2)
    | Truth b => exact absurd same (N.number_truth _ _)
    | Uri t => exact absurd same (number_coded N _ (.uri t.val) cb)
    | Hex o => exact absurd same (number_coded N _ (.hex o.val) trivial)
    | Base64 o => exact absurd same (number_coded N _ (.base64 o.val) trivial)
    | Moment x => exact absurd same (fun e => N.real_moment _ _ (momentValid cb) ((real_rat N _).symm.trans e))
    | Double x => exact absurd same (fun e => N.real_double _ _ (doubleValid cb) ((real_rat N _).symm.trans e))
    | Float x => exact absurd same (fun e => N.real_float _ _ (floatValid cb) ((real_rat N _).symm.trans e))
  | Fraction n a' b' =>
    cases b with
    | Number n' w f => exact absurd (N.number_injective same) (fraction_ne_number (negative := n) ca)
    | Fraction n' a'' b'' =>
      obtain ⟨e1, e2, e3⟩ := fractionOf_injective ca cb (N.number_injective same)
      rw [e1, vec_ext e2, vec_ext e3]
    | Text t => exact absurd same (N.number_text _ _ cb)
    | Tagged t m => exact absurd same (N.number_tagged _ _ _ cb.1 cb.2)
    | Truth b => exact absurd same (N.number_truth _ _)
    | Uri t => exact absurd same (number_coded N _ (.uri t.val) cb)
    | Hex o => exact absurd same (number_coded N _ (.hex o.val) trivial)
    | Base64 o => exact absurd same (number_coded N _ (.base64 o.val) trivial)
    | Moment x => exact absurd same (fun e => N.real_moment _ _ (momentValid cb) ((real_rat N _).symm.trans e))
    | Double x => exact absurd same (fun e => N.real_double _ _ (doubleValid cb) ((real_rat N _).symm.trans e))
    | Float x => exact absurd same (fun e => N.real_float _ _ (floatValid cb) ((real_rat N _).symm.trans e))
  | Text t =>
    cases b with
    | Number n w f => exact absurd same.symm (N.number_text _ _ ca)
    | Fraction n a' b' => exact absurd same.symm (N.number_text _ _ ca)
    | Text t' => rw [vec_ext (N.text_injective _ _ ca cb same)]
    | Tagged t' m => exact absurd same (N.text_tagged _ _ _ ca cb.1 cb.2)
    | Truth b => exact absurd same (N.text_truth _ _ ca)
    | Uri t' => exact absurd same (N.text_coded _ (.uri t'.val) ca cb)
    | Hex o => exact absurd same (N.text_coded _ (.hex o.val) ca trivial)
    | Base64 o => exact absurd same (N.text_coded _ (.base64 o.val) ca trivial)
    | Moment x => exact absurd same (N.text_moment _ _ ca (momentValid cb))
    | Double x => exact absurd same (N.text_double _ _ ca (doubleValid cb))
    | Float x => exact absurd same (N.text_float _ _ ca (floatValid cb))
  | Tagged t m =>
    cases b with
    | Number n w f => exact absurd same.symm (N.number_tagged _ _ _ ca.1 ca.2)
    | Fraction n a' b' => exact absurd same.symm (N.number_tagged _ _ _ ca.1 ca.2)
    | Text t' => exact absurd same.symm (N.text_tagged _ _ _ cb ca.1 ca.2)
    | Tagged t' m' =>
      obtain ⟨e1, e2⟩ := N.tagged_injective _ _ _ _ ca.1 cb.1 ca.2 cb.2 same
      rw [vec_ext e1, vec_ext e2]
    | Truth b => exact absurd same (N.tagged_truth _ _ _ ca.1 ca.2)
    | Uri t' => exact absurd same (N.tagged_coded _ _ (.uri t'.val) ca.1 ca.2 cb)
    | Hex o => exact absurd same (N.tagged_coded _ _ (.hex o.val) ca.1 ca.2 trivial)
    | Base64 o => exact absurd same (N.tagged_coded _ _ (.base64 o.val) ca.1 ca.2 trivial)
    | Moment x => exact absurd same (N.tagged_moment _ _ _ ca.1 ca.2 (momentValid cb))
    | Double x => exact absurd same (N.tagged_double _ _ _ ca.1 ca.2 (doubleValid cb))
    | Float x => exact absurd same (N.tagged_float _ _ _ ca.1 ca.2 (floatValid cb))
  | Truth x =>
    cases b with
    | Number n w f => exact absurd same.symm (N.number_truth _ _)
    | Fraction n a' b' => exact absurd same.symm (N.number_truth _ _)
    | Text t => exact absurd same.symm (N.text_truth _ _ cb)
    | Tagged t m => exact absurd same.symm (N.tagged_truth _ _ _ cb.1 cb.2)
    | Truth y => rw [N.truth_injective same]
    | Uri t => exact absurd same (N.truth_coded _ (.uri t.val) cb)
    | Hex o => exact absurd same (N.truth_coded _ (.hex o.val) trivial)
    | Base64 o => exact absurd same (N.truth_coded _ (.base64 o.val) trivial)
    | Moment x => exact absurd same (N.truth_moment _ _ (momentValid cb))
    | Double x => exact absurd same (N.truth_double _ _ (doubleValid cb))
    | Float x => exact absurd same (N.truth_float _ _ (floatValid cb))
  | Uri t =>
    cases b with
    | Number n w f => exact absurd same.symm (number_coded N _ (.uri t.val) ca)
    | Fraction n a' b' => exact absurd same.symm (number_coded N _ (.uri t.val) ca)
    | Text t' => exact absurd same.symm (N.text_coded _ (.uri t.val) cb ca)
    | Tagged t' m => exact absurd same.symm (N.tagged_coded _ _ (.uri t.val) cb.1 cb.2 ca)
    | Truth y => exact absurd same.symm (N.truth_coded _ (.uri t.val) ca)
    | Uri t' =>
      have := N.coded_injective (.uri t.val) (.uri t'.val) ca cb same
      simp only [Coded.uri.injEq] at this
      rw [vec_ext this]
    | Hex o => have := N.coded_injective (.uri t.val) (.hex o.val) ca trivial same; cases this
    | Base64 o => have := N.coded_injective (.uri t.val) (.base64 o.val) ca trivial same; cases this
    | Moment x => exact absurd same (N.coded_moment (.uri t.val) _ ca (momentValid cb))
    | Double x => exact absurd same (N.coded_double (.uri t.val) _ ca (doubleValid cb))
    | Float x => exact absurd same (N.coded_float (.uri t.val) _ ca (floatValid cb))
  | Hex o =>
    cases b with
    | Number n w f => exact absurd same.symm (number_coded N _ (.hex o.val) trivial)
    | Fraction n a' b' => exact absurd same.symm (number_coded N _ (.hex o.val) trivial)
    | Text t' => exact absurd same.symm (N.text_coded _ (.hex o.val) cb trivial)
    | Tagged t' m => exact absurd same.symm (N.tagged_coded _ _ (.hex o.val) cb.1 cb.2 trivial)
    | Truth y => exact absurd same.symm (N.truth_coded _ (.hex o.val) trivial)
    | Uri t' => have := N.coded_injective (.hex o.val) (.uri t'.val) trivial cb same; cases this
    | Hex o' =>
      have := N.coded_injective (.hex o.val) (.hex o'.val) trivial trivial same
      simp only [Coded.hex.injEq] at this
      rw [vec_ext this]
    | Base64 o' => have := N.coded_injective (.hex o.val) (.base64 o'.val) trivial trivial same; cases this
    | Moment x => exact absurd same (N.coded_moment (.hex o.val) _ trivial (momentValid cb))
    | Double x => exact absurd same (N.coded_double (.hex o.val) _ trivial (doubleValid cb))
    | Float x => exact absurd same (N.coded_float (.hex o.val) _ trivial (floatValid cb))
  | Base64 o =>
    cases b with
    | Number n w f => exact absurd same.symm (number_coded N _ (.base64 o.val) trivial)
    | Fraction n a' b' => exact absurd same.symm (number_coded N _ (.base64 o.val) trivial)
    | Text t' => exact absurd same.symm (N.text_coded _ (.base64 o.val) cb trivial)
    | Tagged t' m => exact absurd same.symm (N.tagged_coded _ _ (.base64 o.val) cb.1 cb.2 trivial)
    | Truth y => exact absurd same.symm (N.truth_coded _ (.base64 o.val) trivial)
    | Uri t' => have := N.coded_injective (.base64 o.val) (.uri t'.val) trivial cb same; cases this
    | Hex o' => have := N.coded_injective (.base64 o.val) (.hex o'.val) trivial trivial same; cases this
    | Base64 o' =>
      have := N.coded_injective (.base64 o.val) (.base64 o'.val) trivial trivial same
      simp only [Coded.base64.injEq] at this
      rw [vec_ext this]
    | Moment x => exact absurd same (N.coded_moment (.base64 o.val) _ trivial (momentValid cb))
    | Double x => exact absurd same (N.coded_double (.base64 o.val) _ trivial (doubleValid cb))
    | Float x => exact absurd same (N.coded_float (.base64 o.val) _ trivial (floatValid cb))
  | Moment x =>
    have va := momentValid ca
    cases b with
    | Number n w f => exact absurd same.symm (fun e => N.real_moment _ _ va ((real_rat N _).symm.trans e))
    | Fraction n a' b' => exact absurd same.symm (fun e => N.real_moment _ _ va ((real_rat N _).symm.trans e))
    | Text t' => exact absurd same.symm (N.text_moment _ _ cb va)
    | Tagged t' m => exact absurd same.symm (N.tagged_moment _ _ _ cb.1 cb.2 va)
    | Truth y => exact absurd same.symm (N.truth_moment _ _ va)
    | Uri t' => exact absurd same.symm (N.coded_moment (.uri t'.val) _ cb va)
    | Hex o => exact absurd same.symm (N.coded_moment (.hex o.val) _ trivial va)
    | Base64 o => exact absurd same.symm (N.coded_moment (.base64 o.val) _ trivial va)
    | Moment y =>
      rw [moment_canonical_injective ca cb (N.moment_injective _ _ va (momentValid cb) same)]
    | Double y => exact absurd same (N.moment_double _ _ va (doubleValid cb))
    | Float y => exact absurd same (N.moment_float _ _ va (floatValid cb))
  | Double x =>
    have va := doubleValid ca
    cases b with
    | Number n w f => exact absurd same.symm (fun e => N.real_double _ _ va ((real_rat N _).symm.trans e))
    | Fraction n a' b' => exact absurd same.symm (fun e => N.real_double _ _ va ((real_rat N _).symm.trans e))
    | Text t' => exact absurd same.symm (N.text_double _ _ cb va)
    | Tagged t' m => exact absurd same.symm (N.tagged_double _ _ _ cb.1 cb.2 va)
    | Truth y => exact absurd same.symm (N.truth_double _ _ va)
    | Uri t' => exact absurd same.symm (N.coded_double (.uri t'.val) _ cb va)
    | Hex o => exact absurd same.symm (N.coded_double (.hex o.val) _ trivial va)
    | Base64 o => exact absurd same.symm (N.coded_double (.base64 o.val) _ trivial va)
    | Moment y => exact absurd same.symm (N.moment_double _ _ (momentValid cb) va)
    | Double y =>
      rw [Rowl.Floats.binary_canonical_injective ca.1 cb.1 (N.double_injective _ _ va (doubleValid cb) same)]
    | Float y => exact absurd same (N.double_float _ _ va (floatValid cb))
  | Float x =>
    have va := floatValid ca
    cases b with
    | Number n w f => exact absurd same.symm (fun e => N.real_float _ _ va ((real_rat N _).symm.trans e))
    | Fraction n a' b' => exact absurd same.symm (fun e => N.real_float _ _ va ((real_rat N _).symm.trans e))
    | Text t' => exact absurd same.symm (N.text_float _ _ cb va)
    | Tagged t' m => exact absurd same.symm (N.tagged_float _ _ _ cb.1 cb.2 va)
    | Truth y => exact absurd same.symm (N.truth_float _ _ va)
    | Uri t' => exact absurd same.symm (N.coded_float (.uri t'.val) _ cb va)
    | Hex o => exact absurd same.symm (N.coded_float (.hex o.val) _ trivial va)
    | Base64 o => exact absurd same.symm (N.coded_float (.base64 o.val) _ trivial va)
    | Moment y => exact absurd same.symm (N.moment_float _ _ (momentValid cb) va)
    | Double y => exact absurd same.symm (N.double_float _ _ (doubleValid cb) va)
    | Float y =>
      rw [Rowl.Floats.binary_canonical_injective ca.1 cb.1 (N.float_injective _ _ va (floatValid cb) same)]

/-! ### The range facets -/

/-- The IRI of a range facet. -/
def facetIri : datatypes.Facet → Iri
  | .MinInclusive => minInclusiveFacet
  | .MaxInclusive => maxInclusiveFacet
  | .MinExclusive => minExclusiveFacet
  | .MaxExclusive => maxExclusiveFacet

/-- The range facet an IRI names, if any. -/
noncomputable def facetOf (iri : Iri) : Option datatypes.Facet :=
  if iri = minInclusiveFacet then some .MinInclusive
  else if iri = maxInclusiveFacet then some .MaxInclusive
  else if iri = minExclusiveFacet then some .MinExclusive
  else if iri = maxExclusiveFacet then some .MaxExclusive
  else none

theorem iri_eq_iff (a b : Iri) : a = b ↔ a.spelling.val = b.spelling.val := by
  cases a; cases b; simp [alloc.vec.Vec.eq_iff]

/-- The kernel recognizes exactly the four range facets by their IRIs. -/
theorem facet_of_correct (iri : Iri) : datatypes.facet_of iri = .ok (facetOf iri) := by
  rw [datatypes.facet_of, facetOf]
  simp only [iri_eq_iff iri minInclusiveFacet, iri_eq_iff iri maxInclusiveFacet, iri_eq_iff iri minExclusiveFacet,
    iri_eq_iff iri maxExclusiveFacet]
  by_cases a : iri.spelling.val = minInclusiveFacet.spelling.val <;>
  by_cases b : iri.spelling.val = maxInclusiveFacet.spelling.val <;>
  by_cases c : iri.spelling.val = minExclusiveFacet.spelling.val <;>
  by_cases d : iri.spelling.val = maxExclusiveFacet.spelling.val <;>
    simp_all [same_pattern_total, Array.to_slice, Array.make, lift, minInclusiveFacet, maxInclusiveFacet,
      minExclusiveFacet, maxExclusiveFacet]

theorem facetOf_facetIri (F : datatypes.Facet) : facetOf (facetIri F) = some F := by
  cases F <;> simp [facetOf, facetIri, iri_eq_iff, minInclusiveFacet, maxInclusiveFacet, minExclusiveFacet,
    maxExclusiveFacet]

theorem facetIri_range (F : datatypes.Facet) : facetIri F ∈ rangeFacets := by
  cases F <;> simp [facetIri, rangeFacets]

/-- Whether a number meets a range facet with a bound. -/
def FacetHolds : datatypes.Facet → ℚ → ℚ → Prop
  | .MinInclusive, bound, x => bound ≤ x
  | .MaxInclusive, bound, x => x ≤ bound
  | .MinExclusive, bound, x => bound < x
  | .MaxExclusive, bound, x => x < bound

theorem facet_order_correct (F : datatypes.Facet) (o : U8) (bound x : ℚ) (h : o.val = orderOf x bound) :
    datatypes.facet_order F o = .ok (decide (FacetHolds F bound x)) := by
  by_cases lt : x < bound
  · have : o = 0#u8 := by apply UScalar.eq_of_val_eq; rw [h, orderOf_lt lt]; rfl
    subst this
    cases F <;> simp [datatypes.facet_order, FacetHolds, lt, le_of_lt lt, not_le.mpr lt, not_lt.mpr (le_of_lt lt)]
  · by_cases eq : x = bound
    · have : o = 1#u8 := by apply UScalar.eq_of_val_eq; rw [h, orderOf_eq eq]; rfl
      subst this; subst eq
      cases F <;> simp [datatypes.facet_order, FacetHolds]
    · have gt : bound < x := lt_of_le_of_ne (not_lt.mp lt) (Ne.symm eq)
      have : o = 2#u8 := by apply UScalar.eq_of_val_eq; rw [h, orderOf_gt gt]; rfl
      subst this
      cases F <;> simp [datatypes.facet_order, FacetHolds, gt, le_of_lt gt, not_le.mpr gt, not_lt.mpr (le_of_lt gt)]

/-- The kernel evaluates a range facet on a canonical number exactly. -/
theorem facet_holds_correct (F : datatypes.Facet) (bound value : datatypes.DataValue)
    (cb : IsNumber bound → CanonicalNumeric bound) (cv : IsNumber value → CanonicalNumeric value) :
    ∃ r, datatypes.facet_holds F bound value = .ok r ∧
      (∀ b, r = some b → IsNumber bound ∧ IsNumber value ∧
        (b = true ↔ FacetHolds F (numValue bound) (numValue value))) ∧
      (r = none → ¬ IsNumber bound ∨ ¬ IsNumber value ∨ Usize.max / 8 ≤ digitWidth bound ∨
        Usize.max / 8 ≤ digitWidth value) := by
  rw [datatypes.facet_holds]
  obtain ⟨res, run, noneCase, someCase⟩ := compare_values_correct value bound cv cb
  cases res with
  | none =>
    refine ⟨none, by simp [run], by simp, fun _ => ?_⟩
    rcases noneCase rfl with h | h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr (.inr h))
    · exact .inr (.inr (.inl h))
  | some o =>
    obtain ⟨nv, nb, value'⟩ := someCase o rfl
    refine ⟨some (decide (FacetHolds F (numValue bound) (numValue value))),
      by simp [run, facet_order_correct F o _ _ value'], fun b h => ?_, by simp⟩
    cases h
    exact ⟨nb, nv, by simp⟩

variable {Native : Type w} {D : DatatypeMap Native}

theorem valueOf_number (N : Normative D) {v : datatypes.DataValue} (h : IsNumber v) :
    valueOf N v = N.real (numValue v) := by
  cases v <;> simp_all [IsNumber, valueOf, numValue, real_rat]

/-- Under every datatype map that is the OWL 2 map on the datatypes here, the
    facet value of a range facet with a numeric bound holds of a numeric value
    exactly as `FacetHolds` says. -/
theorem normative_facet (N : Normative D) (F : datatypes.Facet) {bound value : datatypes.DataValue}
    (nb : IsNumber bound) (nv : IsNumber value) :
    D.facetValue (facetIri F) (valueOf N bound) (valueOf N value) ↔
      FacetHolds F (numValue bound) (numValue value) := by
  rw [valueOf_number N nb, valueOf_number N nv]
  have cast : ∀ s, N.real (numValue value) = N.real s ↔ s = (numValue value : ℝ) := fun s =>
    ⟨fun h => (N.real_injective h).symm, fun h => by rw [h]⟩
  cases F
  · simp only [facetIri, N.min_inclusive_value, FacetHolds, cast]
    constructor
    · rintro ⟨s, le, rfl⟩; exact_mod_cast le
    · intro le; exact ⟨_, by exact_mod_cast le, rfl⟩
  · simp only [facetIri, N.max_inclusive_value, FacetHolds, cast]
    constructor
    · rintro ⟨s, le, rfl⟩; exact_mod_cast le
    · intro le; exact ⟨_, by exact_mod_cast le, rfl⟩
  · simp only [facetIri, N.min_exclusive_value, FacetHolds, cast]
    constructor
    · rintro ⟨s, lt, rfl⟩; exact_mod_cast lt
    · intro lt; exact ⟨_, by exact_mod_cast lt, rfl⟩
  · simp only [facetIri, N.max_exclusive_value, FacetHolds, cast]
    constructor
    · rintro ⟨s, lt, rfl⟩; exact_mod_cast lt
    · intro lt; exact ⟨_, by exact_mod_cast lt, rfl⟩

/-- The numeric datatypes of XML Schema here. -/
def IsXsdNumeric : datatypes.Kind → Prop
  | .String | .Plain | .Boolean | .Real | .Rational | .AnyUri | .HexBinary | .Base64Binary | .NormalizedString
  | .Token | .Language | .NmToken | .Name | .NcName | .DateTime | .DateTimeStamp | .Double | .Float => False
  | _ => True

theorem xsd_listed (k : datatypes.Kind) (h : IsXsdNumeric k) : typeOf k ∈ xsdNumericTypes := by
  cases k <;> simp_all [IsXsdNumeric, xsdNumericTypes, integerSubtypes, typeOf]

theorem facet_applies_xsd (k : datatypes.Kind) (xsd : IsXsdNumeric k) (bound : datatypes.DataValue) :
    datatypes.numeric_facet_applies k bound = (do
      let b ← datatypes.numeric bound
      if b then datatypes.in_kind bound k else .ok false) := by
  cases k <;> simp_all [IsXsdNumeric, datatypes.numeric_facet_applies]

/-- On a bound other than a floating-point value, the kernel decides the facet
    spaces of the numbers. -/
theorem facet_applies_numeric (k : datatypes.Kind) {bound : datatypes.DataValue}
    (notBinary : (∀ x, bound ≠ .Double x) ∧ ∀ x, bound ≠ .Float x) :
    datatypes.facet_applies k bound = datatypes.numeric_facet_applies k bound := by
  cases bound <;> simp_all [datatypes.facet_applies]

/-- Under every datatype map that is the OWL 2 map on the datatypes here, the
    kernel says exactly whether a range facet with a canonical bound is in the
    facet space of a numeric kind's datatype: for `owl:real` and `owl:rational`
    every number, and for the numeric datatypes of XML Schema every number of
    their value space. -/
theorem facet_applies_correct (k : datatypes.Kind) (bound : datatypes.DataValue) (c : Canonical bound) :
    ∃ b, datatypes.facet_applies k bound = .ok b ∧
      ∀ (F : datatypes.Facet) {Native : Type w} (D : DatatypeMap Native) (N : Normative D), IsNumeric k →
        (b = true ↔ D.facetSpace (typeOf k) (facetIri F) (valueOf N bound)) := by
  by_cases binary : (∃ x, bound = .Double x) ∨ ∃ x, bound = .Float x
  · have notReal : ∀ {Native : Type w} {D : DatatypeMap Native} (N : Normative D) (r : ℝ),
        N.real r ≠ valueOf N bound := by
      intro Native D N r same
      rcases binary with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact N.real_double r _ c.2 same
      · exact N.real_float r _ c.2 same
    have space : ∀ (F : datatypes.Facet) {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
        IsNumeric k → ¬ D.facetSpace (typeOf k) (facetIri F) (valueOf N bound) := by
      intro F Native D N numeric space
      by_cases xsd : IsXsdNumeric k
      · rw [N.xsd_facets _ (xsd_listed k xsd), ← normative_in_kind N c] at space
        rcases binary with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> cases k <;> simp_all [InKind, IsXsdNumeric]
      · cases k <;> simp_all [IsNumeric, IsXsdNumeric]
        · obtain ⟨_, r, same⟩ := (N.real_facets _ _).mp space
          exact notReal N r same.symm
        · obtain ⟨_, r, same⟩ := (N.rational_facets _ _).mp space
          exact notReal N r same.symm
    rcases binary with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · refine ⟨decide (k = .Double), by cases k <;> simp [datatypes.facet_applies], fun F Native D N numeric => ?_⟩
      have notDouble : k ≠ .Double := by rintro rfl; simp [IsNumeric] at numeric
      simp only [notDouble, decide_false, Bool.false_eq_true, false_iff]
      exact space F D N numeric
    · refine ⟨decide (k = .Float), by cases k <;> simp [datatypes.facet_applies], fun F Native D N numeric => ?_⟩
      have notFloat : k ≠ .Float := by rintro rfl; simp [IsNumeric] at numeric
      simp only [notFloat, decide_false, Bool.false_eq_true, false_iff]
      exact space F D N numeric
  have notBinary : (∀ x, bound ≠ .Double x) ∧ ∀ x, bound ≠ .Float x :=
    ⟨fun x h => binary (.inl ⟨x, h⟩), fun x h => binary (.inr ⟨x, h⟩)⟩
  rw [facet_applies_numeric k notBinary]
  have range := facetIri_range
  have notReal : ∀ {Native : Type w} {D : DatatypeMap Native} (N : Normative D), ¬ IsNumber bound →
      ∀ r, valueOf N bound ≠ N.real r := by
    intro Native D N nb r same
    cases bound with
    | Number _ _ _ => exact nb trivial
    | Fraction _ _ _ => exact nb trivial
    | Text t => exact N.real_text r _ c same.symm
    | Tagged t m => exact N.real_tagged r _ _ c.1 c.2 same.symm
    | Truth b => exact N.real_truth r b same.symm
    | Uri t => exact N.real_coded r (.uri t.val) c same.symm
    | Hex o => exact N.real_coded r (.hex o.val) trivial same.symm
    | Base64 o => exact N.real_coded r (.base64 o.val) trivial same.symm
    | Moment x => exact N.real_moment r _ (c : Rowl.Moments.CanonicalMoment x).2.2.2.2.2.2 same.symm
    | Double x => exact N.real_double r _ c.2 same.symm
    | Float x => exact N.real_float r _ c.2 same.symm
  by_cases xsd : IsXsdNumeric k
  · rw [facet_applies_xsd k xsd, numeric_correct]
    by_cases nb : IsNumber bound
    · refine ⟨decide (InKind bound k), by simp [nb, in_kind_correct bound c], fun F _ D N _ => ?_⟩
      rw [N.xsd_facets _ (xsd_listed k xsd), ← normative_in_kind N c]
      simp [range F]
    · refine ⟨false, by simp [nb], fun F _ D N _ => ?_⟩
      rw [N.xsd_facets _ (xsd_listed k xsd), ← normative_in_kind N c]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ inKind
      apply nb
      cases bound <;> simp_all [InKind, IsNumber, IsXsdNumeric, TextIn, subtypeOf] <;>
        cases k <;> simp_all [IsXsdNumeric]
  · cases k with
    | Real =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      by_cases nb : IsNumber bound
      · refine ⟨true, by simp [nb], fun F _ D N _ => ?_⟩
        simp only [typeOf, N.real_facets, true_iff]
        exact ⟨range F, _, valueOf_number N nb⟩
      · refine ⟨false, by simp [nb], fun F _ D N _ => ?_⟩
        simp only [typeOf, N.real_facets, Bool.false_eq_true, false_iff, not_and, not_exists]
        exact fun _ r h => notReal N nb r h
    | Rational =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      by_cases nb : IsNumber bound
      · refine ⟨true, by simp [nb], fun F _ D N _ => ?_⟩
        simp only [typeOf, N.rational_facets, true_iff]
        exact ⟨range F, _, valueOf_number N nb⟩
      · refine ⟨false, by simp [nb], fun F _ D N _ => ?_⟩
        simp only [typeOf, N.rational_facets, Bool.false_eq_true, false_iff, not_and, not_exists]
        exact fun _ r h => notReal N nb r h
    | String =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Plain =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Boolean =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | AnyUri =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | HexBinary =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Base64Binary =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | NormalizedString =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Token =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Language =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | NmToken =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Name =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | NcName =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | DateTime =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | DateTimeStamp =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Double =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | Float =>
      simp only [datatypes.numeric_facet_applies, numeric_correct]
      exact ⟨false, by simp only [bind_ok, ite_self], fun _ _ _ _ h => absurd h (by simp [IsNumeric])⟩
    | _ => exact absurd trivial xsd

/-! ### Range facets on floating-point numbers -/

/-- The value of a floating-point value of `xsd:double` (`double`) or
    `xsd:float`. -/
def binaryValue (N : Normative D) : Bool → Binary → Native
  | true, x => N.double x
  | false, x => N.float x

theorem binaryValue_lit (N : Normative D) (double : Bool) (b : datatypes.Binary) :
    valueOf N (if double then .Double b else .Float b) = binaryValue N double (Rowl.Floats.binaryOf b) := by
  cases double <;> rfl

/-- Under every datatype map that is the OWL 2 map on the datatypes here, the
    facet value of a range facet with a floating-point bound is the set of the
    values of its format that meet it in the order of XML Schema. -/
theorem normative_binary_facet (N : Normative D) (F : datatypes.Facet) (double : Bool) {b : Binary}
    (vb : b.Valid (Rowl.Floats.fmt double)) (y : Native) :
    D.facetValue (facetIri F) (binaryValue N double b) y ↔
      ∃ x, x.Valid (Rowl.Floats.fmt double) ∧ Rowl.FloatOrder.FacetHolds F b x ∧ y = binaryValue N double x := by
  cases double <;> cases F <;>
    simp only [binaryValue, facetIri, Rowl.FloatOrder.FacetHolds, Rowl.Floats.fmt] <;>
    first
    | exact N.min_inclusive_float b y vb | exact N.max_inclusive_float b y vb
    | exact N.min_exclusive_float b y vb | exact N.max_exclusive_float b y vb
    | exact N.min_inclusive_double b y vb | exact N.max_inclusive_double b y vb
    | exact N.min_exclusive_double b y vb | exact N.max_exclusive_double b y vb

/-- Under every datatype map that is the OWL 2 map on the datatypes here, the
    kernel says exactly whether a range facet with a canonical bound is in the
    facet space of `xsd:double` or `xsd:float`: a value of the datatype. -/
theorem facet_applies_binary (double : Bool) (bound : datatypes.DataValue) (c : Canonical bound) :
    ∃ b, datatypes.facet_applies (if double then .Double else .Float) bound = .ok b ∧
      ∀ (F : datatypes.Facet) {Native : Type w} (D : DatatypeMap Native) (N : Normative D),
        (b = true ↔ D.facetSpace (typeOf (if double then .Double else .Float)) (facetIri F) (valueOf N bound)) := by
  have range := facetIri_range
  cases double
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨decide (∃ x, bound = .Float x), ?_, fun F Native D N => ?_⟩
    · cases bound <;> simp [datatypes.facet_applies, datatypes.numeric_facet_applies, datatypes.numeric]
    · rw [show typeOf .Float = floatType from rfl, N.float_facets]
      simp only [range F, true_and, decide_eq_true_eq]
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨_, c.2, rfl⟩
      · rintro ⟨b, vb, same⟩
        cases bound with
        | Float x => exact ⟨x, rfl⟩
        | Double x => exact absurd same (N.double_float _ _ c.2 vb)
        | Number n w f => exact absurd ((real_rat N _).symm.trans same) (N.real_float _ _ vb)
        | Fraction n a d => exact absurd ((real_rat N _).symm.trans same) (N.real_float _ _ vb)
        | Text t => exact absurd same (N.text_float _ _ c vb)
        | Tagged t m => exact absurd same (N.tagged_float _ _ _ c.1 c.2 vb)
        | Truth t => exact absurd same (N.truth_float _ _ vb)
        | Uri t => exact absurd same (N.coded_float _ _ c vb)
        | Hex o => exact absurd same (N.coded_float _ _ trivial vb)
        | Base64 o => exact absurd same (N.coded_float _ _ trivial vb)
        | Moment x => exact absurd same (N.moment_float _ _ (c : Rowl.Moments.CanonicalMoment x).2.2.2.2.2.2 vb)
  · simp only [↓reduceIte]
    refine ⟨decide (∃ x, bound = .Double x), ?_, fun F Native D N => ?_⟩
    · cases bound <;> simp [datatypes.facet_applies, datatypes.numeric_facet_applies, datatypes.numeric]
    · rw [show typeOf .Double = doubleType from rfl, N.double_facets]
      simp only [range F, true_and, decide_eq_true_eq]
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨_, c.2, rfl⟩
      · rintro ⟨b, vb, same⟩
        cases bound with
        | Double x => exact ⟨x, rfl⟩
        | Float x => exact absurd same.symm (N.double_float _ _ vb c.2)
        | Number n w f => exact absurd ((real_rat N _).symm.trans same) (N.real_double _ _ vb)
        | Fraction n a d => exact absurd ((real_rat N _).symm.trans same) (N.real_double _ _ vb)
        | Text t => exact absurd same (N.text_double _ _ c vb)
        | Tagged t m => exact absurd same (N.tagged_double _ _ _ c.1 c.2 vb)
        | Truth t => exact absurd same (N.truth_double _ _ vb)
        | Uri t => exact absurd same (N.coded_double _ _ c vb)
        | Hex o => exact absurd same (N.coded_double _ _ trivial vb)
        | Base64 o => exact absurd same (N.coded_double _ _ trivial vb)
        | Moment x => exact absurd same (N.moment_double _ _ (c : Rowl.Moments.CanonicalMoment x).2.2.2.2.2.2 vb)

/-! ### The specification has a model

A datatype map on real numbers, strings, tagged strings and truth values, with
every lexical-to-value mapping chosen by the specification's unique value and
the facet values of the four range facets on the reals, is the OWL 2 map on the
datatypes here: `Normative` is not contradictory. -/

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


/-- An `owl:rational` lexical form writes one number. -/
theorem rational_form_unique {text : List U8} {q q' : ℚ} (a : RationalForm text q) (b : RationalForm text q') :
    q = q' := by
  obtain ⟨n1, d1, p1, s1, i1, _, _, rfl⟩ := a
  obtain ⟨n2, d2, p2, s2, i2, _, _, rfl⟩ := b
  have clean1 := no_slash_of_integer i1
  have clean2 := no_slash_of_integer i2
  have lengths : n1.length = n2.length := by
    have := first_slash s2 clean2 n1.length (by rw [s1]; simp)
      (fun i h less => by
        have inside : text[i] = n1[i] := by simp [s1, List.getElem_append_left less]
        rw [inside]; intro e; exact clean1 (e ▸ List.getElem_mem less))
      (fun h => by simp [s1])
    exact this
  have numerators : n1 = n2 := by
    have := congrArg (List.take n1.length) (s1.symm.trans s2)
    simpa [lengths] using this
  subst numerators
  have denominators : d1 = d2 := by simpa using s1.symm.trans s2
  subst denominators
  rw [number_form_unique (whole := true) i1 i2]

/-- The values of the model map. -/
inductive ModelValue where
  | real (r : ℝ)
  | text (s : List U8)
  | tagged (s l : List U8)
  | truth (b : Bool)
  | coded (a : Coded)
  | moment (m : Moment)
  | double (b : Binary)
  | float (b : Binary)
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
  | .Integer => if h : ∃ q, NumberForm true t q then .real ((Classical.choose h : ℚ) : ℝ) else .other
  | .Decimal => if h : ∃ q, NumberForm false t q then .real ((Classical.choose h : ℚ) : ℝ) else .other
  | .String => .text t
  | .Plain =>
    if h : ∃ p : List U8 × List U8, PlainSplit t p.1 p.2 then
      if (Classical.choose h).2 = [] then .text (Classical.choose h).1
      else .tagged (Classical.choose h).1 ((Classical.choose h).2.map lowerByte)
    else .other
  | .Boolean => if h : ∃ b, TruthForm t b then .truth (Classical.choose h) else .other
  | .Real => .other
  | .Rational => if h : ∃ q, RationalForm t q then .real ((Classical.choose h : ℚ) : ℝ) else .other
  | .AnyUri => .coded (.uri t)
  | .HexBinary => if h : ∃ o, HexForm t o then .coded (.hex (Classical.choose h)) else .other
  | .Base64Binary => if h : ∃ o, Base64Form t o then .coded (.base64 (Classical.choose h)) else .other
  | .NormalizedString | .Token | .Language | .NmToken | .Name | .NcName => .text t
  | .DateTime => if h : ∃ m, MomentForm t m then .moment (Classical.choose h) else .other
  | .DateTimeStamp => if h : ∃ m, MomentForm t m ∧ m.zone ≠ none then .moment (Classical.choose h) else .other
  | .Double => if h : ∃ b, BinaryForm doubleFormat t b then .double (Classical.choose h) else .other
  | .Float => if h : ∃ b, BinaryForm floatFormat t b then .float (Classical.choose h) else .other
  | _ => if h : ∃ q, NumberForm true t q then .real ((Classical.choose h : ℚ) : ℝ) else .other

/-- The value space of the datatype of a kind in the model map. -/
def ModelSpace : datatypes.Kind → ModelValue → Prop
  | .String, x => ∃ s, XmlText s ∧ x = .text s
  | .Plain, x => (∃ s, XmlText s ∧ x = .text s) ∨ ∃ s l, XmlText s ∧ TagValue l ∧ x = .tagged s l
  | .Boolean, x => ∃ b, x = .truth b
  | .AnyUri, x => ∃ s, XmlText s ∧ x = .coded (.uri s)
  | .HexBinary, x => ∃ o, x = .coded (.hex o)
  | .Base64Binary, x => ∃ o, x = .coded (.base64 o)
  | .NormalizedString, x => ∃ s, StringSubtype.normalized.Form s ∧ x = .text s
  | .Token, x => ∃ s, StringSubtype.token.Form s ∧ x = .text s
  | .Language, x => ∃ s, StringSubtype.language.Form s ∧ x = .text s
  | .NmToken, x => ∃ s, StringSubtype.nmtoken.Form s ∧ x = .text s
  | .Name, x => ∃ s, StringSubtype.name.Form s ∧ x = .text s
  | .NcName, x => ∃ s, StringSubtype.ncname.Form s ∧ x = .text s
  | .DateTime, x => ∃ m, m.Valid ∧ x = .moment m
  | .DateTimeStamp, x => ∃ m, m.Valid ∧ m.zone ≠ none ∧ x = .moment m
  | .Double, x => ∃ b, b.Valid doubleFormat ∧ x = .double b
  | .Float, x => ∃ b, b.Valid floatFormat ∧ x = .float b
  | k, x => ∃ r, x = .real r ∧ RealIn k r

/-- The facet space of the datatype of a kind in the model map. -/
def ModelFacetSpace (k : datatypes.Kind) (f : Iri) (v : ModelValue) : Prop :=
  match k with
  | .String => False
  | .Plain => False
  | .Boolean => False
  | .AnyUri => False
  | .HexBinary => False
  | .Base64Binary => False
  | .NormalizedString => False
  | .Token => False
  | .Language => False
  | .NmToken => False
  | .Name => False
  | .NcName => False
  | .DateTime => f ∈ rangeFacets ∧ ∃ m, m.Valid ∧ v = .moment m
  | .DateTimeStamp => f ∈ rangeFacets ∧ ∃ m, m.Valid ∧ m.zone ≠ none ∧ v = .moment m
  | .Double => f ∈ rangeFacets ∧ ∃ b, b.Valid doubleFormat ∧ v = .double b
  | .Float => f ∈ rangeFacets ∧ ∃ b, b.Valid floatFormat ∧ v = .float b
  | .Real => f ∈ rangeFacets ∧ ∃ r, v = .real r
  | .Rational => f ∈ rangeFacets ∧ ∃ r, v = .real r
  | k => f ∈ rangeFacets ∧ ModelSpace k v

/-- Whether a floating-point value is on the side of a range facet of a bound
    in the order of XML Schema. -/
def BinaryFacet (f : Iri) (b x : Binary) : Prop :=
  (f = minInclusiveFacet ∧ b.Le x) ∨ (f = maxInclusiveFacet ∧ x.Le b) ∨
    (f = minExclusiveFacet ∧ b.Lt x) ∨ (f = maxExclusiveFacet ∧ x.Lt b)

/-- Whether a time instant is on the side of a range facet of a bound in the
    order of XML Schema. -/
def MomentFacet (f : Iri) (b x : Moment) : Prop :=
  (f = minInclusiveFacet ∧ b.Le x) ∨ (f = maxInclusiveFacet ∧ x.Le b) ∨
    (f = minExclusiveFacet ∧ b.Lt x) ∨ (f = maxExclusiveFacet ∧ x.Lt b)

/-- The facet values of the range facets in the model map: the reals on the
    facet's side of a real bound, the values of a floating-point format on the
    facet's side of a bound of the format, and the time instants on the
    facet's side of a time instant. -/
def ModelFacetValue (f : Iri) (v y : ModelValue) : Prop :=
  (∃ r s, v = .real r ∧ y = .real s ∧
    ((f = minInclusiveFacet ∧ r ≤ s) ∨ (f = maxInclusiveFacet ∧ s ≤ r) ∨
      (f = minExclusiveFacet ∧ r < s) ∨ (f = maxExclusiveFacet ∧ s < r))) ∨
  (∃ b x, v = .double b ∧ y = .double x ∧ x.Valid doubleFormat ∧ BinaryFacet f b x) ∨
  (∃ b x, v = .float b ∧ y = .float x ∧ x.Valid floatFormat ∧ BinaryFacet f b x) ∨
  (∃ b x, v = .moment b ∧ y = .moment x ∧ x.Valid ∧ MomentFacet f b x)

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

private theorem number_ascii {whole : Bool} {text : List U8} {q : ℚ} (form : NumberForm whole text q) :
    ∀ b ∈ text, b.val < 128 := by
  obtain ⟨sign, w, f, hs, hw, hf, shape, _⟩ := (number_form_shape whole text q).mp form
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

private theorem number_utf8 {whole : Bool} {text : List U8} {q : ℚ} (form : NumberForm whole text q) :
    Rowl.Owl.Utf8Lexical text :=
  ascii_utf8 _ (number_ascii form)

private theorem rational_utf8 {text : List U8} {q : ℚ} (form : RationalForm text q) : Rowl.Owl.Utf8Lexical text := by
  obtain ⟨n, d, p, rfl, i, dd, _, _⟩ := form
  apply ascii_utf8
  intro b m
  simp only [List.mem_append, List.mem_cons] at m
  rcases m with m | m | m
  · exact number_ascii (whole := true) i b m
  · subst m; decide
  · exact ascii_of_digits dd b m

private theorem hex_digit_ascii {byte : U8} {d : Nat} (h : hexDigitValue byte = some d) : byte.val < 128 := by
  unfold hexDigitValue at h
  split_ifs at h with h1 h2 h3 <;> omega

private theorem hex_form_ascii : ∀ {t o : List U8}, HexForm t o → ∀ b ∈ t, b.val < 128
  | [], _, _ => by simp
  | [_], _, h => by simp [HexForm] at h
  | a :: b :: rest, _, h => by
    obtain ⟨x, y, _, o', hx, hy, _, _, hr⟩ := h
    intro c mc
    simp only [List.mem_cons] at mc
    rcases mc with rfl | rfl | mc
    · exact hex_digit_ascii hx
    · exact hex_digit_ascii hy
    · exact hex_form_ascii hr c mc

private theorem sextet_ascii {byte : U8} {d : Nat} (h : base64Value byte = some d) : byte.val < 128 := by
  unfold base64Value at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> omega

private theorem base64_chars_ascii : ∀ {chars o : List U8}, Base64Chars chars o → ∀ c ∈ chars, c.val < 128
  | [], _, _ => by simp
  | a :: b :: c :: d :: rest, _, h => by
    obtain ⟨va, vb, ha, hb, cases⟩ := h
    intro e me
    simp only [List.mem_cons] at me
    rcases cases with ⟨vc, vd, _, _, _, _, hc, hd, _, _, _, _, hr⟩ | ⟨vc, _, _, rfl, hc, rfl, _⟩ |
        ⟨_, rfl, rfl, rfl, _⟩
    · rcases me with rfl | rfl | rfl | rfl | me
      · exact sextet_ascii ha
      · exact sextet_ascii hb
      · exact sextet_ascii hc
      · exact sextet_ascii hd
      · exact base64_chars_ascii hr e me
    · rcases me with rfl | rfl | rfl | rfl | me
      · exact sextet_ascii ha
      · exact sextet_ascii hb
      · exact sextet_ascii hc
      · decide
      · simp at me
    · rcases me with rfl | rfl | rfl | rfl | me
      · exact sextet_ascii ha
      · exact sextet_ascii hb
      · decide
      · decide
      · simp at me
  | [_], _, h => by simp [Base64Chars] at h
  | [_, _], _, h => by simp [Base64Chars] at h
  | [_, _, _], _, h => by simp [Base64Chars] at h

private theorem spaced_from : ∀ {text chars : List U8}, Spaced text chars → ∀ b ∈ text, b ∈ chars ∨ b = 32#u8
  | text, [], h => by simp only [Spaced] at h; subst h; simp
  | text, [c], h => by simp only [Spaced] at h; subst h; simp
  | text, c :: d :: cs, h => by
    obtain ⟨rest, shape, inner⟩ := h
    intro b mb
    rcases shape with rfl | rfl
    · simp only [List.mem_cons] at mb
      rcases mb with rfl | mb
      · exact .inl (by simp)
      · rcases spaced_from inner b mb with m | sp
        · exact .inl (List.mem_cons_of_mem _ m)
        · exact .inr sp
    · simp only [List.mem_cons] at mb
      rcases mb with rfl | rfl | mb
      · exact .inl (by simp)
      · exact .inr rfl
      · rcases spaced_from inner b mb with m | sp
        · exact .inl (List.mem_cons_of_mem _ m)
        · exact .inr sp

private theorem base64_form_ascii {text o : List U8} (h : Base64Form text o) : ∀ b ∈ text, b.val < 128 := by
  obtain ⟨chars, spaced, groups⟩ := h
  intro b mb
  rcases spaced_from spaced b mb with m | sp
  · exact base64_chars_ascii groups b m
  · rw [sp]; decide

theorem modelValue_space (k : datatypes.Kind) (t : List U8) (form : LexicalForm k t) :
    ModelSpace k (modelValue k t) := by
  have subtype : IsSubtype k → ModelSpace k (modelValue k t) := by
    intro sub
    obtain ⟨z, bounded, iform⟩ := (lexical_subtype k sub t).mp form
    have h : ∃ q, NumberForm true t q := ⟨z, iform⟩
    have chosen := number_form_unique (Classical.choose_spec h) iform
    have value : modelValue k t = .real ((Classical.choose h : ℚ) : ℝ) := by
      cases k <;> simp_all [IsSubtype, modelValue]
    rw [value, chosen]
    have space : ModelSpace k (.real ((z : ℚ) : ℝ)) ↔ ∃ r, ModelValue.real ((z : ℚ) : ℝ) = .real r ∧ RealIn k r := by
      cases k <;> simp_all [IsSubtype, ModelSpace]
    rw [space]
    refine ⟨_, rfl, ?_⟩
    have real : RealIn k ((z : ℚ) : ℝ) ↔ ∃ y : ℤ, Bounded (lowerOf k) (upperOf k) y ∧ ((z : ℚ) : ℝ) = y := by
      cases k <;> simp_all [IsSubtype, RealIn]
    exact real.mpr ⟨z, bounded, by simp⟩
  cases k with
  | Integer =>
    have h : ∃ q, NumberForm true t q := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    obtain ⟨z, hz⟩ := integer_of_form (Classical.choose_spec h)
    exact ⟨_, rfl, z, by rw [hz]; simp⟩
  | Decimal =>
    have h : ∃ q, NumberForm false t q := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    obtain ⟨z, n, hz⟩ := decimal_of_form (Classical.choose_spec h)
    exact ⟨_, rfl, z, n, by rw [hz]; push_cast; rfl⟩
  | String => exact ⟨t, form, by simp [modelValue]⟩
  | Plain =>
    obtain ⟨s, l, split, xs, tag⟩ := form
    have h : ∃ p : List U8 × List U8, PlainSplit t p.1 p.2 := ⟨(s, l), split⟩
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
    have h : ∃ b, TruthForm t b := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    exact ⟨_, rfl⟩
  | Real => exact absurd form (by simp [LexicalForm])
  | Rational =>
    have h : ∃ q, RationalForm t q := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace, RealIn]
    exact ⟨_, rfl, _, rfl⟩
  | AnyUri => exact ⟨t, form, rfl⟩
  | HexBinary =>
    have h : ∃ o, HexForm t o := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    exact ⟨_, rfl⟩
  | Base64Binary =>
    have h : ∃ o, Base64Form t o := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    exact ⟨_, rfl⟩
  | NormalizedString => exact ⟨t, form, rfl⟩
  | Token => exact ⟨t, form, rfl⟩
  | Language => exact ⟨t, form, rfl⟩
  | NmToken => exact ⟨t, form, rfl⟩
  | Name => exact ⟨t, form, rfl⟩
  | NcName => exact ⟨t, form, rfl⟩
  | DateTime =>
    have h : ∃ m, MomentForm t m := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    exact ⟨_, Rowl.Moments.momentForm_valid (Classical.choose_spec h), rfl⟩
  | DateTimeStamp =>
    have h : ∃ m, MomentForm t m ∧ m.zone ≠ none := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    exact ⟨_, Rowl.Moments.momentForm_valid (Classical.choose_spec h).1, (Classical.choose_spec h).2, rfl⟩
  | Double =>
    have h : ∃ b, BinaryForm doubleFormat t b := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    exact ⟨_, Rowl.Floats.binaryForm_valid (double := true) (Classical.choose_spec h), rfl⟩
  | Float =>
    have h : ∃ b, BinaryForm floatFormat t b := form
    simp only [modelValue, h, ↓reduceDIte, ModelSpace]
    exact ⟨_, Rowl.Floats.binaryForm_valid (double := false) (Classical.choose_spec h), rfl⟩
  | _ => exact subtype trivial

private theorem ascii_concat {a b : List U8} (ha : ∀ x ∈ a, x.val < 128) (hb : ∀ x ∈ b, x.val < 128) :
    ∀ x ∈ a ++ b, x.val < 128 := by
  intro x m; rcases List.mem_append.mp m with m | m; exacts [ha x m, hb x m]

private theorem ascii_cons {c : U8} {b : List U8} (hc : c.val < 128) (hb : ∀ x ∈ b, x.val < 128) :
    ∀ x ∈ c :: b, x.val < 128 := by
  intro x m; rcases List.mem_cons.mp m with rfl | m; exacts [hc, hb x m]

private theorem digits_ascii {l : List U8} (d : Digits l) : ∀ x ∈ l, x.val < 128 := fun x m => by
  have := (d x m).2; omega

/-- A lexical form of `xsd:dateTime` is ASCII. -/
private theorem moment_form_ascii {t : List U8} {m : Moment} (form : MomentForm t m) : ∀ b ∈ t, b.val < 128 := by
  obtain ⟨yearText, mm, dd, hh, mi, ss, fraction, zoneText, year, month, day, hour, minute, second, zone, rfl,
    ⟨neg, ds, rfl, dds, _, _, _⟩, tmm, _, _, tdd, _, _, thh, tmi, tss, fd, zoneCase, _⟩ := form
  have signAscii : ∀ x ∈ (if neg = true then [45#u8] else []), x.val < 128 := by
    split
    · exact ascii_cons (by simp) (fun x m => by cases m)
    · exact fun x m => by cases m
  have fracAscii : ∀ x ∈ (if fraction = [] then [] else 46#u8 :: fraction), x.val < 128 := by
    split
    · exact fun x m => by cases m
    · exact ascii_cons (by simp) (digits_ascii fd)
  have zoneAscii : ∀ x ∈ zoneText, x.val < 128 := by
    rcases zoneCase with ⟨rfl, _⟩ | ⟨z, ⟨rfl, _⟩ | ⟨west, hh', mm', _, _, rfl, th, tm, _, _⟩, _⟩
    · exact fun x m => by cases m
    · exact ascii_cons (by simp) (fun x m => by cases m)
    · refine ascii_cons (by cases west <;> simp) (ascii_concat (digits_ascii th.2.1)
        (ascii_cons (by simp) (digits_ascii tm.2.1)))
  have hds := digits_ascii dds
  have hmm := digits_ascii tmm.2.1
  have hdd := digits_ascii tdd.2.1
  have hhh := digits_ascii thh.2.1
  have hmi := digits_ascii tmi.2.1
  have hss := digits_ascii tss.2.1
  simp only [List.forall_mem_append, List.forall_mem_cons]
  and_intros
  all_goals first | assumption | simp

/-- The model map: the datatypes here with the specification's spaces, values,
    facet spaces and facet values, and every other datatype unsupported. -/
noncomputable def modelMap : DatatypeMap ModelValue where
  supported dt := ∃ k, kindOf dt = some k
  lexicalSpace dt t := ∃ k, kindOf dt = some k ∧ LexicalForm k t
  facetSpace dt f v := ∃ k, kindOf dt = some k ∧ ModelFacetSpace k f v
  valueSpace dt x := ∃ k, kindOf dt = some k ∧ ModelSpace k x
  lexicalValue dt t := match kindOf dt with
    | some k => modelValue k t
    | none => .other
  facetValue := ModelFacetValue
  excludesLiteral := by
    rintro ⟨k, h⟩
    have := kindOf_some h
    cases k <;> simp_all [typeOf, datatype_eq_iff, Rowl.Owl.literalDatatype, integerType, decimalType, stringType,
      plainType, booleanType, realType, rationalType, nonNegativeIntegerType, nonPositiveIntegerType,
      positiveIntegerType, negativeIntegerType, longType, intType, shortType, byteType, unsignedLongType,
      unsignedIntType, unsignedShortType, unsignedByteType, anyUriType, hexBinaryType, base64BinaryType,
      normalizedStringType, tokenType, languageType, nmtokenType, nameType, ncnameType, dateTimeType,
      dateTimeStampType, doubleType, floatType]
  lexicalUtf8 := by
    rintro dt text ⟨k, kind⟩ ⟨k', kind', form⟩
    rw [kind] at kind'; cases kind'
    have subtype : IsSubtype k → Rowl.Owl.Utf8Lexical text := fun sub => by
      obtain ⟨z, _, iform⟩ := (lexical_subtype k sub text).mp form
      exact number_utf8 (whole := true) iform
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
    | Real => exact absurd form (by simp [LexicalForm])
    | Rational => obtain ⟨q, f⟩ := form; exact rational_utf8 f
    | AnyUri => simpa using text_utf8 (Classical.choose_spec form)
    | HexBinary => obtain ⟨o, f⟩ := form; exact ascii_utf8 _ (hex_form_ascii f)
    | Base64Binary => obtain ⟨o, f⟩ := form; exact ascii_utf8 _ (base64_form_ascii f)
    | NormalizedString => obtain ⟨scalars, f⟩ := Rowl.Strings.form_xml (s := .normalized) form; simpa using text_utf8 f
    | Token => obtain ⟨scalars, f⟩ := Rowl.Strings.form_xml (s := .token) form; simpa using text_utf8 f
    | Language => obtain ⟨scalars, f⟩ := Rowl.Strings.form_xml (s := .language) form; simpa using text_utf8 f
    | NmToken => obtain ⟨scalars, f⟩ := Rowl.Strings.form_xml (s := .nmtoken) form; simpa using text_utf8 f
    | Name => obtain ⟨scalars, f⟩ := Rowl.Strings.form_xml (s := .«name») form; simpa using text_utf8 f
    | NcName => obtain ⟨scalars, f⟩ := Rowl.Strings.form_xml (s := .ncname) form; simpa using text_utf8 f
    | DateTime => obtain ⟨m, f⟩ := form; exact ascii_utf8 _ (moment_form_ascii f)
    | DateTimeStamp => obtain ⟨m, f, _⟩ := form; exact ascii_utf8 _ (moment_form_ascii f)
    | Double => obtain ⟨b, f⟩ := form; exact ascii_utf8 _ (Rowl.Floats.binaryForm_ascii (double := true) f)
    | Float => obtain ⟨b, f⟩ := form; exact ascii_utf8 _ (Rowl.Floats.binaryForm_ascii (double := false) f)
    | _ => exact subtype trivial
  lexicalInSpace := by
    rintro dt text ⟨k, kind⟩ ⟨k', kind', form⟩
    rw [kind] at kind'; cases kind'
    exact ⟨k, kind, by simp only [kind]; exact modelValue_space k text form⟩

theorem model_space (k : datatypes.Kind) (x : ModelValue) : modelMap.valueSpace (typeOf k) x ↔ ModelSpace k x := by
  simp [modelMap, kindOf_typeOf]

theorem model_lexical (k : datatypes.Kind) (t : List U8) :
    modelMap.lexicalSpace (typeOf k) t ↔ LexicalForm k t := by
  simp [modelMap, kindOf_typeOf]

theorem model_value (k : datatypes.Kind) (t : List U8) : modelMap.lexicalValue (typeOf k) t = modelValue k t := by
  simp [modelMap, kindOf_typeOf]

theorem model_facets (k : datatypes.Kind) (f : Iri) (v : ModelValue) :
    modelMap.facetSpace (typeOf k) f v ↔ ModelFacetSpace k f v := by
  simp [modelMap, kindOf_typeOf]

theorem model_supported (k : datatypes.Kind) : modelMap.supported (typeOf k) := ⟨k, kindOf_typeOf k⟩

theorem xsd_kind (dt : Datatype) (h : dt ∈ xsdNumericTypes) : ∃ k, IsXsdNumeric k ∧ dt = typeOf k := by
  simp only [xsdNumericTypes, List.mem_cons, List.mem_map] at h
  rcases h with rfl | rfl | ⟨s, member, rfl⟩
  · exact ⟨.Integer, trivial, rfl⟩
  · exact ⟨.Decimal, trivial, rfl⟩
  · obtain ⟨k, sub, rfl⟩ := listed_subtype s member
    refine ⟨k, ?_, rfl⟩
    cases k <;> simp_all [IsSubtype, IsXsdNumeric]

theorem facets_apart : minInclusiveFacet ≠ maxInclusiveFacet ∧ minInclusiveFacet ≠ minExclusiveFacet ∧
    minInclusiveFacet ≠ maxExclusiveFacet ∧ maxInclusiveFacet ≠ minExclusiveFacet ∧
    maxInclusiveFacet ≠ maxExclusiveFacet ∧ minExclusiveFacet ≠ maxExclusiveFacet := by
  simp [iri_eq_iff, minInclusiveFacet, maxInclusiveFacet, minExclusiveFacet, maxExclusiveFacet]

theorem cast_int (z : ℤ) : (((z : ℚ)) : ℝ) = (z : ℝ) := by simp

theorem model_real_facet (f : Iri) (r : ℝ) (y : ModelValue) :
    ModelFacetValue f (.real r) y ↔ ∃ s, y = .real s ∧
      ((f = minInclusiveFacet ∧ r ≤ s) ∨ (f = maxInclusiveFacet ∧ s ≤ r) ∨
        (f = minExclusiveFacet ∧ r < s) ∨ (f = maxExclusiveFacet ∧ s < r)) := by
  simp only [ModelFacetValue]
  constructor
  · rintro (⟨r', s, h, rfl, facet⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩)
    · cases h; exact ⟨s, rfl, facet⟩
    · cases h
    · cases h
    · cases h
  · rintro ⟨s, rfl, facet⟩
    exact .inl ⟨r, s, rfl, rfl, facet⟩

theorem model_double_facet (f : Iri) (b : Binary) (y : ModelValue) :
    ModelFacetValue f (.double b) y ↔ ∃ x, x.Valid doubleFormat ∧ BinaryFacet f b x ∧ y = .double x := by
  simp only [ModelFacetValue]
  constructor
  · rintro (⟨_, _, h, _⟩ | ⟨b', x, h, rfl, valid, facet⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩)
    · cases h
    · cases h; exact ⟨x, valid, facet, rfl⟩
    · cases h
    · cases h
  · rintro ⟨x, valid, facet, rfl⟩
    exact .inr (.inl ⟨b, x, rfl, rfl, valid, facet⟩)

theorem model_float_facet (f : Iri) (b : Binary) (y : ModelValue) :
    ModelFacetValue f (.float b) y ↔ ∃ x, x.Valid floatFormat ∧ BinaryFacet f b x ∧ y = .float x := by
  simp only [ModelFacetValue]
  constructor
  · rintro (⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨b', x, h, rfl, valid, facet⟩ | ⟨_, _, h, _⟩)
    · cases h
    · cases h
    · cases h; exact ⟨x, valid, facet, rfl⟩
    · cases h
  · rintro ⟨x, valid, facet, rfl⟩
    exact .inr (.inr (.inl ⟨b, x, rfl, rfl, valid, facet⟩))

theorem model_moment_facet (f : Iri) (b : Moment) (y : ModelValue) :
    ModelFacetValue f (.moment b) y ↔ ∃ x, x.Valid ∧ MomentFacet f b x ∧ y = .moment x := by
  simp only [ModelFacetValue]
  constructor
  · rintro (⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨b', x, h, rfl, valid, facet⟩)
    · cases h
    · cases h
    · cases h
    · cases h; exact ⟨x, valid, facet, rfl⟩
  · rintro ⟨x, valid, facet, rfl⟩
    exact .inr (.inr (.inr ⟨b, x, rfl, rfl, valid, facet⟩))

theorem binary_facet_min_inclusive (b x : Binary) : BinaryFacet minInclusiveFacet b x ↔ b.Le x := by
  obtain ⟨a, c, d, _, _, _⟩ := facets_apart
  simp [BinaryFacet, a, c, d]

theorem binary_facet_max_inclusive (b x : Binary) : BinaryFacet maxInclusiveFacet b x ↔ x.Le b := by
  obtain ⟨a, _, _, d, e, _⟩ := facets_apart
  simp [BinaryFacet, a.symm, d, e]

theorem binary_facet_min_exclusive (b x : Binary) : BinaryFacet minExclusiveFacet b x ↔ b.Lt x := by
  obtain ⟨_, c, _, d, _, g⟩ := facets_apart
  simp [BinaryFacet, c.symm, d.symm, g]

theorem binary_facet_max_exclusive (b x : Binary) : BinaryFacet maxExclusiveFacet b x ↔ x.Lt b := by
  obtain ⟨_, _, c, _, e, g⟩ := facets_apart
  simp [BinaryFacet, c.symm, e.symm, g.symm]

theorem moment_facet_min_inclusive (b x : Moment) : MomentFacet minInclusiveFacet b x ↔ b.Le x := by
  obtain ⟨a, c, d, _, _, _⟩ := facets_apart
  simp [MomentFacet, a, c, d]

theorem moment_facet_max_inclusive (b x : Moment) : MomentFacet maxInclusiveFacet b x ↔ x.Le b := by
  obtain ⟨a, _, _, d, e, _⟩ := facets_apart
  simp [MomentFacet, a.symm, d, e]

theorem moment_facet_min_exclusive (b x : Moment) : MomentFacet minExclusiveFacet b x ↔ b.Lt x := by
  obtain ⟨_, c, _, d, _, g⟩ := facets_apart
  simp [MomentFacet, c.symm, d.symm, g]

theorem moment_facet_max_exclusive (b x : Moment) : MomentFacet maxExclusiveFacet b x ↔ x.Lt b := by
  obtain ⟨_, _, c, _, e, g⟩ := facets_apart
  simp [MomentFacet, c.symm, e.symm, g.symm]

/-- The model map is the OWL 2 map on the datatypes here: the specification
    `Normative` is consistent. -/
noncomputable def modelNormative : Normative modelMap where
  number q := .real q
  text := .text
  tagged := .tagged
  truth := .truth
  number_injective := fun a b h => by
    have : ((a : ℚ) : ℝ) = b := by injection h
    exact_mod_cast this
  text_injective := fun _ _ _ _ h => by cases h; rfl
  tagged_injective := fun _ _ _ _ _ _ _ _ h => by cases h; exact ⟨rfl, rfl⟩
  truth_injective := fun _ _ h => by cases h; rfl
  number_text := fun _ _ _ h => by cases h
  number_tagged := fun _ _ _ _ _ h => by cases h
  number_truth := fun _ _ h => by cases h
  text_tagged := fun _ _ _ _ _ _ h => by cases h
  text_truth := fun _ _ _ h => by cases h
  tagged_truth := fun _ _ _ _ _ h => by cases h
  integer_supported := model_supported .Integer
  decimal_supported := model_supported .Decimal
  string_supported := model_supported .String
  plain_supported := model_supported .Plain
  boolean_supported := model_supported .Boolean
  integer_space := fun x => by
    rw [show integerType = typeOf .Integer from rfl, model_space]
    simp only [ModelSpace, RealIn, IsInteger]
    constructor
    · rintro ⟨r, rfl, z, rfl⟩; exact ⟨z, ⟨z, rfl⟩, by rw [cast_int]⟩
    · rintro ⟨q, ⟨z, rfl⟩, rfl⟩; exact ⟨_, rfl, z, cast_int z⟩
  decimal_space := fun x => by
    rw [show decimalType = typeOf .Decimal from rfl, model_space]
    simp only [ModelSpace, RealIn, IsDecimal]
    constructor
    · rintro ⟨r, rfl, z, n, rfl⟩; exact ⟨(z : ℚ) / 10 ^ n, ⟨z, n, rfl⟩, by push_cast; rfl⟩
    · rintro ⟨q, ⟨z, n, rfl⟩, rfl⟩; exact ⟨_, rfl, z, n, by push_cast; rfl⟩
  string_space := fun x => by rw [show stringType = typeOf .String from rfl, model_space]; rfl
  plain_space := fun x => by rw [show plainType = typeOf .Plain from rfl, model_space]; rfl
  boolean_space := fun x => by rw [show booleanType = typeOf .Boolean from rfl, model_space]; rfl
  integer_lexical := fun t => by rw [show integerType = typeOf .Integer from rfl, model_lexical]; rfl
  integer_value := fun t q form => by
    rw [show integerType = typeOf .Integer from rfl, model_value]
    have h : ∃ q, NumberForm true t q := ⟨q, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [number_form_unique (Classical.choose_spec h) form]
  decimal_lexical := fun t => by rw [show decimalType = typeOf .Decimal from rfl, model_lexical]; rfl
  decimal_value := fun t q form => by
    rw [show decimalType = typeOf .Decimal from rfl, model_value]
    have h : ∃ q, NumberForm false t q := ⟨q, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [number_form_unique (Classical.choose_spec h) form]
  string_lexical := fun t => by rw [show stringType = typeOf .String from rfl, model_lexical]; rfl
  string_value := fun t _ => by rw [show stringType = typeOf .String from rfl, model_value]; rfl
  plain_lexical := fun t => by rw [show plainType = typeOf .Plain from rfl, model_lexical]; rfl
  plain_text := fun t s split _ => by
    rw [show plainType = typeOf .Plain from rfl, model_value]
    have h : ∃ p : List U8 × List U8, PlainSplit t p.1 p.2 := ⟨(s, []), split⟩
    obtain ⟨e1, e2⟩ := plain_split_unique (Classical.choose_spec h) split
    simp only [modelValue, h, ↓reduceDIte]
    rw [e1, e2]
    simp
  plain_tagged := fun t s l m split _ isTag lowered => by
    rw [show plainType = typeOf .Plain from rfl, model_value]
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
    simp only [modelValue, h, ↓reduceDIte]
    rw [e1, e2, if_neg nonempty, same]
  boolean_lexical := fun t => by rw [show booleanType = typeOf .Boolean from rfl, model_lexical]; rfl
  boolean_value := fun t b form => by
    rw [show booleanType = typeOf .Boolean from rfl, model_value]
    have h : ∃ b, TruthForm t b := ⟨b, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    have chosen := Classical.choose_spec h
    rcases form with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      rcases chosen with ⟨e, h1 | h1⟩ | ⟨e, h1 | h1⟩ <;> simp_all
  real := .real
  real_injective := fun _ _ h => by cases h; rfl
  real_number := fun _ => rfl
  real_text := fun _ _ _ h => by cases h
  real_tagged := fun _ _ _ _ _ h => by cases h
  real_truth := fun _ _ h => by cases h
  real_supported := model_supported .Real
  rational_supported := model_supported .Rational
  subtype_supported := fun s h => by
    obtain ⟨k, _, rfl⟩ := listed_subtype s h
    exact model_supported k
  real_space := fun x => by
    rw [show realType = typeOf .Real from rfl, model_space]
    simp [ModelSpace, RealIn]
  rational_space := fun x => by
    rw [show rationalType = typeOf .Rational from rfl, model_space]
    simp only [ModelSpace, RealIn]
    constructor
    · rintro ⟨r, rfl, q, rfl⟩; exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩; exact ⟨_, rfl, q, rfl⟩
  subtype_space := fun s h x => by
    obtain ⟨k, sub, rfl⟩ := listed_subtype s h
    rw [model_space]
    have space : ModelSpace k x ↔ ∃ r, x = .real r ∧ ∃ z : ℤ, Bounded (lowerOf k) (upperOf k) z ∧ r = z := by
      cases k <;> simp_all [IsSubtype, ModelSpace, RealIn]
    rw [space]
    constructor
    · rintro ⟨r, rfl, z, bounded, rfl⟩; exact ⟨z, bounded, by rw [cast_int]⟩
    · rintro ⟨z, bounded, rfl⟩; exact ⟨_, rfl, z, bounded, cast_int z⟩
  real_lexical := fun t => by
    rw [show realType = typeOf .Real from rfl, model_lexical]
    simp [LexicalForm]
  rational_lexical := fun t => by rw [show rationalType = typeOf .Rational from rfl, model_lexical]; rfl
  rational_value := fun t q form => by
    rw [show rationalType = typeOf .Rational from rfl, model_value]
    have h : ∃ q, RationalForm t q := ⟨q, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [rational_form_unique (Classical.choose_spec h) form]
  subtype_lexical := fun s h t => by
    obtain ⟨k, sub, rfl⟩ := listed_subtype s h
    rw [model_lexical, lexical_subtype k sub]
  subtype_value := fun s h t z bounded form => by
    obtain ⟨k, sub, rfl⟩ := listed_subtype s h
    rw [model_value]
    have hq : ∃ q, NumberForm true t q := ⟨z, form⟩
    have value : modelValue k t = .real ((Classical.choose hq : ℚ) : ℝ) := by
      cases k <;> simp_all [IsSubtype, modelValue]
    rw [value, number_form_unique (Classical.choose_spec hq) form]
  real_facets := fun f v => by
    rw [show realType = typeOf .Real from rfl, model_facets]
    rfl
  rational_facets := fun f v => by
    rw [show rationalType = typeOf .Rational from rfl, model_facets]
    rfl
  xsd_facets := fun dt h f v => by
    obtain ⟨k, xsd, rfl⟩ := xsd_kind dt h
    rw [model_facets, model_space]
    cases k <;> simp_all [IsXsdNumeric, ModelFacetSpace]
  min_inclusive_value := fun r y => by
    obtain ⟨a, b, c, d, e, f⟩ := facets_apart
    simp only [modelMap]
    rw [model_real_facet]
    constructor
    · rintro ⟨s, rfl, cases⟩
      rcases cases with ⟨_, le⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact ⟨s, le, rfl⟩
      all_goals simp_all
    · rintro ⟨s, le, rfl⟩
      exact ⟨s, rfl, .inl ⟨rfl, le⟩⟩
  max_inclusive_value := fun r y => by
    obtain ⟨a, b, c, d, e, f⟩ := facets_apart
    simp only [modelMap]
    rw [model_real_facet]
    constructor
    · rintro ⟨s, rfl, cases⟩
      rcases cases with ⟨h, _⟩ | ⟨_, le⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · simp_all
      · exact ⟨s, le, rfl⟩
      all_goals simp_all
    · rintro ⟨s, le, rfl⟩
      exact ⟨s, rfl, .inr (.inl ⟨rfl, le⟩)⟩
  min_exclusive_value := fun r y => by
    obtain ⟨a, b, c, d, e, f⟩ := facets_apart
    simp only [modelMap]
    rw [model_real_facet]
    constructor
    · rintro ⟨s, rfl, cases⟩
      rcases cases with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, lt⟩ | ⟨h, _⟩
      · simp_all
      · simp_all
      · exact ⟨s, lt, rfl⟩
      · simp_all
    · rintro ⟨s, lt, rfl⟩
      exact ⟨s, rfl, .inr (.inr (.inl ⟨rfl, lt⟩))⟩
  max_exclusive_value := fun r y => by
    obtain ⟨a, b, c, d, e, f⟩ := facets_apart
    simp only [modelMap]
    rw [model_real_facet]
    constructor
    · rintro ⟨s, rfl, cases⟩
      rcases cases with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, lt⟩
      · simp_all
      · simp_all
      · simp_all
      · exact ⟨s, lt, rfl⟩
    · rintro ⟨s, lt, rfl⟩
      exact ⟨s, rfl, .inr (.inr (.inr ⟨rfl, lt⟩))⟩
  coded := .coded
  coded_injective := fun _ _ _ _ h => by cases h; rfl
  real_coded := fun _ _ _ h => by cases h
  text_coded := fun _ _ _ _ h => by cases h
  tagged_coded := fun _ _ _ _ _ _ h => by cases h
  truth_coded := fun _ _ _ h => by cases h
  uri_supported := model_supported .AnyUri
  hex_supported := model_supported .HexBinary
  base64_supported := model_supported .Base64Binary
  uri_space := fun x => by rw [show anyUriType = typeOf .AnyUri from rfl, model_space]; rfl
  hex_space := fun x => by rw [show hexBinaryType = typeOf .HexBinary from rfl, model_space]; rfl
  base64_space := fun x => by rw [show base64BinaryType = typeOf .Base64Binary from rfl, model_space]; rfl
  uri_lexical := fun t => by rw [show anyUriType = typeOf .AnyUri from rfl, model_lexical]; rfl
  uri_value := fun t _ => by rw [show anyUriType = typeOf .AnyUri from rfl, model_value]; rfl
  hex_lexical := fun t => by rw [show hexBinaryType = typeOf .HexBinary from rfl, model_lexical]; rfl
  hex_value := fun t o form => by
    rw [show hexBinaryType = typeOf .HexBinary from rfl, model_value]
    have h : ∃ o, HexForm t o := ⟨o, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [hex_form_unique (Classical.choose_spec h) form]
  base64_lexical := fun t => by rw [show base64BinaryType = typeOf .Base64Binary from rfl, model_lexical]; rfl
  base64_value := fun t o form => by
    rw [show base64BinaryType = typeOf .Base64Binary from rfl, model_value]
    have h : ∃ o, Base64Form t o := ⟨o, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [base64_form_unique (Classical.choose_spec h) form]
  string_subtype_supported := fun s => by rw [← typeOf_subtypeKind]; exact model_supported _
  string_subtype_space := fun s x => by rw [← typeOf_subtypeKind, model_space]; cases s <;> rfl
  string_subtype_lexical := fun s t => by rw [← typeOf_subtypeKind, model_lexical]; cases s <;> rfl
  string_subtype_value := fun s t _ => by rw [← typeOf_subtypeKind, model_value]; cases s <;> rfl
  moment := .moment
  moment_injective := fun _ _ _ _ h => by cases h; rfl
  real_moment := fun _ _ _ h => by cases h
  text_moment := fun _ _ _ _ h => by cases h
  tagged_moment := fun _ _ _ _ _ _ h => by cases h
  truth_moment := fun _ _ _ h => by cases h
  coded_moment := fun _ _ _ _ h => by cases h
  datetime_supported := model_supported .DateTime
  stamp_supported := model_supported .DateTimeStamp
  datetime_space := fun x => by rw [show dateTimeType = typeOf .DateTime from rfl, model_space]; rfl
  stamp_space := fun x => by rw [show dateTimeStampType = typeOf .DateTimeStamp from rfl, model_space]; rfl
  datetime_lexical := fun t => by rw [show dateTimeType = typeOf .DateTime from rfl, model_lexical]; rfl
  datetime_value := fun t m form => by
    rw [show dateTimeType = typeOf .DateTime from rfl, model_value]
    have h : ∃ m, MomentForm t m := ⟨m, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [Rowl.Moments.momentForm_unique (Classical.choose_spec h) form]
  stamp_lexical := fun t => by rw [show dateTimeStampType = typeOf .DateTimeStamp from rfl, model_lexical]; rfl
  stamp_value := fun t m form zone => by
    rw [show dateTimeStampType = typeOf .DateTimeStamp from rfl, model_value]
    have h : ∃ m, MomentForm t m ∧ m.zone ≠ none := ⟨m, form, zone⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [Rowl.Moments.momentForm_unique (Classical.choose_spec h).1 form]
  double := .double
  float := .float
  double_injective := fun _ _ _ _ h => by cases h; rfl
  float_injective := fun _ _ _ _ h => by cases h; rfl
  double_float := fun _ _ _ _ h => by cases h
  real_double := fun _ _ _ h => by cases h
  real_float := fun _ _ _ h => by cases h
  text_double := fun _ _ _ _ h => by cases h
  text_float := fun _ _ _ _ h => by cases h
  tagged_double := fun _ _ _ _ _ _ h => by cases h
  tagged_float := fun _ _ _ _ _ _ h => by cases h
  truth_double := fun _ _ _ h => by cases h
  truth_float := fun _ _ _ h => by cases h
  coded_double := fun _ _ _ _ h => by cases h
  coded_float := fun _ _ _ _ h => by cases h
  moment_double := fun _ _ _ _ h => by cases h
  moment_float := fun _ _ _ _ h => by cases h
  double_supported := model_supported .Double
  float_supported := model_supported .Float
  double_space := fun x => by rw [show doubleType = typeOf .Double from rfl, model_space]; rfl
  float_space := fun x => by rw [show floatType = typeOf .Float from rfl, model_space]; rfl
  double_lexical := fun t => by rw [show doubleType = typeOf .Double from rfl, model_lexical]; rfl
  double_value := fun t b form => by
    rw [show doubleType = typeOf .Double from rfl, model_value]
    have h : ∃ b, BinaryForm doubleFormat t b := ⟨b, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [Rowl.Floats.binaryForm_unique (double := true) (Classical.choose_spec h) form]
  float_lexical := fun t => by rw [show floatType = typeOf .Float from rfl, model_lexical]; rfl
  float_value := fun t b form => by
    rw [show floatType = typeOf .Float from rfl, model_value]
    have h : ∃ b, BinaryForm floatFormat t b := ⟨b, form⟩
    simp only [modelValue, h, ↓reduceDIte]
    rw [Rowl.Floats.binaryForm_unique (double := false) (Classical.choose_spec h) form]
  double_facets := fun f v => by
    rw [show doubleType = typeOf .Double from rfl, model_facets]
    rfl
  float_facets := fun f v => by
    rw [show floatType = typeOf .Float from rfl, model_facets]
    rfl
  min_inclusive_double := fun b y _ => by
    simp only [modelMap]
    rw [model_double_facet]
    simp only [binary_facet_min_inclusive]
  max_inclusive_double := fun b y _ => by
    simp only [modelMap]
    rw [model_double_facet]
    simp only [binary_facet_max_inclusive]
  min_exclusive_double := fun b y _ => by
    simp only [modelMap]
    rw [model_double_facet]
    simp only [binary_facet_min_exclusive]
  max_exclusive_double := fun b y _ => by
    simp only [modelMap]
    rw [model_double_facet]
    simp only [binary_facet_max_exclusive]
  min_inclusive_float := fun b y _ => by
    simp only [modelMap]
    rw [model_float_facet]
    simp only [binary_facet_min_inclusive]
  max_inclusive_float := fun b y _ => by
    simp only [modelMap]
    rw [model_float_facet]
    simp only [binary_facet_max_inclusive]
  min_exclusive_float := fun b y _ => by
    simp only [modelMap]
    rw [model_float_facet]
    simp only [binary_facet_min_exclusive]
  max_exclusive_float := fun b y _ => by
    simp only [modelMap]
    rw [model_float_facet]
    simp only [binary_facet_max_exclusive]
  datetime_facets := fun f v => by
    rw [show dateTimeType = typeOf .DateTime from rfl, model_facets]
    rfl
  stamp_facets := fun f v => by
    rw [show dateTimeStampType = typeOf .DateTimeStamp from rfl, model_facets]
    rfl
  min_inclusive_moment := fun b y _ => by
    simp only [modelMap]
    rw [model_moment_facet]
    simp only [moment_facet_min_inclusive]
  max_inclusive_moment := fun b y _ => by
    simp only [modelMap]
    rw [model_moment_facet]
    simp only [moment_facet_max_inclusive]
  min_exclusive_moment := fun b y _ => by
    simp only [modelMap]
    rw [model_moment_facet]
    simp only [moment_facet_min_exclusive]
  max_exclusive_moment := fun b y _ => by
    simp only [modelMap]
    rw [model_moment_facet]
    simp only [moment_facet_max_exclusive]

end Rowl.Datatypes
