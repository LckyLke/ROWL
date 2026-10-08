import Rowl.Datatypes
import Rowl.Regions
import Rowl.AlcOntology
import Rowl.Concepts

/-!
The actual kernel functions of `data_ontology` that build the encoding: its own
names, the context of a closure with the cuts of its bounds, and the encodings
of data ranges, class expressions and axioms. This part proves what the
functions return; the meaning of the encoding is proved in `Rowl.DataMeaning`
and the modules after it.
-/
namespace Rowl.DataEncoding
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl
open Rowl.DatatypeMap (Normative)
open Rowl.Datatypes (Canonical valueOf typeOf kindOf InKind)
open Rowl.AlcOntology (RoleOf)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

theorem new_val {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

/-! ### Byte patterns -/

private theorem equal_total (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    data_ontology.equal_from key pattern index =
      .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [data_ontology.equal_from]
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
    data_ontology.same_pattern key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [data_ontology.same_pattern]
  by_cases h : key.val.length = pattern.val.length
  · simpa [h] using equal_total key pattern h 0#usize
  · have unequal : key.val ≠ pattern.val := fun same => h (congrArg List.length same)
    simp [h, unequal]

private theorem same_from_total (left right : alloc.vec.Vec U8)
    (lengths : left.val.length = right.val.length) (index : Usize) :
    data_ontology.same_from left right index =
      .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [data_ontology.same_from]
  by_cases h : index.val < left.val.length
  · have hr : index.val < right.val.length := by omega
    have hl : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hrIndex : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : left.val[index.val] = right.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := same_from_total left right lengths next
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
    data_ontology.same_bytes left right = .ok (decide (left.val = right.val)) := by
  rw [data_ontology.same_bytes]
  by_cases lengths : left.val.length = right.val.length
  · have lengths' : alloc.vec.Vec.len left = alloc.vec.Vec.len right :=
      UScalar.eq_of_val_eq (by simpa using lengths)
    simp only [lengths', ↓reduceIte]
    simpa using same_from_total left right lengths 0#usize
  · have unequal : ¬ left.val = right.val := fun same => lengths (congrArg List.length same)
    have lengths' : ¬ alloc.vec.Vec.len left = alloc.vec.Vec.len right := fun same => lengths (by
      simpa using congrArg UScalar.val same)
    simp [lengths', unequal]

theorem pattern_from_correct (pattern : Slice U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length + (pattern.val.length - index.val) ≤ Usize.max) :
    ∃ v, data_ontology.pattern_from pattern index out = .ok v ∧ v.val = out.val ++ pattern.val.drop index.val := by
  rw [data_ontology.pattern_from]
  by_cases inside : index.val < pattern.val.length
  · have lookup : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem inside]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out pattern.val[index.val] short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := pattern_from_correct pattern next pushed (by rw [contents, nextIndex]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside, lookup, push, advance, run]
    · rw [value, contents, nextIndex, List.drop_eq_getElem_cons inside]
      simp
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show pattern.val.length ≤ index.val by omega)]
termination_by pattern.val.length - index.val
decreasing_by omega

theorem copy_after_correct (source : alloc.vec.Vec U8) (index : Usize) (out : alloc.vec.Vec U8)
    (room : out.val.length + (source.val.length - index.val) ≤ Usize.max) :
    ∃ v, data_ontology.copy_after source index out = .ok v ∧ v.val = out.val ++ source.val.drop index.val := by
  rw [data_ontology.copy_after]
  by_cases inside : index.val < source.val.length
  · have lookup : source.index_usize index = .ok source.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out source.val[index.val] short)
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value⟩ := copy_after_correct source next pushed (by rw [contents, nextIndex]; simp; omega)
    refine ⟨v, ?_, ?_⟩
    · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, push, advance, run]
    · rw [value, contents, nextIndex, List.drop_eq_getElem_cons inside]
      simp
  · refine ⟨out, by simp [UScalar.lt_equiv, inside], ?_⟩
    simp [List.drop_eq_nil_iff.mpr (show source.val.length ≤ index.val by omega)]
termination_by source.val.length - index.val
decreasing_by omega

/-! ### The encoding's own names -/

/-- Names starting with the byte 0, which the encoding keeps for itself. -/
def Reserved (spelling : List U8) : Prop := spelling.head? = some 0#u8

theorem reserved_correct (spelling : alloc.vec.Vec U8) :
    data_ontology.reserved spelling = .ok (decide (Reserved spelling.val)) := by
  rw [data_ontology.reserved]
  cases h : spelling.val with
  | nil =>
    have empty : ¬ (0#usize) < alloc.vec.Vec.len spelling := by simp [UScalar.lt_equiv, h]
    simp [empty, Reserved]
  | cons head tail =>
    have positive : (0#usize) < alloc.vec.Vec.len spelling := by simp [UScalar.lt_equiv, h]
    have lookup : spelling.index_usize 0#usize = .ok head := by simp [alloc.vec.Vec.index_usize, h]
    simp [positive, alloc.vec.Vec.index_slice_index, lookup, Reserved]

/-- The eight bytes of a number, least significant first. -/
def eightBytes (value : Nat) : Nat → List U8
  | 0 => []
  | n + 1 => ⟨BitVec.ofNat 8 (value % 256)⟩ :: eightBytes (value / 256) n

theorem bytes_correct (value count : Usize) (out : alloc.vec.Vec U8) (small : count.val ≤ 8)
    (room : out.val.length + (8 - count.val) ≤ Usize.max) :
    ∃ v, data_ontology.bytes value count out = .ok v ∧ v.val = out.val ++ eightBytes value.val (8 - count.val) := by
  rw [data_ontology.bytes]
  by_cases more : count.val < 8
  · have more' : count < 8#usize := by simpa [UScalar.lt_equiv] using more
    obtain ⟨low, lowRun, lowValue⟩ := WP.spec_imp_exists (Usize.rem_spec value (y := 256#usize) (by simp))
    obtain ⟨byte, byteRun, byteValue⟩ : ∃ byte : U8, (lift (UScalar.cast .U8 low) : Result U8) = .ok byte ∧
        byte.val = value.val % 256 := by
      refine ⟨UScalar.cast .U8 low, rfl, ?_⟩
      rw [UScalar.cast_val_eq, lowValue]
      simp
    have short : out.val.length < Usize.max := by omega
    obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out byte short)
    obtain ⟨high, highRun, highValue⟩ := WP.spec_imp_exists (Usize.div_spec value (y := 256#usize) (by simp))
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := count) (y := 1#usize) (by scalar_tac))
    have nextIs : next.val = count.val + 1 := by simpa using nextValue
    obtain ⟨v, run, value'⟩ := bytes_correct high next pushed (by omega) (by rw [contents]; simp; omega)
    refine ⟨v, by simp [more', lowRun, byteRun, push, highRun, advance, run], ?_⟩
    rw [value', contents, nextIs, highValue]
    have steps : 8 - count.val = (8 - (count.val + 1)) + 1 := by omega
    rw [steps, eightBytes]
    have same : (⟨BitVec.ofNat 8 (value.val % 256)⟩ : U8) = byte := by
      apply UScalar.eq_of_val_eq
      show (BitVec.ofNat 8 (value.val % 256)).toNat = byte.val
      rw [BitVec.toNat_ofNat, byteValue]; omega
    simp [same]
  · have eight : count.val = 8 := by omega
    have notMore : ¬ count < 8#usize := by simp [UScalar.lt_equiv]; omega
    refine ⟨out, by simp [notMore], ?_⟩
    simp [eight, eightBytes]
termination_by 8 - count.val
decreasing_by omega

theorem eightBytes_length (value n : Nat) : (eightBytes value n).length = n := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih => simp [eightBytes, ih]

/-- Two numbers below `256 ^ n` with the same `n` bytes are equal. -/
theorem eightBytes_injective (a b n : Nat) (ha : a < 256 ^ n) (hb : b < 256 ^ n)
    (same : eightBytes a n = eightBytes b n) : a = b := by
  induction n generalizing a b with
  | zero => simp at ha hb; omega
  | succ n ih =>
    simp only [eightBytes, List.cons.injEq] at same
    have low : a % 256 = b % 256 := by
      have := congrArg UScalar.val same.1
      simp only [UScalar.val, BitVec.toNat_ofNat, UScalarTy.U8_numBits_eq] at this
      omega
    have high := ih (a / 256) (b / 256) (by rw [pow_succ] at ha; omega) (by rw [pow_succ] at hb; omega) same.2
    omega

theorem tagged_name_correct (tag : U8) (rest : alloc.vec.Vec U8) (room : rest.val.length + 2 ≤ Usize.max) :
    ∃ v, data_ontology.tagged_name tag rest = .ok v ∧ v.val = 0#u8 :: tag :: rest.val := by
  rw [data_ontology.tagged_name]
  obtain ⟨first, firstRun, firstValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 0#u8 (by simp [new_val]; scalar_tac))
  obtain ⟨second, secondRun, secondValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec first tag (by rw [firstValue]; simp [new_val]; scalar_tac))
  obtain ⟨v, run, value⟩ := copy_after_correct rest 0#usize second
    (by rw [secondValue, firstValue]; simp [new_val]; omega)
  refine ⟨v, by simp [firstRun, secondRun, run], ?_⟩
  rw [value, secondValue, firstValue]
  simp [new_val]

/-- The name of the class `D` of the data nodes. -/
def dataName : List U8 := [0#u8, 68#u8]
/-- The byte of a kind. -/
def kindByte : datatypes.Kind → U8
  | .Integer => 0#u8
  | .Decimal => 1#u8
  | .String => 2#u8
  | .Plain => 3#u8
  | .Boolean => 4#u8
  | .Real => 5#u8
  | .Rational => 6#u8
  | .NonNegativeInteger => 7#u8
  | .NonPositiveInteger => 8#u8
  | .PositiveInteger => 9#u8
  | .NegativeInteger => 10#u8
  | .Long => 11#u8
  | .Int => 12#u8
  | .Short => 13#u8
  | .Byte => 14#u8
  | .UnsignedLong => 15#u8
  | .UnsignedInt => 16#u8
  | .UnsignedShort => 17#u8
  | .UnsignedByte => 18#u8
  | .AnyUri => 19#u8
  | .HexBinary => 20#u8
  | .Base64Binary => 21#u8
  | .NormalizedString => 22#u8
  | .Token => 23#u8
  | .Language => 24#u8
  | .NmToken => 25#u8
  | .Name => 26#u8
  | .NcName => 27#u8
  | .DateTime => 28#u8
  | .DateTimeStamp => 29#u8
  | .Double => 30#u8
  | .Float => 31#u8
/-- The name of the class of a kind. -/
def kindName (k : datatypes.Kind) : List U8 := [0#u8, 65#u8, kindByte k]
/-- The name of a bit class. -/
def bitName (position : Nat) : List U8 := 0#u8 :: 66#u8 :: eightBytes position 8
/-- The name of the individual of a literal value. -/
def valueName (index : Nat) : List U8 := 0#u8 :: 76#u8 :: eightBytes index 8
/-- The name of the further individual. -/
def objectName : List U8 := [0#u8, 79#u8]
/-- The name of the object property of a data property. -/
def dataRoleName (p : DataProperty) : List U8 := 0#u8 :: 80#u8 :: p.iri.spelling.val
/-- The name of the class of the cut at an index. -/
def cutName (index : Nat) : List U8 := 0#u8 :: 71#u8 :: eightBytes index 8
/-- The name of the role above every data property's role. -/
def superName : List U8 := [0#u8, 85#u8]

def edgeName (double : Bool) (index : Nat) : List U8 :=
  0#u8 :: 70#u8 :: (if double then 1#u8 else 0#u8) :: eightBytes index 8

theorem class_named_correct (spelling : alloc.vec.Vec U8) :
    data_ontology.class_named spelling = .ok (.Class ⟨⟨spelling⟩⟩) := rfl

theorem data_class_correct :
    ∃ c : Class, data_ontology.data_class = .ok (.Class c) ∧ c.iri.spelling.val = dataName := by
  obtain ⟨v, run, value⟩ := tagged_name_correct 68#u8 (alloc.vec.Vec.new U8) (by simp [new_val]; scalar_tac)
  refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.data_class, run, class_named_correct], ?_⟩
  simp [value, new_val, dataName]

/-- The class `D` of the data nodes. -/
noncomputable def dataClass : Class := Classical.choose data_class_correct

theorem data_class_eq : data_ontology.data_class = .ok (.Class dataClass) :=
  (Classical.choose_spec data_class_correct).1

theorem dataClass_name : dataClass.iri.spelling.val = dataName :=
  (Classical.choose_spec data_class_correct).2

theorem object_class_eq : data_ontology.object_class = .ok (.ObjectComplementOf (.Class dataClass)) := by
  simp [data_ontology.object_class, data_class_eq]

theorem kind_index_eq (k : datatypes.Kind) : data_ontology.kind_index k = .ok (kindByte k) := by
  cases k <;> rfl

theorem kind_class_correct (k : datatypes.Kind) :
    ∃ c : Class, data_ontology.kind_class k = .ok (.Class c) ∧ c.iri.spelling.val = kindName k := by
  obtain ⟨rest, restRun, restValue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) (kindByte k) (by simp [new_val]; scalar_tac))
  obtain ⟨v, run, value⟩ := tagged_name_correct 65#u8 rest (by rw [restValue]; simp [new_val]; scalar_tac)
  refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.kind_class, kind_index_eq, restRun, run, class_named_correct], ?_⟩
  simp [value, restValue, new_val, kindName]

/-- The class of a kind. -/
noncomputable def kindClass (k : datatypes.Kind) : Class := Classical.choose (kind_class_correct k)

theorem kind_class_eq (k : datatypes.Kind) : data_ontology.kind_class k = .ok (.Class (kindClass k)) :=
  (Classical.choose_spec (kind_class_correct k)).1

theorem kindClass_name (k : datatypes.Kind) : (kindClass k).iri.spelling.val = kindName k :=
  (Classical.choose_spec (kind_class_correct k)).2

theorem bit_class_correct (position : Usize) :
    ∃ c : Class, data_ontology.bit_class position = .ok (.Class c) ∧ c.iri.spelling.val = bitName position.val := by
  obtain ⟨b, bytesRun, bytesValue⟩ := bytes_correct position 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp [new_val]; scalar_tac)
  obtain ⟨v, run, value⟩ := tagged_name_correct 66#u8 b
    (by rw [bytesValue]; simp [new_val, eightBytes_length]; scalar_tac)
  refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.bit_class, bytesRun, run, class_named_correct], ?_⟩
  simp [value, bytesValue, new_val, bitName]

theorem cut_class_correct (index : Usize) :
    ∃ c : Class, data_ontology.cut_class index = .ok (.Class c) ∧ c.iri.spelling.val = cutName index.val := by
  obtain ⟨b, bytesRun, bytesValue⟩ := bytes_correct index 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp [new_val]; scalar_tac)
  obtain ⟨v, run, value⟩ := tagged_name_correct 71#u8 b
    (by rw [bytesValue]; simp [new_val, eightBytes_length]; scalar_tac)
  refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.cut_class, bytesRun, run, class_named_correct], ?_⟩
  simp [value, bytesValue, new_val, cutName]

/-- The class of the cut at an index. -/
noncomputable def cutClass (index : Usize) : Class := Classical.choose (cut_class_correct index)

theorem cut_class_eq (index : Usize) : data_ontology.cut_class index = .ok (.Class (cutClass index)) :=
  (Classical.choose_spec (cut_class_correct index)).1

theorem cutClass_name (index : Usize) : (cutClass index).iri.spelling.val = cutName index.val :=
  (Classical.choose_spec (cut_class_correct index)).2

theorem edge_class_correct (double : Bool) (index : Usize) :
    ∃ c : Class, data_ontology.edge_class double index = .ok (.Class c) ∧
      c.iri.spelling.val = edgeName double index.val := by
  cases double
  · obtain ⟨rest, restRun, restValue⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 0#u8 (by simp [new_val]; scalar_tac))
    obtain ⟨b, bytesRun, bytesValue⟩ := bytes_correct index 0#usize rest (by simp)
      (by rw [restValue]; simp [new_val]; scalar_tac)
    obtain ⟨v, run, value⟩ := tagged_name_correct 70#u8 b
      (by rw [bytesValue, restValue]; simp [new_val, eightBytes_length]; scalar_tac)
    refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.edge_class, restRun, bytesRun, run, class_named_correct], ?_⟩
    simp [value, bytesValue, restValue, new_val, edgeName]
  · obtain ⟨rest, restRun, restValue⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 1#u8 (by simp [new_val]; scalar_tac))
    obtain ⟨b, bytesRun, bytesValue⟩ := bytes_correct index 0#usize rest (by simp)
      (by rw [restValue]; simp [new_val]; scalar_tac)
    obtain ⟨v, run, value⟩ := tagged_name_correct 70#u8 b
      (by rw [bytesValue, restValue]; simp [new_val, eightBytes_length]; scalar_tac)
    refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.edge_class, restRun, bytesRun, run, class_named_correct], ?_⟩
    simp [value, bytesValue, restValue, new_val, edgeName]

/-- The class of the values of a floating-point format at or above the edge at
    an index. -/
noncomputable def edgeClass (double : Bool) (index : Usize) : Class :=
  Classical.choose (edge_class_correct double index)

theorem edge_class_eq (double : Bool) (index : Usize) :
    data_ontology.edge_class double index = .ok (.Class (edgeClass double index)) :=
  (Classical.choose_spec (edge_class_correct double index)).1

theorem edgeClass_name (double : Bool) (index : Usize) :
    (edgeClass double index).iri.spelling.val = edgeName double index.val :=
  (Classical.choose_spec (edge_class_correct double index)).2

/-- The edges of a floating-point format in a context: of `xsd:double`
    (`double`) or of `xsd:float`. -/
def edgesOf (context : data_ontology.Context) (double : Bool) : alloc.vec.Vec U128 :=
  if double then context.double_edges else context.float_edges

/-- The kind of a floating-point format: `xsd:double` (`double`) or `xsd:float`. -/
def floatKind : Bool → datatypes.Kind
  | true => .Double
  | false => .Float

/-- A kernel value of a floating-point format. -/
def floatLit : Bool → datatypes.Binary → datatypes.DataValue
  | true, b => .Double b
  | false, b => .Float b

theorem data_super_correct :
    ∃ r : ObjectProperty, data_ontology.data_super = .ok (.Property r) ∧ r.iri.spelling.val = superName := by
  obtain ⟨v, run, value⟩ := tagged_name_correct 85#u8 (alloc.vec.Vec.new U8) (by simp [new_val]; scalar_tac)
  refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.data_super, run], ?_⟩
  simp [value, new_val, superName]

/-- The role above every data property's role. -/
noncomputable def dataSuper : ObjectProperty := Classical.choose data_super_correct

theorem data_super_eq : data_ontology.data_super = .ok (.Property dataSuper) :=
  (Classical.choose_spec data_super_correct).1

theorem dataSuper_name : dataSuper.iri.spelling.val = superName :=
  (Classical.choose_spec data_super_correct).2

theorem value_individual_correct (index : Usize) :
    ∃ a : NamedIndividual, data_ontology.value_individual index = .ok (.Named a) ∧
      a.iri.spelling.val = valueName index.val := by
  obtain ⟨b, bytesRun, bytesValue⟩ := bytes_correct index 0#usize (alloc.vec.Vec.new U8) (by simp)
    (by simp [new_val]; scalar_tac)
  obtain ⟨v, run, value⟩ := tagged_name_correct 76#u8 b
    (by rw [bytesValue]; simp [new_val, eightBytes_length]; scalar_tac)
  refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.value_individual, bytesRun, run], ?_⟩
  simp [value, bytesValue, new_val, valueName]

theorem object_individual_correct :
    ∃ a : NamedIndividual, data_ontology.object_individual = .ok (.Named a) ∧ a.iri.spelling.val = objectName := by
  obtain ⟨v, run, value⟩ := tagged_name_correct 79#u8 (alloc.vec.Vec.new U8) (by simp [new_val]; scalar_tac)
  refine ⟨⟨⟨v⟩⟩, by simp [data_ontology.object_individual, run], ?_⟩
  simp [value, new_val, objectName]

theorem thing_eq : data_ontology.thing = .ok (.Class thing) := by
  obtain ⟨v, run, value⟩ := pattern_from_correct
    (Array.to_slice (Array.make 35#usize [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8,
      119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8,
      55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 84#u8, 104#u8, 105#u8, 110#u8, 103#u8]))
    0#usize (alloc.vec.Vec.new U8) (by simp [new_val, Array.to_slice, Array.make]; scalar_tac)
  have same : (⟨⟨v⟩⟩ : Class) = thing := by
    rw [Rowl.Tableau.class_eq_iff]
    simp [value, new_val, Array.to_slice, Array.make, thing]
  rw [data_ontology.thing]
  simp only [lift, bind_ok, run, class_named_correct, same]

/-! ### Built-in names -/

theorem dataProperty_eq_iff (a b : DataProperty) : a = b ↔ a.iri.spelling.val = b.iri.spelling.val := by
  cases a with | mk ai => cases b with | mk bi => cases ai; cases bi; simp [alloc.vec.Vec.eq_iff]

theorem individual_eq_iff (a b : NamedIndividual) : a = b ↔ a.iri.spelling.val = b.iri.spelling.val := by
  cases a with | mk ai => cases b with | mk bi => cases ai; cases bi; simp [alloc.vec.Vec.eq_iff]

theorem is_top_object_correct (p : ObjectProperty) :
    data_ontology.is_top_object p = .ok (decide (p = topObject)) := by
  rw [data_ontology.is_top_object, Rowl.Tableau.property_eq_iff]
  simp [same_pattern_total, Array.to_slice, Array.make, lift, topObject]

theorem is_top_data_correct (p : DataProperty) :
    data_ontology.is_top_data p = .ok (decide (p = topData)) := by
  rw [data_ontology.is_top_data, dataProperty_eq_iff]
  simp [same_pattern_total, Array.to_slice, Array.make, lift, topData]

theorem is_bottom_data_correct (p : DataProperty) :
    data_ontology.is_bottom_data p = .ok (decide (p = bottomData)) := by
  rw [data_ontology.is_bottom_data, dataProperty_eq_iff]
  simp [same_pattern_total, Array.to_slice, Array.make, lift, bottomData]

theorem is_thing_correct (c : Class) : data_ontology.is_thing c = .ok (decide (c = thing)) := by
  rw [data_ontology.is_thing, Rowl.Tableau.class_eq_iff]
  simp [same_pattern_total, Array.to_slice, Array.make, lift, thing]

theorem is_literal_correct (dt : Datatype) :
    data_ontology.is_literal dt = .ok (decide (dt = literalDatatype)) := by
  rw [data_ontology.is_literal, Rowl.Datatypes.datatype_eq_iff]
  simp [same_pattern_total, Array.to_slice, Array.make, lift, literalDatatype]

theorem named_eq (r : ObjectPropertyExpression) : data_ontology.named r = .ok (RoleOf r) := by
  cases r <;> rfl

theorem universal_correct (r : ObjectPropertyExpression) :
    data_ontology.universal r = .ok (decide (RoleOf r = topObject)) := by
  simp [data_ontology.universal, named_eq, is_top_object_correct]

/-! ### The context -/

/-- Whether a kind is in use; `xsd:string` is when one of its subtypes is. -/
def Used (kinds : data_ontology.Kinds) : datatypes.Kind → Bool
  | .Integer => kinds.integer
  | .Decimal => kinds.decimal
  | .String => kinds.string || kinds.normalized || kinds.token || kinds.language || kinds.nmtoken || kinds.name ||
      kinds.ncname
  | .Plain => kinds.plain
  | .Boolean => kinds.boolean
  | .Real => kinds.real
  | .Rational => kinds.rational
  | .AnyUri => kinds.uri
  | .HexBinary => kinds.hex
  | .Base64Binary => kinds.base64
  | .NormalizedString => kinds.normalized
  | .Token => kinds.token
  | .Language => kinds.language
  | .NmToken => kinds.nmtoken
  | .Name => kinds.name
  | .NcName => kinds.ncname
  | .DateTime => kinds.datetime || kinds.stamp
  | .DateTimeStamp => kinds.stamp
  | .Double => kinds.double
  | .Float => kinds.float
  | _ => false

theorem used_eq (kinds : data_ontology.Kinds) (k : datatypes.Kind) :
    data_ontology.used kinds k = .ok (Used kinds k) := by
  cases k <;> rfl

/-- The datatypes that the encoding gives a class: the five of the first
    stage, the reals and the rationals, `xsd:anyURI`, `xsd:hexBinary` and
    `xsd:base64Binary`, the six subtypes of `xsd:string`, `xsd:dateTime`,
    `xsd:dateTimeStamp`, `xsd:double` and `xsd:float`; the subtypes of
    `xsd:integer` are integers between cuts. -/
def Classic : datatypes.Kind → Prop
  | .Integer | .Decimal | .String | .Plain | .Boolean | .Real | .Rational | .AnyUri | .HexBinary | .Base64Binary
  | .NormalizedString | .Token | .Language | .NmToken | .Name | .NcName | .DateTime | .DateTimeStamp | .Double
  | .Float => True
  | _ => False

theorem used_classic {kinds : data_ontology.Kinds} {k : datatypes.Kind} (used : Used kinds k = true) : Classic k := by
  cases k <;> simp_all [Used, Classic]

/-- Canonical values, each once. -/
def GoodValues (values : List datatypes.DataValue) : Prop := (∀ v ∈ values, Canonical v) ∧ values.Nodup

/-- Cuts of canonical numbers, each once. -/
def GoodCuts (cuts : List regions.Cut) : Prop :=
  (∀ c ∈ cuts, Rowl.Datatypes.CanonicalNumeric c.value) ∧ cuts.Nodup

/-- A context whose literal values are canonical, each once, whose object
    properties are neither the encoding's nor the universal role, whose data
    properties are neither of the two built-in ones, and whose cuts are of
    canonical numbers, each once. -/
def Good (context : data_ontology.Context) : Prop :=
  GoodValues context.values.val ∧ (∀ r ∈ context.roles.val, ¬ Reserved r.iri.spelling.val ∧ r ≠ topObject) ∧
    (∀ p ∈ context.data.val, p ≠ topData ∧ p ≠ bottomData) ∧ GoodCuts context.cuts.val ∧
    (context.kinds.ordered = true → context.kinds.real = true)

theorem value_index_correct (values : alloc.vec.Vec datatypes.DataValue) (value : datatypes.DataValue)
    (index : Usize) :
    ∃ r, data_ontology.value_index values value index = .ok r ∧
      (r = none → value ∉ values.val.drop index.val) ∧
      ∀ i, r = some i → ∃ h : i.val < values.val.length, values.val[i.val] = value := by
  rw [data_ontology.value_index]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    by_cases same : values.val[index.val] = value
    · refine ⟨some index, ?_, by simp, fun i hi => ?_⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
          Rowl.Datatypes.same_value_correct, same]
      · cases hi; exact ⟨inside, same⟩
    · obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨r, run, absent, present⟩ := value_index_correct values value next
      refine ⟨r, ?_, fun hn => ?_, present⟩
      · simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup,
          Rowl.Datatypes.same_value_correct, same, advance, run]
      · rw [List.drop_eq_getElem_cons inside, List.mem_cons, not_or]
        exact ⟨fun h => same h.symm, by rw [← nextIndex]; exact absent hn⟩
  · refine ⟨none, by simp [UScalar.lt_equiv, inside], fun _ => ?_, by simp⟩
    simp [List.drop_eq_nil_iff.mpr (show values.val.length ≤ index.val by omega)]
termination_by values.val.length - index.val
decreasing_by omega

theorem add_value_correct (values : alloc.vec.Vec datatypes.DataValue) (value : datatypes.DataValue) :
    ∃ v, data_ontology.add_value values value = .ok v ∧
      (GoodValues values.val → Canonical value → GoodValues v.val) := by
  obtain ⟨r, run, absent, _⟩ := value_index_correct values value 0#usize
  rw [data_ontology.add_value, run]
  cases r with
  | some i => exact ⟨values, by simp, fun good _ => good⟩
  | none =>
    have notIn : value ∉ values.val := by simpa using absent rfl
    by_cases room : values.val.length < Usize.max
    · have room' : alloc.vec.Vec.len values < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec values value room)
      refine ⟨pushed, by simp [room', push], fun good canonical => ?_⟩
      rw [contents]
      refine ⟨fun v member => ?_, ?_⟩
      · rcases List.mem_append.mp member with early | late
        · exact good.1 v early
        · simp at late; rw [late]; exact canonical
      · refine List.nodup_append.mpr ⟨good.2, by simp, ?_⟩
        intro a ha b hb same
        simp only [List.mem_singleton] at hb
        exact notIn (hb ▸ same ▸ ha)
    · have full : ¬ alloc.vec.Vec.len values < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
      exact ⟨values, by simp [full], fun good _ => good⟩

theorem has_role_correct (roles : alloc.vec.Vec ObjectProperty) (p : ObjectProperty) (index : Usize) :
    data_ontology.has_role roles p index = .ok (decide (p ∈ roles.val.drop index.val)) := by
  rw [data_ontology.has_role]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split : roles.val.drop index.val = roles.val[index.val] :: roles.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons inside
    by_cases same : roles.val[index.val] = p
    · have spelled : roles.val[index.val].iri.spelling.val = p.iri.spelling.val := by rw [same]
      have member : p ∈ roles.val.drop index.val := by rw [split, same]; exact List.mem_cons_self
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, same_bytes_correct, spelled, member]
    · have spelled : ¬ roles.val[index.val].iri.spelling.val = p.iri.spelling.val :=
        fun h => same ((Rowl.Tableau.property_eq_iff _ _).mpr h)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := has_role_correct roles p next
      rw [nextIndex] at rest
      have member : p ∈ roles.val.drop index.val ↔ p ∈ roles.val.drop (index.val + 1) := by
        rw [split, List.mem_cons]; exact ⟨fun h => h.resolve_left (fun e => same e.symm), .inr⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, same_bytes_correct, spelled,
        advance, rest, member]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega

theorem has_data_correct (data : alloc.vec.Vec DataProperty) (p : DataProperty) (index : Usize) :
    data_ontology.has_data data p index = .ok (decide (p ∈ data.val.drop index.val)) := by
  rw [data_ontology.has_data]
  by_cases inside : index.val < data.val.length
  · have lookup : data.index_usize index = .ok data.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split : data.val.drop index.val = data.val[index.val] :: data.val.drop (index.val + 1) :=
      List.drop_eq_getElem_cons inside
    by_cases same : data.val[index.val] = p
    · have spelled : data.val[index.val].iri.spelling.val = p.iri.spelling.val := by rw [same]
      have member : p ∈ data.val.drop index.val := by rw [split, same]; exact List.mem_cons_self
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, same_bytes_correct, spelled, member]
    · have spelled : ¬ data.val[index.val].iri.spelling.val = p.iri.spelling.val :=
        fun h => same ((dataProperty_eq_iff _ _).mpr h)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      have rest := has_data_correct data p next
      rw [nextIndex] at rest
      have member : p ∈ data.val.drop index.val ↔ p ∈ data.val.drop (index.val + 1) := by
        rw [split, List.mem_cons]; exact ⟨fun h => h.resolve_left (fun e => same e.symm), .inr⟩
      simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, same_bytes_correct, spelled,
        advance, rest, member]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show data.val.length ≤ index.val by omega)]
termination_by data.val.length - index.val
decreasing_by omega

theorem add_role_good (context : data_ontology.Context) (role : ObjectPropertyExpression) :
    ∃ r, data_ontology.add_role context role = .ok r ∧ (Good context → Good r) := by
  rw [data_ontology.add_role, named_eq, bind_ok, is_top_object_correct, bind_ok]
  by_cases top : RoleOf role = topObject
  · exact ⟨context, by simp [top], id⟩
  · simp only [top, decide_false, Bool.false_eq_true, ↓reduceIte, reserved_correct, bind_ok]
    by_cases reserved : Reserved (RoleOf role).iri.spelling.val
    · exact ⟨context, by simp [reserved], id⟩
    simp only [reserved, decide_false, Bool.false_eq_true, ↓reduceIte, has_role_correct, bind_ok,
      show (0#usize : Usize).val = 0 from rfl, List.drop_zero]
    by_cases known : RoleOf role ∈ context.roles.val
    · exact ⟨context, by simp [known], id⟩
    · simp only [known, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases full : alloc.vec.Vec.len context.roles = core.num.Usize.MAX
      · exact ⟨context, by simp [full], id⟩
      · have room : context.roles.val.length < Usize.max := by
          have := context.roles.property
          have : context.roles.val.length ≠ Usize.max := fun h => full
            (UScalar.eq_of_val_eq (by rw [alloc.vec.Vec.len_val, usize_max_val]; exact h))
          omega
        obtain ⟨copy, copyRun⟩ : ∃ copy, nnf.copy_bytes (RoleOf role).iri.spelling = .ok copy :=
          ⟨_, Rowl.Nnf.copy_bytes_identity _⟩
        have copied : copy = (RoleOf role).iri.spelling :=
          (Result.ok_injective ((Rowl.Nnf.copy_bytes_identity (RoleOf role).iri.spelling).symm.trans copyRun)).symm
        obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec context.roles
          ({ iri := { spelling := copy } } : ObjectProperty) room)
        refine ⟨{ context with roles := pushed }, by simp [full, copyRun, push], fun good => ⟨good.1, ?_, good.2.2⟩⟩
        intro r member
        simp only [contents, List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact good.2.1 r old
        · have same : ({ iri := { spelling := copy } } : ObjectProperty) = RoleOf role := by
            rw [copied]
          rw [same]
          exact ⟨reserved, top⟩

theorem add_data_good (context : data_ontology.Context) (property : DataProperty) :
    ∃ r, data_ontology.add_data context property = .ok r ∧ (Good context → Good r) := by
  rw [data_ontology.add_data, is_top_data_correct, bind_ok]
  by_cases top : property = topData
  · exact ⟨context, by simp [top], id⟩
  · simp only [top, decide_false, Bool.false_eq_true, ↓reduceIte, is_bottom_data_correct, bind_ok]
    by_cases bottom : property = bottomData
    · exact ⟨context, by simp [bottom], id⟩
    · simp only [bottom, decide_false, Bool.false_eq_true, ↓reduceIte, has_data_correct, bind_ok,
        show (0#usize : Usize).val = 0 from rfl, List.drop_zero]
      by_cases known : property ∈ context.data.val
      · exact ⟨context, by simp [known], id⟩
      · simp only [known, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases full : alloc.vec.Vec.len context.data = core.num.Usize.MAX
        · exact ⟨context, by simp [full], id⟩
        · have room : context.data.val.length < Usize.max := by
            have := context.data.property
            have : context.data.val.length ≠ Usize.max := fun h => full
              (UScalar.eq_of_val_eq (by rw [alloc.vec.Vec.len_val, usize_max_val]; exact h))
            omega
          obtain ⟨copy, copyRun⟩ : ∃ copy, nnf.copy_bytes property.iri.spelling = .ok copy :=
            ⟨_, Rowl.Nnf.copy_bytes_identity _⟩
          have copied : copy = property.iri.spelling :=
            (Result.ok_injective ((Rowl.Nnf.copy_bytes_identity property.iri.spelling).symm.trans copyRun)).symm
          obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec context.data
            ({ iri := { spelling := copy } } : DataProperty) room)
          refine ⟨{ context with data := pushed }, by simp [full, copyRun, push],
            fun good => ⟨good.1, good.2.1, ?_, good.2.2.2⟩⟩
          intro p member
          simp only [contents, List.mem_append, List.mem_singleton] at member
          rcases member with old | rfl
          · exact good.2.2.1 p old
          · have same : ({ iri := { spelling := copy } } : DataProperty) = property := by rw [copied]
            rw [same]
            exact ⟨top, bottom⟩

theorem canonical_numeric {v : datatypes.DataValue} (c : Canonical v) (number : Rowl.Datatypes.IsNumber v) :
    Rowl.Datatypes.CanonicalNumeric v := by
  cases v <;> simp_all [Canonical, Rowl.Datatypes.CanonicalNumeric, Rowl.Datatypes.IsNumber]

theorem add_cut_good (cuts : alloc.vec.Vec regions.Cut) (value : datatypes.DataValue) («open» : Bool)
    (c : Rowl.Datatypes.CanonicalNumeric value) :
    ∃ r, regions.add_cut cuts value «open» = .ok r ∧ (GoodCuts cuts.val → GoodCuts r.val) := by
  obtain ⟨r, run, members, nodup⟩ := Rowl.Regions.add_cut_correct cuts value «open»
  refine ⟨r, run, fun good => ⟨fun x m => ?_, nodup good.2⟩⟩
  rcases members x m with old | rfl
  · exact good.1 x old
  · exact c

theorem add_literal_good (context : data_ontology.Context) (literal : Literal) :
    ∃ r, data_ontology.add_literal context literal = .ok r ∧ (Good context → Good r) := by
  obtain ⟨result, run, some', _⟩ := Rowl.Datatypes.literal_value_correct.{0} literal
  rw [data_ontology.add_literal, run]
  cases result with
  | none => exact ⟨context, by simp, id⟩
  | some value =>
    have cv := (some' value rfl).1
    obtain ⟨v, addRun, addGood⟩ := add_value_correct context.values value
    refine ⟨{ context with values := v }, by simp [addRun], fun good => ?_⟩
    exact ⟨addGood good.1 cv, good.2⟩

/-! ### Sizes of nested expressions -/

theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) : sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega
theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α) {x : α} (h : x ∈ xs.val) :
    sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega
theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith
theorem member_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) (child : α)
    (member : child ∈ xs.rest.val) : sizeOf child < sizeOf xs := by
  have := vec_mem_size xs.rest member
  have := rest_size xs
  omega

/-! ### Building the context keeps its values good -/

theorem literals_context_good (context : data_ontology.Context) (literals : alloc.vec.Vec Literal)
    (index : Usize) (good : Good context) :
    ∃ r, data_ontology.literals_context context literals index = .ok r ∧ Good r := by
  rw [data_ontology.literals_context]
  by_cases inside : index.val < literals.val.length
  · have lookup : literals.index_usize index = .ok literals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := add_literal_good context literals.val[index.val]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, rest, rGood⟩ := literals_context_good c literals next (cGood good)
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by literals.val.length - index.val
decreasing_by omega

theorem with_kind_eq (kinds : data_ontology.Kinds) (k : datatypes.Kind) :
    ∃ r, data_ontology.with_kind kinds k = .ok r := by
  cases k <;> exact ⟨_, rfl⟩

theorem add_bound_good (cuts : alloc.vec.Vec regions.Cut) (bound : Option datatypes.DataValue) («open» : Bool)
    (c : ∀ v, bound = some v → Rowl.Datatypes.CanonicalNumeric v) :
    ∃ r, data_ontology.add_bound cuts bound «open» = .ok r ∧ (GoodCuts cuts.val → GoodCuts r.val) := by
  cases bound with
  | none => exact ⟨cuts, rfl, id⟩
  | some v =>
    obtain ⟨r, run, good⟩ := add_cut_good cuts v «open» (c v rfl)
    exact ⟨r, by rw [data_ontology.add_bound]; exact run, good⟩

theorem kind_context_good (context : data_ontology.Context) (k : datatypes.Kind) :
    ∃ r, data_ontology.kind_context context k = .ok r ∧ (Good context → Good r) := by
  rw [data_ontology.kind_context]
  obtain ⟨kinds, kindsRun⟩ := with_kind_eq context.kinds k
  obtain ⟨lo, loRun, _, loSome⟩ := Rowl.Datatypes.lower_bound_correct k
  obtain ⟨hi, hiRun, _, hiSome⟩ := Rowl.Datatypes.upper_bound_correct k
  obtain ⟨c1, run1, good1⟩ := add_bound_good context.cuts lo false (fun v h => by
    obtain ⟨l, _, bv⟩ := loSome v h; exact (Rowl.Datatypes.bound_number bv).1)
  obtain ⟨c2, run2, good2⟩ := add_bound_good c1 hi true (fun v h => by
    obtain ⟨u, _, bv⟩ := hiSome v h; exact (Rowl.Datatypes.bound_number bv).1)
  have keeps' : (context.kinds.ordered = true → context.kinds.real = true) → kinds.ordered = true →
      kinds.real = true := by
    intro h o
    cases k <;> simp [data_ontology.with_kind] at kindsRun <;> subst kindsRun <;> simp_all
  refine ⟨{ context with kinds := kinds, cuts := c2 }, by simp [kindsRun, loRun, run1, hiRun, run2],
    fun good => ⟨good.1, good.2.1, good.2.2.1, good2 (good1 good.2.2.2.1), keeps' good.2.2.2.2⟩⟩

theorem facet_context_good (context : data_ontology.Context) (restriction : FacetRestriction) :
    ∃ r, data_ontology.facet_context context restriction = .ok r ∧ (Good context → Good r) := by
  rw [data_ontology.facet_context, Rowl.Datatypes.facet_of_correct]
  obtain ⟨result, run, some', _⟩ := Rowl.Datatypes.literal_value_correct.{0} restriction.value
  rw [run]
  cases facet : Rowl.Datatypes.facetOf restriction.facet with
  | none => exact ⟨context, by simp, id⟩
  | some F =>
    cases result with
    | none => exact ⟨context, by simp, id⟩
    | some value =>
      by_cases number : Rowl.Datatypes.IsNumber value
      · obtain ⟨side, sideRun⟩ : ∃ b, data_ontology.facet_open F = .ok b := by cases F <;> exact ⟨_, rfl⟩
        obtain ⟨c, cRun, cGood⟩ := add_cut_good context.cuts value side
          (canonical_numeric (some' value rfl).1 number)
        refine ⟨{ context with cuts := c }, by simp [Rowl.Datatypes.numeric_correct, number, sideRun, cRun],
          fun good => ⟨good.1, good.2.1, good.2.2.1, cGood good.2.2.2.1, good.2.2.2.2⟩⟩
      · exact ⟨context, by simp [Rowl.Datatypes.numeric_correct, number], id⟩

theorem facets_context_good (context : data_ontology.Context) (restrictions : alloc.vec.Vec FacetRestriction)
    (index : Usize) (good : Good context) :
    ∃ r, data_ontology.facets_context context restrictions index = .ok r ∧ Good r := by
  rw [data_ontology.facets_context]
  by_cases inside : index.val < restrictions.val.length
  · have lookup : restrictions.index_usize index = .ok restrictions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := facet_context_good context restrictions.val[index.val]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, rest, rGood⟩ := facets_context_good c restrictions next (cGood good)
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by restrictions.val.length - index.val
decreasing_by omega

theorem has_edge_correct (edges : alloc.vec.Vec U128) (edge : U128) (index : Usize) :
    data_ontology.has_edge edges edge index = .ok (decide (edge ∈ edges.val.drop index.val)) := by
  rw [data_ontology.has_edge]
  by_cases inside : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    have rest := has_edge_correct edges edge next
    rw [nextIndex] at rest
    have member : edge ∈ edges.val.drop index.val ↔
        edges.val[index.val] = edge ∨ edge ∈ edges.val.drop (index.val + 1) := by
      rw [split, List.mem_cons]; exact or_congr_left eq_comm
    simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, advance, rest, member]
  · simp [UScalar.lt_equiv, inside, List.drop_eq_nil_iff.mpr (show edges.val.length ≤ index.val by omega)]
termination_by edges.val.length - index.val
decreasing_by omega

theorem add_edge_ok (edges : alloc.vec.Vec U128) (edge : U128) : ∃ r, data_ontology.add_edge edges edge = .ok r := by
  rw [data_ontology.add_edge, has_edge_correct]
  by_cases present : edge ∈ edges.val
  · exact ⟨edges, by simp [present]⟩
  · by_cases room : edges.val.length < Usize.max
    · have room' : alloc.vec.Vec.len edges < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
      obtain ⟨pushed, push, _⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec edges edge room)
      exact ⟨pushed, by simp [present, room', push]⟩
    · have full : ¬ alloc.vec.Vec.len edges < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val, usize_max_val]; exact room
      exact ⟨edges, by simp [present, full]⟩

theorem facet_edges_ok (edges : alloc.vec.Vec U128) (F : datatypes.Facet) (bound : datatypes.Binary)
    (double : Bool) (c : Rowl.Floats.CanonicalBinary bound)
    (v : (Rowl.Floats.binaryOf bound).Valid (Rowl.Floats.fmt double)) :
    ∃ r, data_ontology.facet_edges edges F bound double = .ok r := by
  unfold data_ontology.facet_edges
  rw [Rowl.FloatOrder.is_nan_spec]
  by_cases nan : Rowl.Floats.binaryOf bound = .nan
  · exact ⟨edges, by simp [nan]⟩
  · have pf := Rowl.FloatOrder.proper_fmt double
    obtain ⟨lowP, lowRun, lowVal⟩ := Rowl.FloatOrder.low_position_spec bound double c v
    obtain ⟨highP, highRun, highVal⟩ := Rowl.FloatOrder.high_position_spec bound double c v
    have small := Rowl.FloatOrder.top_small double
    have highLe : highP.val ≤ 2 * Rowl.FloatOrder.topPlace (Rowl.Floats.fmt double) + 2 := by
      rw [highVal]
      obtain ⟨_, h, _, ph, _, upper⟩ := Rowl.FloatOrder.places_of pf v nan
      have : (Rowl.FloatOrder.highPosition (Rowl.Floats.fmt double) (Rowl.Floats.binaryOf bound) : ℤ) ≤
          2 * Rowl.FloatOrder.topPlace (Rowl.Floats.fmt double) + 2 := by
        rw [h]; unfold Rowl.FloatOrder.highOf; split_ifs <;> omega
      omega
    obtain ⟨h1, h1Run, _⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := highP) (y := 1#u128) (by simp [UScalar.max, U128.max_eq]; omega))
    cases F with
    | MinInclusive =>
      obtain ⟨r, run⟩ := add_edge_ok edges lowP
      exact ⟨r, by simp [nan, lowRun, run]⟩
    | MinExclusive =>
      obtain ⟨r, run⟩ := add_edge_ok edges h1
      exact ⟨r, by simp [nan, highRun, h1Run, run]⟩
    | MaxInclusive =>
      obtain ⟨r1, run1⟩ := add_edge_ok edges 1#u128
      obtain ⟨r, run⟩ := add_edge_ok r1 h1
      exact ⟨r, by simp [nan, highRun, h1Run, run1, run]⟩
    | MaxExclusive =>
      obtain ⟨r1, run1⟩ := add_edge_ok edges 1#u128
      obtain ⟨r, run⟩ := add_edge_ok r1 lowP
      exact ⟨r, by simp [nan, lowRun, run1, run]⟩

theorem edge_context_good (context : data_ontology.Context) (restriction : FacetRestriction) :
    ∃ r, data_ontology.edge_context context restriction = .ok r ∧ (Good context → Good r) := by
  rw [data_ontology.edge_context, Rowl.Datatypes.facet_of_correct]
  obtain ⟨result, run, some', _⟩ := Rowl.Datatypes.literal_value_correct.{0} restriction.value
  rw [run]
  cases facet : Rowl.Datatypes.facetOf restriction.facet with
  | none => exact ⟨context, by simp, id⟩
  | some F =>
    cases result with
    | none => exact ⟨context, by simp, id⟩
    | some value =>
      have canonical := (some' value rfl).1
      cases value with
      | Double b =>
        obtain ⟨r, run⟩ := facet_edges_ok context.double_edges F b true canonical.1 canonical.2
        exact ⟨{ context with double_edges := r }, by simp [run], fun good => good⟩
      | Float b =>
        obtain ⟨r, run⟩ := facet_edges_ok context.float_edges F b false canonical.1 canonical.2
        exact ⟨{ context with float_edges := r }, by simp [run], fun good => good⟩
      | _ => exact ⟨context, by simp, id⟩

theorem edges_context_good (context : data_ontology.Context) (restrictions : alloc.vec.Vec FacetRestriction)
    (index : Usize) (good : Good context) :
    ∃ r, data_ontology.edges_context context restrictions index = .ok r ∧ Good r := by
  rw [data_ontology.edges_context]
  by_cases inside : index.val < restrictions.val.length
  · have lookup : restrictions.index_usize index = .ok restrictions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := edge_context_good context restrictions.val[index.val]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, rest, rGood⟩ := edges_context_good c restrictions next (cGood good)
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by restrictions.val.length - index.val
decreasing_by omega

theorem binary_kind_eq (k : datatypes.Kind) :
    data_ontology.binary_kind k = .ok (decide (k = .Double ∨ k = .Float)) := by
  cases k <;> simp [data_ontology.binary_kind]

theorem ranges_context_good (ranges : alloc.vec.Vec DataRange) (index : Usize)
    (each : ∀ e ∈ ranges.val, ∀ context, Good context → ∃ r, data_ontology.range_context context e = .ok r ∧ Good r)
    (context : data_ontology.Context) (good : Good context) :
    ∃ r, data_ontology.ranges_context context ranges index = .ok r ∧ Good r := by
  rw [data_ontology.ranges_context]
  by_cases inside : index.val < ranges.val.length
  · have lookup : ranges.index_usize index = .ok ranges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := each _ (List.getElem_mem inside) context good
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    obtain ⟨r, rest, rGood⟩ := ranges_context_good ranges next each c cGood
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by ranges.val.length - index.val
decreasing_by have := nextValue; simp at this; omega

theorem range_context_good (range : DataRange) (context : data_ontology.Context) (good : Good context) :
    ∃ r, data_ontology.range_context context range = .ok r ∧ Good r := by
  cases h : range with
  | Datatype dt =>
    rw [data_ontology.range_context, Rowl.Datatypes.kind_of_correct]
    cases kindOf dt with
    | none => exact ⟨context, by simp, good⟩
    | some k =>
      obtain ⟨r, run, rGood⟩ := kind_context_good context k
      exact ⟨r, by simp [run], rGood good⟩
  | Intersection members =>
    rw [data_ontology.range_context]
    have := first_size members
    have := second_size members
    obtain ⟨c1, run1, good1⟩ := range_context_good members.first context good
    obtain ⟨c2, run2, good2⟩ := range_context_good members.second c1 good1
    obtain ⟨r, run, rGood⟩ := ranges_context_good members.rest 0#usize
      (fun e mem c cg => have := member_size members e mem; range_context_good e c cg) c2 good2
    exact ⟨r, by simp [run1, run2, run], rGood⟩
  | Union members =>
    rw [data_ontology.range_context]
    have := first_size members
    have := second_size members
    obtain ⟨c1, run1, good1⟩ := range_context_good members.first context good
    obtain ⟨c2, run2, good2⟩ := range_context_good members.second c1 good1
    obtain ⟨r, run, rGood⟩ := ranges_context_good members.rest 0#usize
      (fun e mem c cg => have := member_size members e mem; range_context_good e c cg) c2 good2
    exact ⟨r, by simp [run1, run2, run], rGood⟩
  | Complement inner =>
    rw [data_ontology.range_context]
    exact range_context_good inner context good
  | OneOf literals =>
    rw [data_ontology.range_context]
    obtain ⟨c1, run1, good1⟩ := add_literal_good context literals.first
    obtain ⟨r, run, rGood⟩ := literals_context_good c1 literals.rest 0#usize (good1 good)
    exact ⟨r, by simp [run1, run], rGood⟩
  | Restriction dt restrictions =>
    rw [data_ontology.range_context, Rowl.Datatypes.kind_of_correct]
    obtain ⟨kinds, kindsRun⟩ : ∃ k, data_ontology.with_order context.kinds = .ok k := ⟨_, rfl⟩
    have good0 : Good { context with kinds := kinds } := by
      simp [data_ontology.with_order] at kindsRun
      subst kindsRun
      exact ⟨good.1, good.2.1, good.2.2.1, good.2.2.2.1, fun _ => rfl⟩
    cases kindOf dt with
    | none =>
      obtain ⟨c2, run2, good2⟩ := facet_context_good { context with kinds := kinds } restrictions.first
      obtain ⟨r, run, rGood⟩ := facets_context_good c2 restrictions.rest 0#usize (good2 good0)
      exact ⟨r, by simp [kindsRun, run2, run], rGood⟩
    | some k =>
      by_cases binary : k = .Double ∨ k = .Float
      · obtain ⟨c1, run1, good1⟩ := kind_context_good context k
        obtain ⟨c2, run2, good2⟩ := edge_context_good c1 restrictions.first
        obtain ⟨r, run, rGood⟩ := edges_context_good c2 restrictions.rest 0#usize (good2 (good1 good))
        exact ⟨r, by simp [binary_kind_eq, binary, run1, run2, run], rGood⟩
      · obtain ⟨c1, run1, good1⟩ := kind_context_good { context with kinds := kinds } k
        obtain ⟨c2, run2, good2⟩ := facet_context_good c1 restrictions.first
        obtain ⟨r, run, rGood⟩ := facets_context_good c2 restrictions.rest 0#usize (good2 (good1 good0))
        exact ⟨r, by simp [binary_kind_eq, binary, kindsRun, run1, run2, run], rGood⟩
termination_by sizeOf range
decreasing_by all_goals simp_wf; all_goals omega

theorem optional_range_context_good (range : Option DataRange) (context : data_ontology.Context)
    (good : Good context) :
    ∃ r, data_ontology.optional_range_context context range = .ok r ∧ Good r := by
  cases range with
  | none => exact ⟨context, rfl, good⟩
  | some range =>
    rw [data_ontology.optional_range_context]
    exact range_context_good range context good

theorem classes_context_good (classes : alloc.vec.Vec ClassExpression) (index : Usize)
    (each : ∀ e ∈ classes.val, ∀ context, Good context →
      ∃ r, data_ontology.class_context context e = .ok r ∧ Good r)
    (context : data_ontology.Context) (good : Good context) :
    ∃ r, data_ontology.classes_context context classes index = .ok r ∧ Good r := by
  rw [data_ontology.classes_context]
  by_cases inside : index.val < classes.val.length
  · have lookup : classes.index_usize index = .ok classes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := each _ (List.getElem_mem inside) context good
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    obtain ⟨r, rest, rGood⟩ := classes_context_good classes next each c cGood
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by classes.val.length - index.val
decreasing_by have := nextValue; simp at this; omega

theorem class_context_good (class' : ClassExpression) (context : data_ontology.Context) (good : Good context) :
    ∃ r, data_ontology.class_context context class' = .ok r ∧ Good r := by
  have members : ∀ (members : AtLeastTwo ClassExpression), sizeOf members < sizeOf class' →
      ∀ context, Good context → ∃ r, data_ontology.members_context context members = .ok r ∧ Good r := by
    intro members smaller context good
    have := first_size members
    have := second_size members
    rw [data_ontology.members_context]
    obtain ⟨c1, run1, good1⟩ := class_context_good members.first context good
    obtain ⟨c2, run2, good2⟩ := class_context_good members.second c1 good1
    obtain ⟨r, run, rGood⟩ := classes_context_good members.rest 0#usize
      (fun e mem c cg => have := member_size members e mem; class_context_good e c cg) c2 good2
    exact ⟨r, by simp [run1, run2, run], rGood⟩
  cases h : class' with
  | Class _ => exact ⟨context, by rw [data_ontology.class_context], good⟩
  | ObjectIntersectionOf xs =>
    rw [data_ontology.class_context]; exact members xs (by simp [h]) context good
  | ObjectUnionOf xs =>
    rw [data_ontology.class_context]; exact members xs (by simp [h]) context good
  | ObjectComplementOf inner =>
    rw [data_ontology.class_context]; exact class_context_good inner context good
  | ObjectOneOf _ => exact ⟨context, by rw [data_ontology.class_context], good⟩
  | ObjectSomeValuesFrom role filler =>
    rw [data_ontology.class_context]
    obtain ⟨c, run, cGood⟩ := add_role_good context role
    obtain ⟨r, rest, rGood⟩ := class_context_good filler c (cGood good)
    exact ⟨r, by simp [run, rest], rGood⟩
  | ObjectAllValuesFrom role filler =>
    rw [data_ontology.class_context]
    obtain ⟨c, run, cGood⟩ := add_role_good context role
    obtain ⟨r, rest, rGood⟩ := class_context_good filler c (cGood good)
    exact ⟨r, by simp [run, rest], rGood⟩
  | ObjectHasValue role _ =>
    rw [data_ontology.class_context]; exact add_role_good context role |>.imp fun _ h => ⟨h.1, h.2 good⟩
  | ObjectHasSelf role =>
    rw [data_ontology.class_context]; exact add_role_good context role |>.imp fun _ h => ⟨h.1, h.2 good⟩
  | ObjectMinCardinality _ role filler | ObjectMaxCardinality _ role filler
  | ObjectExactCardinality _ role filler =>
    rw [data_ontology.class_context]
    obtain ⟨c, run, cGood⟩ := add_role_good context role
    cases hf : filler with
    | none => exact ⟨c, by simp [run], cGood good⟩
    | some inner =>
      have : sizeOf inner < sizeOf class' := by rw [h, hf]; simp +arith
      obtain ⟨r, rest, rGood⟩ := class_context_good inner c (cGood good)
      exact ⟨r, by simp [run, rest], rGood⟩
  | DataSomeValuesFrom property range | DataAllValuesFrom property range =>
    rw [data_ontology.class_context]
    obtain ⟨c, run, cGood⟩ := add_data_good context property
    obtain ⟨r, rest, rGood⟩ := range_context_good range c (cGood good)
    exact ⟨r, by simp [run, rest], rGood⟩
  | DataHasValue property literal =>
    rw [data_ontology.class_context]
    obtain ⟨c, run, cGood⟩ := add_data_good context property
    obtain ⟨r, rest, rGood⟩ := add_literal_good c literal
    exact ⟨r, by simp [run, rest], rGood (cGood good)⟩
  | DataMinCardinality _ property range | DataMaxCardinality _ property range
  | DataExactCardinality _ property range =>
    rw [data_ontology.class_context]
    obtain ⟨c, run, cGood⟩ := add_data_good context property
    obtain ⟨r, rest, rGood⟩ := optional_range_context_good range c (cGood good)
    exact ⟨r, by simp [run, rest], rGood⟩
termination_by sizeOf class'
decreasing_by all_goals simp_wf; all_goals (subst_vars; omega)

theorem roles_context_good (context : data_ontology.Context) (roles : alloc.vec.Vec ObjectPropertyExpression)
    (index : Usize) (good : Good context) :
    ∃ r, data_ontology.roles_context context roles index = .ok r ∧ Good r := by
  rw [data_ontology.roles_context]
  by_cases inside : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := add_role_good context roles.val[index.val]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, rest, rGood⟩ := roles_context_good c roles next (cGood good)
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by roles.val.length - index.val
decreasing_by omega

theorem role_members_context_good (context : data_ontology.Context) (roles : AtLeastTwo ObjectPropertyExpression)
    (good : Good context) :
    ∃ r, data_ontology.role_members_context context roles = .ok r ∧ Good r := by
  rw [data_ontology.role_members_context]
  obtain ⟨c1, run1, good1⟩ := add_role_good context roles.first
  obtain ⟨c2, run2, good2⟩ := add_role_good c1 roles.second
  obtain ⟨r, run, rGood⟩ := roles_context_good c2 roles.rest 0#usize (good2 (good1 good))
  exact ⟨r, by simp [run1, run2, run], rGood⟩

theorem data_list_context_good (context : data_ontology.Context) (data : alloc.vec.Vec DataProperty)
    (index : Usize) (good : Good context) :
    ∃ r, data_ontology.data_list_context context data index = .ok r ∧ Good r := by
  rw [data_ontology.data_list_context]
  by_cases inside : index.val < data.val.length
  · have lookup : data.index_usize index = .ok data.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := add_data_good context data.val[index.val]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, rest, rGood⟩ := data_list_context_good c data next (cGood good)
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by data.val.length - index.val
decreasing_by omega

theorem members_context_good (context : data_ontology.Context) (members : AtLeastTwo ClassExpression)
    (good : Good context) :
    ∃ r, data_ontology.members_context context members = .ok r ∧ Good r := by
  rw [data_ontology.members_context]
  obtain ⟨c1, run1, good1⟩ := class_context_good members.first context good
  obtain ⟨c2, run2, good2⟩ := class_context_good members.second c1 good1
  obtain ⟨r, run, rGood⟩ := classes_context_good members.rest 0#usize
    (fun e _ c cg => class_context_good e c cg) c2 good2
  exact ⟨r, by simp [run1, run2, run], rGood⟩

private theorem role_step (c : data_ontology.Context) (g : Good c) (r : ObjectPropertyExpression) :
    ∃ x, data_ontology.add_role c r = .ok x ∧ Good x := by
  obtain ⟨x, run, gx⟩ := add_role_good c r; exact ⟨x, run, gx g⟩
private theorem data_step (c : data_ontology.Context) (g : Good c) (p : DataProperty) :
    ∃ x, data_ontology.add_data c p = .ok x ∧ Good x := by
  obtain ⟨x, run, gx⟩ := add_data_good c p; exact ⟨x, run, gx g⟩

theorem axiom_context_good (context : data_ontology.Context) (item : Axiom) (good : Good context) :
    ∃ r, data_ontology.axiom_context context item = .ok r ∧ Good r := by
  have role := role_step
  have data := data_step
  cases item with
  | SubClassOf sub sup =>
    rw [data_ontology.axiom_context]
    obtain ⟨c, run, cGood⟩ := class_context_good sub context good
    obtain ⟨r, rest, rGood⟩ := class_context_good sup c cGood
    exact ⟨r, by simp [run, rest], rGood⟩
  | EquivalentClasses members | DisjointClasses members | DisjointUnion _ members =>
    rw [data_ontology.axiom_context]; exact members_context_good context members good
  | SubObjectPropertyOf sub sup =>
    cases sub with
    | Single r =>
      obtain ⟨c, run, cGood⟩ := role context good r
      obtain ⟨r', rest, rGood⟩ := role c cGood sup
      exact ⟨r', by simp [data_ontology.axiom_context.eq_def, run, rest], rGood⟩
    | Chain roles =>
      obtain ⟨c, run, cGood⟩ := role_members_context_good context roles good
      obtain ⟨r', rest, rGood⟩ := role c cGood sup
      exact ⟨r', by simp [data_ontology.axiom_context.eq_def, run, rest], rGood⟩
  | EquivalentObjectProperties roles | DisjointObjectProperties roles =>
    rw [data_ontology.axiom_context]; exact role_members_context_good context roles good
  | InverseObjectProperties first second =>
    rw [data_ontology.axiom_context]
    obtain ⟨c, run, cGood⟩ := role context good first
    obtain ⟨r, rest, rGood⟩ := role c cGood second
    exact ⟨r, by simp [run, rest], rGood⟩
  | ObjectPropertyDomain r e | ObjectPropertyRange r e =>
    rw [data_ontology.axiom_context]
    obtain ⟨c, run, cGood⟩ := role context good r
    obtain ⟨r', rest, rGood⟩ := class_context_good e c cGood
    exact ⟨r', by simp [run, rest], rGood⟩
  | FunctionalObjectProperty r | InverseFunctionalObjectProperty r | ReflexiveObjectProperty r
  | IrreflexiveObjectProperty r | SymmetricObjectProperty r | AsymmetricObjectProperty r
  | TransitiveObjectProperty r =>
    rw [data_ontology.axiom_context]; exact role context good r
  | SubDataPropertyOf sub sup =>
    rw [data_ontology.axiom_context]
    obtain ⟨c, run, cGood⟩ := data context good sub
    obtain ⟨r, rest, rGood⟩ := data c cGood sup
    exact ⟨r, by simp [run, rest], rGood⟩
  | EquivalentDataProperties ps | DisjointDataProperties ps =>
    rw [data_ontology.axiom_context]
    obtain ⟨c1, run1, good1⟩ := data context good ps.first
    obtain ⟨c2, run2, good2⟩ := data c1 good1 ps.second
    obtain ⟨r, run, rGood⟩ := data_list_context_good c2 ps.rest 0#usize good2
    exact ⟨r, by simp [run1, run2, run], rGood⟩
  | DataPropertyDomain p e =>
    rw [data_ontology.axiom_context]
    obtain ⟨c, run, cGood⟩ := data context good p
    obtain ⟨r, rest, rGood⟩ := class_context_good e c cGood
    exact ⟨r, by simp [run, rest], rGood⟩
  | DataPropertyRange p range =>
    rw [data_ontology.axiom_context]
    obtain ⟨c, run, cGood⟩ := data context good p
    obtain ⟨r, rest, rGood⟩ := range_context_good range c cGood
    exact ⟨r, by simp [run, rest], rGood⟩
  | FunctionalDataProperty p =>
    rw [data_ontology.axiom_context]; exact data context good p
  | ClassAssertion e _ =>
    rw [data_ontology.axiom_context]; exact class_context_good e context good
  | ObjectPropertyAssertion r _ _ | NegativeObjectPropertyAssertion r _ _ =>
    rw [data_ontology.axiom_context]; exact role context good r
  | DataPropertyAssertion p _ literal | NegativeDataPropertyAssertion p _ literal =>
    rw [data_ontology.axiom_context]
    obtain ⟨c, run, cGood⟩ := data context good p
    obtain ⟨r, rest, rGood⟩ := add_literal_good c literal
    exact ⟨r, by simp [run, rest], rGood cGood⟩
  | Declaration _ | DatatypeDefinition _ _ | HasKey _ _ _ | SameIndividual _ | DifferentIndividuals _
  | AnnotationAssertion _ _ _ | SubAnnotationPropertyOf _ _ | AnnotationPropertyDomain _ _
  | AnnotationPropertyRange _ _ =>
    exact ⟨context, by rw [data_ontology.axiom_context], good⟩

theorem items_context_good (context : data_ontology.Context) (items : alloc.vec.Vec AnnotatedAxiom)
    (index : Usize) (good : Good context) :
    ∃ r, data_ontology.items_context context items index = .ok r ∧ Good r := by
  rw [data_ontology.items_context]
  by_cases inside : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨c, run, cGood⟩ := axiom_context_good context items.val[index.val].axiom good
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r, rest, rGood⟩ := items_context_good c items next cGood
    exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, advance, rest], rGood⟩
  · exact ⟨context, by simp [UScalar.lt_equiv, inside], good⟩
termination_by items.val.length - index.val
decreasing_by omega

theorem closure_context_good (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ r, data_ontology.closure_context items = .ok r ∧ Good r := by
  rw [data_ontology.closure_context]
  have empty : Good (data_ontology.Context.mk (alloc.vec.Vec.new datatypes.DataValue)
      (data_ontology.Kinds.mk false false false false false false false false false false false false false false
        false false false false false false false)
      (alloc.vec.Vec.new ObjectProperty)
      (alloc.vec.Vec.new DataProperty) (alloc.vec.Vec.new regions.Cut) (alloc.vec.Vec.new U128)
      (alloc.vec.Vec.new U128)) := by
    simp [Good, GoodValues, GoodCuts, new_val]
  obtain ⟨r, run, rGood⟩ := items_context_good _ items 0#usize empty
  exact ⟨r, by simp [data_ontology.no_kinds, run], rGood⟩

theorem with_truths_good (context : data_ontology.Context) (good : Good context) :
    ∃ r, data_ontology.with_truths context = .ok r ∧ Good r := by
  rw [data_ontology.with_truths]
  by_cases boolean : context.kinds.boolean = true
  · obtain ⟨v1, run1, good1⟩ := add_value_correct context.values (.Truth true)
    obtain ⟨v2, run2, good2⟩ := add_value_correct v1 (.Truth false)
    exact ⟨{ context with values := v2 }, by simp [boolean, run1, run2], good2 (good1 good.1 trivial) trivial, good.2⟩
  · exact ⟨context, by simp [boolean], good⟩

theorem canonical_of_numeric {v : datatypes.DataValue} (c : Rowl.Datatypes.CanonicalNumeric v) : Canonical v := by
  cases v <;> simp_all [Canonical, Rowl.Datatypes.CanonicalNumeric]

theorem points_from_good (cuts : alloc.vec.Vec regions.Cut) (good : GoodCuts cuts.val) (index : Usize)
    (values : alloc.vec.Vec datatypes.DataValue) (gv : GoodValues values.val) :
    ∃ r, data_ontology.points_from cuts index values = .ok r ∧ GoodValues r.val := by
  rw [data_ontology.points_from]
  by_cases inside : index.val < cuts.val.length
  · have lookup : cuts.index_usize index = .ok cuts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨o, oRun, _, _⟩ := Rowl.Regions.cut_index_correct cuts cuts.val[index.val].value
      (!cuts.val[index.val].open) 0#usize
    cases o with
    | none =>
      obtain ⟨r, run, rGood⟩ := points_from_good cuts good next values gv
      exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, oRun, advance, run],
        rGood⟩
    | some _ =>
      obtain ⟨v, vRun, vGood⟩ := add_value_correct values cuts.val[index.val].value
      obtain ⟨r, run, rGood⟩ := points_from_good cuts good next v
        (vGood gv (canonical_of_numeric (good.1 _ (List.getElem_mem inside))))
      exact ⟨r, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, oRun, advance,
        Rowl.Regions.copy_value_eq, vRun, run], rGood⟩
  · exact ⟨values, by simp [UScalar.lt_equiv, inside], gv⟩
termination_by cuts.val.length - index.val
decreasing_by all_goals omega

theorem finished_good (context : data_ontology.Context) (good : Good context) :
    ∃ r, data_ontology.finished context = .ok r ∧ Good r := by
  rw [data_ontology.finished]
  obtain ⟨c, run, cGood⟩ := with_truths_good context good
  obtain ⟨v, vRun, vGood⟩ := points_from_good c.cuts cGood.2.2.2.1 0#usize c.values cGood.1
  exact ⟨{ c with values := v }, by simp [run, vRun], vGood, cGood.2⟩

/-! ### What the encoding's lookups return -/

/-- The individual of the literal value at an index. -/
noncomputable def valueIndividual (index : Usize) : NamedIndividual :=
  Classical.choose (value_individual_correct index)

theorem value_individual_eq (index : Usize) :
    data_ontology.value_individual index = .ok (.Named (valueIndividual index)) :=
  (Classical.choose_spec (value_individual_correct index)).1

theorem valueIndividual_name (index : Usize) :
    (valueIndividual index).iri.spelling.val = valueName index.val :=
  (Classical.choose_spec (value_individual_correct index)).2

theorem zero_val : (0#usize : Usize).val = 0 := rfl

theorem topObject_plain : ¬ Reserved topObject.iri.spelling.val := by simp [Reserved, topObject]

theorem object_role_correct (context : data_ontology.Context) (r : ObjectPropertyExpression) :
    ∃ res, data_ontology.object_role context r = .ok res ∧
      ∀ r', res = some r' → r' = r ∧ ¬ Reserved (RoleOf r).iri.spelling.val ∧
        (RoleOf r = topObject ∨ RoleOf r ∈ context.roles.val) := by
  have eta : ∀ a : ObjectProperty, ({ iri := { spelling := a.iri.spelling } } : ObjectProperty) = a := fun _ => rfl
  cases r with
  | Property a =>
    simp only [data_ontology.object_role, named_eq, RoleOf, bind_ok, reserved_correct, is_top_object_correct,
      has_role_correct, Rowl.Nnf.copy_bytes_identity, zero_val, List.drop_zero, eta]
    by_cases top : a = topObject
    · subst top; simp [topObject_plain]
    · by_cases reserved : Reserved a.iri.spelling.val <;>
        by_cases known : a ∈ context.roles.val <;> simp [reserved, top, known]
  | Inverse a =>
    simp only [data_ontology.object_role, named_eq, RoleOf, bind_ok, reserved_correct, is_top_object_correct,
      has_role_correct, Rowl.Nnf.copy_bytes_identity, zero_val, List.drop_zero, eta]
    by_cases top : a = topObject
    · subst top; simp [topObject_plain]
    · by_cases reserved : Reserved a.iri.spelling.val <;>
        by_cases known : a ∈ context.roles.val <;> simp [reserved, top, known]

theorem object_individual_of_correct (a : Individual) :
    ∃ res, data_ontology.object_individual_of a = .ok res ∧
      ∀ a', res = some a' → a' = a ∧ ∀ n : NamedIndividual, a = .Named n → ¬ Reserved n.iri.spelling.val := by
  cases a with
  | Named n =>
    rw [data_ontology.object_individual_of, reserved_correct]
    by_cases reserved : Reserved n.iri.spelling.val
    · exact ⟨none, by simp [reserved], by simp⟩
    · refine ⟨some (.Named n), by simp [reserved, Rowl.Concepts.copy_individual_identity], ?_⟩
      intro a' h
      cases h
      exact ⟨rfl, fun m same => by cases same; exact reserved⟩
  | Anonymous b =>
    refine ⟨some (.Anonymous b), by simp [data_ontology.object_individual_of,
      Rowl.Concepts.copy_individual_identity], ?_⟩
    intro a' h
    cases h
    exact ⟨rfl, fun m same => by cases same⟩

/-- An individual whose name, if it has one, is not the encoding's. -/
def Plain : Individual → Prop
  | .Named n => ¬ Reserved n.iri.spelling.val
  | .Anonymous _ => True

theorem object_individual_of_some {a a' : Individual}
    (run : data_ontology.object_individual_of a = .ok (some a')) : a' = a ∧ Plain a := by
  obtain ⟨res, run', facts⟩ := object_individual_of_correct a
  rw [run] at run'
  obtain ⟨same, plain⟩ := facts a' (Result.ok_injective run'.symm ▸ rfl)
  refine ⟨same, ?_⟩
  cases a with
  | Named n => exact plain n rfl
  | Anonymous _ => trivial

theorem individuals_from_correct (individuals : alloc.vec.Vec Individual) (index : Usize)
    (out : alloc.vec.Vec Individual) (room : out.val.length + (individuals.val.length - index.val) ≤ Usize.max) :
    ∃ res, data_ontology.individuals_from individuals index out = .ok res ∧
      ∀ v, res = some v → v.val = out.val ++ individuals.val.drop index.val ∧
        ∀ a ∈ individuals.val.drop index.val, Plain a := by
  rw [data_ontology.individuals_from]
  by_cases inside : index.val < individuals.val.length
  · have lookup : individuals.index_usize index = .ok individuals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, facts⟩ := object_individual_of_correct individuals.val[index.val]
    cases res with
    | none =>
      exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some copy =>
      have copySame := object_individual_of_some run
      have short : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out copy short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := individuals_from_correct individuals next pushed
        (by rw [contents, nextIndex]; simp; omega)
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, push,
        advance, restRun], fun v hv => ?_⟩
      obtain ⟨value, plain⟩ := restFacts v hv
      refine ⟨by rw [value, contents, nextIndex, split, copySame.1]; simp, ?_⟩
      rw [split]
      intro a member
      rcases List.mem_cons.mp member with rfl | later
      · exact copySame.2
      · exact plain a (by rw [nextIndex]; exact later)
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ?_⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show individuals.val.length ≤ index.val by omega)]
termination_by individuals.val.length - index.val
decreasing_by omega

theorem bottom_role_eq :
    ∃ v, data_ontology.pattern_from
      (Array.to_slice (Array.make 50#usize [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8,
        119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8,
        55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 98#u8, 111#u8, 116#u8, 116#u8, 111#u8, 109#u8, 79#u8, 98#u8,
        106#u8, 101#u8, 99#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]))
      0#usize (alloc.vec.Vec.new U8) = .ok v ∧ (⟨⟨v⟩⟩ : ObjectProperty) = bottomObject := by
  obtain ⟨v, run, value⟩ := pattern_from_correct
    (Array.to_slice (Array.make 50#usize [104#u8, 116#u8, 116#u8, 112#u8, 58#u8, 47#u8, 47#u8, 119#u8, 119#u8,
      119#u8, 46#u8, 119#u8, 51#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 50#u8, 48#u8, 48#u8, 50#u8, 47#u8, 48#u8,
      55#u8, 47#u8, 111#u8, 119#u8, 108#u8, 35#u8, 98#u8, 111#u8, 116#u8, 116#u8, 111#u8, 109#u8, 79#u8, 98#u8,
      106#u8, 101#u8, 99#u8, 116#u8, 80#u8, 114#u8, 111#u8, 112#u8, 101#u8, 114#u8, 116#u8, 121#u8]))
    0#usize (alloc.vec.Vec.new U8) (by simp [new_val, Array.to_slice, Array.make]; scalar_tac)
  refine ⟨v, run, ?_⟩
  rw [Rowl.Tableau.property_eq_iff]
  simp [value, new_val, Array.to_slice, Array.make, bottomObject]

/-- The object property of a data property other than `owl:bottomDataProperty`. -/
def DataRoleOf (p : DataProperty) (q : ObjectProperty) : Prop := q.iri.spelling.val = dataRoleName p

theorem data_role_correct (context : data_ontology.Context) (p : DataProperty) :
    ∃ res, data_ontology.data_role context p = .ok res ∧
      ∀ r, res = some r → (p = bottomData ∧ r = .Property bottomObject) ∨
        (p ≠ bottomData ∧ p ∈ context.data.val ∧ ¬ Reserved p.iri.spelling.val ∧
          ∃ q, r = .Property q ∧ DataRoleOf p q) := by
  rw [data_ontology.data_role, is_bottom_data_correct, bind_ok]
  by_cases bottom : p = bottomData
  · obtain ⟨v, run, same⟩ := bottom_role_eq
    have nb : decide (p = bottomData) = true := decide_eq_true bottom
    refine ⟨some (.Property ⟨⟨v⟩⟩), by simp [nb, lift, run], fun r h => .inl ⟨bottom, ?_⟩⟩
    cases h; rw [same]
  · have nb : decide (p = bottomData) = false := decide_eq_false bottom
    simp only [nb, Bool.false_eq_true, ↓reduceIte, has_data_correct, bind_ok]
    by_cases known : p ∈ context.data.val
    · have nk : decide (p ∈ context.data.val.drop (0#usize).val) = true := by simpa using known
      simp only [nk, ↓reduceIte, reserved_correct, bind_ok]
      by_cases reserved : Reserved p.iri.spelling.val
      · have nr : decide (Reserved p.iri.spelling.val) = true := decide_eq_true reserved
        exact ⟨none, by simp [nr], by simp⟩
      · have nr : decide (Reserved p.iri.spelling.val) = false := decide_eq_false reserved
        simp only [nr, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨limit, limitRun, limitValue⟩ := WP.spec_imp_exists
          (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize) (by simp [usize_max_val]; scalar_tac))
        rw [limitRun, bind_ok]
        have limitIs : limit.val = Usize.max - 1 := by simp [usize_max_val] at limitValue; exact limitValue.1
        by_cases short : p.iri.spelling.val.length < limit.val
        · have short' : alloc.vec.Vec.len p.iri.spelling < limit := by
            simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact short
          obtain ⟨v, run, value⟩ := tagged_name_correct 80#u8 p.iri.spelling (by omega)
          refine ⟨some (.Property ⟨⟨v⟩⟩), by simp [short', Rowl.Nnf.copy_bytes_identity, run], fun r h => ?_⟩
          cases h
          exact .inr ⟨bottom, known, reserved, _, rfl, by simp [DataRoleOf, dataRoleName, value]⟩
        · have notShort : ¬ alloc.vec.Vec.len p.iri.spelling < limit := by
            simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact short
          exact ⟨none, by simp [notShort], by simp⟩
    · have nk : decide (p ∈ context.data.val.drop (0#usize).val) = false := by simpa using known
      exact ⟨none, by simp [nk, known, zero_val], by simp⟩

theorem literal_individual_correct (context : data_ontology.Context) (lt : Literal) :
    ∃ res, data_ontology.literal_individual context lt = .ok res ∧
      ∀ a, res = some a → ∃ w i, ∃ h : i.val < context.values.val.length,
        datatypes.literal_value lt = .ok (some w) ∧ context.values.val[i.val] = w ∧
          a = .Named (valueIndividual i) := by
  obtain ⟨value, valueRun, _, _⟩ := Rowl.Datatypes.literal_value_correct.{0} lt
  rw [data_ontology.literal_individual, valueRun, bind_ok]
  cases value with
  | none => exact ⟨none, by simp, by simp⟩
  | some w =>
    obtain ⟨index, indexRun, _, present⟩ := value_index_correct context.values w 0#usize
    simp only [indexRun, bind_ok]
    cases index with
    | none => exact ⟨none, by simp, by simp⟩
    | some i =>
      obtain ⟨h, same⟩ := present i rfl
      exact ⟨some (.Named (valueIndividual i)), by simp [value_individual_eq],
        fun a ha => ⟨w, i, h, rfl, same, (Option.some.inj ha).symm⟩⟩

theorem literal_individuals_correct (context : data_ontology.Context) (literals : alloc.vec.Vec Literal)
    (index : Usize) (out : alloc.vec.Vec Individual)
    (room : out.val.length + (literals.val.length - index.val) ≤ Usize.max) :
    ∃ res, data_ontology.literal_individuals context literals index out = .ok res ∧
      ∀ v, res = some v → List.Forall₂
        (fun a lt => ∃ r, data_ontology.literal_individual context lt = .ok (some r) ∧ r = a)
        (v.val.drop out.val.length) (literals.val.drop index.val) ∧ v.val.take out.val.length = out.val := by
  rw [data_ontology.literal_individuals]
  by_cases inside : index.val < literals.val.length
  · have lookup : literals.index_usize index = .ok literals.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have split := List.drop_eq_getElem_cons inside
    obtain ⟨res, run, _⟩ := literal_individual_correct context literals.val[index.val]
    cases res with
    | none =>
      exact ⟨none, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run], by simp⟩
    | some a =>
      have short : out.val.length < Usize.max := by omega
      obtain ⟨pushed, push, contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out a short)
      obtain ⟨next, advance, nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val + 1 := by simpa using nextValue
      obtain ⟨rest, restRun, restFacts⟩ := literal_individuals_correct context literals next pushed
        (by rw [contents, nextIndex]; simp; omega)
      refine ⟨rest, by simp [UScalar.lt_equiv, inside, alloc.vec.Vec.index_slice_index, lookup, run, push,
        advance, restRun], fun v hv => ?_⟩
      obtain ⟨tail, prefix'⟩ := restFacts v hv
      rw [contents] at tail prefix'
      rw [nextIndex] at tail
      have pushedLength : (out.val ++ [a]).length = out.val.length + 1 := by simp
      rw [pushedLength] at tail prefix'
      have vLength : out.val.length < v.val.length := by
        have := congrArg List.length prefix'
        simp at this; omega
      refine ⟨?_, ?_⟩
      · rw [split, List.drop_eq_getElem_cons vLength]
        have head : v.val[out.val.length] = a := by
          have := congrArg (fun l => l[out.val.length]?) prefix'
          simp [List.getElem?_take] at this
          rw [List.getElem?_eq_getElem vLength] at this
          simpa using this
        rw [head]
        exact .cons ⟨a, run, rfl⟩ tail
      · have := congrArg (List.take out.val.length) prefix'
        simpa [List.take_take] using this
  · refine ⟨some out, by simp [UScalar.lt_equiv, inside], fun v hv => ?_⟩
    cases hv
    simp [List.drop_eq_nil_iff.mpr (show literals.val.length ≤ index.val by omega)]
termination_by literals.val.length - index.val
decreasing_by omega

end Rowl.DataEncoding
