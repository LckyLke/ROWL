import Rowl.RangeEquality

namespace Rowl.ClassEquality
open Aeneas Aeneas.Std RowlRust.model RowlRust.class_equality
open Rowl.AssertionEquality
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList,List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]; omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val,Slice.val]; omega

def Members (xs : AtLeastTwo ClassExpression) : List ClassExpression := xs.first :: xs.second :: xs.rest.val

private theorem member_size (xs : AtLeastTwo ClassExpression) (child : ClassExpression) (member : child ∈ Members xs) :
    sizeOf child < sizeOf xs := by
  simp only [Members,List.mem_cons] at member
  rcases member with rfl | rfl | member
  · cases xs; simp +arith
  · cases xs; simp +arith
  · have := vec_mem_size xs.rest member
    cases xs; simp_all; omega


open Rowl.RangeEquality (RangeEq RangeSetEq SetEq)
def ThingBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,50#u8,47#u8,48#u8,55#u8,47#u8,111#u8,119#u8,108#u8,35#u8,84#u8,104#u8,105#u8,110#u8,103#u8]
def LiteralBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,48#u8,47#u8,48#u8,49#u8,47#u8,114#u8,100#u8,102#u8,45#u8,115#u8,99#u8,104#u8,101#u8,109#u8,97#u8,35#u8,76#u8,105#u8,116#u8,101#u8,114#u8,97#u8,108#u8]

/-- Only the named default class, not any logically universal expression. -/
def IsThing (value : ClassExpression) : Prop :=
  match value with
  | .Class c => c.iri.spelling.val = ThingBytes
  | _ => False
def NothingBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,50#u8,47#u8,48#u8,55#u8,47#u8,111#u8,119#u8,108#u8,35#u8,78#u8,111#u8,116#u8,104#u8,105#u8,110#u8,103#u8]
/-- Only the named built-in empty class, which the tableau reads as bottom. -/
def IsNothing (value : ClassExpression) : Prop :=
  match value with
  | .Class c => c.iri.spelling.val = NothingBytes
  | _ => False
/-- Only the named default data range, retaining exact IRI identity. -/
def IsLiteral (value : DataRange) : Prop :=
  match value with
  | .Datatype d => d.iri.spelling.val = LiteralBytes
  | _ => False
/-- Omitted data cardinality qualifiers expand to the named top data range. -/
def OptionalRangeEq (left right : Option DataRange) : Prop :=
  match left,right with
  | none,none => True
  | some a,some b => RangeEq a b
  | none,some a | some a,none => IsLiteral a
/-- Complete recursive structure with unordered member sets and the normative
    defaults for omitted cardinality qualifiers; no logical simplification. -/
def ClassEq (left right : ClassExpression) : Prop :=
  match left,right with
  | .Class a,.Class b => a = b
  | .ObjectIntersectionOf xs,.ObjectIntersectionOf ys | .ObjectUnionOf xs,.ObjectUnionOf ys =>
    (∀ a : {a // a ∈ Members xs}, ∃ b : {b // b ∈ Members ys}, ClassEq a.val b.val) ∧
    (∀ b : {b // b ∈ Members ys}, ∃ a : {a // a ∈ Members xs}, ClassEq b.val a.val)
  | .ObjectComplementOf a,.ObjectComplementOf b => ClassEq a b
  | .ObjectOneOf xs,.ObjectOneOf ys => SetEq xs.elements ys.elements
  | .ObjectSomeValuesFrom p a,.ObjectSomeValuesFrom q b
  | .ObjectAllValuesFrom p a,.ObjectAllValuesFrom q b => p = q ∧ ClassEq a b
  | .ObjectHasValue p a,.ObjectHasValue q b => p = q ∧ a = b
  | .ObjectHasSelf p,.ObjectHasSelf q => p = q
  | .ObjectMinCardinality n p xs,.ObjectMinCardinality m q ys => n = m ∧ p = q ∧
      match xs,ys with
      | none,none => True
      | some a,some b => ClassEq a b
      | none,some a | some a,none => IsThing a
  | .ObjectMaxCardinality n p xs,.ObjectMaxCardinality m q ys => n = m ∧ p = q ∧
      match xs,ys with
      | none,none => True
      | some a,some b => ClassEq a b
      | none,some a | some a,none => IsThing a
  | .ObjectExactCardinality n p xs,.ObjectExactCardinality m q ys => n = m ∧ p = q ∧
      match xs,ys with
      | none,none => True
      | some a,some b => ClassEq a b
      | none,some a | some a,none => IsThing a
  | .DataSomeValuesFrom p a,.DataSomeValuesFrom q b
  | .DataAllValuesFrom p a,.DataAllValuesFrom q b => p = q ∧ RangeEq a b
  | .DataHasValue p a,.DataHasValue q b => p = q ∧ a = b
  | .DataMinCardinality n p xs,.DataMinCardinality m q ys => n = m ∧ p = q ∧ OptionalRangeEq xs ys
  | .DataMaxCardinality n p xs,.DataMaxCardinality m q ys => n = m ∧ p = q ∧ OptionalRangeEq xs ys
  | .DataExactCardinality n p xs,.DataExactCardinality m q ys => n = m ∧ p = q ∧ OptionalRangeEq xs ys
  | _,_ => False
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := member_size xs a.val a.property; have := member_size ys b.val b.property; omega)

def ClassSetEq (left right : List ClassExpression) : Prop :=
  (∀ a ∈ left, ∃ b ∈ right, ClassEq a b) ∧ (∀ b ∈ right, ∃ a ∈ left, ClassEq b a)
def OptionalClassEq (left right : Option ClassExpression) : Prop :=
  match left,right with
  | none,none => True
  | some a,some b => ClassEq a b
  | none,some a | some a,none => IsThing a

private theorem iri_eq (left right : Iri) : left.spelling.val = right.spelling.val ↔ left = right := by
  cases left; cases right; simp
private theorem class_eq (left right : Class) :
    left.iri.spelling.val = right.iri.spelling.val ↔ left = right := by
  cases left; cases right; simp [iri_eq]
private theorem data_property_eq (left right : DataProperty) :
    left.iri.spelling.val = right.iri.spelling.val ↔ left = right := by
  cases left; cases right; simp [iri_eq]

/-- Actual exact natural comparison is total, including arbitrary cardinalities. -/
theorem same_natural_total_correct (left right : RowlRust.probes.Natural) :
    same_natural left right = .ok (decide (left = right)) := by
  induction left generalizing right with
  | Zero => cases right <;> simp [same_natural]
  | Succ left ih => cases right <;> simp [same_natural,ih]

private theorem natural_value_injective : Function.Injective Rowl.Probes.naturalValue := by
  intro left
  induction left with
  | Zero => intro right equal; cases right <;> simp_all [Rowl.Probes.naturalValue]
  | Succ left ih =>
    intro right equal
    cases right with
    | Zero => simp [Rowl.Probes.naturalValue] at equal
    | Succ right =>
      have same := ih (by simpa [Rowl.Probes.naturalValue] using equal)
      simp [same]
/-- The compared unary values are exactly their mathematical natural numbers. -/
theorem same_natural_value_total_correct (left right : RowlRust.probes.Natural) :
    same_natural left right = .ok (decide (Rowl.Probes.naturalValue left = Rowl.Probes.naturalValue right)) := by
  rw [same_natural_total_correct]
  exact congrArg Result.ok (decide_eq_decide.mpr natural_value_injective.eq_iff.symm)
private theorem equal_total (key : alloc.vec.Vec U8) (pattern : Slice U8)
    (equalLength : key.val.length = pattern.val.length) (index : Usize) :
    equal_from key pattern index = .ok (decide (key.val.drop index.val = pattern.val.drop index.val)) := by
  rw [equal_from]
  by_cases h : index.val < key.val.length
  · have hr : index.val < pattern.val.length := by omega
    have hkIndex : key.index_usize index = .ok key.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hpIndex : pattern.index_usize index = .ok pattern.val[index.val] := by
      simp [Slice.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : key.val[index.val] = pattern.val[index.val]
    · have size := key.property
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
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

private theorem same_pattern_total (key : alloc.vec.Vec U8) (pattern : Slice U8) :
    same_pattern key pattern = .ok (decide (key.val = pattern.val)) := by
  rw [same_pattern]
  by_cases h : key.val.length = pattern.val.length
  · have ih := equal_total key pattern h 0#usize
    simpa [h] using ih
  · have unequal : key.val ≠ pattern.val := fun eq => h (congrArg List.length eq)
    simp [h, unequal]


/-- Exact built-in object filler recognition, without logical equivalence. -/
theorem is_thing_total_correct (value : ClassExpression) :
    is_thing value = .ok (decide (IsThing value)) := by
  cases value <;> simp [is_thing,IsThing,same_pattern_total,ThingBytes,Array.to_slice,Array.make,lift]
/-- Exact built-in empty-class recognition, without logical equivalence. -/
theorem is_nothing_total_correct (value : ClassExpression) :
    is_nothing value = .ok (decide (IsNothing value)) := by
  cases value <;> simp [is_nothing,IsNothing,same_pattern_total,NothingBytes,Array.to_slice,Array.make,lift]
/-- Exact built-in data filler recognition. -/
theorem is_literal_total_correct (value : DataRange) :
    is_literal value = .ok (decide (IsLiteral value)) := by
  cases value <;> simp [is_literal,IsLiteral,same_pattern_total,LiteralBytes,Array.to_slice,Array.make,lift]
/-- Optional data fillers compare exactly after inserting the normative default. -/
theorem same_optional_range_total_correct (left right : Option DataRange) :
    same_optional_range left right = .ok (decide (OptionalRangeEq left right)) := by
  cases left <;> cases right <;>
    simp [same_optional_range,OptionalRangeEq,Rowl.RangeEquality.same_range_total_correct,is_literal_total_correct]
private theorem set_eq_iff_subsets {α : Type} (left right : List α) :
    SetEq left right ↔ (∀ a ∈ left, a ∈ right) ∧ (∀ b ∈ right, b ∈ left) := by
  constructor
  · intro equal; exact ⟨fun a mem => (equal a).mp mem,fun b mem => (equal b).mpr mem⟩
  · rintro ⟨forward,backward⟩ a; exact ⟨forward a,backward a⟩


private theorem individual_contains_total (values : alloc.vec.Vec Individual) (sought : Individual) (index : Usize) :
    individual_contains_from values sought index = .ok (decide (sought ∈ values.val.drop index.val)) := by
  rw [individual_contains_from]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have splitting : (sought ∈ values.val.drop index.val) ↔
        sought = values.val[index.val] ∨ sought ∈ values.val.drop (index.val+1) := by
      rw [List.drop_eq_getElem_cons inside]; exact List.mem_cons
    have splitBool : decide (sought ∈ values.val.drop index.val) =
        decide (sought = values.val[index.val] ∨ sought ∈ values.val.drop (index.val+1)) :=
      decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases equal : sought = values.val[index.val]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,same_individual_value_total_correct,equal]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := individual_contains_total values sought next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,same_individual_value_total_correct,equal,advance,recursive,nv]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem individual_member_total (sought : Individual) (values : NonEmpty Individual) :
    individual_member sought values = .ok (decide (sought ∈ values.elements)) := by
  rw [individual_member]
  by_cases equal : sought = values.first <;>
    simp [same_individual_value_total_correct,equal,individual_contains_total,NonEmpty.elements]

private theorem individual_subset_from_total (left : alloc.vec.Vec Individual) (right : NonEmpty Individual) (index : Usize) :
    individual_subset_from left right index = .ok (decide (∀ a ∈ left.val.drop index.val, a ∈ right.elements)) := by
  rw [individual_subset_from]
  by_cases inside : index.val < left.val.length
  · have lookup : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have splitting : (∀ a ∈ left.val.drop index.val, a ∈ right.elements) ↔
        left.val[index.val] ∈ right.elements ∧ ∀ a ∈ left.val.drop (index.val+1), a ∈ right.elements := by
      rw [List.drop_eq_getElem_cons inside]; exact List.forall_mem_cons
    have splitBool : decide (∀ a ∈ left.val.drop index.val, a ∈ right.elements) =
        decide (left.val[index.val] ∈ right.elements ∧ ∀ a ∈ left.val.drop (index.val+1), a ∈ right.elements) :=
      decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases member : left.val[index.val] ∈ right.elements
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := individual_subset_from_total left right next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,individual_member_total,member,advance,recursive,nv]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,individual_member_total,member]
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by left.val.length - index.val
decreasing_by omega

private theorem individual_subset_total (left right : NonEmpty Individual) :
    individual_subset left right = .ok (decide (∀ a ∈ left.elements, a ∈ right.elements)) := by
  rw [individual_subset,individual_member_total]
  by_cases member : left.first ∈ right.elements
  · simp only [member,decide_true,bind_ok,↓reduceIte,individual_subset_from_total,
      show (0#usize).val = 0 from rfl,List.drop_zero]
    apply congrArg Result.ok
    exact decide_eq_decide.mpr (by simp only [NonEmpty.elements,List.forall_mem_cons]; exact (and_iff_right member).symm)
  · simp only [member,decide_false,bind_ok,Bool.false_eq_true,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_false (by intro valid; exact member (valid _ (by simp [NonEmpty.elements])))).symm

/-- Exact unordered individual membership; equivalent raw repetitions count once. -/
theorem same_individual_set_total_correct (left right : NonEmpty Individual) :
    same_individual_set left right = .ok (decide (SetEq left.elements right.elements)) := by
  rw [same_individual_set,individual_subset_total]
  by_cases forward : ∀ a ∈ left.elements, a ∈ right.elements
  · have yes := decide_eq_true forward
    simp only [yes,bind_ok,↓reduceIte,individual_subset_total]
    apply congrArg Result.ok
    exact decide_eq_decide.mpr ((and_iff_right forward).symm.trans (set_eq_iff_subsets _ _).symm)
  · have no := decide_eq_false forward
    simp only [no,bind_ok,Bool.false_eq_true,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_false (fun equal => forward ((set_eq_iff_subsets _ _).mp equal).1)).symm

private theorem class_contains_total_of (values : alloc.vec.Vec ClassExpression) (sought : ClassExpression)
    (child : ∀ item ∈ values.val, same_class sought item = .ok (decide (ClassEq sought item)))
    (index : Usize) :
    class_contains_from values sought index =
      .ok (decide (∃ item ∈ values.val.drop index.val, ClassEq sought item)) := by
  rw [class_contains_from]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := child values.val[index.val] (List.getElem_mem inside)
    have splitting : (∃ item ∈ values.val.drop index.val, ClassEq sought item) ↔
        ClassEq sought values.val[index.val] ∨
          ∃ item ∈ values.val.drop (index.val+1), ClassEq sought item := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons,exists_eq_or_imp]
    have splitBool : decide (∃ item ∈ values.val.drop index.val, ClassEq sought item) =
        decide (ClassEq sought values.val[index.val] ∨
          ∃ item ∈ values.val.drop (index.val+1), ClassEq sought item) := decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases found : ClassEq sought values.val[index.val]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_true,true_or]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := class_contains_total_of values sought child next
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_false,
        Bool.false_eq_true,advance,recursive,nv,false_or]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,empty,
      List.not_mem_nil,false_and,exists_false,decide_false]
termination_by values.val.length - index.val
decreasing_by omega

private theorem class_member_total_of (sought : ClassExpression) (values : AtLeastTwo ClassExpression)
    (child : ∀ item ∈ Members values, same_class sought item = .ok (decide (ClassEq sought item))) :
    class_member sought values = .ok (decide (∃ item ∈ Members values, ClassEq sought item)) := by
  rw [class_member]
  have first := child values.first (by simp [Members])
  have second := child values.second (by simp [Members])
  have rest := class_contains_total_of values.rest sought
    (fun item mem => child item (by simp only [Members,List.mem_cons]; exact Or.inr (Or.inr mem))) 0#usize
  have splitting : (∃ item ∈ Members values, ClassEq sought item) ↔
      ClassEq sought values.first ∨ ClassEq sought values.second ∨ ∃ item ∈ values.rest.val, ClassEq sought item := by
    simp only [Members,List.mem_cons,exists_eq_or_imp]
  have splitBool : decide (∃ item ∈ Members values, ClassEq sought item) =
      decide (ClassEq sought values.first ∨ ClassEq sought values.second ∨ ∃ item ∈ values.rest.val, ClassEq sought item) :=
    decide_eq_decide.mpr splitting
  rw [splitBool]
  by_cases a : ClassEq sought values.first <;> by_cases b : ClassEq sought values.second <;>
    simp only [first,second,rest,show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,
      a,b,decide_true,decide_false,↓reduceIte,Bool.false_eq_true,true_or,or_true,false_or]

private theorem class_subset_from_total_of (left : alloc.vec.Vec ClassExpression) (right : AtLeastTwo ClassExpression)
    (child : ∀ a ∈ left.val, ∀ b ∈ Members right, same_class a b = .ok (decide (ClassEq a b)))
    (index : Usize) :
    class_subset_from left right index = .ok (decide (∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, ClassEq a b)) := by
  rw [class_subset_from]
  by_cases inside : index.val < left.val.length
  · have lookup : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := class_member_total_of left.val[index.val] right
      (child left.val[index.val] (List.getElem_mem inside))
    have splitting : (∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, ClassEq a b) ↔
        (∃ b ∈ Members right, ClassEq left.val[index.val] b) ∧
          ∀ a ∈ left.val.drop (index.val+1), ∃ b ∈ Members right, ClassEq a b := by
      rw [List.drop_eq_getElem_cons inside]; exact List.forall_mem_cons
    have splitBool : decide (∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, ClassEq a b) =
        decide ((∃ b ∈ Members right, ClassEq left.val[index.val] b) ∧
          ∀ a ∈ left.val.drop (index.val+1), ∃ b ∈ Members right, ClassEq a b) := decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases found : ∃ b ∈ Members right, ClassEq left.val[index.val] b
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := class_subset_from_total_of left right child next
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_true,advance,recursive,nv,true_and]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_false,Bool.false_eq_true,false_and]
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have vacuous : ∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, ClassEq a b := by
      rw [empty]; intro a mem; cases mem
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte]
    exact congrArg Result.ok (decide_eq_true vacuous).symm
termination_by left.val.length - index.val
decreasing_by omega

private theorem class_subset_total_of (left right : AtLeastTwo ClassExpression)
    (child : ∀ a ∈ Members left, ∀ b ∈ Members right, same_class a b = .ok (decide (ClassEq a b))) :
    class_subset left right = .ok (decide (∀ a ∈ Members left, ∃ b ∈ Members right, ClassEq a b)) := by
  have first := class_member_total_of left.first right (child left.first (by simp [Members]))
  have second := class_member_total_of left.second right (child left.second (by simp [Members]))
  have tail := class_subset_from_total_of left.rest right
    (fun a mem => child a (by simp only [Members,List.mem_cons]; exact Or.inr (Or.inr mem))) 0#usize
  have splitting : (∀ a ∈ Members left, ∃ b ∈ Members right, ClassEq a b) ↔
      (∃ b ∈ Members right, ClassEq left.first b) ∧
      (∃ b ∈ Members right, ClassEq left.second b) ∧
      ∀ a ∈ left.rest.val, ∃ b ∈ Members right, ClassEq a b := by
    simp only [Members,List.forall_mem_cons]
  have splitBool : decide (∀ a ∈ Members left, ∃ b ∈ Members right, ClassEq a b) =
      decide ((∃ b ∈ Members right, ClassEq left.first b) ∧
        (∃ b ∈ Members right, ClassEq left.second b) ∧
        ∀ a ∈ left.rest.val, ∃ b ∈ Members right, ClassEq a b) := decide_eq_decide.mpr splitting
  rw [class_subset,splitBool]
  by_cases a : ∃ b ∈ Members right, ClassEq left.first b <;>
    by_cases b : ∃ b ∈ Members right, ClassEq left.second b <;>
    simp only [first,second,tail,show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,
      a,b,decide_true,decide_false,↓reduceIte,Bool.false_eq_true,true_and,false_and,and_false]

private theorem class_set_total_of (left right : AtLeastTwo ClassExpression)
    (forward : ∀ a ∈ Members left, ∀ b ∈ Members right, same_class a b = .ok (decide (ClassEq a b)))
    (backward : ∀ b ∈ Members right, ∀ a ∈ Members left, same_class b a = .ok (decide (ClassEq b a))) :
    same_class_set left right = .ok (decide (ClassSetEq (Members left) (Members right))) := by
  rw [same_class_set,class_subset_total_of left right forward]
  by_cases all : ∀ a ∈ Members left, ∃ b ∈ Members right, ClassEq a b
  · have yes := decide_eq_true all
    simp only [yes,bind_ok,↓reduceIte,class_subset_total_of right left backward]
    exact congrArg Result.ok (decide_eq_decide.mpr (and_iff_right all).symm)
  · have no := decide_eq_false all
    simp only [no,bind_ok,Bool.false_eq_true,↓reduceIte]
    exact congrArg Result.ok (decide_eq_false (fun equal : ClassSetEq _ _ => all equal.1)).symm



private theorem optional_class_total_of (left right : Option ClassExpression)
    (child : ∀ a b, left = some a → right = some b → same_class a b = .ok (decide (ClassEq a b))) :
    same_optional_class left right = .ok (decide (OptionalClassEq left right)) := by
  cases left <;> cases right <;>
    simp [same_optional_class,OptionalClassEq,is_thing_total_correct,child]

/-- Every actual Rust class comparison terminates and decides the independent
    full recursive structure, including omitted qualifiers and nested sets. -/
theorem same_class_total_correct (left right : ClassExpression) :
    same_class left right = .ok (decide (ClassEq left right)) := by
  cases hLeft : left <;> cases hRight : right <;> try simp [same_class,ClassEq]
  case Class.Class a b =>
    simp [Rowl.Symbols.same_spelling_total_correct,class_eq]
  case ObjectIntersectionOf.ObjectIntersectionOf xs ys =>
    have nested := class_set_total_of xs ys
      (fun a aMem b bMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_class_total_correct a b)
      (fun b bMem a aMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_class_total_correct b a)
    simpa [ClassSetEq] using nested
  case ObjectUnionOf.ObjectUnionOf xs ys =>
    have nested := class_set_total_of xs ys
      (fun a aMem b bMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_class_total_correct a b)
      (fun b bMem a aMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_class_total_correct b a)
    simpa [ClassSetEq] using nested
  case ObjectComplementOf.ObjectComplementOf a b =>
    exact same_class_total_correct a b
  case ObjectOneOf.ObjectOneOf xs ys =>
    exact same_individual_set_total_correct xs ys
  case ObjectSomeValuesFrom.ObjectSomeValuesFrom p a q b =>
    have nested := same_class_total_correct a b
    by_cases property : p = q <;> simp [same_property_total_correct,property,nested]
  case ObjectAllValuesFrom.ObjectAllValuesFrom p a q b =>
    have nested := same_class_total_correct a b
    by_cases property : p = q <;> simp [same_property_total_correct,property,nested]
  case ObjectHasValue.ObjectHasValue p a q b =>
    by_cases property : p = q <;> simp [same_property_total_correct,property,same_individual_value_total_correct]
  case ObjectHasSelf.ObjectHasSelf p q =>
    exact same_property_total_correct p q
  case ObjectMinCardinality.ObjectMinCardinality n p xs m q ys =>
    rw [ClassEq.eq_def]
    have nested := optional_class_total_of xs ys (fun a b ax bys =>
      have sa : sizeOf a < sizeOf xs := by rw [ax]; simp +arith
      have sb : sizeOf b < sizeOf ys := by rw [bys]; simp +arith
      same_class_total_correct a b)
    by_cases natural : n = m <;> by_cases property : p = q <;>
      simp [same_natural_total_correct,same_property_total_correct,natural,property,nested,OptionalClassEq]
  case ObjectMaxCardinality.ObjectMaxCardinality n p xs m q ys =>
    rw [ClassEq.eq_def]
    have nested := optional_class_total_of xs ys (fun a b ax bys =>
      have sa : sizeOf a < sizeOf xs := by rw [ax]; simp +arith
      have sb : sizeOf b < sizeOf ys := by rw [bys]; simp +arith
      same_class_total_correct a b)
    by_cases natural : n = m <;> by_cases property : p = q <;>
      simp [same_natural_total_correct,same_property_total_correct,natural,property,nested,OptionalClassEq]
  case ObjectExactCardinality.ObjectExactCardinality n p xs m q ys =>
    rw [ClassEq.eq_def]
    have nested := optional_class_total_of xs ys (fun a b ax bys =>
      have sa : sizeOf a < sizeOf xs := by rw [ax]; simp +arith
      have sb : sizeOf b < sizeOf ys := by rw [bys]; simp +arith
      same_class_total_correct a b)
    by_cases natural : n = m <;> by_cases property : p = q <;>
      simp [same_natural_total_correct,same_property_total_correct,natural,property,nested,OptionalClassEq]
  case DataSomeValuesFrom.DataSomeValuesFrom p a q b =>
    by_cases property : p = q <;>
      simp [Rowl.Symbols.same_spelling_total_correct,data_property_eq,property,Rowl.RangeEquality.same_range_total_correct]
  case DataAllValuesFrom.DataAllValuesFrom p a q b =>
    by_cases property : p = q <;>
      simp [Rowl.Symbols.same_spelling_total_correct,data_property_eq,property,Rowl.RangeEquality.same_range_total_correct]
  case DataHasValue.DataHasValue p a q b =>
    by_cases property : p = q <;> simp [Rowl.Symbols.same_spelling_total_correct,data_property_eq,property,same_literal_total_correct]
  case DataMinCardinality.DataMinCardinality n p xs m q ys =>
    by_cases natural : n = m <;> by_cases property : p = q <;>
      simp [same_natural_total_correct,Rowl.Symbols.same_spelling_total_correct,data_property_eq,natural,property,same_optional_range_total_correct]
  case DataMaxCardinality.DataMaxCardinality n p xs m q ys =>
    by_cases natural : n = m <;> by_cases property : p = q <;>
      simp [same_natural_total_correct,Rowl.Symbols.same_spelling_total_correct,data_property_eq,natural,property,same_optional_range_total_correct]
  case DataExactCardinality.DataExactCardinality n p xs m q ys =>
    by_cases natural : n = m <;> by_cases property : p = q <;>
      simp [same_natural_total_correct,Rowl.Symbols.same_spelling_total_correct,data_property_eq,natural,property,same_optional_range_total_correct]
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals simp only [hLeft,hRight,ClassExpression.ObjectIntersectionOf.sizeOf_spec,
    ClassExpression.ObjectUnionOf.sizeOf_spec,ClassExpression.ObjectComplementOf.sizeOf_spec,
    ClassExpression.ObjectSomeValuesFrom.sizeOf_spec,ClassExpression.ObjectAllValuesFrom.sizeOf_spec,
    ClassExpression.ObjectMinCardinality.sizeOf_spec,ClassExpression.ObjectMaxCardinality.sizeOf_spec,
    ClassExpression.ObjectExactCardinality.sizeOf_spec]
  all_goals omega
/-- Exact unordered class-member association, retaining nesting. -/
theorem same_class_set_total_correct (left right : AtLeastTwo ClassExpression) :
    same_class_set left right = .ok (decide (ClassSetEq (Members left) (Members right))) :=
  class_set_total_of left right (fun a _ b _ => same_class_total_correct a b)
    (fun b _ a _ => same_class_total_correct b a)
/-- Exact object cardinality qualifiers after inserting owl:Thing when omitted. -/
theorem same_optional_class_total_correct (left right : Option ClassExpression) :
    same_optional_class left right = .ok (decide (OptionalClassEq left right)) :=
  optional_class_total_of left right (fun a b _ _ => same_class_total_correct a b)

private theorem range_literal_left (left right : DataRange) (lit : IsLiteral left)
    (equal : RangeEq left right) : IsLiteral right := by
  cases left <;> cases right <;> simp_all [IsLiteral,Rowl.RangeEquality.RangeEq]
private theorem range_literals_equal (left right : DataRange) (a : IsLiteral left)
    (b : IsLiteral right) : RangeEq left right := by
  cases left <;> cases right <;> simp only [IsLiteral] at a b; try contradiction
  rename_i x y
  cases x; cases y
  simp_all [Rowl.RangeEquality.RangeEq,iri_eq]
  exact (iri_eq _ _).mp (a.trans b.symm)
private theorem optional_range_refl (value : Option DataRange) : OptionalRangeEq value value := by
  cases value <;> simp [OptionalRangeEq,Rowl.RangeEquality.range_eq_refl]
private theorem optional_range_symm (left right : Option DataRange) (equal : OptionalRangeEq left right) :
    OptionalRangeEq right left := by
  cases left <;> cases right <;> simp_all [OptionalRangeEq,Rowl.RangeEquality.range_eq_symm]
private theorem optional_range_trans (left middle right : Option DataRange)
    (first : OptionalRangeEq left middle) (second : OptionalRangeEq middle right) : OptionalRangeEq left right := by
  cases left <;> cases middle <;> cases right <;> simp only [OptionalRangeEq] at first second ⊢
  case none.none.some c =>
    exact second
  case none.some.some b c =>
    exact range_literal_left b c first second
  case some.none.none a =>
    exact first
  case some.none.some a c =>
    exact range_literals_equal a c first second
  case some.some.none a b =>
    exact range_literal_left b a second (Rowl.RangeEquality.range_eq_symm a b first)
  case some.some.some a b c =>
    exact Rowl.RangeEquality.range_eq_trans a b c first second

private theorem class_thing_left (left right : ClassExpression) (thing : IsThing left)
    (equal : ClassEq left right) : IsThing right := by
  cases left <;> cases right <;> simp_all [IsThing,ClassEq]
private theorem class_things_equal (left right : ClassExpression) (a : IsThing left)
    (b : IsThing right) : ClassEq left right := by
  cases left <;> cases right <;> simp only [IsThing] at a b; try contradiction
  rename_i x y
  cases x; cases y
  simp_all [ClassEq,iri_eq]
  exact (iri_eq _ _).mp (a.trans b.symm)
private theorem optional_class_trans_of (left middle right : Option ClassExpression)
    (first : OptionalClassEq left middle) (second : OptionalClassEq middle right)
    (compose : ∀ a b c, left = some a → middle = some b → right = some c →
      ClassEq a b → ClassEq b c → ClassEq a c)
    (reverse : ∀ a b, left = some a → middle = some b → ClassEq a b → ClassEq b a) :
    OptionalClassEq left right := by
  cases left <;> cases middle <;> cases right <;> simp only [OptionalClassEq] at first second ⊢
  case none.none.some c =>
    exact second
  case none.some.some b c =>
    exact class_thing_left b c first second
  case some.none.none a =>
    exact first
  case some.none.some a c =>
    exact class_things_equal a c first second
  case some.some.none a b =>
    exact class_thing_left b a second (reverse a b rfl rfl first)
  case some.some.some a b c =>
    exact compose a b c rfl rfl rfl first second

/-- Reflexivity includes raw repetitions and omitted cardinality qualifiers. -/
theorem class_eq_refl (value : ClassExpression) : ClassEq value value := by
  cases h : value with
  | Class c =>
    rw [ClassEq.eq_def]
  | ObjectIntersectionOf xs =>
    rw [ClassEq.eq_def]
    constructor <;> intro child <;> exact ⟨child,class_eq_refl child.val⟩
  | ObjectUnionOf xs =>
    rw [ClassEq.eq_def]
    constructor <;> intro child <;> exact ⟨child,class_eq_refl child.val⟩
  | ObjectComplementOf x =>
    rw [ClassEq.eq_def]
    exact class_eq_refl x
  | ObjectOneOf xs =>
    rw [ClassEq.eq_def]
    exact fun _ => Iff.rfl
  | ObjectSomeValuesFrom p x =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,class_eq_refl x⟩
  | ObjectAllValuesFrom p x =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,class_eq_refl x⟩
  | ObjectHasValue p i =>
    rw [ClassEq.eq_def]
    simp
  | ObjectHasSelf p =>
    rw [ClassEq.eq_def]
  | ObjectMinCardinality n p xs =>
    rw [ClassEq.eq_def]
    refine ⟨rfl,rfl,?_⟩
    cases xs with
    | none => trivial
    | some child => exact class_eq_refl child
  | ObjectMaxCardinality n p xs =>
    rw [ClassEq.eq_def]
    refine ⟨rfl,rfl,?_⟩
    cases xs with
    | none => trivial
    | some child => exact class_eq_refl child
  | ObjectExactCardinality n p xs =>
    rw [ClassEq.eq_def]
    refine ⟨rfl,rfl,?_⟩
    cases xs with
    | none => trivial
    | some child => exact class_eq_refl child
  | DataSomeValuesFrom p x =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,Rowl.RangeEquality.range_eq_refl x⟩
  | DataAllValuesFrom p x =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,Rowl.RangeEquality.range_eq_refl x⟩
  | DataHasValue p l =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,rfl⟩
  | DataMinCardinality n p xs =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,rfl,optional_range_refl xs⟩
  | DataMaxCardinality n p xs =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,rfl,optional_range_refl xs⟩
  | DataExactCardinality n p xs =>
    rw [ClassEq.eq_def]
    exact ⟨rfl,rfl,optional_range_refl xs⟩
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := member_size xs child.val child.property; omega)

/-- Structural class equivalence is symmetric for every standard constructor. -/
theorem class_eq_symm (left right : ClassExpression) (equal : ClassEq left right) : ClassEq right left := by
  cases hLeft : left <;> cases hRight : right <;> simp only [hLeft,hRight] at equal ⊢
  all_goals rw [ClassEq.eq_def] at equal ⊢
  all_goals dsimp only at equal ⊢
  case Class.Class a b =>
    exact equal.symm
  case ObjectIntersectionOf.ObjectIntersectionOf xs ys =>
    exact ⟨equal.2,equal.1⟩
  case ObjectUnionOf.ObjectUnionOf xs ys =>
    exact ⟨equal.2,equal.1⟩
  case ObjectComplementOf.ObjectComplementOf a b =>
    exact class_eq_symm a b equal
  case ObjectOneOf.ObjectOneOf xs ys =>
    exact fun x => (equal x).symm
  case ObjectSomeValuesFrom.ObjectSomeValuesFrom p a q b =>
    exact ⟨equal.1.symm,class_eq_symm a b equal.2⟩
  case ObjectAllValuesFrom.ObjectAllValuesFrom p a q b =>
    exact ⟨equal.1.symm,class_eq_symm a b equal.2⟩
  case ObjectHasValue.ObjectHasValue p a q b =>
    exact ⟨equal.1.symm,equal.2.symm⟩
  case ObjectHasSelf.ObjectHasSelf p q =>
    exact equal.symm
  case ObjectMinCardinality.ObjectMinCardinality n p xs m q ys =>
    refine ⟨equal.1.symm,equal.2.1.symm,?_⟩
    cases xs <;> cases ys <;> simp only at equal ⊢
    case none.some b => exact equal.2.2
    case some.none a => exact equal.2.2
    case some.some a b => exact class_eq_symm a b equal.2.2
  case ObjectMaxCardinality.ObjectMaxCardinality n p xs m q ys =>
    refine ⟨equal.1.symm,equal.2.1.symm,?_⟩
    cases xs <;> cases ys <;> simp only at equal ⊢
    case none.some b => exact equal.2.2
    case some.none a => exact equal.2.2
    case some.some a b => exact class_eq_symm a b equal.2.2
  case ObjectExactCardinality.ObjectExactCardinality n p xs m q ys =>
    refine ⟨equal.1.symm,equal.2.1.symm,?_⟩
    cases xs <;> cases ys <;> simp only at equal ⊢
    case none.some b => exact equal.2.2
    case some.none a => exact equal.2.2
    case some.some a b => exact class_eq_symm a b equal.2.2
  case DataSomeValuesFrom.DataSomeValuesFrom p a q b =>
    exact ⟨equal.1.symm,Rowl.RangeEquality.range_eq_symm a b equal.2⟩
  case DataAllValuesFrom.DataAllValuesFrom p a q b =>
    exact ⟨equal.1.symm,Rowl.RangeEquality.range_eq_symm a b equal.2⟩
  case DataHasValue.DataHasValue p a q b =>
    exact ⟨equal.1.symm,equal.2.symm⟩
  case DataMinCardinality.DataMinCardinality n p xs m q ys =>
    exact ⟨equal.1.symm,equal.2.1.symm,optional_range_symm xs ys equal.2.2⟩
  case DataMaxCardinality.DataMaxCardinality n p xs m q ys =>
    exact ⟨equal.1.symm,equal.2.1.symm,optional_range_symm xs ys equal.2.2⟩
  case DataExactCardinality.DataExactCardinality n p xs m q ys =>
    exact ⟨equal.1.symm,equal.2.1.symm,optional_range_symm xs ys equal.2.2⟩
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals simp_all only [hLeft,hRight,
ClassExpression.Class.sizeOf_spec,ClassExpression.ObjectIntersectionOf.sizeOf_spec,ClassExpression.ObjectUnionOf.sizeOf_spec,ClassExpression.ObjectComplementOf.sizeOf_spec,ClassExpression.ObjectOneOf.sizeOf_spec,ClassExpression.ObjectSomeValuesFrom.sizeOf_spec,ClassExpression.ObjectAllValuesFrom.sizeOf_spec,ClassExpression.ObjectHasValue.sizeOf_spec,ClassExpression.ObjectHasSelf.sizeOf_spec,ClassExpression.ObjectMinCardinality.sizeOf_spec,ClassExpression.ObjectMaxCardinality.sizeOf_spec,ClassExpression.ObjectExactCardinality.sizeOf_spec,ClassExpression.DataSomeValuesFrom.sizeOf_spec,ClassExpression.DataAllValuesFrom.sizeOf_spec,ClassExpression.DataHasValue.sizeOf_spec,ClassExpression.DataMinCardinality.sizeOf_spec,ClassExpression.DataMaxCardinality.sizeOf_spec,ClassExpression.DataExactCardinality.sizeOf_spec]
  all_goals simp_wf
  all_goals omega

/-- Structural class equivalence is transitive through all nested associations. -/
theorem class_eq_trans (left middle right : ClassExpression) (first : ClassEq left middle)
    (second : ClassEq middle right) : ClassEq left right := by
  cases hLeft : left <;> cases hMiddle : middle <;> simp only [hLeft,hMiddle] at first
  all_goals rw [ClassEq.eq_def] at first
  all_goals dsimp only at first
  all_goals cases hRight : right <;> simp only [hLeft,hMiddle,hRight] at second ⊢
  all_goals rw [ClassEq.eq_def] at second ⊢
  all_goals dsimp only at second ⊢
  case Class.Class.Class a b c =>
    exact first.trans second
  case ObjectIntersectionOf.ObjectIntersectionOf.ObjectIntersectionOf xs ys zs =>
    constructor
    · intro a
      obtain ⟨b,ab⟩ := first.1 a
      obtain ⟨c,bc⟩ := second.1 b
      have sa := member_size xs a.val a.property
      have sb := member_size ys b.val b.property
      have sc := member_size zs c.val c.property
      exact ⟨c,class_eq_trans a.val b.val c.val ab bc⟩
    · intro c
      obtain ⟨b,cb⟩ := second.2 c
      obtain ⟨a,ba⟩ := first.2 b
      have sa := member_size xs a.val a.property
      have sb := member_size ys b.val b.property
      have sc := member_size zs c.val c.property
      exact ⟨a,class_eq_trans c.val b.val a.val cb ba⟩
  case ObjectUnionOf.ObjectUnionOf.ObjectUnionOf xs ys zs =>
    constructor
    · intro a
      obtain ⟨b,ab⟩ := first.1 a
      obtain ⟨c,bc⟩ := second.1 b
      have sa := member_size xs a.val a.property
      have sb := member_size ys b.val b.property
      have sc := member_size zs c.val c.property
      exact ⟨c,class_eq_trans a.val b.val c.val ab bc⟩
    · intro c
      obtain ⟨b,cb⟩ := second.2 c
      obtain ⟨a,ba⟩ := first.2 b
      have sa := member_size xs a.val a.property
      have sb := member_size ys b.val b.property
      have sc := member_size zs c.val c.property
      exact ⟨a,class_eq_trans c.val b.val a.val cb ba⟩
  case ObjectComplementOf.ObjectComplementOf.ObjectComplementOf a b c =>
    exact class_eq_trans a b c first second
  case ObjectOneOf.ObjectOneOf.ObjectOneOf xs ys zs =>
    exact fun x => (first x).trans (second x)
  case ObjectSomeValuesFrom.ObjectSomeValuesFrom.ObjectSomeValuesFrom p a q b r c =>
    exact ⟨first.1.trans second.1,class_eq_trans a b c first.2 second.2⟩
  case ObjectAllValuesFrom.ObjectAllValuesFrom.ObjectAllValuesFrom p a q b r c =>
    exact ⟨first.1.trans second.1,class_eq_trans a b c first.2 second.2⟩
  case ObjectHasValue.ObjectHasValue.ObjectHasValue p a q b r c =>
    exact ⟨first.1.trans second.1,first.2.trans second.2⟩
  case ObjectHasSelf.ObjectHasSelf.ObjectHasSelf p q r =>
    exact first.trans second
  case ObjectMinCardinality.ObjectMinCardinality.ObjectMinCardinality n p xs m q ys k r zs =>
    refine ⟨first.1.trans second.1,first.2.1.trans second.2.1,?_⟩
    change OptionalClassEq xs zs
    have one : OptionalClassEq xs ys := first.2.2
    have two : OptionalClassEq ys zs := second.2.2
    exact optional_class_trans_of xs ys zs one two
      (fun a b c ax bys cz ab bc =>
        have sa : sizeOf a < sizeOf xs := by rw [ax]; simp +arith
        have sb : sizeOf b < sizeOf ys := by rw [bys]; simp +arith
        have sc : sizeOf c < sizeOf zs := by rw [cz]; simp +arith
        class_eq_trans a b c ab bc)
      (fun a b _ _ ab => class_eq_symm a b ab)
  case ObjectMaxCardinality.ObjectMaxCardinality.ObjectMaxCardinality n p xs m q ys k r zs =>
    refine ⟨first.1.trans second.1,first.2.1.trans second.2.1,?_⟩
    change OptionalClassEq xs zs
    have one : OptionalClassEq xs ys := first.2.2
    have two : OptionalClassEq ys zs := second.2.2
    exact optional_class_trans_of xs ys zs one two
      (fun a b c ax bys cz ab bc =>
        have sa : sizeOf a < sizeOf xs := by rw [ax]; simp +arith
        have sb : sizeOf b < sizeOf ys := by rw [bys]; simp +arith
        have sc : sizeOf c < sizeOf zs := by rw [cz]; simp +arith
        class_eq_trans a b c ab bc)
      (fun a b _ _ ab => class_eq_symm a b ab)
  case ObjectExactCardinality.ObjectExactCardinality.ObjectExactCardinality n p xs m q ys k r zs =>
    refine ⟨first.1.trans second.1,first.2.1.trans second.2.1,?_⟩
    change OptionalClassEq xs zs
    have one : OptionalClassEq xs ys := first.2.2
    have two : OptionalClassEq ys zs := second.2.2
    exact optional_class_trans_of xs ys zs one two
      (fun a b c ax bys cz ab bc =>
        have sa : sizeOf a < sizeOf xs := by rw [ax]; simp +arith
        have sb : sizeOf b < sizeOf ys := by rw [bys]; simp +arith
        have sc : sizeOf c < sizeOf zs := by rw [cz]; simp +arith
        class_eq_trans a b c ab bc)
      (fun a b _ _ ab => class_eq_symm a b ab)
  case DataSomeValuesFrom.DataSomeValuesFrom.DataSomeValuesFrom p a q b r c =>
    exact ⟨first.1.trans second.1,Rowl.RangeEquality.range_eq_trans a b c first.2 second.2⟩
  case DataAllValuesFrom.DataAllValuesFrom.DataAllValuesFrom p a q b r c =>
    exact ⟨first.1.trans second.1,Rowl.RangeEquality.range_eq_trans a b c first.2 second.2⟩
  case DataHasValue.DataHasValue.DataHasValue p a q b r c =>
    exact ⟨first.1.trans second.1,first.2.trans second.2⟩
  case DataMinCardinality.DataMinCardinality.DataMinCardinality n p xs m q ys k r zs =>
    exact ⟨first.1.trans second.1,first.2.1.trans second.2.1,optional_range_trans xs ys zs first.2.2 second.2.2⟩
  case DataMaxCardinality.DataMaxCardinality.DataMaxCardinality n p xs m q ys k r zs =>
    exact ⟨first.1.trans second.1,first.2.1.trans second.2.1,optional_range_trans xs ys zs first.2.2 second.2.2⟩
  case DataExactCardinality.DataExactCardinality.DataExactCardinality n p xs m q ys k r zs =>
    exact ⟨first.1.trans second.1,first.2.1.trans second.2.1,optional_range_trans xs ys zs first.2.2 second.2.2⟩
termination_by sizeOf left + sizeOf middle + sizeOf right
decreasing_by
  all_goals simp only [hLeft,hMiddle,hRight,
ClassExpression.Class.sizeOf_spec,ClassExpression.ObjectIntersectionOf.sizeOf_spec,ClassExpression.ObjectUnionOf.sizeOf_spec,ClassExpression.ObjectComplementOf.sizeOf_spec,ClassExpression.ObjectOneOf.sizeOf_spec,ClassExpression.ObjectSomeValuesFrom.sizeOf_spec,ClassExpression.ObjectAllValuesFrom.sizeOf_spec,ClassExpression.ObjectHasValue.sizeOf_spec,ClassExpression.ObjectHasSelf.sizeOf_spec,ClassExpression.ObjectMinCardinality.sizeOf_spec,ClassExpression.ObjectMaxCardinality.sizeOf_spec,ClassExpression.ObjectExactCardinality.sizeOf_spec,ClassExpression.DataSomeValuesFrom.sizeOf_spec,ClassExpression.DataAllValuesFrom.sizeOf_spec,ClassExpression.DataHasValue.sizeOf_spec,ClassExpression.DataMinCardinality.sizeOf_spec,ClassExpression.DataMaxCardinality.sizeOf_spec,ClassExpression.DataExactCardinality.sizeOf_spec]
  all_goals omega
end Rowl.ClassEquality
