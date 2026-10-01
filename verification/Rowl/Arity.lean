import Rowl.ClassEquality
import Rowl.Keys

namespace Rowl.Arity
open Aeneas Aeneas.Std RowlRust.model RowlRust.arity
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-- At least two structural equivalence classes, independent of storage order. -/
def TwoDistinct {α : Type} (equal : α → α → Prop) (values : List α) : Prop :=
  ∃ a ∈ values, ∃ b ∈ values, ¬ equal a b
/-- Pairwise different original occurrences, before dropping any duplicates. -/
def Unique {α : Type} (equal : α → α → Prop) (values : List α) : Prop :=
  values.Pairwise (fun a b => ¬ equal a b)

private theorem two_distinct_anchor {α : Type} (equal : α → α → Prop)
    (refl : ∀ a, equal a a) (symm : ∀ a b, equal a b → equal b a)
    (trans : ∀ a b c, equal a b → equal b c → equal a c) (xs : AtLeastTwo α) :
    TwoDistinct equal xs.elements ↔ ¬ equal xs.first xs.second ∨ ∃ b ∈ xs.rest.val, ¬ equal xs.first b := by
  have anchored : TwoDistinct equal xs.elements ↔ ∃ b ∈ xs.elements, ¬ equal xs.first b := by
    constructor
    · rintro ⟨a,ma,b,mb,different⟩
      by_contra no
      have all : ∀ x ∈ xs.elements, equal xs.first x := by
        intro x mx
        by_contra unequal
        exact no ⟨x,mx,unequal⟩
      exact different (trans a xs.first b (symm xs.first a (all a ma)) (all b mb))
    · rintro ⟨b,mb,unequal⟩
      exact ⟨xs.first,by simp [AtLeastTwo.elements],b,mb,unequal⟩
  rw [anchored]
  simp [AtLeastTwo.elements,refl,List.mem_cons,exists_eq_or_imp]

private theorem iri_eq (left right : Iri) : left.spelling.val = right.spelling.val ↔ left = right := by
  cases left; cases right; simp
/-- Data properties have exact structural IRI identity. -/
theorem same_data_property_total_correct (left right : DataProperty) :
    same_data_property left right = .ok (decide (left = right)) := by
  cases left; cases right
  simp [same_data_property,Rowl.Symbols.same_spelling_total_correct,iri_eq]

private theorem exists_other_total {α : Type} (values : alloc.vec.Vec α)
    (compare : α → Result Bool) (equal : α → Prop) (loop : Usize → Result Bool)
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let same ← compare item
        if same then
          let next ← index + 1#usize
          loop next
        else .ok true
      else .ok false)
    (child : ∀ item ∈ values.val, compare item = .ok (decide (equal item))) (index : Usize) :
    loop index = .ok (decide (∃ item ∈ values.val.drop index.val, ¬ equal item)) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := child values.val[index.val] (List.getElem_mem inside)
    have split : (∃ item ∈ values.val.drop index.val, ¬ equal item) ↔
        ¬ equal values.val[index.val] ∨ ∃ item ∈ values.val.drop (index.val+1), ¬ equal item := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons,exists_eq_or_imp]
    have splitBool : decide (∃ item ∈ values.val.drop index.val, ¬ equal item) =
        decide (¬ equal values.val[index.val] ∨ ∃ item ∈ values.val.drop (index.val+1), ¬ equal item) :=
      decide_eq_decide.mpr split
    rw [splitBool]
    by_cases same : equal values.val[index.val]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val+1 := by simpa using nextval
      have recurse := exists_other_total values compare equal loop equation child next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,same,advance,recurse,nv]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,same]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem all_different_total {α : Type} (values : alloc.vec.Vec α)
    (compare : α → Result Bool) (equal : α → Prop) (loop : Usize → Result Bool)
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let same ← compare item
        if same then .ok false else
          let next ← index + 1#usize
          loop next
      else .ok true)
    (child : ∀ item ∈ values.val, compare item = .ok (decide (equal item))) (index : Usize) :
    loop index = .ok (decide (∀ item ∈ values.val.drop index.val, ¬ equal item)) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := child values.val[index.val] (List.getElem_mem inside)
    have split : (∀ item ∈ values.val.drop index.val, ¬ equal item) ↔
        ¬ equal values.val[index.val] ∧ ∀ item ∈ values.val.drop (index.val+1), ¬ equal item := by
      rw [List.drop_eq_getElem_cons inside]
      exact List.forall_mem_cons
    have splitBool : decide (∀ item ∈ values.val.drop index.val, ¬ equal item) =
        decide (¬ equal values.val[index.val] ∧ ∀ item ∈ values.val.drop (index.val+1), ¬ equal item) :=
      decide_eq_decide.mpr split
    rw [splitBool]
    by_cases same : equal values.val[index.val]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,same]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val+1 := by simpa using nextval
      have recurse := all_different_total values compare equal loop equation child next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,same,advance,recurse,nv]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem unique_loop_total {α : Type} (values : alloc.vec.Vec α) (equal : α → α → Prop)
    (different : α → Usize → Result Bool) (loop : Usize → Result Bool)
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let next ← index + 1#usize
        let distinct ← different item next
        if distinct then loop next else .ok false
      else .ok true)
    (child : ∀ item index, different item index = .ok (decide (∀ b ∈ values.val.drop index.val, ¬ equal item b)))
    (index : Usize) :
    loop index = .ok (decide (Unique equal (values.val.drop index.val))) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val+1 := by simpa using nextval
    have recurse := unique_loop_total values equal different loop equation child next
    have split : Unique equal (values.val.drop index.val) ↔
        (∀ b ∈ values.val.drop next.val, ¬ equal values.val[index.val] b) ∧
        Unique equal (values.val.drop next.val) := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [Unique,List.pairwise_cons,nv]
    have splitBool : decide (Unique equal (values.val.drop index.val)) =
        decide ((∀ b ∈ values.val.drop next.val, ¬ equal values.val[index.val] b) ∧
        Unique equal (values.val.drop next.val)) := decide_eq_decide.mpr split
    rw [splitBool]
    by_cases all : ∀ b ∈ values.val.drop next.val, ¬ equal values.val[index.val] b
    · have yes := decide_eq_true all
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,advance,child,yes,recurse]
      exact congrArg Result.ok (decide_eq_decide.mpr (and_iff_right all).symm)
    · have no := decide_eq_false all
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,advance,child,no,Bool.false_eq_true]
      exact congrArg Result.ok (decide_eq_false (fun pair => all pair.1)).symm
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty,Unique]
termination_by values.val.length - index.val
decreasing_by omega

private theorem other_ranges_total (values : alloc.vec.Vec DataRange) (sought : DataRange) (index : Usize) :
    other_ranges_from values sought index = .ok (decide (∃ item ∈ values.val.drop index.val, ¬ Rowl.RangeEquality.RangeEq sought item)) :=
  exists_other_total values (RowlRust.range_equality.same_range sought) (Rowl.RangeEquality.RangeEq sought) (other_ranges_from values sought)
    (fun i => by rw [other_ranges_from]) (fun item _ => Rowl.RangeEquality.same_range_total_correct sought item) index
/-- Complete structural equivalence-class count, allowing harmless raw repetitions. -/
theorem has_two_ranges_total_correct (values : AtLeastTwo DataRange) :
    has_two_ranges values = .ok (decide (TwoDistinct Rowl.RangeEquality.RangeEq values.elements)) := by
  have anchor := two_distinct_anchor Rowl.RangeEquality.RangeEq Rowl.RangeEquality.range_eq_refl Rowl.RangeEquality.range_eq_symm Rowl.RangeEquality.range_eq_trans values
  rw [has_two_ranges,Rowl.RangeEquality.same_range_total_correct]
  by_cases same : Rowl.RangeEquality.RangeEq values.first values.second <;>
    simp [other_ranges_total,same,anchor]

private theorem other_classes_total (values : alloc.vec.Vec ClassExpression) (sought : ClassExpression) (index : Usize) :
    other_classes_from values sought index = .ok (decide (∃ item ∈ values.val.drop index.val, ¬ Rowl.ClassEquality.ClassEq sought item)) :=
  exists_other_total values (RowlRust.class_equality.same_class sought) (Rowl.ClassEquality.ClassEq sought) (other_classes_from values sought)
    (fun i => by rw [other_classes_from]) (fun item _ => Rowl.ClassEquality.same_class_total_correct sought item) index
/-- Complete structural equivalence-class count, allowing harmless raw repetitions. -/
theorem has_two_classes_total_correct (values : AtLeastTwo ClassExpression) :
    has_two_classes values = .ok (decide (TwoDistinct Rowl.ClassEquality.ClassEq values.elements)) := by
  have anchor := two_distinct_anchor Rowl.ClassEquality.ClassEq Rowl.ClassEquality.class_eq_refl Rowl.ClassEquality.class_eq_symm Rowl.ClassEquality.class_eq_trans values
  rw [has_two_classes,Rowl.ClassEquality.same_class_total_correct]
  by_cases same : Rowl.ClassEquality.ClassEq values.first values.second <;>
    simp [other_classes_total,same,anchor]

private theorem different_classes_total (values : alloc.vec.Vec ClassExpression) (sought : ClassExpression) (index : Usize) :
    different_classes_from values sought index = .ok (decide (∀ item ∈ values.val.drop index.val, ¬ Rowl.ClassEquality.ClassEq sought item)) :=
  all_different_total values (RowlRust.class_equality.same_class sought) (Rowl.ClassEquality.ClassEq sought) (different_classes_from values sought)
    (fun i => by rw [different_classes_from]) (fun item _ => Rowl.ClassEquality.same_class_total_correct sought item) index
private theorem unique_classes_from_total (values : alloc.vec.Vec ClassExpression) (index : Usize) :
    unique_classes_from values index = .ok (decide (Unique Rowl.ClassEquality.ClassEq (values.val.drop index.val))) :=
  unique_loop_total values Rowl.ClassEquality.ClassEq (different_classes_from values) (unique_classes_from values)
    (fun i => by rw [unique_classes_from]) (different_classes_total values) index
/-- Exact pairwise structural distinctness of original raw occurrences. -/
theorem unique_classes_total_correct (values : AtLeastTwo ClassExpression) :
    unique_classes values = .ok (decide (Unique Rowl.ClassEquality.ClassEq values.elements)) := by
  rw [unique_classes,Rowl.ClassEquality.same_class_total_correct]
  by_cases same : Rowl.ClassEquality.ClassEq values.first values.second <;>
    by_cases first : ∀ item ∈ values.rest.val, ¬ Rowl.ClassEquality.ClassEq values.first item <;>
    by_cases second : ∀ item ∈ values.rest.val, ¬ Rowl.ClassEquality.ClassEq values.second item <;>
    simp [different_classes_total,unique_classes_from_total,same,first,second,
      Unique,AtLeastTwo.elements,List.pairwise_cons]
  all_goals repeat' split <;> simp_all

private theorem other_properties_total (values : alloc.vec.Vec ObjectPropertyExpression) (sought : ObjectPropertyExpression) (index : Usize) :
    other_properties_from values sought index = .ok (decide (∃ item ∈ values.val.drop index.val, ¬ Eq sought item)) :=
  exists_other_total values (RowlRust.assertion_equality.same_property sought) (Eq sought) (other_properties_from values sought)
    (fun i => by rw [other_properties_from]) (fun item _ => Rowl.AssertionEquality.same_property_total_correct sought item) index
/-- Complete structural equivalence-class count, allowing harmless raw repetitions. -/
theorem has_two_properties_total_correct (values : AtLeastTwo ObjectPropertyExpression) :
    has_two_properties values = .ok (decide (TwoDistinct Eq values.elements)) := by
  have anchor := two_distinct_anchor Eq (fun _ => rfl) (fun _ _ h => h.symm) (fun _ _ _ h k => h.trans k) values
  rw [has_two_properties,Rowl.AssertionEquality.same_property_total_correct]
  by_cases same : Eq values.first values.second <;>
    simp [other_properties_total,same,anchor]

private theorem different_properties_total (values : alloc.vec.Vec ObjectPropertyExpression) (sought : ObjectPropertyExpression) (index : Usize) :
    different_properties_from values sought index = .ok (decide (∀ item ∈ values.val.drop index.val, ¬ Eq sought item)) :=
  all_different_total values (RowlRust.assertion_equality.same_property sought) (Eq sought) (different_properties_from values sought)
    (fun i => by rw [different_properties_from]) (fun item _ => Rowl.AssertionEquality.same_property_total_correct sought item) index
private theorem unique_properties_from_total (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    unique_properties_from values index = .ok (decide (Unique Eq (values.val.drop index.val))) :=
  unique_loop_total values Eq (different_properties_from values) (unique_properties_from values)
    (fun i => by rw [unique_properties_from]) (different_properties_total values) index
/-- Exact pairwise structural distinctness of original raw occurrences. -/
theorem unique_properties_total_correct (values : AtLeastTwo ObjectPropertyExpression) :
    unique_properties values = .ok (decide (Unique Eq values.elements)) := by
  rw [unique_properties,Rowl.AssertionEquality.same_property_total_correct]
  by_cases same : Eq values.first values.second <;>
    by_cases first : ∀ item ∈ values.rest.val, ¬ Eq values.first item <;>
    by_cases second : ∀ item ∈ values.rest.val, ¬ Eq values.second item <;>
    simp [different_properties_total,unique_properties_from_total,same,first,second,
      Unique,AtLeastTwo.elements,List.pairwise_cons]
  all_goals repeat' split <;> simp_all

private theorem other_data_properties_total (values : alloc.vec.Vec DataProperty) (sought : DataProperty) (index : Usize) :
    other_data_properties_from values sought index = .ok (decide (∃ item ∈ values.val.drop index.val, ¬ Eq sought item)) :=
  exists_other_total values (same_data_property sought) (Eq sought) (other_data_properties_from values sought)
    (fun i => by rw [other_data_properties_from]) (fun item _ => same_data_property_total_correct sought item) index
/-- Complete structural equivalence-class count, allowing harmless raw repetitions. -/
theorem has_two_data_properties_total_correct (values : AtLeastTwo DataProperty) :
    has_two_data_properties values = .ok (decide (TwoDistinct Eq values.elements)) := by
  have anchor := two_distinct_anchor Eq (fun _ => rfl) (fun _ _ h => h.symm) (fun _ _ _ h k => h.trans k) values
  rw [has_two_data_properties,same_data_property_total_correct]
  by_cases same : Eq values.first values.second <;>
    simp [other_data_properties_total,same,anchor]

private theorem different_data_properties_total (values : alloc.vec.Vec DataProperty) (sought : DataProperty) (index : Usize) :
    different_data_properties_from values sought index = .ok (decide (∀ item ∈ values.val.drop index.val, ¬ Eq sought item)) :=
  all_different_total values (same_data_property sought) (Eq sought) (different_data_properties_from values sought)
    (fun i => by rw [different_data_properties_from]) (fun item _ => same_data_property_total_correct sought item) index
private theorem unique_data_properties_from_total (values : alloc.vec.Vec DataProperty) (index : Usize) :
    unique_data_properties_from values index = .ok (decide (Unique Eq (values.val.drop index.val))) :=
  unique_loop_total values Eq (different_data_properties_from values) (unique_data_properties_from values)
    (fun i => by rw [unique_data_properties_from]) (different_data_properties_total values) index
/-- Exact pairwise structural distinctness of original raw occurrences. -/
theorem unique_data_properties_total_correct (values : AtLeastTwo DataProperty) :
    unique_data_properties values = .ok (decide (Unique Eq values.elements)) := by
  rw [unique_data_properties,same_data_property_total_correct]
  by_cases same : Eq values.first values.second <;>
    by_cases first : ∀ item ∈ values.rest.val, ¬ Eq values.first item <;>
    by_cases second : ∀ item ∈ values.rest.val, ¬ Eq values.second item <;>
    simp [different_data_properties_total,unique_data_properties_from_total,same,first,second,
      Unique,AtLeastTwo.elements,List.pairwise_cons]
  all_goals repeat' split <;> simp_all

private theorem other_individuals_total (values : alloc.vec.Vec Individual) (sought : Individual) (index : Usize) :
    other_individuals_from values sought index = .ok (decide (∃ item ∈ values.val.drop index.val, ¬ Eq sought item)) :=
  exists_other_total values (RowlRust.assertion_equality.same_individual_value sought) (Eq sought) (other_individuals_from values sought)
    (fun i => by rw [other_individuals_from]) (fun item _ => Rowl.AssertionEquality.same_individual_value_total_correct sought item) index
/-- Complete structural equivalence-class count, allowing harmless raw repetitions. -/
theorem has_two_individuals_total_correct (values : AtLeastTwo Individual) :
    has_two_individuals values = .ok (decide (TwoDistinct Eq values.elements)) := by
  have anchor := two_distinct_anchor Eq (fun _ => rfl) (fun _ _ h => h.symm) (fun _ _ _ h k => h.trans k) values
  rw [has_two_individuals,Rowl.AssertionEquality.same_individual_value_total_correct]
  by_cases same : Eq values.first values.second <;>
    simp [other_individuals_total,same,anchor]

private theorem different_individuals_total (values : alloc.vec.Vec Individual) (sought : Individual) (index : Usize) :
    different_individuals_from values sought index = .ok (decide (∀ item ∈ values.val.drop index.val, ¬ Eq sought item)) :=
  all_different_total values (RowlRust.assertion_equality.same_individual_value sought) (Eq sought) (different_individuals_from values sought)
    (fun i => by rw [different_individuals_from]) (fun item _ => Rowl.AssertionEquality.same_individual_value_total_correct sought item) index
private theorem unique_individuals_from_total (values : alloc.vec.Vec Individual) (index : Usize) :
    unique_individuals_from values index = .ok (decide (Unique Eq (values.val.drop index.val))) :=
  unique_loop_total values Eq (different_individuals_from values) (unique_individuals_from values)
    (fun i => by rw [unique_individuals_from]) (different_individuals_total values) index
/-- Exact pairwise structural distinctness of original raw occurrences. -/
theorem unique_individuals_total_correct (values : AtLeastTwo Individual) :
    unique_individuals values = .ok (decide (Unique Eq values.elements)) := by
  rw [unique_individuals,Rowl.AssertionEquality.same_individual_value_total_correct]
  by_cases same : Eq values.first values.second <;>
    by_cases first : ∀ item ∈ values.rest.val, ¬ Eq values.first item <;>
    by_cases second : ∀ item ∈ values.rest.val, ¬ Eq values.second item <;>
    simp [different_individuals_total,unique_individuals_from_total,same,first,second,
      Unique,AtLeastTwo.elements,List.pairwise_cons]
  all_goals repeat' split <;> simp_all

private theorem listN_mem_size {α : Type} [SizeOf α] {n : Nat}
    (xs : Aeneas.Data.ListN.ListN α n) {x : α} (h : x ∈ xs.toList) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp [Aeneas.Data.ListN.ListN.toList] at h
  | cons head tail ih =>
    simp only [Aeneas.Data.ListN.ListN.toList, List.mem_cons] at h
    rcases h with rfl | h
    · simp +arith
    · have := ih h
      simp only [Data.ListN.ListN.cons.sizeOf_spec]
      omega
private theorem vec_mem_size {α : Type} [SizeOf α] (xs : alloc.vec.Vec α)
    {x : α} (h : x ∈ xs.val) : sizeOf x < sizeOf xs := by
  have := listN_mem_size xs.slice.list h
  cases xs with | mk slice => cases slice; simp_all [alloc.vec.Vec.val, Slice.val]; omega
private theorem first_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.first < sizeOf xs := by
  cases xs; simp +arith
private theorem second_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.second < sizeOf xs := by
  cases xs; simp +arith
private theorem rest_size {α : Type} [SizeOf α] (xs : AtLeastTwo α) : sizeOf xs.rest < sizeOf xs := by
  cases xs; simp +arith



/-- Every nested data association has its minimum number of distinct members.
    Nonempty literal/facet associations are guaranteed by the raw constructors. -/
def RangeAllowed (value : DataRange) : Prop :=
  match value with
  | .Datatype _ => True
  | .Intersection xs | .Union xs => TwoDistinct Rowl.RangeEquality.RangeEq xs.elements ∧
      RangeAllowed xs.first ∧ RangeAllowed xs.second ∧ ∀ e : {e // e ∈ xs.rest.val}, RangeAllowed e.val
  | .Complement x => RangeAllowed x
  | .OneOf _ => True
  | .Restriction _ _ => True
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega)

/-- Every standard class form is traversed; qualifiers keep their raw recursive
    structure. Nonempty nominals and natural cardinalities follow from types. -/
def ClassAllowed (value : ClassExpression) : Prop :=
  match value with
  | .Class _ => True
  | .ObjectIntersectionOf xs | .ObjectUnionOf xs => TwoDistinct Rowl.ClassEquality.ClassEq xs.elements ∧
      ClassAllowed xs.first ∧ ClassAllowed xs.second ∧ ∀ e : {e // e ∈ xs.rest.val}, ClassAllowed e.val
  | .ObjectComplementOf x => ClassAllowed x
  | .ObjectOneOf _ => True
  | .ObjectSomeValuesFrom _ x => ClassAllowed x
  | .ObjectAllValuesFrom _ x => ClassAllowed x
  | .ObjectHasValue _ _ => True
  | .ObjectHasSelf _ => True
  | .ObjectMinCardinality _ _ xs => ∀ x ∈ xs, ClassAllowed x
  | .ObjectMaxCardinality _ _ xs => ∀ x ∈ xs, ClassAllowed x
  | .ObjectExactCardinality _ _ xs => ∀ x ∈ xs, ClassAllowed x
  | .DataSomeValuesFrom _ range => RangeAllowed range
  | .DataAllValuesFrom _ range => RangeAllowed range
  | .DataHasValue _ _ => True
  | .DataMinCardinality _ _ xs => ∀ x ∈ xs, RangeAllowed x
  | .DataMaxCardinality _ _ xs => ∀ x ∈ xs, RangeAllowed x
  | .DataExactCardinality _ _ xs => ∀ x ∈ xs, RangeAllowed x
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest e.property; have := rest_size xs; omega) |
    (cases xs <;> simp_all +arith)

/-- Full standard axiom arity and the documented duplicate-disjointness rule.
    Defined DisjointUnion class names are outside the checked member association.
    Ordered property chains retain repetitions and written minimum arity by type. -/
def AxiomAllowed (item : AnnotatedAxiom) : Prop :=
  match item.axiom with
  | .Declaration _ => True
  | .SubClassOf a b => ClassAllowed a ∧ ClassAllowed b
  | .EquivalentClasses xs => TwoDistinct Rowl.ClassEquality.ClassEq xs.elements ∧ ∀ x ∈ xs.elements, ClassAllowed x
  | .DisjointClasses xs => Unique Rowl.ClassEquality.ClassEq xs.elements ∧ ∀ x ∈ xs.elements, ClassAllowed x
  | .DisjointUnion _ xs => Unique Rowl.ClassEquality.ClassEq xs.elements ∧ ∀ x ∈ xs.elements, ClassAllowed x
  | .SubObjectPropertyOf _ _ => True
  | .EquivalentObjectProperties xs => TwoDistinct Eq xs.elements
  | .DisjointObjectProperties xs => Unique Eq xs.elements
  | .InverseObjectProperties _ _ => True
  | .ObjectPropertyDomain _ c => ClassAllowed c
  | .ObjectPropertyRange _ c => ClassAllowed c
  | .FunctionalObjectProperty _ => True
  | .InverseFunctionalObjectProperty _ => True
  | .ReflexiveObjectProperty _ => True
  | .IrreflexiveObjectProperty _ => True
  | .SymmetricObjectProperty _ => True
  | .AsymmetricObjectProperty _ => True
  | .TransitiveObjectProperty _ => True
  | .SubDataPropertyOf _ _ => True
  | .EquivalentDataProperties xs => TwoDistinct Eq xs.elements
  | .DisjointDataProperties xs => Unique Eq xs.elements
  | .DataPropertyDomain _ c => ClassAllowed c
  | .DataPropertyRange _ r => RangeAllowed r
  | .FunctionalDataProperty _ => True
  | .DatatypeDefinition _ r => RangeAllowed r
  | .HasKey c _ _ => ClassAllowed c ∧ Rowl.Keys.AxiomAllowed item
  | .SameIndividual xs => TwoDistinct Eq xs.elements
  | .DifferentIndividuals xs => Unique Eq xs.elements
  | .ClassAssertion c _ => ClassAllowed c
  | .ObjectPropertyAssertion _ _ _ => True
  | .NegativeObjectPropertyAssertion _ _ _ => True
  | .DataPropertyAssertion _ _ _ => True
  | .NegativeDataPropertyAssertion _ _ _ => True
  | .AnnotationAssertion _ _ _ => True
  | .SubAnnotationPropertyOf _ _ => True
  | .AnnotationPropertyDomain _ _ => True
  | .AnnotationPropertyRange _ _ => True

def ClosureOK (axioms : List AnnotatedAxiom) : Prop := ∀ item ∈ axioms, AxiomAllowed item
def FirstForbidden (axioms : List AnnotatedAxiom) (item : AnnotatedAxiom) : Prop :=
  ¬ AxiomAllowed item ∧ ∃ before after, axioms = before ++ item :: after ∧ ClosureOK before

private theorem vector_total {α : Type} (values : alloc.vec.Vec α)
    (visit : α → Result Bool) (allowed : α → Prop) (loop : Usize → Result Bool)
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let accepted ← visit item
        if accepted then
          let next ← index + 1#usize
          loop next
        else .ok false
      else .ok true)
    (child : ∀ item ∈ values.val, visit item = .ok (decide (allowed item)))
    (index : Usize) :
    loop index = .ok (decide (∀ item ∈ values.val.drop index.val, allowed item)) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have accepted := child values.val[index.val] (List.getElem_mem inside)
    simp only [inside, alloc.vec.Vec.len_val, ↓reduceIte,
      alloc.vec.Vec.index_slice_index, lookup, bind_ok, accepted]
    by_cases head : allowed values.val[index.val]
    · simp only [head, decide_true, ↓reduceIte]
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have recurse := vector_total values visit allowed loop equation child next
      simp only [hn, bind_ok, recurse]
      simp [nextval, inside]
      have splitting : (∀ item ∈ values.val.drop index.val, allowed item) ↔
          allowed values.val[index.val] ∧ ∀ item ∈ values.val.drop (index.val + 1), allowed item := by
        rw [List.drop_eq_getElem_cons inside]
        exact List.forall_mem_cons
      rw [splitting]
      simp only [head, true_and]
    · simp [head, inside]
      refine ⟨values.val[index.val], ?_, head⟩
      rw [List.drop_eq_getElem_cons inside]
      exact List.mem_cons_self
  · have drop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside, drop]
termination_by values.val.length - index.val
decreasing_by omega

private theorem subtype_forall {α : Type} (xs : List α) (p : α → Prop) :
    (∀ e : {e // e ∈ xs}, p e.val) ↔ ∀ e ∈ xs, p e := by
  constructor
  · intro all e mem; exact all ⟨e, mem⟩
  · intro all e; exact all e.val e.property


private theorem ranges_total_of (values : alloc.vec.Vec DataRange)
    (child : ∀ item ∈ values.val, range_allowed item = .ok (decide (RangeAllowed item))) (index : Usize) :
    ranges_from values index = .ok (decide (∀ item ∈ values.val.drop index.val, RangeAllowed item)) :=
  vector_total values range_allowed RangeAllowed (ranges_from values)
    (fun i => by rw [ranges_from]) child index
private theorem classes_total_of (values : alloc.vec.Vec ClassExpression)
    (child : ∀ item ∈ values.val, class_allowed item = .ok (decide (ClassAllowed item))) (index : Usize) :
    classes_from values index = .ok (decide (∀ item ∈ values.val.drop index.val, ClassAllowed item)) :=
  vector_total values class_allowed ClassAllowed (classes_from values)
    (fun i => by rw [classes_from]) child index

/-- Total and exact checking of every data-range constructor and nested member. -/
theorem range_allowed_total_correct (value : DataRange) :
    range_allowed value = .ok (decide (RangeAllowed value)) := by
  cases value with
  | Datatype _ | OneOf _ | Restriction _ _ => simp [range_allowed,RangeAllowed]
  | Intersection xs | Union xs =>
    have first := range_allowed_total_correct xs.first
    have second := range_allowed_total_correct xs.second
    have rest := ranges_total_of xs.rest (fun item _ => range_allowed_total_correct item) 0#usize
    by_cases arity : TwoDistinct Rowl.RangeEquality.RangeEq xs.elements <;>
      by_cases f : RangeAllowed xs.first <;> by_cases g : RangeAllowed xs.second <;>
      simp [range_allowed,RangeAllowed,has_two_ranges_total_correct,arity,first,second,rest,f,g,subtype_forall]
  | Complement x => simpa [range_allowed,RangeAllowed] using range_allowed_total_correct x
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

/-- Total and exact recursive arity checking of all eighteen class forms. -/
theorem class_allowed_total_correct (value : ClassExpression) :
    class_allowed value = .ok (decide (ClassAllowed value)) := by
  cases value with
  | Class _ | ObjectOneOf _ | ObjectHasValue _ _ | ObjectHasSelf _ | DataHasValue _ _ =>
    simp [class_allowed,ClassAllowed]
  | ObjectIntersectionOf xs | ObjectUnionOf xs =>
    have first := class_allowed_total_correct xs.first
    have second := class_allowed_total_correct xs.second
    have rest := classes_total_of xs.rest (fun item _ => class_allowed_total_correct item) 0#usize
    by_cases arity : TwoDistinct Rowl.ClassEquality.ClassEq xs.elements <;>
      by_cases f : ClassAllowed xs.first <;> by_cases g : ClassAllowed xs.second <;>
      simp [class_allowed,ClassAllowed,has_two_classes_total_correct,arity,first,second,rest,f,g,subtype_forall]
  | ObjectComplementOf x | ObjectSomeValuesFrom _ x | ObjectAllValuesFrom _ x =>
    simpa [class_allowed,ClassAllowed] using class_allowed_total_correct x
  | ObjectMinCardinality n p xs | ObjectMaxCardinality n p xs | ObjectExactCardinality n p xs =>
    cases xs with
    | none => simp [class_allowed,ClassAllowed]
    | some x => simpa [class_allowed,ClassAllowed] using class_allowed_total_correct x
  | DataSomeValuesFrom p r | DataAllValuesFrom p r =>
    simp [class_allowed,ClassAllowed,range_allowed_total_correct]
  | DataMinCardinality n p xs | DataMaxCardinality n p xs | DataExactCardinality n p xs =>
    cases xs <;> simp [class_allowed,ClassAllowed,range_allowed_total_correct]
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := first_size xs; omega) | (have := second_size xs; omega) |
    (have := vec_mem_size xs.rest ‹_ ∈ _›; have := rest_size xs; omega)

private theorem classes_total (values : alloc.vec.Vec ClassExpression) (index : Usize) :
    classes_from values index = .ok (decide (∀ item ∈ values.val.drop index.val, ClassAllowed item)) :=
  classes_total_of values (fun item _ => class_allowed_total_correct item) index
/-- Every actual raw axiom constructor has exactly the independently specified rule. -/
theorem axiom_allowed_total_correct (item : AnnotatedAxiom) :
    axiom_allowed item = .ok (decide (AxiomAllowed item)) := by
  cases h : item.axiom <;> simp [axiom_allowed,AxiomAllowed,h,class_allowed_total_correct,
    range_allowed_total_correct,classes_total,has_two_classes_total_correct,unique_classes_total_correct,
    has_two_properties_total_correct,unique_properties_total_correct,has_two_data_properties_total_correct,
    unique_data_properties_total_correct,has_two_individuals_total_correct,unique_individuals_total_correct,
    Rowl.Keys.axiom_allowed_total_correct,AtLeastTwo.elements]
  all_goals repeat' split <;> simp_all

private noncomputable def forbidden (item : AnnotatedAxiom) : Bool := decide (¬ AxiomAllowed item)

private theorem axioms_from_total (values : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    axioms_from values index = .ok ((values.val.drop index.val).find? forbidden) := by
  rw [axioms_from]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem inside]
    have foundStep : (values.val.drop index.val).find? forbidden =
        if AxiomAllowed values.val[index.val] then
          (values.val.drop (index.val + 1)).find? forbidden else some values.val[index.val] := by
      rw [List.drop_eq_getElem_cons inside]
      by_cases accepted : AxiomAllowed values.val[index.val] <;>
        simp only [List.find?_cons, forbidden, accepted, not_true_eq_false, not_false_eq_true,
          decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
    by_cases accepted : AxiomAllowed values.val[index.val]
    · obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have recurse := axioms_from_total values next
      simp [inside, alloc.vec.Vec.index_slice_index, lookup, axiom_allowed_total_correct,
        accepted, hn, recurse, foundStep, nextval]
    · simp [inside, alloc.vec.Vec.index_slice_index, lookup, axiom_allowed_total_correct,
        accepted, foundStep]
  · have drop : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside, drop]
termination_by values.val.length - index.val
decreasing_by omega

/-- The complete closure scan terminates and returns its exact first forbidden
    occurrence; annotations are carried through without modification. -/
theorem check_arities_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_arities axioms = .ok result ∧
      match result with
      | none => ClosureOK axioms.val
      | some item => FirstForbidden axioms.val item := by
  have total : check_arities axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_arities] using axioms_from_total axioms 0#usize
  refine ⟨axioms.val.find? forbidden, total, ?_⟩
  cases h : axioms.val.find? forbidden with
  | none =>
    simpa [ClosureOK, forbidden] using List.find?_eq_none.mp h
  | some item =>
    simpa [FirstForbidden, ClosureOK, forbidden] using List.find?_eq_some_iff_append.mp h

/-- No false acceptance or rejection of the arity and documented duplicate-disjointness restrictions. -/
theorem check_arities_valid_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_arities axioms = .ok none ↔ ClosureOK axioms.val := by
  have total : check_arities axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_arities] using axioms_from_total axioms 0#usize
  simp [total, List.find?_eq_none, forbidden, ClosureOK]


end Rowl.Arity
