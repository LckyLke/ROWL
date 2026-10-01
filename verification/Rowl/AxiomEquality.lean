import Rowl.ClassEquality
import Rowl.Arity

namespace Rowl.AxiomEquality
open Aeneas Aeneas.Std RowlRust.model RowlRust.axiom_equality
open Rowl.AssertionEquality
open Rowl.ClassEquality (ClassEq ClassSetEq)
open Rowl.RangeEquality (RangeEq SetEq)
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

/-- Distinct fixed fields and ordered, nonunique property chains. -/
def SubPropertyEq (left right : SubObjectPropertyExpression) : Prop :=
  match left,right with
  | .Single a,.Single b => a = b
  | .Chain a,.Chain b => a.elements = b.elements
  | _,_ => False
/-- Complete OWL structural axiom-body relation. Unordered associations are
    sets, while separate fields retain their positions. It is not logical
    equivalence and does not validate duplicate-sensitive raw input. -/
def BodyEq (left right : Axiom) : Prop :=
  match left,right with
  | .Declaration a,.Declaration x => a = x
  | .SubClassOf a b,.SubClassOf x y => ClassEq a x ∧ ClassEq b y
  | .EquivalentClasses a,.EquivalentClasses x => ClassSetEq a.elements x.elements
  | .DisjointClasses a,.DisjointClasses x => ClassSetEq a.elements x.elements
  | .DisjointUnion a b,.DisjointUnion x y => a = x ∧ ClassSetEq b.elements y.elements
  | .SubObjectPropertyOf a b,.SubObjectPropertyOf x y => SubPropertyEq a x ∧ b = y
  | .EquivalentObjectProperties a,.EquivalentObjectProperties x => SetEq a.elements x.elements
  | .DisjointObjectProperties a,.DisjointObjectProperties x => SetEq a.elements x.elements
  | .InverseObjectProperties a b,.InverseObjectProperties x y => a = x ∧ b = y
  | .ObjectPropertyDomain a b,.ObjectPropertyDomain x y => a = x ∧ ClassEq b y
  | .ObjectPropertyRange a b,.ObjectPropertyRange x y => a = x ∧ ClassEq b y
  | .FunctionalObjectProperty a,.FunctionalObjectProperty x => a = x
  | .InverseFunctionalObjectProperty a,.InverseFunctionalObjectProperty x => a = x
  | .ReflexiveObjectProperty a,.ReflexiveObjectProperty x => a = x
  | .IrreflexiveObjectProperty a,.IrreflexiveObjectProperty x => a = x
  | .SymmetricObjectProperty a,.SymmetricObjectProperty x => a = x
  | .AsymmetricObjectProperty a,.AsymmetricObjectProperty x => a = x
  | .TransitiveObjectProperty a,.TransitiveObjectProperty x => a = x
  | .SubDataPropertyOf a b,.SubDataPropertyOf x y => a = x ∧ b = y
  | .EquivalentDataProperties a,.EquivalentDataProperties x => SetEq a.elements x.elements
  | .DisjointDataProperties a,.DisjointDataProperties x => SetEq a.elements x.elements
  | .DataPropertyDomain a b,.DataPropertyDomain x y => a = x ∧ ClassEq b y
  | .DataPropertyRange a b,.DataPropertyRange x y => a = x ∧ RangeEq b y
  | .FunctionalDataProperty a,.FunctionalDataProperty x => a = x
  | .DatatypeDefinition a b,.DatatypeDefinition x y => a = x ∧ RangeEq b y
  | .HasKey a b c,.HasKey x y z => ClassEq a x ∧ SetEq b.val y.val ∧ SetEq c.val z.val
  | .SameIndividual a,.SameIndividual x => SetEq a.elements x.elements
  | .DifferentIndividuals a,.DifferentIndividuals x => SetEq a.elements x.elements
  | .ClassAssertion a b,.ClassAssertion x y => ClassEq a x ∧ b = y
  | .ObjectPropertyAssertion a b c,.ObjectPropertyAssertion x y z => a = x ∧ b = y ∧ c = z
  | .NegativeObjectPropertyAssertion a b c,.NegativeObjectPropertyAssertion x y z => a = x ∧ b = y ∧ c = z
  | .DataPropertyAssertion a b c,.DataPropertyAssertion x y z => a = x ∧ b = y ∧ c = z
  | .NegativeDataPropertyAssertion a b c,.NegativeDataPropertyAssertion x y z => a = x ∧ b = y ∧ c = z
  | .AnnotationAssertion a b c,.AnnotationAssertion x y z => a = x ∧ b = y ∧ c = z
  | .SubAnnotationPropertyOf a b,.SubAnnotationPropertyOf x y => a = x ∧ b = y
  | .AnnotationPropertyDomain a b,.AnnotationPropertyDomain x y => a = x ∧ b = y
  | .AnnotationPropertyRange a b,.AnnotationPropertyRange x y => a = x ∧ b = y
  | _,_ => False
/-- A complete axiom includes the recursively structured metadata association. -/
def AxiomEq (left right : AnnotatedAxiom) : Prop :=
  BodyEq left.axiom right.axiom ∧ AnnotationSetEq left.annotations.val right.annotations.val

private theorem iri_eq (left right : Iri) : left.spelling.val = right.spelling.val ↔ left = right := by
  cases left; cases right; simp
private theorem class_eq (left right : Class) : left.iri.spelling.val = right.iri.spelling.val ↔ left = right := by
  cases left; cases right; simp [iri_eq]
private theorem datatype_eq (left right : Datatype) : left.iri.spelling.val = right.iri.spelling.val ↔ left = right := by
  cases left; cases right; simp [iri_eq]
private theorem annotation_property_eq (left right : AnnotationProperty) : left.iri.spelling.val = right.iri.spelling.val ↔ left = right := by
  cases left; cases right; simp [iri_eq]
/-- Entity kind remains part of structural identity, even with legal punning. -/
theorem same_entity_total_correct (left right : Entity) :
    same_entity left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;> simp [same_entity,Rowl.Symbols.same_spelling_total_correct]
  all_goals rename_i a b; cases a; cases b; simp [iri_eq]
/-- Annotation subjects retain their variant and exact scoped identity. -/
theorem same_subject_total_correct (left right : AnnotationSubject) :
    same_subject left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;>
    simp [same_subject,Rowl.Symbols.same_spelling_total_correct,iri_eq,
      Rowl.AnonymousGraph.same_individual_total_correct,Rowl.AnonymousGraph.key_injective.eq_iff]

private theorem class_iri_eq (left right : Class) : left.iri = right.iri ↔ left = right := by
  cases left; cases right; simp
private theorem datatype_iri_eq (left right : Datatype) : left.iri = right.iri ↔ left = right := by
  cases left; cases right; simp
private theorem annotation_property_iri_eq (left right : AnnotationProperty) : left.iri = right.iri ↔ left = right := by
  cases left; cases right; simp
private theorem and_ok (p q : Prop) [Decidable p] [Decidable q] [Decidable (p ∧ q)] :
    (if decide p then Result.ok (decide q) else Result.ok false) = Result.ok (decide (p ∧ q)) := by
  by_cases yes : p <;> simp [yes]

private theorem set_eq_iff_subsets {α : Type} (left right : List α) :
    SetEq left right ↔ (∀ a ∈ left, a ∈ right) ∧ (∀ b ∈ right, b ∈ left) := by
  constructor
  · intro equal; exact ⟨fun a mem => (equal a).mp mem,fun b mem => (equal b).mpr mem⟩
  · rintro ⟨forward,backward⟩ a; exact ⟨forward a,backward a⟩

private theorem contains_total {α : Type} (values : alloc.vec.Vec α)
    (compare : α → Result Bool) (equal : α → Prop) (loop : Usize → Result Bool)
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let same ← compare item
        if same then .ok true else
          let next ← index + 1#usize
          loop next
      else .ok false)
    (child : ∀ item ∈ values.val, compare item = .ok (decide (equal item))) (index : Usize) :
    loop index = .ok (decide (∃ item ∈ values.val.drop index.val, equal item)) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := child values.val[index.val] (List.getElem_mem inside)
    have split : (∃ item ∈ values.val.drop index.val, equal item) ↔
        equal values.val[index.val] ∨ ∃ item ∈ values.val.drop (index.val+1), equal item := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons,exists_eq_or_imp]
    have splitBool : decide (∃ item ∈ values.val.drop index.val, equal item) =
        decide (equal values.val[index.val] ∨ ∃ item ∈ values.val.drop (index.val+1), equal item) :=
      decide_eq_decide.mpr split
    rw [splitBool]
    by_cases same : equal values.val[index.val]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,same]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val+1 := by simpa using nextval
      have recurse := contains_total values compare equal loop equation child next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,same,advance,recurse,nv]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem all_total {α : Type} (values : alloc.vec.Vec α)
    (compare : α → Result Bool) (allowed : α → Prop) (loop : Usize → Result Bool)
    (equation : ∀ index, loop index = do
      if index < values.len then
        let item ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index
        let yes ← compare item
        if yes then
          let next ← index + 1#usize
          loop next
        else .ok false
      else .ok true)
    (child : ∀ item ∈ values.val, compare item = .ok (decide (allowed item))) (index : Usize) :
    loop index = .ok (decide (∀ item ∈ values.val.drop index.val, allowed item)) := by
  rw [equation]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := child values.val[index.val] (List.getElem_mem inside)
    have split : (∀ item ∈ values.val.drop index.val, allowed item) ↔
        allowed values.val[index.val] ∧ ∀ item ∈ values.val.drop (index.val+1), allowed item := by
      rw [List.drop_eq_getElem_cons inside]
      exact List.forall_mem_cons
    have splitBool : decide (∀ item ∈ values.val.drop index.val, allowed item) =
        decide (allowed values.val[index.val] ∧ ∀ item ∈ values.val.drop (index.val+1), allowed item) :=
      decide_eq_decide.mpr split
    rw [splitBool]
    by_cases yes : allowed values.val[index.val]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val+1 := by simpa using nextval
      have recurse := all_total values compare allowed loop equation child next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,yes,advance,recurse,nv]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,head,yes]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem properties_contains_total (values : alloc.vec.Vec ObjectPropertyExpression) (sought : ObjectPropertyExpression) (index : Usize) :
    properties_contains_from values sought index = .ok (decide (sought ∈ values.val.drop index.val)) := by
  have total := contains_total values (RowlRust.assertion_equality.same_property sought) (fun item => sought = item) (properties_contains_from values sought)
    (fun i => by rw [properties_contains_from]) (fun item _ => same_property_total_correct sought item) index
  rw [total]
  exact congrArg Result.ok (decide_eq_decide.mpr (by simp))
private theorem properties_subset_total (left right : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    properties_subset_from left right index = .ok (decide (∀ item ∈ left.val.drop index.val, item ∈ right.val)) :=
  by
    have total := all_total left (fun item => properties_contains_from right item 0#usize) (fun item => item ∈ right.val)
      (properties_subset_from left right) (fun i => by rw [properties_subset_from])
      (fun item _ => by
        rw [properties_contains_total]
        exact congrArg Result.ok (decide_eq_decide.mpr (by simp))) index
    rw [total]
    exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)
/-- Complete unordered property association comparison, including empty key lists. -/
theorem same_properties_set_total_correct (left right : alloc.vec.Vec ObjectPropertyExpression) :
    same_properties_set left right = .ok (decide (SetEq left.val right.val)) := by
  rw [same_properties_set]
  by_cases forward : ∀ a ∈ left.val, a ∈ right.val <;>
    simp [properties_subset_total,forward,set_eq_iff_subsets]
  all_goals repeat' split <;> simp_all
private theorem properties_member_total (sought : ObjectPropertyExpression) (values : AtLeastTwo ObjectPropertyExpression) :
    properties_member sought values = .ok (decide (sought ∈ values.elements)) := by
  by_cases first : sought = values.first <;> by_cases second : sought = values.second <;>
    simp [properties_member,same_property_total_correct,properties_contains_total,AtLeastTwo.elements,first,second]
private theorem properties_association_subset_from_total (left : alloc.vec.Vec ObjectPropertyExpression) (right : AtLeastTwo ObjectPropertyExpression) (index : Usize) :
    properties_association_subset_from left right index = .ok (decide (∀ item ∈ left.val.drop index.val, item ∈ right.elements)) :=
  by
    have total := all_total left (fun item => properties_member item right) (fun item => item ∈ right.elements)
      (properties_association_subset_from left right) (fun i => by rw [properties_association_subset_from])
      (fun item _ => by
        rw [properties_member_total]
        exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)) index
    rw [total]
    exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)
private theorem properties_association_subset_total (left right : AtLeastTwo ObjectPropertyExpression) :
    properties_association_subset left right = .ok (decide (∀ item ∈ left.elements, item ∈ right.elements)) := by
  have split : (∀ item ∈ left.elements, item ∈ right.elements) ↔
      left.first ∈ right.elements ∧ left.second ∈ right.elements ∧ ∀ item ∈ left.rest.val, item ∈ right.elements := by
    change (∀ item ∈ left.first :: left.second :: left.rest.val, item ∈ right.elements) ↔ _
    simp only [List.forall_mem_cons]
  rw [properties_association_subset]
  simp only [properties_member_total,properties_association_subset_from_total,
    show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,and_ok]
  exact congrArg Result.ok (decide_eq_decide.mpr split.symm)
/-- Written repetitions do not change unordered structural membership. -/
theorem same_properties_association_total_correct (left right : AtLeastTwo ObjectPropertyExpression) :
    same_properties_association left right = .ok (decide (SetEq left.elements right.elements)) := by
  rw [same_properties_association]
  by_cases forward : ∀ a ∈ left.elements, a ∈ right.elements <;>
    simp [properties_association_subset_total,forward,set_eq_iff_subsets]
  all_goals repeat' split <;> simp_all

private theorem data_properties_contains_total (values : alloc.vec.Vec DataProperty) (sought : DataProperty) (index : Usize) :
    data_properties_contains_from values sought index = .ok (decide (sought ∈ values.val.drop index.val)) := by
  have total := contains_total values (RowlRust.arity.same_data_property sought) (fun item => sought = item) (data_properties_contains_from values sought)
    (fun i => by rw [data_properties_contains_from]) (fun item _ => Rowl.Arity.same_data_property_total_correct sought item) index
  rw [total]
  exact congrArg Result.ok (decide_eq_decide.mpr (by simp))
private theorem data_properties_subset_total (left right : alloc.vec.Vec DataProperty) (index : Usize) :
    data_properties_subset_from left right index = .ok (decide (∀ item ∈ left.val.drop index.val, item ∈ right.val)) :=
  by
    have total := all_total left (fun item => data_properties_contains_from right item 0#usize) (fun item => item ∈ right.val)
      (data_properties_subset_from left right) (fun i => by rw [data_properties_subset_from])
      (fun item _ => by
        rw [data_properties_contains_total]
        exact congrArg Result.ok (decide_eq_decide.mpr (by simp))) index
    rw [total]
    exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)
/-- Complete unordered property association comparison, including empty key lists. -/
theorem same_data_properties_set_total_correct (left right : alloc.vec.Vec DataProperty) :
    same_data_properties_set left right = .ok (decide (SetEq left.val right.val)) := by
  rw [same_data_properties_set]
  by_cases forward : ∀ a ∈ left.val, a ∈ right.val <;>
    simp [data_properties_subset_total,forward,set_eq_iff_subsets]
  all_goals repeat' split <;> simp_all
private theorem data_properties_member_total (sought : DataProperty) (values : AtLeastTwo DataProperty) :
    data_properties_member sought values = .ok (decide (sought ∈ values.elements)) := by
  by_cases first : sought = values.first <;> by_cases second : sought = values.second <;>
    simp [data_properties_member,Rowl.Arity.same_data_property_total_correct,data_properties_contains_total,AtLeastTwo.elements,first,second]
private theorem data_properties_association_subset_from_total (left : alloc.vec.Vec DataProperty) (right : AtLeastTwo DataProperty) (index : Usize) :
    data_properties_association_subset_from left right index = .ok (decide (∀ item ∈ left.val.drop index.val, item ∈ right.elements)) :=
  by
    have total := all_total left (fun item => data_properties_member item right) (fun item => item ∈ right.elements)
      (data_properties_association_subset_from left right) (fun i => by rw [data_properties_association_subset_from])
      (fun item _ => by
        rw [data_properties_member_total]
        exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)) index
    rw [total]
    exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)
private theorem data_properties_association_subset_total (left right : AtLeastTwo DataProperty) :
    data_properties_association_subset left right = .ok (decide (∀ item ∈ left.elements, item ∈ right.elements)) := by
  have split : (∀ item ∈ left.elements, item ∈ right.elements) ↔
      left.first ∈ right.elements ∧ left.second ∈ right.elements ∧ ∀ item ∈ left.rest.val, item ∈ right.elements := by
    change (∀ item ∈ left.first :: left.second :: left.rest.val, item ∈ right.elements) ↔ _
    simp only [List.forall_mem_cons]
  rw [data_properties_association_subset]
  simp only [data_properties_member_total,data_properties_association_subset_from_total,
    show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,and_ok]
  exact congrArg Result.ok (decide_eq_decide.mpr split.symm)
/-- Written repetitions do not change unordered structural membership. -/
theorem same_data_properties_association_total_correct (left right : AtLeastTwo DataProperty) :
    same_data_properties_association left right = .ok (decide (SetEq left.elements right.elements)) := by
  rw [same_data_properties_association]
  by_cases forward : ∀ a ∈ left.elements, a ∈ right.elements <;>
    simp [data_properties_association_subset_total,forward,set_eq_iff_subsets]
  all_goals repeat' split <;> simp_all

private theorem individuals_contains_total (values : alloc.vec.Vec Individual) (sought : Individual) (index : Usize) :
    individuals_contains_from values sought index = .ok (decide (sought ∈ values.val.drop index.val)) := by
  have total := contains_total values (RowlRust.assertion_equality.same_individual_value sought) (fun item => sought = item) (individuals_contains_from values sought)
    (fun i => by rw [individuals_contains_from]) (fun item _ => same_individual_value_total_correct sought item) index
  rw [total]
  exact congrArg Result.ok (decide_eq_decide.mpr (by simp))
private theorem individuals_member_total (sought : Individual) (values : AtLeastTwo Individual) :
    individuals_member sought values = .ok (decide (sought ∈ values.elements)) := by
  by_cases first : sought = values.first <;> by_cases second : sought = values.second <;>
    simp [individuals_member,same_individual_value_total_correct,individuals_contains_total,AtLeastTwo.elements,first,second]
private theorem individuals_association_subset_from_total (left : alloc.vec.Vec Individual) (right : AtLeastTwo Individual) (index : Usize) :
    individuals_association_subset_from left right index = .ok (decide (∀ item ∈ left.val.drop index.val, item ∈ right.elements)) :=
  by
    have total := all_total left (fun item => individuals_member item right) (fun item => item ∈ right.elements)
      (individuals_association_subset_from left right) (fun i => by rw [individuals_association_subset_from])
      (fun item _ => by
        rw [individuals_member_total]
        exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)) index
    rw [total]
    exact congrArg Result.ok (decide_eq_decide.mpr Iff.rfl)
private theorem individuals_association_subset_total (left right : AtLeastTwo Individual) :
    individuals_association_subset left right = .ok (decide (∀ item ∈ left.elements, item ∈ right.elements)) := by
  have split : (∀ item ∈ left.elements, item ∈ right.elements) ↔
      left.first ∈ right.elements ∧ left.second ∈ right.elements ∧ ∀ item ∈ left.rest.val, item ∈ right.elements := by
    change (∀ item ∈ left.first :: left.second :: left.rest.val, item ∈ right.elements) ↔ _
    simp only [List.forall_mem_cons]
  rw [individuals_association_subset]
  simp only [individuals_member_total,individuals_association_subset_from_total,
    show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,and_ok]
  exact congrArg Result.ok (decide_eq_decide.mpr split.symm)
/-- Written repetitions do not change unordered structural membership. -/
theorem same_individuals_association_total_correct (left right : AtLeastTwo Individual) :
    same_individuals_association left right = .ok (decide (SetEq left.elements right.elements)) := by
  rw [same_individuals_association]
  by_cases forward : ∀ a ∈ left.elements, a ∈ right.elements <;>
    simp [individuals_association_subset_total,forward,set_eq_iff_subsets]
  all_goals repeat' split <;> simp_all

private theorem chain_equal_total (left right : alloc.vec.Vec ObjectPropertyExpression)
    (length : left.val.length = right.val.length) (index : Usize) :
    chain_equal_from left right index = .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [chain_equal_from]
  by_cases inside : index.val < left.val.length
  · have other : index.val < right.val.length := by omega
    have lookup : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have rightLookup : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem other]
    by_cases heads : left.val[index.val] = right.val[index.val]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val+1 := by simpa using nextval
      have recurse := chain_equal_total left right length next
      simp [inside,lookup,rightLookup,same_property_total_correct,heads,advance,recurse]
      rw [List.drop_eq_getElem_cons inside,List.drop_eq_getElem_cons other]
      simp only [List.cons.injEq,heads,true_and,nv]
    · simp [inside,lookup,rightLookup,same_property_total_correct,heads]
      rw [List.drop_eq_getElem_cons inside,List.drop_eq_getElem_cons other]
      simp only [List.cons.injEq,heads,false_and,not_false_eq_true]
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have otherEmpty : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty,otherEmpty]
termination_by left.val.length - index.val
decreasing_by omega
/-- Ordered chains require identical positions, repetitions and total length. -/
theorem same_chain_total_correct (left right : AtLeastTwo ObjectPropertyExpression) :
    same_chain left right = .ok (decide (left.elements = right.elements)) := by
  by_cases first : left.first = right.first <;> by_cases second : left.second = right.second <;>
    simp [same_chain,same_property_total_correct,first,second,AtLeastTwo.elements]
  by_cases length : left.rest.val.length = right.rest.val.length
  · simp [length,chain_equal_total left.rest right.rest length]
  · have unequal : left.rest.val ≠ right.rest.val := fun h => length (congrArg List.length h)
    simp [length,unequal]
/-- A singleton subproperty and an ordered chain remain distinct variants. -/
theorem same_sub_property_total_correct (left right : SubObjectPropertyExpression) :
    same_sub_property left right = .ok (decide (SubPropertyEq left right)) := by
  cases left <;> cases right <;> simp [same_sub_property,SubPropertyEq,same_property_total_correct,same_chain_total_correct]
/-- Total actual-source structural comparison for all thirty-seven body forms. -/
theorem same_body_total_correct (left right : Axiom) :
    same_body left right = .ok (decide (BodyEq left right)) := by
  cases left <;> cases right <;> simp [same_body,BodyEq]
  all_goals simp only [same_entity_total_correct,same_subject_total_correct,same_sub_property_total_correct,
    same_properties_set_total_correct,same_data_properties_set_total_correct,
    same_properties_association_total_correct,same_data_properties_association_total_correct,
    same_individuals_association_total_correct,Rowl.ClassEquality.same_class_total_correct,
    Rowl.ClassEquality.same_class_set_total_correct,Rowl.ClassEquality.Members,
    Rowl.RangeEquality.same_range_total_correct,Rowl.Arity.same_data_property_total_correct,
    same_property_total_correct,same_individual_value_total_correct,same_literal_total_correct,
    same_annotation_value_total_correct,Rowl.Symbols.same_spelling_total_correct,
    class_eq,datatype_eq,annotation_property_eq,iri_eq,class_iri_eq,datatype_iri_eq,annotation_property_iri_eq,AtLeastTwo.elements,bind_ok,and_ok]
  all_goals simp
  all_goals exact congrArg₂ Bool.and (decide_eq_decide.mpr Iff.rfl) (decide_eq_decide.mpr Iff.rfl)
/-- Complete annotated structural comparison preserves metadata membership. -/
theorem same_axiom_total_correct (left right : AnnotatedAxiom) :
    same_axiom left right = .ok (decide (AxiomEq left right)) := by
  by_cases body : BodyEq left.axiom right.axiom <;>
    simp [same_axiom,AxiomEq,same_body_total_correct,same_annotation_set_total_correct,body]

private theorem sub_property_eq_iff (left right : SubObjectPropertyExpression) :
    SubPropertyEq left right ↔ left = right := by
  cases left <;> cases right <;> simp [SubPropertyEq]
  rename_i a b
  cases a; cases b
  simp [AtLeastTwo.elements]
private theorem set_eq_refl {α : Type} (values : List α) : SetEq values values := fun _ => Iff.rfl
private theorem set_eq_symm {α : Type} {left right : List α} (equal : SetEq left right) : SetEq right left :=
  fun value => (equal value).symm
private theorem set_eq_trans {α : Type} {left middle right : List α}
    (first : SetEq left middle) (second : SetEq middle right) : SetEq left right :=
  fun value => (first value).trans (second value)
private theorem class_set_refl (values : List ClassExpression) : ClassSetEq values values :=
  ⟨fun a mem => ⟨a,mem,Rowl.ClassEquality.class_eq_refl a⟩,
    fun a mem => ⟨a,mem,Rowl.ClassEquality.class_eq_refl a⟩⟩
private theorem class_set_symm {left right : List ClassExpression} (equal : ClassSetEq left right) :
    ClassSetEq right left := ⟨equal.2,equal.1⟩
private theorem class_set_trans {left middle right : List ClassExpression}
    (first : ClassSetEq left middle) (second : ClassSetEq middle right) : ClassSetEq left right := by
  constructor
  · intro a mem
    obtain ⟨b,mb,ab⟩ := first.1 a mem
    obtain ⟨c,mc,bc⟩ := second.1 b mb
    exact ⟨c,mc,Rowl.ClassEquality.class_eq_trans a b c ab bc⟩
  · intro c mem
    obtain ⟨b,mb,cb⟩ := second.2 c mem
    obtain ⟨a,ma,ba⟩ := first.2 b mb
    exact ⟨a,ma,Rowl.ClassEquality.class_eq_trans c b a cb ba⟩
/-- Reflexivity covers every body constructor, including raw duplicate lists. -/
theorem body_eq_refl (value : Axiom) : BodyEq value value := by
  cases value <;> simp [BodyEq,sub_property_eq_iff,Rowl.ClassEquality.class_eq_refl,
    Rowl.RangeEquality.range_eq_refl,set_eq_refl,class_set_refl]
/-- Structural identity is symmetric for all axiom forms. -/
theorem body_eq_symm (left right : Axiom) (equal : BodyEq left right) : BodyEq right left := by
  cases left <;> cases right <;> simp only [BodyEq,sub_property_eq_iff] at equal ⊢
  case Declaration.Declaration =>
    have f0 := equal
    exact f0.symm
  case SubClassOf.SubClassOf =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨Rowl.ClassEquality.class_eq_symm _ _ f0,Rowl.ClassEquality.class_eq_symm _ _ f1⟩
  case EquivalentClasses.EquivalentClasses =>
    have f0 := equal
    exact class_set_symm f0
  case DisjointClasses.DisjointClasses =>
    have f0 := equal
    exact class_set_symm f0
  case DisjointUnion.DisjointUnion =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,class_set_symm f1⟩
  case SubObjectPropertyOf.SubObjectPropertyOf =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,f1.symm⟩
  case EquivalentObjectProperties.EquivalentObjectProperties =>
    have f0 := equal
    exact set_eq_symm f0
  case DisjointObjectProperties.DisjointObjectProperties =>
    have f0 := equal
    exact set_eq_symm f0
  case InverseObjectProperties.InverseObjectProperties =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,f1.symm⟩
  case ObjectPropertyDomain.ObjectPropertyDomain =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,Rowl.ClassEquality.class_eq_symm _ _ f1⟩
  case ObjectPropertyRange.ObjectPropertyRange =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,Rowl.ClassEquality.class_eq_symm _ _ f1⟩
  case FunctionalObjectProperty.FunctionalObjectProperty =>
    have f0 := equal
    exact f0.symm
  case InverseFunctionalObjectProperty.InverseFunctionalObjectProperty =>
    have f0 := equal
    exact f0.symm
  case ReflexiveObjectProperty.ReflexiveObjectProperty =>
    have f0 := equal
    exact f0.symm
  case IrreflexiveObjectProperty.IrreflexiveObjectProperty =>
    have f0 := equal
    exact f0.symm
  case SymmetricObjectProperty.SymmetricObjectProperty =>
    have f0 := equal
    exact f0.symm
  case AsymmetricObjectProperty.AsymmetricObjectProperty =>
    have f0 := equal
    exact f0.symm
  case TransitiveObjectProperty.TransitiveObjectProperty =>
    have f0 := equal
    exact f0.symm
  case SubDataPropertyOf.SubDataPropertyOf =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,f1.symm⟩
  case EquivalentDataProperties.EquivalentDataProperties =>
    have f0 := equal
    exact set_eq_symm f0
  case DisjointDataProperties.DisjointDataProperties =>
    have f0 := equal
    exact set_eq_symm f0
  case DataPropertyDomain.DataPropertyDomain =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,Rowl.ClassEquality.class_eq_symm _ _ f1⟩
  case DataPropertyRange.DataPropertyRange =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,Rowl.RangeEquality.range_eq_symm _ _ f1⟩
  case FunctionalDataProperty.FunctionalDataProperty =>
    have f0 := equal
    exact f0.symm
  case DatatypeDefinition.DatatypeDefinition =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,Rowl.RangeEquality.range_eq_symm _ _ f1⟩
  case HasKey.HasKey =>
    rcases equal with ⟨f0,f1,f2⟩
    exact ⟨Rowl.ClassEquality.class_eq_symm _ _ f0,set_eq_symm f1,set_eq_symm f2⟩
  case SameIndividual.SameIndividual =>
    have f0 := equal
    exact set_eq_symm f0
  case DifferentIndividuals.DifferentIndividuals =>
    have f0 := equal
    exact set_eq_symm f0
  case ClassAssertion.ClassAssertion =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨Rowl.ClassEquality.class_eq_symm _ _ f0,f1.symm⟩
  case ObjectPropertyAssertion.ObjectPropertyAssertion =>
    rcases equal with ⟨f0,f1,f2⟩
    exact ⟨f0.symm,f1.symm,f2.symm⟩
  case NegativeObjectPropertyAssertion.NegativeObjectPropertyAssertion =>
    rcases equal with ⟨f0,f1,f2⟩
    exact ⟨f0.symm,f1.symm,f2.symm⟩
  case DataPropertyAssertion.DataPropertyAssertion =>
    rcases equal with ⟨f0,f1,f2⟩
    exact ⟨f0.symm,f1.symm,f2.symm⟩
  case NegativeDataPropertyAssertion.NegativeDataPropertyAssertion =>
    rcases equal with ⟨f0,f1,f2⟩
    exact ⟨f0.symm,f1.symm,f2.symm⟩
  case AnnotationAssertion.AnnotationAssertion =>
    rcases equal with ⟨f0,f1,f2⟩
    exact ⟨f0.symm,f1.symm,f2.symm⟩
  case SubAnnotationPropertyOf.SubAnnotationPropertyOf =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,f1.symm⟩
  case AnnotationPropertyDomain.AnnotationPropertyDomain =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,f1.symm⟩
  case AnnotationPropertyRange.AnnotationPropertyRange =>
    rcases equal with ⟨f0,f1⟩
    exact ⟨f0.symm,f1.symm⟩
/-- Whole-body structural comparison composes through arbitrary raw copies. -/
theorem body_eq_trans (left middle right : Axiom)
    (first : BodyEq left middle) (second : BodyEq middle right) : BodyEq left right := by
  cases left <;> cases middle <;> simp only [BodyEq,sub_property_eq_iff] at first
  all_goals cases right <;> simp only [BodyEq,sub_property_eq_iff] at second ⊢
  case Declaration.Declaration.Declaration =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case SubClassOf.SubClassOf.SubClassOf =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨Rowl.ClassEquality.class_eq_trans _ _ _ f0 g0,Rowl.ClassEquality.class_eq_trans _ _ _ f1 g1⟩
  case EquivalentClasses.EquivalentClasses.EquivalentClasses =>
    have f0 := first
    have g0 := second
    exact class_set_trans f0 g0
  case DisjointClasses.DisjointClasses.DisjointClasses =>
    have f0 := first
    have g0 := second
    exact class_set_trans f0 g0
  case DisjointUnion.DisjointUnion.DisjointUnion =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,class_set_trans f1 g1⟩
  case SubObjectPropertyOf.SubObjectPropertyOf.SubObjectPropertyOf =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,f1.trans g1⟩
  case EquivalentObjectProperties.EquivalentObjectProperties.EquivalentObjectProperties =>
    have f0 := first
    have g0 := second
    exact set_eq_trans f0 g0
  case DisjointObjectProperties.DisjointObjectProperties.DisjointObjectProperties =>
    have f0 := first
    have g0 := second
    exact set_eq_trans f0 g0
  case InverseObjectProperties.InverseObjectProperties.InverseObjectProperties =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,f1.trans g1⟩
  case ObjectPropertyDomain.ObjectPropertyDomain.ObjectPropertyDomain =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,Rowl.ClassEquality.class_eq_trans _ _ _ f1 g1⟩
  case ObjectPropertyRange.ObjectPropertyRange.ObjectPropertyRange =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,Rowl.ClassEquality.class_eq_trans _ _ _ f1 g1⟩
  case FunctionalObjectProperty.FunctionalObjectProperty.FunctionalObjectProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case InverseFunctionalObjectProperty.InverseFunctionalObjectProperty.InverseFunctionalObjectProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case ReflexiveObjectProperty.ReflexiveObjectProperty.ReflexiveObjectProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case IrreflexiveObjectProperty.IrreflexiveObjectProperty.IrreflexiveObjectProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case SymmetricObjectProperty.SymmetricObjectProperty.SymmetricObjectProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case AsymmetricObjectProperty.AsymmetricObjectProperty.AsymmetricObjectProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case TransitiveObjectProperty.TransitiveObjectProperty.TransitiveObjectProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case SubDataPropertyOf.SubDataPropertyOf.SubDataPropertyOf =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,f1.trans g1⟩
  case EquivalentDataProperties.EquivalentDataProperties.EquivalentDataProperties =>
    have f0 := first
    have g0 := second
    exact set_eq_trans f0 g0
  case DisjointDataProperties.DisjointDataProperties.DisjointDataProperties =>
    have f0 := first
    have g0 := second
    exact set_eq_trans f0 g0
  case DataPropertyDomain.DataPropertyDomain.DataPropertyDomain =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,Rowl.ClassEquality.class_eq_trans _ _ _ f1 g1⟩
  case DataPropertyRange.DataPropertyRange.DataPropertyRange =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,Rowl.RangeEquality.range_eq_trans _ _ _ f1 g1⟩
  case FunctionalDataProperty.FunctionalDataProperty.FunctionalDataProperty =>
    have f0 := first
    have g0 := second
    exact f0.trans g0
  case DatatypeDefinition.DatatypeDefinition.DatatypeDefinition =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,Rowl.RangeEquality.range_eq_trans _ _ _ f1 g1⟩
  case HasKey.HasKey.HasKey =>
    rcases first with ⟨f0,f1,f2⟩
    rcases second with ⟨g0,g1,g2⟩
    exact ⟨Rowl.ClassEquality.class_eq_trans _ _ _ f0 g0,set_eq_trans f1 g1,set_eq_trans f2 g2⟩
  case SameIndividual.SameIndividual.SameIndividual =>
    have f0 := first
    have g0 := second
    exact set_eq_trans f0 g0
  case DifferentIndividuals.DifferentIndividuals.DifferentIndividuals =>
    have f0 := first
    have g0 := second
    exact set_eq_trans f0 g0
  case ClassAssertion.ClassAssertion.ClassAssertion =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨Rowl.ClassEquality.class_eq_trans _ _ _ f0 g0,f1.trans g1⟩
  case ObjectPropertyAssertion.ObjectPropertyAssertion.ObjectPropertyAssertion =>
    rcases first with ⟨f0,f1,f2⟩
    rcases second with ⟨g0,g1,g2⟩
    exact ⟨f0.trans g0,f1.trans g1,f2.trans g2⟩
  case NegativeObjectPropertyAssertion.NegativeObjectPropertyAssertion.NegativeObjectPropertyAssertion =>
    rcases first with ⟨f0,f1,f2⟩
    rcases second with ⟨g0,g1,g2⟩
    exact ⟨f0.trans g0,f1.trans g1,f2.trans g2⟩
  case DataPropertyAssertion.DataPropertyAssertion.DataPropertyAssertion =>
    rcases first with ⟨f0,f1,f2⟩
    rcases second with ⟨g0,g1,g2⟩
    exact ⟨f0.trans g0,f1.trans g1,f2.trans g2⟩
  case NegativeDataPropertyAssertion.NegativeDataPropertyAssertion.NegativeDataPropertyAssertion =>
    rcases first with ⟨f0,f1,f2⟩
    rcases second with ⟨g0,g1,g2⟩
    exact ⟨f0.trans g0,f1.trans g1,f2.trans g2⟩
  case AnnotationAssertion.AnnotationAssertion.AnnotationAssertion =>
    rcases first with ⟨f0,f1,f2⟩
    rcases second with ⟨g0,g1,g2⟩
    exact ⟨f0.trans g0,f1.trans g1,f2.trans g2⟩
  case SubAnnotationPropertyOf.SubAnnotationPropertyOf.SubAnnotationPropertyOf =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,f1.trans g1⟩
  case AnnotationPropertyDomain.AnnotationPropertyDomain.AnnotationPropertyDomain =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,f1.trans g1⟩
  case AnnotationPropertyRange.AnnotationPropertyRange.AnnotationPropertyRange =>
    rcases first with ⟨f0,f1⟩
    rcases second with ⟨g0,g1⟩
    exact ⟨f0.trans g0,f1.trans g1⟩
/-- Complete identity remains reflexive with nested annotation sets. -/
theorem axiom_eq_refl (value : AnnotatedAxiom) : AxiomEq value value :=
  ⟨body_eq_refl value.axiom,annotation_set_equivalence.refl value.annotations.val⟩
/-- Metadata and body equivalence are both symmetric. -/
theorem axiom_eq_symm (left right : AnnotatedAxiom) (equal : AxiomEq left right) : AxiomEq right left :=
  ⟨body_eq_symm left.axiom right.axiom equal.1,annotation_set_equivalence.symm equal.2⟩
/-- Complete structural identity is an equivalence relation. -/
theorem axiom_eq_trans (left middle right : AnnotatedAxiom)
    (first : AxiomEq left middle) (second : AxiomEq middle right) : AxiomEq left right :=
  ⟨body_eq_trans left.axiom middle.axiom right.axiom first.1 second.1,
    annotation_set_equivalence.trans first.2 second.2⟩
/-- Existing positive-assertion restrictions use the same complete identity. -/
theorem object_assertion_compatibility (left right : AnnotatedAxiom)
    (p : ObjectPropertyExpression) (a b : Individual)
    (body : left.axiom = .ObjectPropertyAssertion p a b) :
    AxiomEq left right ↔ AssertionEq left right := by
  cases h : right.axiom <;> simp [AxiomEq,BodyEq,AssertionEq,body,h,and_assoc]
/-- Existing datatype-definition restrictions agree with complete identity. -/
theorem datatype_definition_compatibility (left right : AnnotatedAxiom)
    (datatype : Datatype) (range : DataRange)
    (body : left.axiom = .DatatypeDefinition datatype range) :
    AxiomEq left right ↔ Rowl.RangeEquality.DefinitionEq left right := by
  cases h : right.axiom <;> simp [AxiomEq,BodyEq,Rowl.RangeEquality.DefinitionEq,body,h,and_assoc]

end Rowl.AxiomEquality
