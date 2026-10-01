import Rowl.AnonymousGraph

namespace Rowl.AssertionEquality
open Aeneas Aeneas.Std RowlRust.model RowlRust.assertion_equality
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

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

private theorem iri_eq (left right : Iri) : left.spelling.val = right.spelling.val ↔ left = right := by
  cases left; cases right
  simp

/-- Literal structural equality preserves exact lexical spelling and datatype;
    datatype-value equivalence is deliberately a different relation. -/
theorem same_literal_total_correct (left right : Literal) :
    same_literal left right = .ok (decide (left = right)) := by
  cases left with
  | mk a dt =>
    cases right with
    | mk b du =>
      cases dt with
      | mk x =>
        cases du with
        | mk y =>
          by_cases text : a.val = b.val <;>
            simp [same_literal,Rowl.Symbols.same_spelling_total_correct,text,iri_eq]

/-- Value variants remain distinct, even when their printed text is equal. -/
theorem same_annotation_value_total_correct (left right : AnnotationValue) :
    same_annotation_value left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;>
    simp [same_annotation_value,Rowl.Symbols.same_spelling_total_correct,iri_eq,
      Rowl.AnonymousGraph.same_individual_total_correct,
      Rowl.AnonymousGraph.key_injective.eq_iff,same_literal_total_correct]

/-- Named and anonymous identities compare structurally, not by denotation. -/
theorem same_individual_value_total_correct (left right : Individual) :
    same_individual_value left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;>
    simp [same_individual_value,Rowl.Symbols.same_spelling_total_correct,
      Rowl.AnonymousGraph.same_individual_total_correct,Rowl.AnonymousGraph.key_injective.eq_iff]
  all_goals rename_i a b; cases a; cases b; simp [iri_eq]

/-- A direct property and its inverse are structurally different expressions. -/
theorem same_property_total_correct (left right : ObjectPropertyExpression) :
    same_property left right = .ok (decide (left = right)) := by
  cases left <;> cases right <;> simp [same_property,Rowl.Symbols.same_spelling_total_correct]
  all_goals rename_i a b; cases a; cases b; simp [iri_eq]

/-- Recursive OWL structural equivalence of annotations: atomic property/value
    identity and mutual membership at every unordered association. -/
def AnnotationEq (left right : Annotation) : Prop :=
  match left, right with
  | .mk xs p v, .mk ys q w => p = q ∧ v = w ∧
      (∀ a : {a // a ∈ xs.val}, ∃ b : {b // b ∈ ys.val}, AnnotationEq a.val b.val) ∧
      (∀ b : {b // b ∈ ys.val}, ∃ a : {a // a ∈ xs.val}, AnnotationEq a.val b.val)
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals
    have leftSize := vec_mem_size xs a.property
    have rightSize := vec_mem_size ys b.property
    simp_wf
    omega

/-- Extensional set comparison retains recursively equivalent members, not order
    or the number of repeated equivalent occurrences. -/
def AnnotationSetEq (left right : List Annotation) : Prop :=
  (∀ a ∈ left, ∃ b ∈ right, AnnotationEq a b) ∧
  (∀ b ∈ right, ∃ a ∈ left, AnnotationEq a b)

private theorem annotation_eq_fields (left right : Annotation) :
    AnnotationEq left right ↔ left.property = right.property ∧ left.value = right.value ∧
      AnnotationSetEq left.annotations.val right.annotations.val := by
  cases left; cases right
  simp [AnnotationEq,AnnotationSetEq]

/-- Structural equivalence is reflexive even on raw duplicate annotation lists. -/
theorem annotation_eq_refl (value : Annotation) : AnnotationEq value value := by
  cases value with
  | mk xs p v =>
    rw [AnnotationEq]
    refine ⟨rfl,rfl,?_,?_⟩
    · intro child; exact ⟨child,annotation_eq_refl child.val⟩
    · intro child; exact ⟨child,annotation_eq_refl child.val⟩
termination_by sizeOf value
decreasing_by
  all_goals have := vec_mem_size xs child.property; simp_wf; omega

/-- The recursive equivalence does not privilege either association order. -/
theorem annotation_eq_symm (left right : Annotation) (equal : AnnotationEq left right) :
    AnnotationEq right left := by
  cases hLeft : left with
  | mk xs p v =>
    cases hRight : right with
    | mk ys q w =>
      simp only [hLeft,hRight] at equal ⊢
      rw [AnnotationEq] at equal ⊢
      rcases equal with ⟨prop,value,forward,backward⟩
      refine ⟨prop.symm,value.symm,?_,?_⟩
      · intro b
        obtain ⟨a,equal⟩ := backward b
        exact ⟨a,annotation_eq_symm a.val b.val equal⟩
      · intro a
        obtain ⟨b,equal⟩ := forward a
        exact ⟨b,annotation_eq_symm a.val b.val equal⟩
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals
    have := vec_mem_size xs a.property
    have := vec_mem_size ys b.property
    simp_all only [hLeft,hRight,Annotation.mk.sizeOf_spec]
    omega

/-- Mutual membership composes through arbitrary nested duplicate associations. -/
theorem annotation_eq_trans (left middle right : Annotation)
    (first : AnnotationEq left middle) (second : AnnotationEq middle right) : AnnotationEq left right := by
  cases hLeft : left with
  | mk xs p v =>
    cases hMiddle : middle with
    | mk ys q w =>
      cases hRight : right with
      | mk zs r u =>
        simp only [hLeft,hMiddle,hRight] at first second ⊢
        rw [AnnotationEq] at first second ⊢
        rcases first with ⟨prop1,value1,forward1,backward1⟩
        rcases second with ⟨prop2,value2,forward2,backward2⟩
        refine ⟨prop1.trans prop2,value1.trans value2,?_,?_⟩
        · intro a
          obtain ⟨b,ab⟩ := forward1 a
          obtain ⟨c,bc⟩ := forward2 b
          exact ⟨c,annotation_eq_trans a.val b.val c.val ab bc⟩
        · intro c
          obtain ⟨b,bc⟩ := backward2 c
          obtain ⟨a,ab⟩ := backward1 b
          exact ⟨a,annotation_eq_trans a.val b.val c.val ab bc⟩
termination_by sizeOf left + sizeOf middle + sizeOf right
decreasing_by
  all_goals
    have := vec_mem_size xs a.property
    have := vec_mem_size ys b.property
    have := vec_mem_size zs c.property
    simp_all only [hLeft,hMiddle,hRight,Annotation.mk.sizeOf_spec]
    omega

/-- Annotation association equality is a genuine equivalence relation. -/
theorem annotation_set_equivalence : Equivalence AnnotationSetEq := by
  constructor
  · intro values
    exact ⟨fun a mem => ⟨a,mem,annotation_eq_refl a⟩,fun a mem => ⟨a,mem,annotation_eq_refl a⟩⟩
  · intro xs ys equal
    constructor
    · intro b mem; obtain ⟨a,member,eq⟩ := equal.2 b mem
      exact ⟨a,member,annotation_eq_symm a b eq⟩
    · intro a mem; obtain ⟨b,member,eq⟩ := equal.1 a mem
      exact ⟨b,member,annotation_eq_symm a b eq⟩
  · intro xs ys zs first second
    constructor
    · intro a mem
      obtain ⟨b,mb,ab⟩ := first.1 a mem
      obtain ⟨c,mc,bc⟩ := second.1 b mb
      exact ⟨c,mc,annotation_eq_trans a b c ab bc⟩
    · intro c mem
      obtain ⟨b,mb,bc⟩ := second.2 c mem
      obtain ⟨a,ma,ab⟩ := first.2 b mb
      exact ⟨a,ma,annotation_eq_trans a b c ab bc⟩

private theorem contains_total_of (values : alloc.vec.Vec Annotation) (sought : Annotation)
    (child : ∀ item ∈ values.val, same_annotation sought item = .ok (decide (AnnotationEq sought item)))
    (index : Usize) :
    contains_from values sought index =
      .ok (decide (∃ item ∈ values.val.drop index.val, AnnotationEq sought item)) := by
  rw [contains_from]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := child values.val[index.val] (List.getElem_mem inside)
    have splitting : (∃ item ∈ values.val.drop index.val, AnnotationEq sought item) ↔
        AnnotationEq sought values.val[index.val] ∨
          ∃ item ∈ values.val.drop (index.val + 1), AnnotationEq sought item := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons,exists_eq_or_imp]
    have splitBool : decide (∃ item ∈ values.val.drop index.val, AnnotationEq sought item) =
        decide (AnnotationEq sought values.val[index.val] ∨
          ∃ item ∈ values.val.drop (index.val + 1), AnnotationEq sought item) :=
      decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases found : AnnotationEq sought values.val[index.val]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_true,true_or]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := contains_total_of values sought child next
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_false,
        Bool.false_eq_true,advance,recursive,nv,false_or]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,empty,
      List.not_mem_nil,false_and,exists_false,decide_false]
termination_by values.val.length - index.val
decreasing_by omega

private theorem subset_total_of (left right : alloc.vec.Vec Annotation)
    (child : ∀ a ∈ left.val, ∀ b ∈ right.val, same_annotation a b = .ok (decide (AnnotationEq a b)))
    (index : Usize) :
    subset_from left right index =
      .ok (decide (∀ a ∈ left.val.drop index.val, ∃ b ∈ right.val, AnnotationEq a b)) := by
  rw [subset_from]
  by_cases inside : index.val < left.val.length
  · have lookup : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head : contains_from right left.val[index.val] 0#usize =
        .ok (decide (∃ b ∈ right.val, AnnotationEq left.val[index.val] b)) := by
      simpa only [show (0#usize).val = 0 from rfl,List.drop_zero] using
        contains_total_of right left.val[index.val]
          (child left.val[index.val] (List.getElem_mem inside)) 0#usize
    have splitting : (∀ a ∈ left.val.drop index.val, ∃ b ∈ right.val, AnnotationEq a b) ↔
        (∃ b ∈ right.val, AnnotationEq left.val[index.val] b) ∧
          ∀ a ∈ left.val.drop (index.val + 1), ∃ b ∈ right.val, AnnotationEq a b := by
      rw [List.drop_eq_getElem_cons inside]
      exact List.forall_mem_cons
    have splitBool : decide (∀ a ∈ left.val.drop index.val, ∃ b ∈ right.val, AnnotationEq a b) =
        decide ((∃ b ∈ right.val, AnnotationEq left.val[index.val] b) ∧
          ∀ a ∈ left.val.drop (index.val + 1), ∃ b ∈ right.val, AnnotationEq a b) :=
      decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases found : ∃ b ∈ right.val, AnnotationEq left.val[index.val] b
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := subset_total_of left right child next
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,
        found,decide_true,advance,recursive,nv,true_and]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,
        found,decide_false,Bool.false_eq_true,false_and]
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have vacuous : ∀ a ∈ left.val.drop index.val, ∃ b ∈ right.val, AnnotationEq a b := by
      rw [empty]; intro a mem; cases mem
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_true vacuous).symm
termination_by left.val.length - index.val
decreasing_by omega

private theorem annotation_set_total_of (left right : alloc.vec.Vec Annotation)
    (forward : ∀ a ∈ left.val, ∀ b ∈ right.val, same_annotation a b = .ok (decide (AnnotationEq a b)))
    (backward : ∀ b ∈ right.val, ∀ a ∈ left.val, same_annotation b a = .ok (decide (AnnotationEq b a))) :
    same_annotation_set left right = .ok (decide (AnnotationSetEq left.val right.val)) := by
  rw [same_annotation_set,subset_total_of left right forward 0#usize]
  by_cases all : ∀ a ∈ left.val, ∃ b ∈ right.val, AnnotationEq a b
  · have reverse : (∀ b ∈ right.val, ∃ a ∈ left.val, AnnotationEq b a) ↔
        ∀ b ∈ right.val, ∃ a ∈ left.val, AnnotationEq a b := by
      constructor <;> intro h b mb <;> obtain ⟨a,ma,equal⟩ := h b mb
      · exact ⟨a,ma,annotation_eq_symm b a equal⟩
      · exact ⟨a,ma,annotation_eq_symm a b equal⟩
    have forwardTrue := decide_eq_true all
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,
      forwardTrue,↓reduceIte,subset_total_of right left backward 0#usize]
    apply congrArg Result.ok
    apply decide_eq_decide.mpr
    exact reverse.trans (and_iff_right all).symm
  · have forwardFalse := decide_eq_false all
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,forwardFalse,
      Bool.false_eq_true,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_false (fun equal : AnnotationSetEq left.val right.val => all equal.1)).symm

/-- The actual recursive comparator is total and exact for OWL annotation
    structural equivalence, including all nested unordered associations. -/
theorem same_annotation_total_correct (left right : Annotation) :
    same_annotation left right = .ok (decide (AnnotationEq left right)) := by
  cases left with
  | mk xs p v =>
    cases right with
    | mk ys q w =>
      have nested := annotation_set_total_of xs ys
        (fun a _ b _ => same_annotation_total_correct a b)
        (fun b _ a _ => same_annotation_total_correct b a)
      rw [same_annotation,Rowl.Symbols.same_spelling_total_correct,annotation_eq_fields]
      by_cases property : p.iri = q.iri <;> by_cases value : v = w <;>
        simp [iri_eq,property,value,same_annotation_value_total_correct,nested,
          ]
      all_goals cases p; cases q; simp_all
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals
    have := vec_mem_size xs ‹_ ∈ xs.val›
    have := vec_mem_size ys ‹_ ∈ ys.val›
    simp_wf
    omega

/-- Exact equality of arbitrary finite annotation occurrence lists as sets. -/
theorem same_annotation_set_total_correct (left right : alloc.vec.Vec Annotation) :
    same_annotation_set left right = .ok (decide (AnnotationSetEq left.val right.val)) :=
  annotation_set_total_of left right (fun a _ b _ => same_annotation_total_correct a b)
    (fun b _ a _ => same_annotation_total_correct b a)

/-- Two positive assertions are structurally equivalent precisely when their
    ordered logical fields and recursively unordered annotations are equivalent. -/
def AssertionEq (left right : AnnotatedAxiom) : Prop :=
  match left.axiom, right.axiom with
  | .ObjectPropertyAssertion p a b, .ObjectPropertyAssertion q c d =>
    p = q ∧ a = c ∧ b = d ∧ AnnotationSetEq left.annotations.val right.annotations.val
  | _, _ => False

/-- Actual comparison of positive assertion set members, without dropping metadata. -/
theorem same_object_assertion_total_correct (left right : AnnotatedAxiom) :
    same_object_assertion left right = .ok (decide (AssertionEq left right)) := by
  cases h : left.axiom <;> cases k : right.axiom <;>
    simp [same_object_assertion,AssertionEq,h,k]
  case ObjectPropertyAssertion.ObjectPropertyAssertion p a b q c d =>
    by_cases prop : p = q <;> by_cases source : a = c <;> by_cases target : b = d <;>
      simp [same_property_total_correct,same_individual_value_total_correct,
        same_annotation_set_total_correct,prop,source,target]

end Rowl.AssertionEquality
