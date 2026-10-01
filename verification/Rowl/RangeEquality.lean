import Rowl.AssertionEquality
import Rowl.OwlSemantics

namespace Rowl.RangeEquality
open Aeneas Aeneas.Std RowlRust.model RowlRust.range_equality
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

def Members (xs : AtLeastTwo DataRange) : List DataRange := xs.first :: xs.second :: xs.rest.val

private theorem member_size (xs : AtLeastTwo DataRange) (child : DataRange) (member : child ∈ Members xs) :
    sizeOf child < sizeOf xs := by
  simp only [Members,List.mem_cons] at member
  rcases member with rfl | rfl | member
  · cases xs; simp +arith
  · cases xs; simp +arith
  · have := vec_mem_size xs.rest member
    cases xs; simp_all; omega

/-- Exact extensional equality of an unordered atomic association. -/
def SetEq {α : Type} (left right : List α) : Prop := ∀ value, value ∈ left ↔ value ∈ right

/-- The complete recursive OWL structural-equivalence relation on data ranges.
    Each unordered association uses mutual equivalent membership; constructors,
    nesting, facet/datatype identity and literal spelling remain significant. -/
def RangeEq (left right : DataRange) : Prop :=
  match left,right with
  | .Datatype a,.Datatype b => a = b
  | .Intersection xs,.Intersection ys | .Union xs,.Union ys =>
    (∀ a : {a // a ∈ Members xs}, ∃ b : {b // b ∈ Members ys}, RangeEq a.val b.val) ∧
    (∀ b : {b // b ∈ Members ys}, ∃ a : {a // a ∈ Members xs}, RangeEq b.val a.val)
  | .Complement a,.Complement b => RangeEq a b
  | .OneOf xs,.OneOf ys => SetEq xs.elements ys.elements
  | .Restriction a xs,.Restriction b ys => a = b ∧ SetEq xs.elements ys.elements
  | _,_ => False
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals simp_wf
  all_goals first | omega |
    (have := member_size xs a.val a.property; have := member_size ys b.val b.property; omega)

/-- Recursive unordered range-member association, retaining nested structure. -/
def RangeSetEq (left right : List DataRange) : Prop :=
  (∀ a ∈ left, ∃ b ∈ right, RangeEq a b) ∧ (∀ b ∈ right, ∃ a ∈ left, RangeEq b a)

/-- Only datatype-definition bodies have this equivalence; enclosing metadata
    uses the independently proved recursive annotation-set relation. -/
def DefinitionEq (left right : AnnotatedAxiom) : Prop :=
  match left.axiom,right.axiom with
  | .DatatypeDefinition a x,.DatatypeDefinition b y =>
    a = b ∧ RangeEq x y ∧ AnnotationSetEq left.annotations.val right.annotations.val
  | _,_ => False

private theorem iri_eq (left right : Iri) : left.spelling.val = right.spelling.val ↔ left = right := by
  cases left; cases right; simp
private theorem datatype_eq (left right : Datatype) :
    left.iri.spelling.val = right.iri.spelling.val ↔ left = right := by
  cases left; cases right; simp [iri_eq]

/-- Facet identity includes exact literal lexical form and datatype. -/
theorem same_facet_total_correct (left right : FacetRestriction) :
    same_facet left right = .ok (decide (left = right)) := by
  cases left with
  | mk f l =>
    cases right with
    | mk g m =>
      by_cases iri : f = g <;>
        simp [same_facet,Rowl.Symbols.same_spelling_total_correct,iri_eq,same_literal_total_correct,iri]

private theorem set_eq_iff_subsets {α : Type} (left right : List α) :
    SetEq left right ↔ (∀ a ∈ left, a ∈ right) ∧ (∀ b ∈ right, b ∈ left) := by
  constructor
  · intro equal; exact ⟨fun a mem => (equal a).mp mem,fun b mem => (equal b).mpr mem⟩
  · rintro ⟨forward,backward⟩ a; exact ⟨forward a,backward a⟩


private theorem literal_contains_total (values : alloc.vec.Vec Literal) (sought : Literal) (index : Usize) :
    literal_contains_from values sought index = .ok (decide (sought ∈ values.val.drop index.val)) := by
  rw [literal_contains_from]
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
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,same_literal_total_correct,equal]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := literal_contains_total values sought next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,same_literal_total_correct,equal,advance,recursive,nv]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem literal_member_total (sought : Literal) (values : NonEmpty Literal) :
    literal_member sought values = .ok (decide (sought ∈ values.elements)) := by
  rw [literal_member]
  by_cases equal : sought = values.first <;>
    simp [same_literal_total_correct,equal,literal_contains_total,NonEmpty.elements]

private theorem literal_subset_from_total (left : alloc.vec.Vec Literal) (right : NonEmpty Literal) (index : Usize) :
    literal_subset_from left right index = .ok (decide (∀ a ∈ left.val.drop index.val, a ∈ right.elements)) := by
  rw [literal_subset_from]
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
      have recursive := literal_subset_from_total left right next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,literal_member_total,member,advance,recursive,nv]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,literal_member_total,member]
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by left.val.length - index.val
decreasing_by omega

private theorem literal_subset_total (left right : NonEmpty Literal) :
    literal_subset left right = .ok (decide (∀ a ∈ left.elements, a ∈ right.elements)) := by
  rw [literal_subset,literal_member_total]
  by_cases member : left.first ∈ right.elements
  · simp only [member,decide_true,bind_ok,↓reduceIte,literal_subset_from_total,
      show (0#usize).val = 0 from rfl,List.drop_zero]
    apply congrArg Result.ok
    exact decide_eq_decide.mpr (by simp only [NonEmpty.elements,List.forall_mem_cons]; exact (and_iff_right member).symm)
  · simp only [member,decide_false,bind_ok,Bool.false_eq_true,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_false (by intro valid; exact member (valid _ (by simp [NonEmpty.elements])))).symm

/-- Exact unordered literal membership; equivalent raw repetitions count once. -/
theorem same_literal_set_total_correct (left right : NonEmpty Literal) :
    same_literal_set left right = .ok (decide (SetEq left.elements right.elements)) := by
  rw [same_literal_set,literal_subset_total]
  by_cases forward : ∀ a ∈ left.elements, a ∈ right.elements
  · have yes := decide_eq_true forward
    simp only [yes,bind_ok,↓reduceIte,literal_subset_total]
    apply congrArg Result.ok
    exact decide_eq_decide.mpr ((and_iff_right forward).symm.trans (set_eq_iff_subsets _ _).symm)
  · have no := decide_eq_false forward
    simp only [no,bind_ok,Bool.false_eq_true,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_false (fun equal => forward ((set_eq_iff_subsets _ _).mp equal).1)).symm

private theorem facet_contains_total (values : alloc.vec.Vec FacetRestriction) (sought : FacetRestriction) (index : Usize) :
    facet_contains_from values sought index = .ok (decide (sought ∈ values.val.drop index.val)) := by
  rw [facet_contains_from]
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
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,same_facet_total_correct,equal]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := facet_contains_total values sought next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,same_facet_total_correct,equal,advance,recursive,nv]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by values.val.length - index.val
decreasing_by omega

private theorem facet_member_total (sought : FacetRestriction) (values : NonEmpty FacetRestriction) :
    facet_member sought values = .ok (decide (sought ∈ values.elements)) := by
  rw [facet_member]
  by_cases equal : sought = values.first <;>
    simp [same_facet_total_correct,equal,facet_contains_total,NonEmpty.elements]

private theorem facet_subset_from_total (left : alloc.vec.Vec FacetRestriction) (right : NonEmpty FacetRestriction) (index : Usize) :
    facet_subset_from left right index = .ok (decide (∀ a ∈ left.val.drop index.val, a ∈ right.elements)) := by
  rw [facet_subset_from]
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
      have recursive := facet_subset_from_total left right next
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,facet_member_total,member,advance,recursive,nv]
    · simp [inside,alloc.vec.Vec.index_slice_index,lookup,facet_member_total,member]
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by left.val.length - index.val
decreasing_by omega

private theorem facet_subset_total (left right : NonEmpty FacetRestriction) :
    facet_subset left right = .ok (decide (∀ a ∈ left.elements, a ∈ right.elements)) := by
  rw [facet_subset,facet_member_total]
  by_cases member : left.first ∈ right.elements
  · simp only [member,decide_true,bind_ok,↓reduceIte,facet_subset_from_total,
      show (0#usize).val = 0 from rfl,List.drop_zero]
    apply congrArg Result.ok
    exact decide_eq_decide.mpr (by simp only [NonEmpty.elements,List.forall_mem_cons]; exact (and_iff_right member).symm)
  · simp only [member,decide_false,bind_ok,Bool.false_eq_true,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_false (by intro valid; exact member (valid _ (by simp [NonEmpty.elements])))).symm

/-- Exact unordered facet membership; equivalent raw repetitions count once. -/
theorem same_facet_set_total_correct (left right : NonEmpty FacetRestriction) :
    same_facet_set left right = .ok (decide (SetEq left.elements right.elements)) := by
  rw [same_facet_set,facet_subset_total]
  by_cases forward : ∀ a ∈ left.elements, a ∈ right.elements
  · have yes := decide_eq_true forward
    simp only [yes,bind_ok,↓reduceIte,facet_subset_total]
    apply congrArg Result.ok
    exact decide_eq_decide.mpr ((and_iff_right forward).symm.trans (set_eq_iff_subsets _ _).symm)
  · have no := decide_eq_false forward
    simp only [no,bind_ok,Bool.false_eq_true,↓reduceIte]
    apply congrArg Result.ok
    exact (decide_eq_false (fun equal => forward ((set_eq_iff_subsets _ _).mp equal).1)).symm

private theorem range_set_fields (left right : AtLeastTwo DataRange) :
    ((∀ a : {a // a ∈ Members left}, ∃ b : {b // b ∈ Members right}, RangeEq a.val b.val) ∧
    (∀ b : {b // b ∈ Members right}, ∃ a : {a // a ∈ Members left}, RangeEq b.val a.val)) ↔
    RangeSetEq (Members left) (Members right) := by
  simp [RangeSetEq]

/-- Reflexivity includes raw repetitions in every nested association. -/
theorem range_eq_refl (value : DataRange) : RangeEq value value := by
  cases value with
  | Datatype d => rw [RangeEq]
  | Intersection xs | Union xs =>
    rw [RangeEq]
    constructor <;> intro child <;> exact ⟨child,range_eq_refl child.val⟩
  | Complement value => rw [RangeEq]; exact range_eq_refl value
  | OneOf xs => rw [RangeEq]; intro value; rfl
  | Restriction d xs => rw [RangeEq]; exact ⟨rfl,fun _ => Iff.rfl⟩
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := member_size xs child.val child.property; omega)

/-- Structural data-range equivalence is symmetric. -/
theorem range_eq_symm (left right : DataRange) (equal : RangeEq left right) : RangeEq right left := by
  cases hLeft : left <;> cases hRight : right <;>
    simp only [hLeft,hRight] at equal ⊢
  all_goals simp [RangeEq] at equal ⊢
  case Datatype.Datatype a b => exact equal.symm
  case Intersection.Intersection xs ys => exact ⟨equal.2,equal.1⟩
  case Union.Union xs ys => exact ⟨equal.2,equal.1⟩
  case Complement.Complement a b => exact range_eq_symm a b equal
  case OneOf.OneOf xs ys => exact fun value => (equal value).symm
  case Restriction.Restriction a xs b ys => exact ⟨equal.1.symm,fun value => (equal.2 value).symm⟩
termination_by sizeOf left + sizeOf right
decreasing_by simp only [hLeft,hRight,DataRange.Complement.sizeOf_spec]; omega

/-- Structural data-range equivalence is transitive, including nested sets. -/
theorem range_eq_trans (left middle right : DataRange) (first : RangeEq left middle)
    (second : RangeEq middle right) : RangeEq left right := by
  cases hLeft : left <;> cases hMiddle : middle <;> cases hRight : right <;>
    simp only [hLeft,hMiddle,hRight] at first second ⊢
  all_goals simp [RangeEq] at first second ⊢
  case Datatype.Datatype.Datatype a b c => exact first.trans second
  case Intersection.Intersection.Intersection xs ys zs =>
    constructor
    · intro a aMem
      obtain ⟨b,bMem,ab⟩ := first.1 a aMem
      obtain ⟨c,cMem,bc⟩ := second.1 b bMem
      have sa := member_size xs a aMem
      have sb := member_size ys b bMem
      have sc := member_size zs c cMem
      exact ⟨c,cMem,range_eq_trans a b c ab bc⟩
    · intro c cMem
      obtain ⟨b,bMem,cb⟩ := second.2 c cMem
      obtain ⟨a,aMem,ba⟩ := first.2 b bMem
      have sa := member_size xs a aMem
      have sb := member_size ys b bMem
      have sc := member_size zs c cMem
      exact ⟨a,aMem,range_eq_trans c b a cb ba⟩
  case Union.Union.Union xs ys zs =>
    constructor
    · intro a aMem
      obtain ⟨b,bMem,ab⟩ := first.1 a aMem
      obtain ⟨c,cMem,bc⟩ := second.1 b bMem
      have sa := member_size xs a aMem
      have sb := member_size ys b bMem
      have sc := member_size zs c cMem
      exact ⟨c,cMem,range_eq_trans a b c ab bc⟩
    · intro c cMem
      obtain ⟨b,bMem,cb⟩ := second.2 c cMem
      obtain ⟨a,aMem,ba⟩ := first.2 b bMem
      have sa := member_size xs a aMem
      have sb := member_size ys b bMem
      have sc := member_size zs c cMem
      exact ⟨a,aMem,range_eq_trans c b a cb ba⟩
  case Complement.Complement.Complement a b c => exact range_eq_trans a b c first second
  case OneOf.OneOf.OneOf xs ys zs => exact fun value => (first value).trans (second value)
  case Restriction.Restriction.Restriction a xs b ys c zs =>
    exact ⟨first.1.trans second.1,fun value => (first.2 value).trans (second.2 value)⟩
termination_by sizeOf left + sizeOf middle + sizeOf right
decreasing_by
  all_goals simp only [hLeft,hMiddle,hRight,DataRange.Intersection.sizeOf_spec,
    DataRange.Union.sizeOf_spec,DataRange.Complement.sizeOf_spec]
  all_goals omega


private theorem range_contains_total_of (values : alloc.vec.Vec DataRange) (sought : DataRange)
    (child : ∀ item ∈ values.val, same_range sought item = .ok (decide (RangeEq sought item)))
    (index : Usize) :
    range_contains_from values sought index =
      .ok (decide (∃ item ∈ values.val.drop index.val, RangeEq sought item)) := by
  rw [range_contains_from]
  by_cases inside : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := child values.val[index.val] (List.getElem_mem inside)
    have splitting : (∃ item ∈ values.val.drop index.val, RangeEq sought item) ↔
        RangeEq sought values.val[index.val] ∨
          ∃ item ∈ values.val.drop (index.val+1), RangeEq sought item := by
      rw [List.drop_eq_getElem_cons inside]
      simp only [List.mem_cons,exists_eq_or_imp]
    have splitBool : decide (∃ item ∈ values.val.drop index.val, RangeEq sought item) =
        decide (RangeEq sought values.val[index.val] ∨
          ∃ item ∈ values.val.drop (index.val+1), RangeEq sought item) := decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases found : RangeEq sought values.val[index.val]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_true,true_or]
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := range_contains_total_of values sought child next
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_false,
        Bool.false_eq_true,advance,recursive,nv,false_or]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,empty,
      List.not_mem_nil,false_and,exists_false,decide_false]
termination_by values.val.length - index.val
decreasing_by omega

private theorem range_member_total_of (sought : DataRange) (values : AtLeastTwo DataRange)
    (child : ∀ item ∈ Members values, same_range sought item = .ok (decide (RangeEq sought item))) :
    range_member sought values = .ok (decide (∃ item ∈ Members values, RangeEq sought item)) := by
  rw [range_member]
  have first := child values.first (by simp [Members])
  have second := child values.second (by simp [Members])
  have rest := range_contains_total_of values.rest sought
    (fun item mem => child item (by simp only [Members,List.mem_cons]; exact Or.inr (Or.inr mem))) 0#usize
  have splitting : (∃ item ∈ Members values, RangeEq sought item) ↔
      RangeEq sought values.first ∨ RangeEq sought values.second ∨ ∃ item ∈ values.rest.val, RangeEq sought item := by
    simp only [Members,List.mem_cons,exists_eq_or_imp]
  have splitBool : decide (∃ item ∈ Members values, RangeEq sought item) =
      decide (RangeEq sought values.first ∨ RangeEq sought values.second ∨ ∃ item ∈ values.rest.val, RangeEq sought item) :=
    decide_eq_decide.mpr splitting
  rw [splitBool]
  by_cases a : RangeEq sought values.first <;> by_cases b : RangeEq sought values.second <;>
    simp only [first,second,rest,show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,
      a,b,decide_true,decide_false,↓reduceIte,Bool.false_eq_true,true_or,or_true,false_or]

private theorem range_subset_from_total_of (left : alloc.vec.Vec DataRange) (right : AtLeastTwo DataRange)
    (child : ∀ a ∈ left.val, ∀ b ∈ Members right, same_range a b = .ok (decide (RangeEq a b)))
    (index : Usize) :
    range_subset_from left right index = .ok (decide (∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, RangeEq a b)) := by
  rw [range_subset_from]
  by_cases inside : index.val < left.val.length
  · have lookup : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have head := range_member_total_of left.val[index.val] right
      (child left.val[index.val] (List.getElem_mem inside))
    have splitting : (∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, RangeEq a b) ↔
        (∃ b ∈ Members right, RangeEq left.val[index.val] b) ∧
          ∀ a ∈ left.val.drop (index.val+1), ∃ b ∈ Members right, RangeEq a b := by
      rw [List.drop_eq_getElem_cons inside]; exact List.forall_mem_cons
    have splitBool : decide (∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, RangeEq a b) =
        decide ((∃ b ∈ Members right, RangeEq left.val[index.val] b) ∧
          ∀ a ∈ left.val.drop (index.val+1), ∃ b ∈ Members right, RangeEq a b) := decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases found : ∃ b ∈ Members right, RangeEq left.val[index.val] b
    · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      have recursive := range_subset_from_total_of left right child next
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_true,advance,recursive,nv,true_and]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,head,found,decide_false,Bool.false_eq_true,false_and]
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have vacuous : ∀ a ∈ left.val.drop index.val, ∃ b ∈ Members right, RangeEq a b := by
      rw [empty]; intro a mem; cases mem
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte]
    exact congrArg Result.ok (decide_eq_true vacuous).symm
termination_by left.val.length - index.val
decreasing_by omega

private theorem range_subset_total_of (left right : AtLeastTwo DataRange)
    (child : ∀ a ∈ Members left, ∀ b ∈ Members right, same_range a b = .ok (decide (RangeEq a b))) :
    range_subset left right = .ok (decide (∀ a ∈ Members left, ∃ b ∈ Members right, RangeEq a b)) := by
  have first := range_member_total_of left.first right (child left.first (by simp [Members]))
  have second := range_member_total_of left.second right (child left.second (by simp [Members]))
  have tail := range_subset_from_total_of left.rest right
    (fun a mem => child a (by simp only [Members,List.mem_cons]; exact Or.inr (Or.inr mem))) 0#usize
  have splitting : (∀ a ∈ Members left, ∃ b ∈ Members right, RangeEq a b) ↔
      (∃ b ∈ Members right, RangeEq left.first b) ∧
      (∃ b ∈ Members right, RangeEq left.second b) ∧
      ∀ a ∈ left.rest.val, ∃ b ∈ Members right, RangeEq a b := by
    simp only [Members,List.forall_mem_cons]
  have splitBool : decide (∀ a ∈ Members left, ∃ b ∈ Members right, RangeEq a b) =
      decide ((∃ b ∈ Members right, RangeEq left.first b) ∧
        (∃ b ∈ Members right, RangeEq left.second b) ∧
        ∀ a ∈ left.rest.val, ∃ b ∈ Members right, RangeEq a b) := decide_eq_decide.mpr splitting
  rw [range_subset,splitBool]
  by_cases a : ∃ b ∈ Members right, RangeEq left.first b <;>
    by_cases b : ∃ b ∈ Members right, RangeEq left.second b <;>
    simp only [first,second,tail,show (0#usize).val = 0 from rfl,List.drop_zero,bind_ok,
      a,b,decide_true,decide_false,↓reduceIte,Bool.false_eq_true,true_and,false_and,and_false]

private theorem range_set_total_of (left right : AtLeastTwo DataRange)
    (forward : ∀ a ∈ Members left, ∀ b ∈ Members right, same_range a b = .ok (decide (RangeEq a b)))
    (backward : ∀ b ∈ Members right, ∀ a ∈ Members left, same_range b a = .ok (decide (RangeEq b a))) :
    same_range_set left right = .ok (decide (RangeSetEq (Members left) (Members right))) := by
  rw [same_range_set,range_subset_total_of left right forward]
  by_cases all : ∀ a ∈ Members left, ∃ b ∈ Members right, RangeEq a b
  · have yes := decide_eq_true all
    simp only [yes,bind_ok,↓reduceIte,range_subset_total_of right left backward]
    exact congrArg Result.ok (decide_eq_decide.mpr (and_iff_right all).symm)
  · have no := decide_eq_false all
    simp only [no,bind_ok,Bool.false_eq_true,↓reduceIte]
    exact congrArg Result.ok (decide_eq_false (fun equal : RangeSetEq _ _ => all equal.1)).symm


/-- The actual recursive Rust data-range comparator terminates and decides the
    independent full structural-equivalence relation exactly. -/
theorem same_range_total_correct (left right : DataRange) :
    same_range left right = .ok (decide (RangeEq left right)) := by
  cases hLeft : left <;> cases hRight : right <;> try simp [same_range,RangeEq]
  case Datatype.Datatype a b =>
    simp [Rowl.Symbols.same_spelling_total_correct,datatype_eq]
  case Intersection.Intersection xs ys =>
    have nested := range_set_total_of xs ys
      (fun a aMem b bMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_range_total_correct a b)
      (fun b bMem a aMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_range_total_correct b a)
    simpa [RangeSetEq] using nested
  case Union.Union xs ys =>
    have nested := range_set_total_of xs ys
      (fun a aMem b bMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_range_total_correct a b)
      (fun b bMem a aMem =>
        have sa := member_size xs a aMem
        have sb := member_size ys b bMem
        same_range_total_correct b a)
    simpa [RangeSetEq] using nested
  case Complement.Complement a b => exact same_range_total_correct a b
  case OneOf.OneOf xs ys => exact same_literal_set_total_correct xs ys
  case Restriction.Restriction a xs b ys =>
    by_cases equal : a = b <;>
      simp [Rowl.Symbols.same_spelling_total_correct,datatype_eq,equal,same_facet_set_total_correct]
termination_by sizeOf left + sizeOf right
decreasing_by
  all_goals simp only [hLeft,hRight,DataRange.Intersection.sizeOf_spec,
    DataRange.Union.sizeOf_spec,DataRange.Complement.sizeOf_spec]
  all_goals omega

/-- Exact recursive unordered range association on arbitrarily nested raw forms. -/
theorem same_range_set_total_correct (left right : AtLeastTwo DataRange) :
    same_range_set left right = .ok (decide (RangeSetEq (Members left) (Members right))) :=
  range_set_total_of left right (fun a _ b _ => same_range_total_correct a b)
    (fun b _ a _ => same_range_total_correct b a)

/-- Actual annotated datatype-definition comparison is total and exact; other
    axiom types are never mistaken for datatype definitions. -/
theorem same_definition_total_correct (left right : AnnotatedAxiom) :
    same_definition left right = .ok (decide (DefinitionEq left right)) := by
  cases h : left.axiom <;> cases k : right.axiom <;> simp [same_definition,DefinitionEq,h,k]
  case DatatypeDefinition.DatatypeDefinition a x b y =>
    by_cases dtype : a = b <;> by_cases range : RangeEq x y <;>
      simp [Rowl.Symbols.same_spelling_total_correct,datatype_eq,same_range_total_correct,
        same_annotation_set_total_correct,dtype,range]


private theorem definition_fields (left right : AnnotatedAxiom) (equal : DefinitionEq left right) :
    ∃ a x b y, left.axiom = .DatatypeDefinition a x ∧ right.axiom = .DatatypeDefinition b y ∧
      a = b ∧ RangeEq x y ∧ AnnotationSetEq left.annotations.val right.annotations.val := by
  cases h : left.axiom <;> simp [DefinitionEq,h] at equal
  case DatatypeDefinition a x =>
    cases k : right.axiom <;> simp [DefinitionEq,k] at equal
    case DatatypeDefinition b y => exact ⟨a,x,b,y,rfl,rfl,equal⟩

/-- Reflexivity applies precisely to annotated datatype-definition axioms. -/
theorem definition_eq_refl (item : AnnotatedAxiom) (datatype : Datatype) (range : DataRange)
    (body : item.axiom = .DatatypeDefinition datatype range) : DefinitionEq item item := by
  simp only [DefinitionEq,body]
  exact ⟨True.intro,range_eq_refl range,annotation_set_equivalence.refl _⟩

/-- Structural definition equivalence is symmetric. -/
theorem definition_eq_symm (left right : AnnotatedAxiom) (equal : DefinitionEq left right) :
    DefinitionEq right left := by
  obtain ⟨a,x,b,y,h,k,dt,range,metadata⟩ := definition_fields left right equal
  simp only [DefinitionEq,h,k]
  exact ⟨dt.symm,range_eq_symm x y range,annotation_set_equivalence.symm metadata⟩

/-- Structural definition equivalence is transitive; no value-space equality or
    logical redundancy is substituted for syntactic identity. -/
theorem definition_eq_trans (left middle right : AnnotatedAxiom)
    (first : DefinitionEq left middle) (second : DefinitionEq middle right) : DefinitionEq left right := by
  obtain ⟨a,x,b,y,h,k,dt1,range1,metadata1⟩ := definition_fields left middle first
  obtain ⟨b',y',c,z,k',l,dt2,range2,metadata2⟩ := definition_fields middle right second
  have same : b = b' ∧ y = y' := by simpa only [k,Axiom.DatatypeDefinition.injEq] using k'
  rcases same with ⟨rfl,rfl⟩
  simp only [DefinitionEq,h,l]
  exact ⟨dt1.trans dt2,range_eq_trans x y z range1 range2,annotation_set_equivalence.trans metadata1 metadata2⟩


end Rowl.RangeEquality
