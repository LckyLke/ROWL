import Rowl.Concepts

/-!
Role hierarchies with inverse roles: inclusions between object property
expressions and transitive object property expressions. `Below` is the
tableau's inclusion test, equality or a listed inclusion; `Respects` is what the
role axioms mean in an interpretation, read with `objectRelation`; and `Closed`
says that the lists already include every composition of inclusions, the
inverse of every inclusion, and the inverse of every transitive role, which the
completion graph tableau relies on.
-/
namespace Rowl.Hierarchy
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv same_role_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

/-- The listed inclusions, in order. -/
def inclusionList (h : hierarchy.RoleHierarchy) : List (ObjectPropertyExpression × ObjectPropertyExpression) :=
  h.inclusions.val.map (fun i => (i.sub,i.sup))
/-- The transitive roles, in order. -/
def transitives (h : hierarchy.RoleHierarchy) : List ObjectPropertyExpression := h.transitive.val
/-- `sub` is `sup` or listed as included in it. -/
def Below (h : hierarchy.RoleHierarchy) (sub sup : ObjectPropertyExpression) : Prop :=
  sub = sup ∨ (sub,sup) ∈ inclusionList h
/-- The lists include every composition of inclusions, the inverse of every
    inclusion and the inverse of every transitive role. -/
def Closed (h : hierarchy.RoleHierarchy) : Prop :=
  (∀ a b c, Below h a b → Below h b c → Below h a c) ∧
  (∀ a b, Below h a b → Below h (inv a) (inv b)) ∧
  (∀ t ∈ transitives h, inv t ∈ transitives h)
/-- The interpretation satisfies every listed inclusion and every listed
    transitivity. -/
def Respects {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (h : hierarchy.RoleHierarchy) :
    Prop :=
  (∀ s r, (s,r) ∈ inclusionList h → ∀ x y, objectRelation I s x y → objectRelation I r x y) ∧
  ∀ t ∈ transitives h, ∀ x y z, objectRelation I t x y → objectRelation I t y z → objectRelation I t x z

theorem below_refl (h : hierarchy.RoleHierarchy) (r : ObjectPropertyExpression) : Below h r r := .inl rfl
/-- An interpretation respecting the role axioms relates along every role that
    includes a role relating the same pair. -/
theorem respects_below {Object : Type u} {Value : Type v} {I : Interpretation Object Value}
    {h : hierarchy.RoleHierarchy} (respects : Respects I h) {s r : ObjectPropertyExpression} (below : Below h s r)
    {x y : Object} (edge : objectRelation I s x y) : objectRelation I r x y := by
  rcases below with rfl | listed
  · exact edge
  · exact respects.1 s r listed x y edge

private theorem listed_from_correct (inclusions : alloc.vec.Vec hierarchy.Inclusion) (index : Usize)
    (sub sup : ObjectPropertyExpression) :
    hierarchy.listed_from inclusions index sub sup =
      .ok (decide ((sub,sup) ∈ (inclusions.val.drop index.val).map (fun i => (i.sub,i.sup)))) := by
  rw [hierarchy.listed_from]
  by_cases more : index.val < inclusions.val.length
  · have lookup : inclusions.index_usize index = .ok inclusions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : inclusions.val.drop index.val = inclusions.val[index.val] :: inclusions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := listed_from_correct inclusions index' sub sup
    rw [nextIndex] at rest
    rw [split,List.map_cons]
    by_cases first : inclusions.val[index.val].sub = sub
    · by_cases second : inclusions.val[index.val].sup = sup
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,same_role_correct,first,second,decide_true]
        simp
      · have second' : ¬ sup = inclusions.val[index.val].sup := fun same => second same.symm
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,same_role_correct,first,second,decide_true,decide_false,Bool.false_eq_true,advance,rest]
        simp [second']
    · have first' : ¬ sub = inclusions.val[index.val].sub := fun same => first same.symm
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,same_role_correct,first,decide_false,Bool.false_eq_true,advance,rest]
      simp [first']
  · have empty : inclusions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by inclusions.val.length - index.val
decreasing_by omega

/-- The actual inclusion test decides `Below`, comparing roles by orientation
    and exact spelling. -/
theorem below_correct (h : hierarchy.RoleHierarchy) (sub sup : ObjectPropertyExpression) :
    hierarchy.below h sub sup = .ok (decide (Below h sub sup)) := by
  rw [hierarchy.below,same_role_correct,listed_from_correct]
  by_cases same : sub = sup
  · subst same; simp [Below]
  · simp [same,Below,inclusionList]

private theorem transitive_from_correct (transitive : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (role : ObjectPropertyExpression) :
    hierarchy.transitive_from transitive index role = .ok (decide (role ∈ transitive.val.drop index.val)) := by
  rw [hierarchy.transitive_from]
  by_cases more : index.val < transitive.val.length
  · have lookup : transitive.index_usize index = .ok transitive.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : transitive.val.drop index.val = transitive.val[index.val] :: transitive.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := transitive_from_correct transitive index' role
    rw [nextIndex] at rest
    rw [split]
    by_cases first : transitive.val[index.val] = role
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,same_role_correct,first,decide_true]
      simp
    · have first' : ¬ role = transitive.val[index.val] := fun same => first same.symm
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,same_role_correct,first,decide_false,Bool.false_eq_true,advance,rest,List.mem_cons,first',
        false_or]
  · have empty : transitive.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by transitive.val.length - index.val
decreasing_by omega

/-- The actual transitivity test decides membership in the transitive list. -/
theorem is_transitive_correct (h : hierarchy.RoleHierarchy) (role : ObjectPropertyExpression) :
    hierarchy.is_transitive h role = .ok (decide (role ∈ transitives h)) := by
  rw [hierarchy.is_transitive,transitive_from_correct]
  simp [transitives]

/-- In a closed hierarchy, an interpretation respecting the role axioms relates
    along `inv r` exactly the reversed pairs it relates along `r`, and inclusions
    and transitivity carry over to inverses. -/
theorem respects_inv {Object : Type u} {Value : Type v} {I : Interpretation Object Value}
    {h : hierarchy.RoleHierarchy} (respects : Respects I h) (closed : Closed h) {s r : ObjectPropertyExpression}
    (below : Below h s r) {x y : Object} (edge : objectRelation I (inv s) x y) : objectRelation I (inv r) x y :=
  respects_below respects (closed.2.1 s r below) edge

/-- Without listed inclusions or transitive roles, `Below` is equality and every
    interpretation respects the role axioms. -/
theorem closed_of_empty (h : hierarchy.RoleHierarchy) (noInclusions : h.inclusions.val = [])
    (noTransitive : h.transitive.val = []) : Closed h := by
  refine ⟨?_,?_,?_⟩
  · intro a b c first second
    simp only [Below,inclusionList,noInclusions,List.map_nil,List.not_mem_nil,or_false] at first second ⊢
    exact first.trans second
  · intro a b below
    simp only [Below,inclusionList,noInclusions,List.map_nil,List.not_mem_nil,or_false] at below ⊢
    rw [below]
  · intro t member
    simp [transitives,noTransitive] at member
theorem respects_of_empty {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (h : hierarchy.RoleHierarchy) (noInclusions : h.inclusions.val = []) (noTransitive : h.transitive.val = []) :
    Respects I h := by
  refine ⟨?_,?_⟩
  · intro s r listed
    simp [inclusionList,noInclusions] at listed
  · intro t listed
    simp [transitives,noTransitive] at listed
end Rowl.Hierarchy
