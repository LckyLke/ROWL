import Rowl.Tableau

/-!
Role axioms for the tableaux: inclusions between named object properties and
transitive named object properties. `Below` is the procedures' inclusion test,
equality or a listed inclusion; `Respects` is what the role axioms mean in an
interpretation; and `Closed` says that the listed inclusions already include
their compositions, which the tableaux' models rely on.
-/
namespace Rowl.RoleBox
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation)
open Rowl.Tableau (property_eq_iff)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

/-- The listed inclusions, in order. -/
def inclusionList (rb : role_box.RoleBox) : List (ObjectProperty × ObjectProperty) :=
  rb.inclusions.val.map (fun i => (i.sub,i.sup))
/-- The transitive properties, in order. -/
def transitives (rb : role_box.RoleBox) : List ObjectProperty := rb.transitive.val
/-- `sub` is `sup` or listed as included in it. -/
def Below (rb : role_box.RoleBox) (sub sup : ObjectProperty) : Prop :=
  sub = sup ∨ (sub,sup) ∈ inclusionList rb
/-- The listed inclusions include their compositions. -/
def Closed (rb : role_box.RoleBox) : Prop :=
  ∀ a b c, Below rb a b → Below rb b c → Below rb a c
/-- The interpretation satisfies every listed inclusion and every listed
    transitivity. -/
def Respects {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (rb : role_box.RoleBox) : Prop :=
  (∀ s r, (s,r) ∈ inclusionList rb → ∀ x y, I.objectProperties s x y → I.objectProperties r x y) ∧
  ∀ t ∈ transitives rb, ∀ x y z, I.objectProperties t x y → I.objectProperties t y z → I.objectProperties t x z

theorem below_refl (rb : role_box.RoleBox) (r : ObjectProperty) : Below rb r r := .inl rfl
/-- An interpretation respecting the role axioms relates along every property
    that includes a property relating the same pair. -/
theorem respects_below {Object : Type u} {Value : Type v} {I : Interpretation Object Value}
    {rb : role_box.RoleBox} (respects : Respects I rb) {s r : ObjectProperty} (below : Below rb s r)
    {x y : Object} (edge : I.objectProperties s x y) : I.objectProperties r x y := by
  rcases below with rfl | listed
  · exact edge
  · exact respects.1 s r listed x y edge

private theorem included_from_correct (inclusions : alloc.vec.Vec role_box.RoleInclusion) (index : Usize)
    (sub sup : ObjectProperty) :
    role_box.included_from inclusions index sub sup =
      .ok (decide ((sub,sup) ∈ (inclusions.val.drop index.val).map (fun i => (i.sub,i.sup)))) := by
  rw [role_box.included_from]
  by_cases more : index.val < inclusions.val.length
  · have lookup : inclusions.index_usize index = .ok inclusions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : inclusions.val.drop index.val = inclusions.val[index.val] :: inclusions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := included_from_correct inclusions index' sub sup
    rw [nextIndex] at rest
    rw [split,List.map_cons]
    by_cases first : inclusions.val[index.val].sub = sub
    · by_cases second : inclusions.val[index.val].sup = sup
      · have firstBytes := (property_eq_iff _ _).mp first
        have secondBytes := (property_eq_iff _ _).mp second
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,firstBytes,secondBytes,decide_true]
        simp [first,second]
      · have firstBytes := (property_eq_iff _ _).mp first
        have secondBytes : ¬ inclusions.val[index.val].sup.iri.spelling.val = sup.iri.spelling.val :=
          fun h => second ((property_eq_iff _ _).mpr h)
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,firstBytes,secondBytes,decide_true,
          decide_false,Bool.false_eq_true,advance,rest]
        have second' : ¬ sup = inclusions.val[index.val].sup := fun h => second h.symm
        simp [second']
    · have firstBytes : ¬ inclusions.val[index.val].sub.iri.spelling.val = sub.iri.spelling.val :=
        fun h => first ((property_eq_iff _ _).mpr h)
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,firstBytes,decide_false,Bool.false_eq_true,
        advance,rest]
      have first' : ¬ sub = inclusions.val[index.val].sub := fun h => first h.symm
      simp [first']
  · have empty : inclusions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by inclusions.val.length - index.val
decreasing_by omega

/-- The actual inclusion test decides `Below`, comparing properties by exact
    spelling. -/
theorem below_correct (rb : role_box.RoleBox) (sub sup : ObjectProperty) :
    role_box.below rb sub sup = .ok (decide (Below rb sub sup)) := by
  rw [role_box.below,Rowl.Symbols.same_spelling_total_correct,included_from_correct]
  by_cases same : sub = sup
  · subst same; simp [Below]
  · have different : ¬ sub.iri.spelling.val = sup.iri.spelling.val := fun h => same ((property_eq_iff _ _).mpr h)
    simp [different,Below,inclusionList,same]

/-- Without listed inclusions, `Below` is equality, which is closed. -/
theorem closed_of_empty (rb : role_box.RoleBox) (empty : rb.inclusions.val = []) : Closed rb := by
  intro a b c first second
  simp only [Below,inclusionList,empty,List.map_nil,List.not_mem_nil,or_false] at first second ⊢
  exact first.trans second
/-- Without listed inclusions or transitive properties, every interpretation
    respects the role axioms. -/
theorem respects_of_empty {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (rb : role_box.RoleBox) (noInclusions : rb.inclusions.val = []) (noTransitive : rb.transitive.val = []) :
    Respects I rb := by
  refine ⟨?_,?_⟩
  · intro s r listed
    simp [inclusionList,noInclusions] at listed
  · intro t listed
    simp [transitives,noTransitive] at listed
end Rowl.RoleBox
