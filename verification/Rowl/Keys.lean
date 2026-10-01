import Rowl.Generated.RowlKernel

namespace Rowl.Keys
open Aeneas Aeneas.Std RowlRust.model RowlRust.keys
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- §9.5 requires at least one key property of either permitted kind. -/
def AxiomAllowed (item : AnnotatedAxiom) : Prop :=
  match item.axiom with
  | .HasKey _ objects data => objects.val ≠ [] ∨ data.val ≠ []
  | _ => True
/-- The actual axiom check terminates and decides the nonempty-key rule exactly. -/
theorem axiom_allowed_total_correct (item : AnnotatedAxiom) :
    axiom_allowed item = .ok (decide (AxiomAllowed item)) := by
  cases h : item.axiom <;> simp [axiom_allowed,AxiomAllowed,h]
  case HasKey c objects data =>
    by_cases a : objects.val = [] <;> by_cases b : data.val = [] <;>
      simp_all [List.length_eq_zero_iff,UScalar.eq_equiv]
/-- Whole supplied axiom closure, including imported axioms supplied by caller. -/
def ClosureOK (axioms : List AnnotatedAxiom) : Prop := ∀ item ∈ axioms, AxiomAllowed item

/-- Return the complete first violating axiom in its original input order. -/
def FirstForbidden (axioms : List AnnotatedAxiom) (item : AnnotatedAxiom) : Prop :=
  ¬ AxiomAllowed item ∧ ∃ before after, axioms = before ++ item :: after ∧ ClosureOK before

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
theorem check_keys_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_keys axioms = .ok result ∧
      match result with
      | none => ClosureOK axioms.val
      | some item => FirstForbidden axioms.val item := by
  have total : check_keys axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_keys] using axioms_from_total axioms 0#usize
  refine ⟨axioms.val.find? forbidden, total, ?_⟩
  cases h : axioms.val.find? forbidden with
  | none =>
    simpa [ClosureOK, forbidden] using List.find?_eq_none.mp h
  | some item =>
    simpa [FirstForbidden, ClosureOK, forbidden] using List.find?_eq_some_iff_append.mp h

/-- No false acceptance or rejection of the nonempty-key-property restriction. -/
theorem check_keys_valid_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_keys axioms = .ok none ↔ ClosureOK axioms.val := by
  have total : check_keys axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_keys] using axioms_from_total axioms 0#usize
  simp [total, List.find?_eq_none, forbidden, ClosureOK]

end Rowl.Keys
