import Rowl.Collection

namespace Rowl.TopData
open Aeneas Aeneas.Std RowlRust.model RowlRust.topdata RowlRust.collection RowlRust.typing
open Rowl.Collection
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- Exact reserved IRI spelling; prefix/case/Unicode normalization is absent. -/
def TopBytes : List U8 := [104#u8,116#u8,116#u8,112#u8,58#u8,47#u8,47#u8,119#u8,119#u8,119#u8,46#u8,119#u8,51#u8,46#u8,111#u8,114#u8,103#u8,47#u8,50#u8,48#u8,48#u8,50#u8,47#u8,48#u8,55#u8,47#u8,111#u8,119#u8,108#u8,35#u8,116#u8,111#u8,112#u8,68#u8,97#u8,116#u8,97#u8,80#u8,114#u8,111#u8,112#u8,101#u8,114#u8,116#u8,121#u8]

/-- Typed occurrence relation from the independent complete OWL AST traversal.
    Annotation IRI values contribute no data-property occurrence. -/
def RowsAllowed (values : List Row) : Prop :=
  ∀ row ∈ values, row.2 = .DataProperty → row.1.spelling.val ≠ TopBytes

/-- Only the super-data-property expression is exempt. All other typed uses,
    including declarations, nested restrictions and key members are checked. -/
def AxiomAllowed (item : AnnotatedAxiom) : Prop :=
  match item.axiom with
  | .SubDataPropertyOf sub _ => sub.iri.spelling.val ≠ TopBytes
  | _ => RowsAllowed (annotatedUses item)

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

private theorem is_top_total (key : alloc.vec.Vec U8) :
    is_top key = .ok (decide (key.val = TopBytes)) := by
  simp [is_top,same_pattern_total,TopBytes,Array.to_slice,Array.make,lift]

private theorem uses_allowed_total (values : EntityUses) :
    uses_allowed values = .ok (decide (RowsAllowed (rows values))) := by
  induction values with
  | Empty => simp [uses_allowed,RowsAllowed,rows]
  | Entry iri kind next ih =>
    cases kind <;> simp [uses_allowed,rows,RowsAllowed,is_top_total,ih]
    repeat' split <;> simp_all

/-- Actual Rust checking covers the full collected AST and its precise single
    allowed position, with no unknown failure or unsupported syntax case. -/
theorem axiom_allowed_total_correct (item : AnnotatedAxiom) :
    axiom_allowed item = .ok (decide (AxiomAllowed item)) := by
  obtain ⟨uses,collected,correct⟩ := axiom_entities_total_correct item
  cases shape : item.axiom <;>
    simp [axiom_allowed,AxiomAllowed,shape,collected,uses_allowed_total,correct,is_top_total]

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
theorem check_axioms_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_axioms axioms = .ok result ∧
      match result with
      | none => ClosureOK axioms.val
      | some item => FirstForbidden axioms.val item := by
  have total : check_axioms axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_axioms] using axioms_from_total axioms 0#usize
  refine ⟨axioms.val.find? forbidden, total, ?_⟩
  cases h : axioms.val.find? forbidden with
  | none =>
    simpa [ClosureOK, forbidden] using List.find?_eq_none.mp h
  | some item =>
    simpa [FirstForbidden, ClosureOK, forbidden] using List.find?_eq_some_iff_append.mp h

/-- No false acceptance or rejection of the specified positional restriction. -/
theorem check_axioms_valid_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_axioms axioms = .ok none ↔ ClosureOK axioms.val := by
  have total : check_axioms axioms = .ok (axioms.val.find? forbidden) := by
    simpa [check_axioms] using axioms_from_total axioms 0#usize
  simp [total, List.find?_eq_none, forbidden, ClosureOK]

end Rowl.TopData
