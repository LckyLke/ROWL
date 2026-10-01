import Rowl.Prepare

namespace Rowl.Batch
open Aeneas Aeneas.Std RowlRust.model RowlRust.prepare RowlRust.batch
open Rowl.Owl Rowl.Prepare
universe u v

def sourceRows : SourceAxioms → List (AxiomOrigin × AnnotatedAxiom)
  | .Empty => []
  | .Cons origin item next => (origin, item) :: sourceRows next

def preparedRows : PreparedAxioms → List (AxiomOrigin × PreparedAnnotatedAxiom)
  | .Empty => []
  | .Cons origin item next => (origin, item) :: preparedRows next

/-- The relation includes every occurrence, preserving origin and annotations.
    Its logical component is exact meaning over arbitrary interpretations. -/
def Corresponds (source : AxiomOrigin × AnnotatedAxiom)
    (prepared : AxiomOrigin × PreparedAnnotatedAxiom) : Prop :=
  prepared.1 = source.1 ∧ prepared.2.annotations = source.2.annotations ∧
  ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value),
    preparedSatisfies I prepared.2.logical ↔ satisfies I source.2.axiom

theorem prepare_all_total_correct (source : SourceAxioms) :
    ∃ prepared, prepare_all source = .ok prepared ∧
      List.Forall₂ Corresponds.{u,v} (sourceRows source) (preparedRows prepared) := by
  induction source with
  | Empty => exact ⟨.Empty, by simp [prepare_all], .nil⟩
  | Cons origin item next ih =>
    obtain ⟨head, hh, metadata, meaning⟩ := prepare_axiom_total_correct.{u,v} item
    obtain ⟨tail, ht, paired⟩ := ih
    refine ⟨.Cons origin head tail, by simp [prepare_all, hh, ht], ?_⟩
    exact .cons ⟨rfl, metadata, meaning⟩ paired

private theorem layout (source : List (AxiomOrigin × AnnotatedAxiom))
    (prepared : List (AxiomOrigin × PreparedAnnotatedAxiom))
    (paired : List.Forall₂ Corresponds.{u,v} source prepared) :
    prepared.map Prod.fst = source.map Prod.fst ∧
    prepared.map (fun row => row.2.annotations) = source.map (fun row => row.2.annotations) := by
  induction paired with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨origin, metadata, _⟩ := head
    simp only [List.map_cons, origin, metadata, ih.1, ih.2, and_self]

/-- No dropped, duplicated or reordered occurrence, origin, or annotation record. -/
theorem prepare_all_preserves_layout (source : SourceAxioms) :
    ∃ prepared, prepare_all source = .ok prepared ∧
      (preparedRows prepared).map Prod.fst = (sourceRows source).map Prod.fst ∧
      (preparedRows prepared).map (fun row => row.2.annotations) =
        (sourceRows source).map (fun row => row.2.annotations) ∧
      (preparedRows prepared).length = (sourceRows source).length := by
  obtain ⟨prepared, hr, paired⟩ := prepare_all_total_correct.{0,0} source
  obtain ⟨origins, metadata⟩ := layout _ _ paired
  exact ⟨prepared, hr, origins, metadata, paired.length_eq.symm⟩

private theorem all_meanings (source : List (AxiomOrigin × AnnotatedAxiom))
    (prepared : List (AxiomOrigin × PreparedAnnotatedAxiom))
    (paired : List.Forall₂ Corresponds.{u,v} source prepared)
    {Object : Type u} {Value : Type v} (I : Interpretation Object Value) :
    (∀ row ∈ source, satisfies I row.2.axiom) ↔
      ∀ row ∈ prepared, preparedSatisfies I row.2.logical := by
  induction paired with
  | nil => simp
  | cons head tail ih =>
    simp only [List.forall_mem_cons]
    exact and_congr (head.2.2 I).symm ih

/-- Batch preparation preserves OWL's existential anonymous assignment for the
    entire supplied item list, with no fresh individuals or vocabulary change. -/
theorem prepare_all_preserves_models (source : SourceAxioms) (prepared : PreparedAxioms)
    (checked : prepare_all source = .ok prepared)
    {Object : Type u} {Value : Type v} (I : Interpretation Object Value) :
    modelsClosure I ((sourceRows source).map Prod.snd) ↔
      ∃ assignment, ∀ row ∈ preparedRows prepared,
        preparedSatisfies (withAnonymous I assignment) row.2.logical := by
  obtain ⟨result, hr, paired⟩ := prepare_all_total_correct.{u,v} source
  have same := Result.ok_injective (hr.symm.trans checked)
  rw [same] at paired
  unfold modelsClosure satisfiesClosure
  simp only [List.forall_mem_map]
  exact exists_congr (fun assignment => all_meanings _ _ paired (withAnonymous I assignment))

end Rowl.Batch
