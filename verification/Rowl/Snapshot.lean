import Rowl.Imports
import Rowl.Unicode

namespace Rowl.Snapshot
open Aeneas Aeneas.Std RowlRust.imports RowlRust.snapshot
open RowlRust.unicode Rowl.Unicode

def TextReady (catalog : DocumentCatalog) : Prop :=
  ∀ row ∈ Rowl.Imports.rows catalog, ∃ text, TextFrom row.2.1.val 0 text

/-- The first bad record in the resolver's deterministic output order. -/
inductive SourceFailure : DocumentCatalog → U32 → TextError → Prop
  | here {key bytes dependencies next error} :
      Rejected bytes.val 0 error →
      SourceFailure (.Document key bytes dependencies next) key error
  | later {key bytes dependencies next document error} :
      (∃ text, TextFrom bytes.val 0 text) → SourceFailure next document error →
      SourceFailure (.Document key bytes dependencies next) document error

def SourceCorrect (catalog : DocumentCatalog) : SourceCheck → Prop
  | .Valid => TextReady catalog
  | .Invalid document error => SourceFailure catalog document error

private theorem ready_cons (key : U32) (bytes : alloc.vec.Vec U8) (dependencies : DocumentIds)
    (next : DocumentCatalog) :
    TextReady (.Document key bytes dependencies next) ↔
      (∃ text, TextFrom bytes.val 0 text) ∧ TextReady next := by
  simp [TextReady, Rowl.Imports.rows]

/-- Every returned diagnostic is the first invalid source; no source is skipped. -/
theorem check_sources_total_correct (catalog : DocumentCatalog) :
    ∃ result, check_sources catalog = .ok result ∧ SourceCorrect catalog result := by
  induction catalog with
  | Empty => exact ⟨.Valid, by simp [check_sources], by simp [SourceCorrect, TextReady, Rowl.Imports.rows]⟩
  | Document key bytes dependencies next ih =>
    obtain ⟨scan, hs, hc⟩ := read_text_total_correct bytes
    cases scan with
    | Invalid error =>
      exact ⟨.Invalid key error, by simp [check_sources, hs], .here hc⟩
    | Valid scalars =>
      obtain ⟨result, hr, correct⟩ := ih
      refine ⟨result, by simp [check_sources, hs, hr], ?_⟩
      cases result with
      | Valid => exact ready_cons _ _ _ _ |>.mpr ⟨⟨scalarValues scalars, hc⟩, correct⟩
      | Invalid document error => exact .later ⟨scalarValues scalars, hc⟩ correct

private theorem failure_not_ready {catalog : DocumentCatalog} {document : U32} {error : TextError}
    (failure : SourceFailure catalog document error) : ¬ TextReady catalog := by
  induction failure with
  | here invalid =>
    intro ready
    obtain ⟨text, accepted⟩ := (ready_cons _ _ _ _).mp ready |>.1
    exact rejected_excludes_text _ _ _ invalid text accepted
  | later valid failure ih =>
    intro ready
    exact ih ((ready_cons _ _ _ _).mp ready).2

/-- Source acceptance is exactly complete UTF-8/XML-character text for every record. -/
theorem check_sources_valid_iff (catalog : DocumentCatalog) :
    check_sources catalog = .ok .Valid ↔ TextReady catalog := by
  obtain ⟨result, hr, hc⟩ := check_sources_total_correct catalog
  constructor
  · intro h
    have same := Result.ok_injective (hr.symm.trans h)
    rw [same] at hc
    exact hc
  · intro ready
    cases result with
    | Valid => exact hr
    | Invalid document error => exact False.elim (failure_not_ready hc ready)

def Correct (catalog : DocumentCatalog) (root : U32) : TextResolution → Prop
  | .Complete closure =>
      Rowl.Imports.Correct catalog root (.Complete closure) ∧ TextReady closure
  | .MissingDocument key => Rowl.Imports.Correct catalog root (.MissingDocument key)
  | .DuplicateDocument key => Rowl.Imports.Correct catalog root (.DuplicateDocument key)
  | .InvalidText document error =>
      ∃ closure, RowlRust.imports.resolve root catalog = .ok (.Complete closure) ∧
        Rowl.Imports.Correct catalog root (.Complete closure) ∧ SourceFailure closure document error

/-- Compose proved closure and byte checks. Complete retains exactly the reachable
    input records, including their bytes and import metadata. Errors keep their source. -/
theorem resolve_texts_total_correct (root : U32) (catalog : DocumentCatalog) :
    ∃ result, resolve_texts root catalog = .ok result ∧ Correct catalog root result := by
  obtain ⟨resolution, hr, hc⟩ := Rowl.Imports.resolve_total_correct root catalog
  cases resolution with
  | MissingDocument key => exact ⟨.MissingDocument key, by simp [resolve_texts, hr], hc⟩
  | DuplicateDocument key => exact ⟨.DuplicateDocument key, by simp [resolve_texts, hr], hc⟩
  | Complete closure =>
    obtain ⟨check, hs, correct⟩ := check_sources_total_correct closure
    cases check with
    | Valid => exact ⟨.Complete closure, by simp [resolve_texts, hr, hs], hc, correct⟩
    | Invalid document error =>
      exact ⟨.InvalidText document error, by simp [resolve_texts, hr, hs], closure, hr, hc, correct⟩

/-- With a known complete closure, byte validation accepts iff every source is valid. -/
theorem resolve_texts_complete_iff (root : U32) (catalog closure : DocumentCatalog)
    (resolved : RowlRust.imports.resolve root catalog = .ok (.Complete closure)) :
    resolve_texts root catalog = .ok (.Complete closure) ↔ TextReady closure := by
  obtain ⟨check, hs, hc⟩ := check_sources_total_correct closure
  cases check with
  | Valid => simp [resolve_texts, resolved, hs, SourceCorrect] at hc ⊢
             exact hc
  | Invalid document error =>
    have bad : ¬ TextReady closure := failure_not_ready hc
    simp [resolve_texts, resolved, hs, bad]

end Rowl.Snapshot
