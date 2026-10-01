import Rowl.Anonymous
import Rowl.AnonymousMultiplicity
import Rowl.AnonymousBoundary

namespace Rowl.AnonymousRestrictions
open Aeneas Aeneas.Std RowlRust.model RowlRust.anonymous_restrictions
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- All normative anonymous-individual conditions on a supplied standardized-apart
    complete raw closure. This does not establish the other OWL 2 DL restrictions. -/
def Restriction (axioms : List AnnotatedAxiom) : Prop :=
  Rowl.Anonymous.PositionsOK axioms ∧
  Rowl.AnonymousGraph.Forest (Rowl.AnonymousGraph.closureEdges axioms) ∧
  Rowl.AnonymousMultiplicity.Restriction axioms ∧
  Rowl.AnonymousBoundary.Restriction axioms

/-- Success is exact. Each failure retains its stage's proved original evidence,
    proves rejection of the conjunction and establishes every preceding stage. -/
def Correct (axioms : List AnnotatedAxiom) : AnonymousCheck → Prop
  | .Allowed => Restriction axioms
  | .ForbiddenPosition item => Rowl.Anonymous.FirstForbidden axioms item ∧ ¬ Restriction axioms
  | .SelfLoop value => Rowl.Anonymous.PositionsOK axioms ∧
      Rowl.AnonymousGraph.Correct (Rowl.AnonymousGraph.closureEdges axioms) (.SelfLoop value) ∧
      ¬ Restriction axioms
  | .Cycle a b => Rowl.Anonymous.PositionsOK axioms ∧
      Rowl.AnonymousGraph.Correct (Rowl.AnonymousGraph.closureEdges axioms) (.Cycle a b) ∧
      ¬ Restriction axioms
  | .MultipleAssertions first second => Rowl.Anonymous.PositionsOK axioms ∧
      Rowl.AnonymousGraph.Forest (Rowl.AnonymousGraph.closureEdges axioms) ∧
      Rowl.AnonymousMultiplicity.Correct axioms (.MultipleAssertions first second) ∧
      ¬ Restriction axioms
  | .NoBoundaryRoot root => Rowl.Anonymous.PositionsOK axioms ∧
      Rowl.AnonymousGraph.Forest (Rowl.AnonymousGraph.closureEdges axioms) ∧
      Rowl.AnonymousMultiplicity.Restriction axioms ∧
      Rowl.AnonymousBoundary.Correct axioms (.NoRoot root) ∧ ¬ Restriction axioms

/-- The actual composite operation terminates, decides all anonymous conditions
    and preserves the specified failure priority without trusting caller metadata. -/
theorem check_anonymous_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_anonymous axioms = .ok result ∧ Correct axioms.val result := by
  obtain ⟨position,checkedPosition,positionCorrect⟩ := Rowl.Anonymous.check_positions_total_correct axioms
  cases position with
  | some item =>
    refine ⟨.ForbiddenPosition item,by simp [check_anonymous,checkedPosition],positionCorrect,?_⟩
    intro valid
    rcases positionCorrect with ⟨forbidden,before,after,decomposition,_⟩
    have member : item ∈ axioms.val := by simp [decomposition]
    exact forbidden (valid.1 item member)
  | none =>
    obtain ⟨forest,checkedForest,forestCorrect⟩ := Rowl.AnonymousGraph.check_forest_total_correct axioms
    cases forest with
    | SelfLoop value =>
      refine ⟨.SelfLoop value,by simp [check_anonymous,checkedPosition,checkedForest],
        positionCorrect,forestCorrect,?_⟩
      intro valid; exact forestCorrect.2 valid.2.1
    | Cycle a b =>
      refine ⟨.Cycle a b,by simp [check_anonymous,checkedPosition,checkedForest],
        positionCorrect,forestCorrect,?_⟩
      intro valid; exact forestCorrect.2.2 valid.2.1
    | Forest =>
      obtain ⟨multiplicity,checkedMultiplicity,multiplicityCorrect⟩ :=
        Rowl.AnonymousMultiplicity.check_multiplicity_total_correct axioms
      cases multiplicity with
      | MultipleAssertions first second =>
        refine ⟨.MultipleAssertions first second,
          by simp [check_anonymous,checkedPosition,checkedForest,checkedMultiplicity],
          positionCorrect,forestCorrect,multiplicityCorrect,?_⟩
        intro valid; exact multiplicityCorrect.2.2.2 valid.2.2.1
      | Allowed =>
        obtain ⟨boundary,checkedBoundary,boundaryCorrect⟩ := Rowl.AnonymousBoundary.check_boundary_total_correct axioms
        cases boundary with
        | Allowed =>
          exact ⟨.Allowed,by simp [check_anonymous,checkedPosition,checkedForest,checkedMultiplicity,checkedBoundary],
            positionCorrect,forestCorrect,multiplicityCorrect,boundaryCorrect⟩
        | NoRoot root =>
          refine ⟨.NoBoundaryRoot root,
            by simp [check_anonymous,checkedPosition,checkedForest,checkedMultiplicity,checkedBoundary],
            positionCorrect,forestCorrect,multiplicityCorrect,boundaryCorrect,?_⟩
          intro valid; exact boundaryCorrect.2.2 valid.2.2.2

/-- No false acceptance or rejection for the complete anonymous restrictions. -/
theorem check_anonymous_accepted_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_anonymous axioms = .ok .Allowed ↔ Restriction axioms.val := by
  obtain ⟨result,executed,correct⟩ := check_anonymous_total_correct axioms
  rw [executed]
  cases result with
  | Allowed => simp [Correct] at correct; simp [correct]
  | ForbiddenPosition item => simp [Correct] at correct; simp [correct.2]
  | SelfLoop value => simp [Correct] at correct; simp [correct.2.2]
  | Cycle a b => simp [Correct] at correct; simp [correct.2.2]
  | MultipleAssertions a b => simp [Correct] at correct; simp [correct.2.2.2]
  | NoBoundaryRoot root => simp [Correct] at correct; simp [correct.2.2.2.2]

end Rowl.AnonymousRestrictions
