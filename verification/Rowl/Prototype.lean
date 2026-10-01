import Rowl.Semantics

namespace Rowl
open Aeneas Aeneas.Std RowlRust.prototype

/-- Position in the exhaustive enumeration; distinct from individual equality. -/
def valuationRank (v : Valuation) : Nat :=
  (if v.a then 2 else 0) + (if v.b then 1 else 0)

/-- Mutable transition either advances by one or stops at the final valuation. -/
theorem next_valuation_total_correct (v : Valuation) :
    ∃ advance next, next_valuation v = .ok (advance, next) ∧
      (if advance then valuationRank next = valuationRank v + 1
       else next = v ∧ valuationRank v = 3) := by
  obtain ⟨a, b⟩ := v
  cases a <;> cases b <;> simp [next_valuation, valuationRank]

/-- Total correctness of the actual extracted recursive Rust evaluator.
    Equality to `ok` excludes failure and divergence in the translation model. -/
theorem evaluate_total_correct (f : Formula) (v : Valuation) :
    ∃ b, evaluate f v = .ok b ∧ (b = true ↔ denotes f v) := by
  induction f with
  | Top => exact ⟨true, by simp [evaluate], by simp [denotes]⟩
  | Bottom => exact ⟨false, by simp [evaluate], by simp [denotes]⟩
  | Atom a =>
    cases a with
    | A => exact ⟨v.a, by simp [evaluate], by simp [denotes]⟩
    | B => exact ⟨v.b, by simp [evaluate], by simp [denotes]⟩
  | Not f ih =>
    obtain ⟨b, hb, hs⟩ := ih
    refine ⟨!b, ?_, ?_⟩
    · simp [evaluate, hb]
    · cases b <;> simp_all [denotes]
  | And left right ihLeft ihRight =>
    obtain ⟨a, ha, hsa⟩ := ihLeft
    obtain ⟨b, hb, hsb⟩ := ihRight
    refine ⟨a && b, ?_, ?_⟩
    · simp [evaluate, ha, hb]
      cases a <;> rfl
    · cases a <;> cases b <;> simp_all [denotes]

  | Or left right ihLeft ihRight =>
    obtain ⟨a, ha, hsa⟩ := ihLeft
    obtain ⟨b, hb, hsb⟩ := ihRight
    refine ⟨a || b, ?_, ?_⟩
    · simp [evaluate, ha, hb]
      cases a <;> rfl
    · cases a <;> cases b <;> simp_all [denotes]

/-- One actual search iteration, unfolded once so recursion stays explicit. -/
theorem decide_loop_step (f : Formula) (v next : Valuation) (b advance : Bool)
    (hEval : evaluate f v = .ok b)
    (hNext : next_valuation v = .ok (advance, next)) :
    decide_loop f v =
      if b then .ok (.Satisfiable v)
      else if advance then decide_loop f next else .ok .Unsatisfiable := by
  rw [decide_loop]
  simp [hEval, hNext]

/-- Total correctness of the actual extracted search, including all branches. -/
theorem decide_total_correct (f : Formula) :
    ∃ answer, decide f = .ok answer ∧ correctDecision f answer := by
  obtain ⟨ff, hff, sff⟩ := evaluate_total_correct f ⟨false, false⟩
  obtain ⟨ft, hft, sft⟩ := evaluate_total_correct f ⟨false, true⟩
  obtain ⟨tf, htf, stf⟩ := evaluate_total_correct f ⟨true, false⟩
  obtain ⟨tt, htt, stt⟩ := evaluate_total_correct f ⟨true, true⟩
  have loopFF := decide_loop_step f ⟨false, false⟩ ⟨false, true⟩ ff true hff (by simp [next_valuation])
  have loopFT := decide_loop_step f ⟨false, true⟩ ⟨true, false⟩ ft true hft (by simp [next_valuation])
  have loopTF := decide_loop_step f ⟨true, false⟩ ⟨true, true⟩ tf true htf (by simp [next_valuation])
  have loopTT := decide_loop_step f ⟨true, true⟩ ⟨true, true⟩ tt false htt (by simp [next_valuation])
  cases ff with
  | true =>
    refine ⟨.Satisfiable ⟨false, false⟩, ?_, sff.mp rfl⟩
    simp [RowlRust.prototype.decide, loopFF]
  | false =>
    cases ft with
    | true =>
      refine ⟨.Satisfiable ⟨false, true⟩, ?_, sft.mp rfl⟩
      simp [RowlRust.prototype.decide, loopFF, loopFT]
    | false =>
      cases tf with
      | true =>
        refine ⟨.Satisfiable ⟨true, false⟩, ?_, stf.mp rfl⟩
        simp [RowlRust.prototype.decide, loopFF, loopFT, loopTF]
      | false =>
        cases tt with
        | true =>
          refine ⟨.Satisfiable ⟨true, true⟩, ?_, stt.mp rfl⟩
          simp [RowlRust.prototype.decide, loopFF, loopFT, loopTF, loopTT]
        | false =>
          refine ⟨.Unsatisfiable, ?_, ?_⟩
          · simp [RowlRust.prototype.decide, loopFF, loopFT, loopTF, loopTT]
          · intro ⟨⟨a, b⟩, h⟩
            cases a <;> cases b
            · have impossible : false = true := sff.mpr h
              cases impossible
            · have impossible : false = true := sft.mpr h
              cases impossible
            · have impossible : false = true := stf.mpr h
              cases impossible
            · have impossible : false = true := stt.mpr h
              cases impossible

/-- Every returned satisfying witness satisfies the declarative semantics. -/
theorem decide_sound (f : Formula) (v : Valuation)
    (h : decide f = .ok (.Satisfiable v)) : denotes f v := by
  obtain ⟨answer, result, correct⟩ := decide_total_correct f
  have same := Result.ok_injective (h.symm.trans result)
  rw [← same] at correct
  exact correct

/-- Unsatisfiability is returned exactly when no interpretation exists. -/
theorem decide_complete (f : Formula) :
    decide f = .ok .Unsatisfiable ↔ ¬ satisfiable f := by
  obtain ⟨answer, result, correct⟩ := decide_total_correct f
  constructor
  · intro h
    have same := Result.ok_injective (result.symm.trans h)
    rw [same] at correct
    exact correct
  · intro noModel
    cases answer with
    | Satisfiable v => exact False.elim (noModel ⟨v, correct⟩)
    | Unsatisfiable => exact result

/-- Actual search reaches a successful result; no fuel or termination axiom. -/
theorem decide_terminates (f : Formula) : ∃ answer, decide f = .ok answer := by
  obtain ⟨answer, result, _⟩ := decide_total_correct f
  exact ⟨answer, result⟩

end Rowl
