import Rowl.AssertionEquality

namespace Rowl.AnonymousMultiplicity
open Aeneas Aeneas.Std RowlRust.model RowlRust.anonymous_multiplicity Rowl.AssertionEquality
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000

/-- Unordered endpoint identity of positive anonymous-to-anonymous assertions. -/
def SamePair (left right : AnnotatedAxiom) : Prop :=
  match left.axiom, right.axiom with
  | .ObjectPropertyAssertion _ (.Anonymous a) (.Anonymous b),
      .ObjectPropertyAssertion _ (.Anonymous c) (.Anonymous d) =>
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)
  | _, _ => False

/-- Distinct structural axiom-set members on the same anonymous edge. -/
def Conflict (first second : AnnotatedAxiom) : Prop :=
  SamePair first second ∧ ¬ AssertionEq first second

/-- Each unordered anonymous pair has at most one structural assertion member. -/
def Restriction (axioms : List AnnotatedAxiom) : Prop :=
  ∀ first ∈ axioms, ∀ second ∈ axioms, SamePair first second → AssertionEq first second

/-- Failures preserve original conflicting annotated axioms, not merely labels. -/
def Correct (axioms : List AnnotatedAxiom) : MultiplicityCheck → Prop
  | .Allowed => Restriction axioms
  | .MultipleAssertions first second =>
    first ∈ axioms ∧ second ∈ axioms ∧ Conflict first second ∧ ¬ Restriction axioms

/-- Properties and assertion orientation do not affect the undirected pair. -/
theorem same_pair_total_correct (left right : AnnotatedAxiom) :
    same_pair left right = .ok (decide (SamePair left right)) := by
  cases h : left.axiom <;> cases k : right.axiom <;> simp [same_pair,SamePair,h,k]
  case ObjectPropertyAssertion.ObjectPropertyAssertion p a b q c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> simp [SamePair]
    case Anonymous.Anonymous.Anonymous.Anonymous a b c d =>
      by_cases ac : a = c <;> by_cases bd : b = d <;>
        by_cases ad : a = d <;> by_cases bc : b = c <;>
        simp_all [Rowl.AnonymousGraph.same_individual_total_correct,
          Rowl.AnonymousGraph.key_injective.eq_iff,eq_comm]

private noncomputable def conflicting (first : AnnotatedAxiom) (second : AnnotatedAxiom) : Bool :=
  decide (Conflict first second)

private theorem against_from_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (first : AnnotatedAxiom) (index : Usize) :
    against_from axioms first index = .ok ((axioms.val.drop index.val).find? (conflicting first)) := by
  rw [against_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    have recursive := against_from_total axioms first next
    have stepFind : (axioms.val.drop index.val).find? (conflicting first) =
        if Conflict first axioms.val[index.val] then some axioms.val[index.val]
        else (axioms.val.drop (index.val + 1)).find? (conflicting first) := by
      rw [List.drop_eq_getElem_cons inside]
      by_cases actual : Conflict first axioms.val[index.val] <;>
        simp only [List.find?_cons,conflicting,actual,decide_true,decide_false,↓reduceIte]
    by_cases pair : SamePair first axioms.val[index.val] <;>
      by_cases equal : AssertionEq first axioms.val[index.val] <;>
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,same_pair_total_correct,
        same_object_assertion_total_correct,pair,equal,advance,recursive,nv,stepFind,Conflict]
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty]
termination_by axioms.val.length - index.val
decreasing_by omega

private def RowsOK (all rows : List AnnotatedAxiom) : Prop :=
  ∀ first ∈ rows, ∀ second ∈ all, ¬ Conflict first second

private def CorrectFrom (all rows : List AnnotatedAxiom) : MultiplicityCheck → Prop
  | .Allowed => RowsOK all rows
  | .MultipleAssertions first second =>
    first ∈ rows ∧ second ∈ all ∧ Conflict first second ∧ ¬ RowsOK all rows

private theorem check_from_total (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ result, check_from axioms index = .ok result ∧
      CorrectFrom axioms.val (axioms.val.drop index.val) result := by
  rw [check_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have against := against_from_total axioms axioms.val[index.val] 0#usize
    cases found : axioms.val.find? (conflicting axioms.val[index.val]) with
    | some second =>
      have member := List.mem_of_find?_eq_some found
      have conflict := List.find?_some found
      have actual : Conflict axioms.val[index.val] second := by
        simpa [conflicting] using conflict
      have firstMember : axioms.val[index.val] ∈ axioms.val.drop index.val := by
        rw [List.drop_eq_getElem_cons inside]; exact List.mem_cons_self
      refine ⟨.MultipleAssertions axioms.val[index.val] second,
        by simp [inside,alloc.vec.Vec.index_slice_index,lookup,against,found],
        firstMember,member,actual,?_⟩
      intro valid
      exact valid axioms.val[index.val] firstMember second member actual
    | none =>
      have row : ∀ second ∈ axioms.val, ¬ Conflict axioms.val[index.val] second := by
        simpa [conflicting] using List.find?_eq_none.mp found
      obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nv : next.val = index.val + 1 := by simpa using nextval
      obtain ⟨result,executed,correct⟩ := check_from_total axioms next
      refine ⟨result,by simp [inside,alloc.vec.Vec.index_slice_index,lookup,against,found,advance,executed],?_⟩
      have splitting : RowsOK axioms.val (axioms.val.drop index.val) ↔
          RowsOK axioms.val (axioms.val.drop (index.val + 1)) := by
        unfold RowsOK
        rw [List.drop_eq_getElem_cons inside,List.forall_mem_cons]
        exact and_iff_right row
      cases result with
      | Allowed => exact splitting.mpr (by simpa [CorrectFrom,nv] using correct)
      | MultipleAssertions first second =>
        rcases correct with ⟨firstMem,secondMem,actual,invalid⟩
        refine ⟨?_,secondMem,actual,?_⟩
        · rw [List.drop_eq_getElem_cons inside]
          exact List.mem_cons_of_mem _ (by simpa [nv] using firstMem)
        · intro valid; exact invalid (by simpa [nv] using splitting.mp valid)
  · refine ⟨.Allowed,by simp [inside],?_⟩
    have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [CorrectFrom,RowsOK,empty]
termination_by axioms.val.length - index.val
decreasing_by omega

private theorem rows_iff_restriction (axioms : List AnnotatedAxiom) :
    RowsOK axioms axioms ↔ Restriction axioms := by
  simp [RowsOK,Restriction,Conflict]

/-- The raw occurrence-vector checker terminates and decides the axiom-set
    condition exactly, preserving the original conflicting annotated axioms. -/
theorem check_multiplicity_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_multiplicity axioms = .ok result ∧ Correct axioms.val result := by
  obtain ⟨result,executed,correct⟩ := check_from_total axioms 0#usize
  refine ⟨result,by simpa [check_multiplicity] using executed,?_⟩
  cases result with
  | Allowed => exact rows_iff_restriction axioms.val |>.mp (by simpa [CorrectFrom] using correct)
  | MultipleAssertions first second =>
    simpa [CorrectFrom,Correct,rows_iff_restriction] using correct

/-- No false rejection from equivalent duplicate occurrences and no missed pair
    of structurally distinct assertions, even when annotations differ. -/
theorem check_multiplicity_accepted_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_multiplicity axioms = .ok .Allowed ↔ Restriction axioms.val := by
  obtain ⟨result,executed,correct⟩ := check_multiplicity_total_correct axioms
  rw [executed]
  cases result with
  | Allowed => simp [Correct] at correct; simp [correct]
  | MultipleAssertions first second => simp [Correct] at correct; simp [correct.2.2.2]

end Rowl.AnonymousMultiplicity
