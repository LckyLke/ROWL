import Rowl.Chains
import Rowl.AlcOntology
import Rowl.AssertionEquality

/-!
The universal role for the completion forest, through a case split, proved
against the independent Direct Semantics. `owl:topObjectProperty`, the
universal role `U`, relates every pair, which no model of the forest has to. A
restriction along it, `∃U.C` or `∀U.C` in either orientation (`Global`), holds
at every element or at none once `U` relates every pair (`withUniversal`), so
its truth is one global choice (`GlobalTruth`). `universal::satisfiable`
collects these restrictions, the atoms, and decides every guess of their
truths with the completion forest: under a guess every atom becomes `⊤` or `⊥`
(`fixedOf`), and the guess is made good by what it requires (`Required`): a
further element in the filler of a true `∃U.C` or outside the filler of a false
`∀U.C`, and the filler of a true `∀U.C` or the complement of the filler of a
false `∃U.C` everywhere. In a model of one guess every guess is right, the atoms
of a filler before the atom itself (`requirements_exact`), so with `U` relating
every pair it is a model of the question (`fixed_meaning`); and a model of the
question in which `U` relates every pair is a model of the guess of its own
truths. Number restrictions must not count along `U` (`NoTopCount`).
-/
namespace Rowl.Universal
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation topObject)
open Rowl.Concepts (denote inv relation_inv)
open Rowl.AlcOntology (RoleOf)
open Rowl.Hierarchy (Closed Respects Constrained)
open Rowl.ChainSemantics (Chained)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
universe u v

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The check for the universal role is exact. -/
theorem not_top_correct (r : ObjectPropertyExpression) :
    universal.not_top r = .ok (decide (RoleOf r ≠ topObject)) := by
  rw [universal.not_top]
  simp only [Rowl.AlcOntology.named_property_correct,bind_ok,ne_eq,
    Rowl.Tableau.property_eq_iff (RoleOf r) topObject]
  by_cases top : (RoleOf r).iri.spelling.val = topObject.iri.spelling.val <;>
    simp_all [Rowl.AlcOntology.same_pattern_total,Array.to_slice,Array.make,lift,topObject]

/-- The universal role is a role of the concept. -/
def UsesTop : concepts.Concept → Prop
  | .HasSelf r => RoleOf r = topObject
  | .NotSelf r => RoleOf r = topObject
  | .And a b => UsesTop a ∨ UsesTop b
  | .Or a b => UsesTop a ∨ UsesTop b
  | .Exists r c => RoleOf r = topObject ∨ UsesTop c
  | .Forall r c => RoleOf r = topObject ∨ UsesTop c
  | .AtLeast _ r c => RoleOf r = topObject ∨ UsesTop c
  | .AtMost _ r c => RoleOf r = topObject ∨ UsesTop c
  | _ => False

/-- No number restriction counts along the universal role. -/
def NoTopCount : concepts.Concept → Prop
  | .And a b => NoTopCount a ∧ NoTopCount b
  | .Or a b => NoTopCount a ∧ NoTopCount b
  | .Exists _ c => NoTopCount c
  | .Forall _ c => NoTopCount c
  | .AtLeast _ r c => RoleOf r ≠ topObject ∧ NoTopCount c
  | .AtMost _ r c => RoleOf r ≠ topObject ∧ NoTopCount c
  | _ => True

/-- A restriction along the universal role: an atom, whose truth is global. -/
def Global : concepts.Concept → Prop
  | .Exists r _ => RoleOf r = topObject
  | .Forall r _ => RoleOf r = topObject
  | _ => False

/-- `a` is a proper part of the concept. -/
def Within (a : concepts.Concept) : concepts.Concept → Prop
  | .And l r => (a = l ∨ Within a l) ∨ (a = r ∨ Within a r)
  | .Or l r => (a = l ∨ Within a l) ∨ (a = r ∨ Within a r)
  | .Exists _ c => a = c ∨ Within a c
  | .Forall _ c => a = c ∨ Within a c
  | .AtLeast _ _ c => a = c ∨ Within a c
  | .AtMost _ _ c => a = c ∨ Within a c
  | _ => False

/-- `a` occurs in the concept: it is the concept or a proper part of it. -/
def Occurs (a c : concepts.Concept) : Prop := a = c ∨ Within a c

/-- The index of the first atom that is the concept, or the number of atoms. -/
noncomputable def atomIndex (atoms : List concepts.Concept) (c : concepts.Concept) : Nat :=
  atoms.findIdx (fun a => decide (a = c))

/-- `⊤` when the guess for the atom of the concept is true, else `⊥`. -/
noncomputable def truthOf (atoms : List concepts.Concept) (guess : List Bool) (c : concepts.Concept) :
    concepts.Concept :=
  if guess[atomIndex atoms c]? = some true then .Top else .Bottom

/-- The concept with every atom replaced by the guess for it, `∃U.Self` by `⊤`
    and its complement by `⊥`. -/
noncomputable def fixedOf (atoms : List concepts.Concept) (guess : List Bool) : concepts.Concept → concepts.Concept
  | .HasSelf r => if RoleOf r = topObject then .Top else .HasSelf r
  | .NotSelf r => if RoleOf r = topObject then .Bottom else .NotSelf r
  | .And a b => .And (fixedOf atoms guess a) (fixedOf atoms guess b)
  | .Or a b => .Or (fixedOf atoms guess a) (fixedOf atoms guess b)
  | .Exists r c => if RoleOf r = topObject then truthOf atoms guess (.Exists r c)
      else .Exists r (fixedOf atoms guess c)
  | .Forall r c => if RoleOf r = topObject then truthOf atoms guess (.Forall r c)
      else .Forall r (fixedOf atoms guess c)
  | .AtLeast n r c => .AtLeast n r (fixedOf atoms guess c)
  | .AtMost n r c => .AtMost n r (fixedOf atoms guess c)
  | c => c

/-- A fact under the guess. -/
noncomputable def fixedFact (atoms : List concepts.Concept) (guess : List Bool) (q : completion.Fact) :
    completion.Fact :=
  ⟨q.node,fixedOf atoms guess q.concept⟩
/-- A definition under the guess. -/
noncomputable def fixedDefinition (atoms : List concepts.Concept) (guess : List Bool) (d : completion.Definition) :
    completion.Definition :=
  ⟨d.class,fixedOf atoms guess d.concept⟩

variable {Object : Type u} {Value : Type v}

/-- The interpretation with the universal role relating every pair. -/
def withUniversal (J : Interpretation Object Value) : Interpretation Object Value :=
  { J with objectProperties := fun p x y => p = topObject ∨ J.objectProperties p x y }

/-- The truth of an atom, the same at every element once the universal role
    relates every pair: some element is in the filler of `∃U.C`, every element
    in the filler of `∀U.C`. -/
def GlobalTruth (J : Interpretation Object Value) : concepts.Concept → Prop
  | .Exists _ c => ∃ y, denote J c y
  | .Forall _ c => ∀ y, denote J c y
  | _ => False

/-- The check for the universal role in a concept is exact. -/
theorem usesTop_correct (c : concepts.Concept) : universal.universal c = .ok (decide (UsesTop c)) := by
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ => rw [universal.universal]; simp [UsesTop]
  | HasSelf r => rw [universal.universal]; simp [UsesTop,not_top_correct]
  | NotSelf r => rw [universal.universal]; simp [UsesTop,not_top_correct]
  | And a b iha ihb =>
    rw [universal.universal,iha]
    by_cases left : UsesTop a <;> simp [UsesTop,left,ihb]
  | Or a b iha ihb =>
    rw [universal.universal,iha]
    by_cases left : UsesTop a <;> simp [UsesTop,left,ihb]
  | Exists r c ih =>
    rw [universal.universal,not_top_correct]
    by_cases top : RoleOf r = topObject <;> simp [UsesTop,top,ih]
  | Forall r c ih =>
    rw [universal.universal,not_top_correct]
    by_cases top : RoleOf r = topObject <;> simp [UsesTop,top,ih]
  | AtLeast n r c ih =>
    rw [universal.universal,not_top_correct]
    by_cases top : RoleOf r = topObject <;> simp [UsesTop,top,ih]
  | AtMost n r c ih =>
    rw [universal.universal,not_top_correct]
    by_cases top : RoleOf r = topObject <;> simp [UsesTop,top,ih]

/-- The check for the universal role in the facts from `index` on is exact. -/
theorem facts_universal_correct (facts : alloc.vec.Vec completion.Fact) (index : Usize) :
    universal.facts_universal facts index =
      .ok (decide (∃ q ∈ facts.val.drop index.val, UsesTop q.concept)) := by
  rw [universal.facts_universal]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := facts_universal_correct facts next
    rw [nextIndex] at rest
    rw [split]
    by_cases here : UsesTop facts.val[index.val].concept
    · simp [more,lookup,usesTop_correct,here]
      exact ⟨facts.val[index.val],by rw [split]; exact List.mem_cons_self ..,here⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,usesTop_correct,decide_eq_true_eq,here,Bool.false_eq_true,advance,rest,List.mem_cons]
      congr 1
      simp [here]
  · have empty : facts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by facts.val.length - index.val
decreasing_by omega

/-- The check for the universal role in the definitions from `index` on is exact. -/
theorem definitions_universal_correct (definitions : alloc.vec.Vec completion.Definition) (index : Usize) :
    universal.definitions_universal definitions index =
      .ok (decide (∃ d ∈ definitions.val.drop index.val, UsesTop d.concept)) := by
  rw [universal.definitions_universal]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : definitions.val.drop index.val =
        definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := definitions_universal_correct definitions next
    rw [nextIndex] at rest
    rw [split]
    by_cases here : UsesTop definitions.val[index.val].concept
    · simp [more,lookup,usesTop_correct,here]
      exact ⟨definitions.val[index.val],by rw [split]; exact List.mem_cons_self ..,here⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,usesTop_correct,decide_eq_true_eq,here,Bool.false_eq_true,advance,rest,List.mem_cons]
      congr 1
      simp [here]
  · have empty : definitions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [more,empty]
termination_by definitions.val.length - index.val
decreasing_by omega

/-- The actual concept comparison decides structural equality. -/
theorem same_concept_correct (a : concepts.Concept) :
    ∀ b, universal.same_concept a b = .ok (decide (a = b)) := by
  induction a with
  | Top => intro b; cases b <;> rw [universal.same_concept] <;> simp
  | Bottom => intro b; cases b <;> rw [universal.same_concept] <;> simp
  | Atom k =>
    intro b
    cases b with
    | Atom k' =>
      rw [universal.same_concept,Rowl.Symbols.same_spelling_total_correct]
      have same : (concepts.Concept.Atom k = .Atom k') ↔ k.iri.spelling.val = k'.iri.spelling.val := by
        rw [concepts.Concept.Atom.injEq,Rowl.Tableau.class_eq_iff]
      simp only [same]
    | _ => rw [universal.same_concept]; simp
  | NotAtom k =>
    intro b
    cases b with
    | NotAtom k' =>
      rw [universal.same_concept,Rowl.Symbols.same_spelling_total_correct]
      have same : (concepts.Concept.NotAtom k = .NotAtom k') ↔ k.iri.spelling.val = k'.iri.spelling.val := by
        rw [concepts.Concept.NotAtom.injEq,Rowl.Tableau.class_eq_iff]
      simp only [same]
    | _ => rw [universal.same_concept]; simp
  | One a =>
    intro b
    cases b with
    | One a' => rw [universal.same_concept,Rowl.AssertionEquality.same_individual_value_total_correct]; simp
    | _ => rw [universal.same_concept]; simp
  | NotOne a =>
    intro b
    cases b with
    | NotOne a' => rw [universal.same_concept,Rowl.AssertionEquality.same_individual_value_total_correct]; simp
    | _ => rw [universal.same_concept]; simp
  | HasSelf r1 =>
    intro b
    cases b with
    | HasSelf r2 => rw [universal.same_concept]; simp [Rowl.Concepts.same_role_correct]
    | _ => rw [universal.same_concept]; simp
  | NotSelf r1 =>
    intro b
    cases b with
    | NotSelf r2 => rw [universal.same_concept]; simp [Rowl.Concepts.same_role_correct]
    | _ => rw [universal.same_concept]; simp
  | And l1 r1 ihl ihr =>
    intro b
    cases b with
    | And l2 r2 =>
      rw [universal.same_concept,ihl]
      by_cases left : l1 = l2
      · subst left; simp [ihr]
      · simp [left]
    | _ => rw [universal.same_concept]; simp
  | Or l1 r1 ihl ihr =>
    intro b
    cases b with
    | Or l2 r2 =>
      rw [universal.same_concept,ihl]
      by_cases left : l1 = l2
      · subst left; simp [ihr]
      · simp [left]
    | _ => rw [universal.same_concept]; simp
  | Exists r1 c1 ih =>
    intro b
    cases b with
    | Exists r2 c2 =>
      rw [universal.same_concept,Rowl.Concepts.same_role_correct]
      by_cases role : r1 = r2
      · subst role; simp [ih]
      · simp [role]
    | _ => rw [universal.same_concept]; simp
  | Forall r1 c1 ih =>
    intro b
    cases b with
    | Forall r2 c2 =>
      rw [universal.same_concept,Rowl.Concepts.same_role_correct]
      by_cases role : r1 = r2
      · subst role; simp [ih]
      · simp [role]
    | _ => rw [universal.same_concept]; simp
  | AtLeast n1 r1 c1 ih =>
    intro b
    cases b with
    | AtLeast n2 r2 c2 =>
      rw [universal.same_concept]
      by_cases bound : n1 = n2
      · subst bound
        by_cases role : r1 = r2
        · subst role; simp [Rowl.Concepts.same_role_correct,ih]
        · simp [Rowl.Concepts.same_role_correct,role]
      · simp [bound]
    | _ => rw [universal.same_concept]; simp
  | AtMost n1 r1 c1 ih =>
    intro b
    cases b with
    | AtMost n2 r2 c2 =>
      rw [universal.same_concept]
      by_cases bound : n1 = n2
      · subst bound
        by_cases role : r1 = r2
        · subst role; simp [Rowl.Concepts.same_role_correct,ih]
        · simp [Rowl.Concepts.same_role_correct,role]
      · simp [bound]
    | _ => rw [universal.same_concept]; simp

/-- The atom search from `index` on finds the first atom that is the concept, or
    ends at the number of atoms. -/
theorem atom_index_correct (atoms : alloc.vec.Vec concepts.Concept) (c : concepts.Concept) (index : Usize)
    (le : index.val ≤ atoms.val.length) :
    ∃ r : Usize, universal.atom_index atoms c index = .ok r ∧
      r.val = index.val + atomIndex (atoms.val.drop index.val) c := by
  rw [universal.atom_index]
  by_cases more : index.val < atoms.val.length
  · have lookup : atoms.index_usize index = .ok atoms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : atoms.val.drop index.val = atoms.val[index.val] :: atoms.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases here : atoms.val[index.val] = c
    · refine ⟨index,?_,?_⟩
      · simp [more,lookup,same_concept_correct,here]
      · rw [split]; simp [atomIndex,List.findIdx_cons,here]
    · obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val+1 := by simpa using nextValue
      obtain ⟨r,run,value⟩ := atom_index_correct atoms c next (by omega)
      refine ⟨r,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,same_concept_correct,decide_eq_true_eq,here,Bool.false_eq_true,advance,run]
      · rw [value,nextIndex,split]
        simp only [atomIndex,List.findIdx_cons,decide_eq_true_eq,here,decide_false,cond_false]
        omega
  · have done : index.val = atoms.val.length := by omega
    refine ⟨alloc.vec.Vec.len atoms,by simp [more],?_⟩
    rw [List.drop_eq_nil_iff.mpr (by omega)]
    simp [atomIndex,done]
termination_by atoms.val.length - index.val
decreasing_by omega

/-- The actual truth of a guess is `truthOf`. -/
theorem truth_correct (atoms : alloc.vec.Vec concepts.Concept) (guess : alloc.vec.Vec Bool) (c : concepts.Concept) :
    universal.truth atoms guess c = .ok (truthOf atoms.val guess.val c) := by
  obtain ⟨r,run,value⟩ := atom_index_correct atoms c 0#usize (by simp)
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero,Nat.zero_add] at value
  rw [universal.truth,run,bind_ok]
  by_cases inside : r.val < guess.val.length
  · have lookup : guess.index_usize r = .ok guess.val[r.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have small : r < alloc.vec.Vec.len guess := by simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact inside
    simp only [small,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,bind_ok]
    rw [truthOf,← value,List.getElem?_eq_getElem inside]
    cases guess.val[r.val] <;> simp
  · have big : ¬ r < alloc.vec.Vec.len guess := by simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact inside
    simp only [big,↓reduceIte]
    rw [truthOf,← value,List.getElem?_eq_none (by omega)]
    simp

/-- The actual concept under a guess is `fixedOf`. -/
theorem fixed_correct (atoms : alloc.vec.Vec concepts.Concept) (guess : alloc.vec.Vec Bool) (c : concepts.Concept) :
    universal.fixed c atoms guess = .ok (fixedOf atoms.val guess.val c) := by
  induction c with
  | Top => rw [universal.fixed]; rfl
  | Bottom => rw [universal.fixed]; rfl
  | Atom k => rw [universal.fixed]; cases k; simp [Rowl.Nnf.copy_iri_identity,fixedOf]
  | NotAtom k => rw [universal.fixed]; cases k; simp [Rowl.Nnf.copy_iri_identity,fixedOf]
  | One a => rw [universal.fixed]; simp [Rowl.Concepts.copy_individual_identity,fixedOf]
  | NotOne a => rw [universal.fixed]; simp [Rowl.Concepts.copy_individual_identity,fixedOf]
  | HasSelf r =>
    rw [universal.fixed,not_top_correct]
    by_cases top : RoleOf r = topObject <;> simp [top,fixedOf,Rowl.Concepts.copy_role_identity]
  | NotSelf r =>
    rw [universal.fixed,not_top_correct]
    by_cases top : RoleOf r = topObject <;> simp [top,fixedOf,Rowl.Concepts.copy_role_identity]
  | And a b iha ihb => rw [universal.fixed,iha,ihb]; simp [fixedOf]
  | Or a b iha ihb => rw [universal.fixed,iha,ihb]; simp [fixedOf]
  | Exists r c ih =>
    rw [universal.fixed,not_top_correct]
    by_cases top : RoleOf r = topObject
    · simp [top,fixedOf,truth_correct]
    · simp [top,fixedOf,Rowl.Concepts.copy_role_identity,ih]
  | Forall r c ih =>
    rw [universal.fixed,not_top_correct]
    by_cases top : RoleOf r = topObject
    · simp [top,fixedOf,truth_correct]
    · simp [top,fixedOf,Rowl.Concepts.copy_role_identity,ih]
  | AtLeast n r c ih => rw [universal.fixed]; simp [fixedOf,Rowl.Concepts.copy_role_identity,ih]
  | AtMost n r c ih => rw [universal.fixed]; simp [fixedOf,Rowl.Concepts.copy_role_identity,ih]

/-- The facts under a guess, appended to `out`. -/
theorem fixed_facts_correct (facts : alloc.vec.Vec completion.Fact) (atoms : alloc.vec.Vec concepts.Concept)
    (guess : alloc.vec.Vec Bool) (index : Usize) (out : alloc.vec.Vec completion.Fact)
    (room : out.val.length + (facts.val.length - index.val) ≤ Usize.max) :
    ∃ v, universal.fixed_facts facts atoms guess index out = .ok (some v) ∧
      v.val = out.val ++ (facts.val.drop index.val).map (fixedFact atoms.val guess.val) := by
  rw [universal.fixed_facts]
  by_cases more : index.val < facts.val.length
  · have more' : index < alloc.vec.Vec.len facts := by simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    have fits : out.val.length < Usize.max := by omega
    have fits' : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,usize_max_val]; exact fits
    have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      rfl
    obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (fixedFact atoms.val guess.val facts.val[index.val]) fits)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v,run,value⟩ := fixed_facts_correct facts atoms guess next pushed
      (by rw [contents,nextIndex]; simp; omega)
    refine ⟨v,?_,?_⟩
    · simp only [more',↓reduceIte,fits',alloc.vec.Vec.index_slice_index,lookup,bind_ok,fixed_correct]
      have same : ({ facts.val[index.val] with concept := fixedOf atoms.val guess.val facts.val[index.val].concept } :
          completion.Fact) = fixedFact atoms.val guess.val facts.val[index.val] := rfl
      rw [same,push,bind_ok,advance,bind_ok,run]
    · rw [value,contents,nextIndex,List.drop_eq_getElem_cons more,List.map_cons,List.append_assoc,
        List.singleton_append]
      rfl
  · have more' : ¬ index < alloc.vec.Vec.len facts := by simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    refine ⟨out,by simp only [more',↓reduceIte],?_⟩
    simp [List.drop_eq_nil_iff.mpr (show facts.val.length ≤ index.val by omega)]
termination_by facts.val.length - index.val
decreasing_by omega

private theorem fixed_definition_shape (atoms : List concepts.Concept) (guess : List Bool)
    (d : completion.Definition) :
    ({ «class» := { iri := d.«class».iri }, concept := fixedOf atoms guess d.concept } : completion.Definition) =
      fixedDefinition atoms guess d := rfl

/-- The definitions under a guess, appended to `out`. -/
theorem fixed_definitions_correct (definitions : alloc.vec.Vec completion.Definition)
    (atoms : alloc.vec.Vec concepts.Concept) (guess : alloc.vec.Vec Bool) (index : Usize)
    (out : alloc.vec.Vec completion.Definition)
    (room : out.val.length + (definitions.val.length - index.val) ≤ Usize.max) :
    ∃ v, universal.fixed_definitions definitions atoms guess index out = .ok (some v) ∧
      v.val = out.val ++ (definitions.val.drop index.val).map (fixedDefinition atoms.val guess.val) := by
  rw [universal.fixed_definitions]
  by_cases more : index.val < definitions.val.length
  · have more' : index < alloc.vec.Vec.len definitions := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    have fits : out.val.length < Usize.max := by omega
    have fits' : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,usize_max_val]; exact fits
    have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      rfl
    obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (fixedDefinition atoms.val guess.val definitions.val[index.val]) fits)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v,run,value⟩ := fixed_definitions_correct definitions atoms guess next pushed
      (by rw [contents,nextIndex]; simp; omega)
    refine ⟨v,?_,?_⟩
    · simp only [more',↓reduceIte,fits',alloc.vec.Vec.index_slice_index,lookup,bind_ok,fixed_correct,
        Rowl.Nnf.copy_iri_identity]
      rw [fixed_definition_shape,push,bind_ok,advance,bind_ok,run]
    · rw [value,contents,nextIndex,List.drop_eq_getElem_cons more,List.map_cons,List.append_assoc,
        List.singleton_append]
      rfl
  · have more' : ¬ index < alloc.vec.Vec.len definitions := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    refine ⟨out,by simp only [more',↓reduceIte],?_⟩
    simp [List.drop_eq_nil_iff.mpr (show definitions.val.length ≤ index.val by omega)]
termination_by definitions.val.length - index.val
decreasing_by omega

/-- A witness fact goes last. -/
theorem witness_correct (query : alloc.vec.Vec completion.Fact) (node : Usize) (concept : concepts.Concept) :
    ∃ r, universal.witness query node concept = .ok r ∧ ∀ q, r = some q → q.val = query.val ++ [⟨node,concept⟩] := by
  rw [universal.witness]
  by_cases fits : query.val.length < Usize.max
  · have fits' : alloc.vec.Vec.len query < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,usize_max_val]; exact fits
    obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec query ⟨node,concept⟩ fits)
    refine ⟨some pushed,by simp only [fits',↓reduceIte,push,bind_ok],?_⟩
    intro q same
    cases same
    exact contents
  · have fits' : ¬ alloc.vec.Vec.len query < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,usize_max_val]; exact fits
    exact ⟨none,by simp only [fits',↓reduceIte],by simp⟩

/-- Copying a guess from `index` on appends it to `out`. -/
theorem copy_guess_correct (guess : alloc.vec.Vec Bool) (index : Usize) (out : alloc.vec.Vec Bool)
    (room : out.val.length + (guess.val.length - index.val) ≤ Usize.max) :
    ∃ v, universal.copy_guess guess index out = .ok v ∧ v.val = out.val ++ guess.val.drop index.val := by
  rw [universal.copy_guess]
  by_cases more : index.val < guess.val.length
  · have more' : index < alloc.vec.Vec.len guess := by simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    have fits : out.val.length < Usize.max := by omega
    have fits' : alloc.vec.Vec.len out < core.num.Usize.MAX := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,usize_max_val]; exact fits
    have lookup : guess.index_usize index = .ok guess.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      rfl
    obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out guess.val[index.val] fits)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨v,run,value⟩ := copy_guess_correct guess next pushed (by rw [contents,nextIndex]; simp; omega)
    refine ⟨v,?_,?_⟩
    · simp only [more',↓reduceIte,fits',alloc.vec.Vec.index_slice_index,lookup,bind_ok,push,advance,run]
    · rw [value,contents,nextIndex,List.drop_eq_getElem_cons more,List.append_assoc,List.singleton_append]
      rfl
  · have more' : ¬ index < alloc.vec.Vec.len guess := by simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    refine ⟨out,by simp only [more',↓reduceIte],?_⟩
    simp [List.drop_eq_nil_iff.mpr (show guess.val.length ≤ index.val by omega)]
termination_by guess.val.length - index.val
decreasing_by omega

/-- The atom search ends inside the atoms exactly when the concept is one. -/
theorem atomIndex_lt (atoms : List concepts.Concept) (c : concepts.Concept) :
    atomIndex atoms c < atoms.length ↔ c ∈ atoms := by
  rw [atomIndex,List.findIdx_lt_length]
  simp

/-- The atom search finds the concept itself. -/
theorem atomIndex_get (atoms : List concepts.Concept) (c : concepts.Concept)
    (inside : atomIndex atoms c < atoms.length) : atoms[atomIndex atoms c] = c := by
  have found := List.findIdx_getElem (xs := atoms) (p := fun a => decide (a = c)) (w := inside)
  simp only [decide_eq_true_eq] at found
  exact found

/-- Adding an atom keeps the atoms and has the concept. -/
theorem add_atom_correct (atoms : alloc.vec.Vec concepts.Concept) (c : concepts.Concept) :
    ∃ r, universal.add_atom atoms c = .ok r ∧ ∀ atoms', r = some atoms' →
      ∀ a, a ∈ atoms'.val ↔ a ∈ atoms.val ∨ a = c := by
  obtain ⟨i,run,value⟩ := atom_index_correct atoms c 0#usize (by simp)
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero,Nat.zero_add] at value
  rw [universal.add_atom,run,bind_ok]
  by_cases present : i.val < atoms.val.length
  · have present' : i < alloc.vec.Vec.len atoms := by simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact present
    have member : c ∈ atoms.val := (atomIndex_lt atoms.val c).mp (by rw [← value]; exact present)
    refine ⟨some atoms,by simp only [present',↓reduceIte],?_⟩
    intro atoms' same a
    cases same
    constructor
    · exact .inl
    · rintro (old | rfl)
      · exact old
      · exact member
  · have present' : ¬ i < alloc.vec.Vec.len atoms := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact present
    by_cases fits : atoms.val.length < Usize.max
    · have fits' : alloc.vec.Vec.len atoms < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,usize_max_val]; exact fits
      obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec atoms c fits)
      refine ⟨some pushed,by simp only [present',↓reduceIte,fits',Rowl.Concepts.copy_concept_identity,bind_ok,push],?_⟩
      intro atoms' same a
      cases same
      rw [contents]
      simp
    · have fits' : ¬ alloc.vec.Vec.len atoms < core.num.Usize.MAX := by
        simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,usize_max_val]; exact fits
      exact ⟨none,by simp only [present',↓reduceIte,fits'],by simp⟩

/-- A concept occurs in itself. -/
theorem occurs_self (c : concepts.Concept) : Occurs c c := .inl rfl

/-- Collecting the atoms of a concept keeps the atoms, adds only atoms that
    occur in it, and has every atom that does. -/
theorem collect_correct (c : concepts.Concept) : ∀ (atoms : alloc.vec.Vec concepts.Concept),
    ∃ r, universal.collect c atoms = .ok r ∧ ∀ atoms', r = some atoms' →
      (∀ a ∈ atoms.val, a ∈ atoms'.val) ∧
      (∀ a ∈ atoms'.val, a ∈ atoms.val ∨ (Occurs a c ∧ Global a)) ∧
      (∀ a, Occurs a c → Global a → a ∈ atoms'.val) := by
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ | HasSelf _ | NotSelf _ =>
    intro atoms
    refine ⟨some atoms,by rw [universal.collect],?_⟩
    intro atoms' same
    cases same
    refine ⟨fun a m => m,fun a m => .inl m,?_⟩
    intro a occurs global
    rcases occurs with rfl | inner
    · simp [Global] at global
    · simp [Within] at inner
  | And l r ihl ihr =>
    intro atoms
    obtain ⟨r1,run1,spec1⟩ := ihl atoms
    cases r1 with
    | none => exact ⟨none,by rw [universal.collect]; simp [run1],by simp⟩
    | some atoms1 =>
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms1 rfl
    obtain ⟨r2,run2,spec2⟩ := ihr atoms1
    refine ⟨r2,by rw [universal.collect,run1,bind_ok]; exact run2,?_⟩
    intro atoms' same
    obtain ⟨kept2,new2,all2⟩ := spec2 atoms' same
    refine ⟨fun a m => kept2 a (kept1 a m),?_,?_⟩
    · intro a m
      rcases new2 a m with old | ⟨occurs,global⟩
      · rcases new1 a old with older | ⟨occurs,global⟩
        · exact .inl older
        · exact .inr ⟨.inr (.inl occurs),global⟩
      · exact .inr ⟨.inr (.inr occurs),global⟩
    · intro a occurs global
      rcases occurs with rfl | ((inner | inner) | (inner | inner))
      · simp [Global] at global
      · exact kept2 a (all1 a (.inl inner) global)
      · exact kept2 a (all1 a (.inr inner) global)
      · exact all2 a (.inl inner) global
      · exact all2 a (.inr inner) global
  | Or l r ihl ihr =>
    intro atoms
    obtain ⟨r1,run1,spec1⟩ := ihl atoms
    cases r1 with
    | none => exact ⟨none,by rw [universal.collect]; simp [run1],by simp⟩
    | some atoms1 =>
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms1 rfl
    obtain ⟨r2,run2,spec2⟩ := ihr atoms1
    refine ⟨r2,by rw [universal.collect,run1,bind_ok]; exact run2,?_⟩
    intro atoms' same
    obtain ⟨kept2,new2,all2⟩ := spec2 atoms' same
    refine ⟨fun a m => kept2 a (kept1 a m),?_,?_⟩
    · intro a m
      rcases new2 a m with old | ⟨occurs,global⟩
      · rcases new1 a old with older | ⟨occurs,global⟩
        · exact .inl older
        · exact .inr ⟨.inr (.inl occurs),global⟩
      · exact .inr ⟨.inr (.inr occurs),global⟩
    · intro a occurs global
      rcases occurs with rfl | ((inner | inner) | (inner | inner))
      · simp [Global] at global
      · exact kept2 a (all1 a (.inl inner) global)
      · exact kept2 a (all1 a (.inr inner) global)
      · exact all2 a (.inl inner) global
      · exact all2 a (.inr inner) global
  | Exists role f ih =>
    intro atoms
    obtain ⟨r1,run1,spec1⟩ := ih atoms
    cases r1 with
    | none => exact ⟨none,by rw [universal.collect]; simp [run1],by simp⟩
    | some atoms1 =>
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms1 rfl
    by_cases top : RoleOf role = topObject
    · obtain ⟨r2,run2,spec2⟩ := add_atom_correct atoms1 (.Exists role f)
      refine ⟨r2,by rw [universal.collect,run1]; simp [not_top_correct,top,run2],?_⟩
      intro atoms' same
      have members := spec2 atoms' same
      refine ⟨fun a m => (members a).mpr (.inl (kept1 a m)),?_,?_⟩
      · intro a m
        rcases (members a).mp m with old | rfl
        · rcases new1 a old with older | ⟨occurs,global⟩
          · exact .inl older
          · exact .inr ⟨.inr occurs,global⟩
        · exact .inr ⟨occurs_self _,top⟩
      · intro a occurs global
        rcases occurs with rfl | inner
        · exact (members _).mpr (.inr rfl)
        · exact (members a).mpr (.inl (all1 a inner global))
    · refine ⟨some atoms1,by rw [universal.collect,run1]; simp [not_top_correct,top],?_⟩
      intro atoms' same
      cases same
      refine ⟨kept1,?_,?_⟩
      · intro a m
        rcases new1 a m with old | ⟨occurs,global⟩
        · exact .inl old
        · exact .inr ⟨.inr occurs,global⟩
      · intro a occurs global
        rcases occurs with rfl | inner
        · exact absurd global top
        · exact all1 a inner global
  | Forall role f ih =>
    intro atoms
    obtain ⟨r1,run1,spec1⟩ := ih atoms
    cases r1 with
    | none => exact ⟨none,by rw [universal.collect]; simp [run1],by simp⟩
    | some atoms1 =>
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms1 rfl
    by_cases top : RoleOf role = topObject
    · obtain ⟨r2,run2,spec2⟩ := add_atom_correct atoms1 (.Forall role f)
      refine ⟨r2,by rw [universal.collect,run1]; simp [not_top_correct,top,run2],?_⟩
      intro atoms' same
      have members := spec2 atoms' same
      refine ⟨fun a m => (members a).mpr (.inl (kept1 a m)),?_,?_⟩
      · intro a m
        rcases (members a).mp m with old | rfl
        · rcases new1 a old with older | ⟨occurs,global⟩
          · exact .inl older
          · exact .inr ⟨.inr occurs,global⟩
        · exact .inr ⟨occurs_self _,top⟩
      · intro a occurs global
        rcases occurs with rfl | inner
        · exact (members _).mpr (.inr rfl)
        · exact (members a).mpr (.inl (all1 a inner global))
    · refine ⟨some atoms1,by rw [universal.collect,run1]; simp [not_top_correct,top],?_⟩
      intro atoms' same
      cases same
      refine ⟨kept1,?_,?_⟩
      · intro a m
        rcases new1 a m with old | ⟨occurs,global⟩
        · exact .inl old
        · exact .inr ⟨.inr occurs,global⟩
      · intro a occurs global
        rcases occurs with rfl | inner
        · exact absurd global top
        · exact all1 a inner global
  | AtLeast n role f ih =>
    intro atoms
    obtain ⟨r1,run1,spec1⟩ := ih atoms
    refine ⟨r1,by rw [universal.collect]; exact run1,?_⟩
    intro atoms' same
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms' same
    refine ⟨kept1,?_,?_⟩
    · intro a m
      rcases new1 a m with old | ⟨occurs,global⟩
      · exact .inl old
      · exact .inr ⟨.inr occurs,global⟩
    · intro a occurs global
      rcases occurs with rfl | inner
      · simp [Global] at global
      · exact all1 a inner global
  | AtMost n role f ih =>
    intro atoms
    obtain ⟨r1,run1,spec1⟩ := ih atoms
    refine ⟨r1,by rw [universal.collect]; exact run1,?_⟩
    intro atoms' same
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms' same
    refine ⟨kept1,?_,?_⟩
    · intro a m
      rcases new1 a m with old | ⟨occurs,global⟩
      · exact .inl old
      · exact .inr ⟨.inr occurs,global⟩
    · intro a occurs global
      rcases occurs with rfl | inner
      · simp [Global] at global
      · exact all1 a inner global

/-- Collecting the atoms of the facts from `index` on keeps the atoms, adds only
    atoms that occur in them, and has every atom that does. -/
theorem collect_facts_correct (facts : alloc.vec.Vec completion.Fact) (index : Usize)
    (atoms : alloc.vec.Vec concepts.Concept) :
    ∃ r, universal.collect_facts facts index atoms = .ok r ∧ ∀ atoms', r = some atoms' →
      (∀ a ∈ atoms.val, a ∈ atoms'.val) ∧
      (∀ a ∈ atoms'.val, a ∈ atoms.val ∨ ∃ q ∈ facts.val.drop index.val, Occurs a q.concept ∧ Global a) ∧
      (∀ q ∈ facts.val.drop index.val, ∀ a, Occurs a q.concept → Global a → a ∈ atoms'.val) := by
  rw [universal.collect_facts]
  by_cases more : index.val < facts.val.length
  · have more' : index < alloc.vec.Vec.len facts := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      rfl
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨r1,run1,spec1⟩ := collect_correct facts.val[index.val].concept atoms
    cases r1 with
    | none =>
      exact ⟨none,by simp only [more',↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,bind_ok,run1],by simp⟩
    | some atoms1 =>
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms1 rfl
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r2,run2,spec2⟩ := collect_facts_correct facts next atoms1
    refine ⟨r2,by simp only [more',↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,bind_ok,run1,advance,run2],?_⟩
    intro atoms' same
    obtain ⟨kept2,new2,all2⟩ := spec2 atoms' same
    rw [nextIndex] at new2 all2
    rw [split]
    refine ⟨fun a m => kept2 a (kept1 a m),?_,?_⟩
    · intro a m
      rcases new2 a m with old | ⟨q,qIn,occurs,global⟩
      · rcases new1 a old with older | ⟨occurs,global⟩
        · exact .inl older
        · exact .inr ⟨_,List.mem_cons_self ..,occurs,global⟩
      · exact .inr ⟨q,List.mem_cons_of_mem _ qIn,occurs,global⟩
    · intro q qIn a occurs global
      rcases List.mem_cons.mp qIn with rfl | later
      · exact kept2 a (all1 a occurs global)
      · exact all2 q later a occurs global
  · have more' : ¬ index < alloc.vec.Vec.len facts := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    refine ⟨some atoms,by simp only [more',↓reduceIte],?_⟩
    intro atoms' same
    cases same
    have empty : facts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [empty]
    simp
termination_by facts.val.length - index.val
decreasing_by omega

/-- Collecting the atoms of the definitions from `index` on keeps the atoms, adds only
    atoms that occur in them, and has every atom that does. -/
theorem collect_definitions_correct (definitions : alloc.vec.Vec completion.Definition) (index : Usize)
    (atoms : alloc.vec.Vec concepts.Concept) :
    ∃ r, universal.collect_definitions definitions index atoms = .ok r ∧ ∀ atoms', r = some atoms' →
      (∀ a ∈ atoms.val, a ∈ atoms'.val) ∧
      (∀ a ∈ atoms'.val, a ∈ atoms.val ∨ ∃ d ∈ definitions.val.drop index.val, Occurs a d.concept ∧ Global a) ∧
      (∀ d ∈ definitions.val.drop index.val, ∀ a, Occurs a d.concept → Global a → a ∈ atoms'.val) := by
  rw [universal.collect_definitions]
  by_cases more : index.val < definitions.val.length
  · have more' : index < alloc.vec.Vec.len definitions := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      rfl
    have split : definitions.val.drop index.val = definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨r1,run1,spec1⟩ := collect_correct definitions.val[index.val].concept atoms
    cases r1 with
    | none =>
      exact ⟨none,by simp only [more',↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,bind_ok,run1],by simp⟩
    | some atoms1 =>
    obtain ⟨kept1,new1,all1⟩ := spec1 atoms1 rfl
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val + 1 := by simpa using nextValue
    obtain ⟨r2,run2,spec2⟩ := collect_definitions_correct definitions next atoms1
    refine ⟨r2,by simp only [more',↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,bind_ok,run1,advance,run2],?_⟩
    intro atoms' same
    obtain ⟨kept2,new2,all2⟩ := spec2 atoms' same
    rw [nextIndex] at new2 all2
    rw [split]
    refine ⟨fun a m => kept2 a (kept1 a m),?_,?_⟩
    · intro a m
      rcases new2 a m with old | ⟨d,dIn,occurs,global⟩
      · rcases new1 a old with older | ⟨occurs,global⟩
        · exact .inl older
        · exact .inr ⟨_,List.mem_cons_self ..,occurs,global⟩
      · exact .inr ⟨d,List.mem_cons_of_mem _ dIn,occurs,global⟩
    · intro d dIn a occurs global
      rcases List.mem_cons.mp dIn with rfl | later
      · exact kept2 a (all1 a occurs global)
      · exact all2 d later a occurs global
  · have more' : ¬ index < alloc.vec.Vec.len definitions := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    refine ⟨some atoms,by simp only [more',↓reduceIte],?_⟩
    intro atoms' same
    cases same
    have empty : definitions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [empty]
    simp
termination_by definitions.val.length - index.val
decreasing_by omega

/-- With the universal role relating every pair, an object property expression
    relates what it related, and every pair when its property is universal. -/
theorem relation_with_universal (J : Interpretation Object Value) (r : ObjectPropertyExpression) (x y : Object) :
    objectRelation (withUniversal J) r x y ↔ RoleOf r = topObject ∨ objectRelation J r x y := by
  cases r <;> rfl

/-- Where the universal role already relates every pair, making it do so
    changes no relation. -/
theorem relation_with_total (I : Interpretation Object Value) (full : ∀ x y, I.objectProperties topObject x y)
    (r : ObjectPropertyExpression) (x y : Object) :
    objectRelation (withUniversal I) r x y ↔ objectRelation I r x y := by
  rw [relation_with_universal]
  constructor
  · rintro (top | related)
    · cases r with
      | Property p => simp only [RoleOf] at top; subst top; exact full x y
      | Inverse p => simp only [RoleOf] at top; subst top; exact full y x
    · exact related
  · exact .inr

/-- A concept without the universal role means the same once the universal role
    relates every pair. -/
theorem plain_meaning (J : Interpretation Object Value) :
    ∀ c, ¬ UsesTop c → ∀ x, denote (withUniversal J) c x ↔ denote J c x := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ => intro _ x; exact Iff.rfl
  | HasSelf r =>
    intro plain x
    simp only [UsesTop] at plain
    simp only [denote,relation_with_universal,plain,false_or]
  | NotSelf r =>
    intro plain x
    simp only [UsesTop] at plain
    simp only [denote,relation_with_universal,plain,false_or]
  | And a b iha ihb =>
    intro plain x
    simp only [UsesTop,not_or] at plain
    simp only [denote,iha plain.1 x,ihb plain.2 x]
  | Or a b iha ihb =>
    intro plain x
    simp only [UsesTop,not_or] at plain
    simp only [denote,iha plain.1 x,ihb plain.2 x]
  | Exists r c ih =>
    intro plain x
    simp only [UsesTop,not_or] at plain
    simp only [denote,relation_with_universal,plain.1,false_or,ih plain.2]
  | Forall r c ih =>
    intro plain x
    simp only [UsesTop,not_or] at plain
    simp only [denote,relation_with_universal,plain.1,false_or,ih plain.2]
  | AtLeast n r c ih =>
    intro plain x
    simp only [UsesTop,not_or] at plain
    simp only [denote,relation_with_universal,plain.1,false_or,ih plain.2]
  | AtMost n r c ih =>
    intro plain x
    simp only [UsesTop,not_or] at plain
    simp only [denote,relation_with_universal,plain.1,false_or,ih plain.2]

/-- Where the universal role already relates every pair, making it do so
    changes no meaning. -/
theorem denote_with_total (I : Interpretation Object Value) (full : ∀ x y, I.objectProperties topObject x y) :
    ∀ c x, denote (withUniversal I) c x ↔ denote I c x := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ => intro x; exact Iff.rfl
  | HasSelf r => intro x; exact relation_with_total I full r x x
  | NotSelf r => intro x; exact not_congr (relation_with_total I full r x x)
  | And a b iha ihb => intro x; simp only [denote,iha x,ihb x]
  | Or a b iha ihb => intro x; simp only [denote,iha x,ihb x]
  | Exists r c ih => intro x; simp only [denote,relation_with_total I full,ih]
  | Forall r c ih => intro x; simp only [denote,relation_with_total I full,ih]
  | AtLeast n r c ih => intro x; simp only [denote,relation_with_total I full,ih]
  | AtMost n r c ih => intro x; simp only [denote,relation_with_total I full,ih]

/-- An atom holds at an element exactly when it is true, once the universal role
    relates every pair. -/
theorem global_denote (J : Interpretation Object Value) (a : concepts.Concept) (global : Global a) (x : Object) :
    denote (withUniversal J) a x ↔ GlobalTruth (withUniversal J) a := by
  cases a with
  | Exists r c =>
    simp only [Global] at global
    simp [denote,GlobalTruth,relation_with_universal,global]
  | Forall r c =>
    simp only [Global] at global
    simp [denote,GlobalTruth,relation_with_universal,global]
  | _ => simp [Global] at global

/-- Occurrence is transitive. -/
theorem occurs_trans {a b : concepts.Concept} (first : Occurs a b) : ∀ c, Occurs b c → Occurs a c := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ | HasSelf _ | NotSelf _ =>
    rintro (rfl | inner)
    · exact first
    · simp [Within] at inner
  | And l r ihl ihr =>
    rintro (rfl | ((same | inner) | (same | inner)))
    · exact first
    · subst same; rcases ihl (.inl rfl) with h | h <;> exact .inr (.inl (by first | exact .inl h | exact .inr h))
    · rcases ihl (.inr inner) with h | h <;> exact .inr (.inl (by first | exact .inl h | exact .inr h))
    · subst same; rcases ihr (.inl rfl) with h | h <;> exact .inr (.inr (by first | exact .inl h | exact .inr h))
    · rcases ihr (.inr inner) with h | h <;> exact .inr (.inr (by first | exact .inl h | exact .inr h))
  | Or l r ihl ihr =>
    rintro (rfl | ((same | inner) | (same | inner)))
    · exact first
    · subst same; rcases ihl (.inl rfl) with h | h <;> exact .inr (.inl (by first | exact .inl h | exact .inr h))
    · rcases ihl (.inr inner) with h | h <;> exact .inr (.inl (by first | exact .inl h | exact .inr h))
    · subst same; rcases ihr (.inl rfl) with h | h <;> exact .inr (.inr (by first | exact .inl h | exact .inr h))
    · rcases ihr (.inr inner) with h | h <;> exact .inr (.inr (by first | exact .inl h | exact .inr h))
  | Exists _ f ih =>
    rintro (rfl | (same | inner))
    · exact first
    · subst same; exact .inr (ih (.inl rfl))
    · exact .inr (ih (.inr inner))
  | Forall _ f ih =>
    rintro (rfl | (same | inner))
    · exact first
    · subst same; exact .inr (ih (.inl rfl))
    · exact .inr (ih (.inr inner))
  | AtLeast _ _ f ih =>
    rintro (rfl | (same | inner))
    · exact first
    · subst same; exact .inr (ih (.inl rfl))
    · exact .inr (ih (.inr inner))
  | AtMost _ _ f ih =>
    rintro (rfl | (same | inner))
    · exact first
    · subst same; exact .inr (ih (.inl rfl))
    · exact .inr (ih (.inr inner))

/-- What occurs in a concept that counts nowhere along the universal role
    counts nowhere along it either. -/
theorem occurs_count {a : concepts.Concept} : ∀ c, Occurs a c → NoTopCount c → NoTopCount a := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ | HasSelf _ | NotSelf _ =>
    rintro (rfl | inner) count
    · exact count
    · simp [Within] at inner
  | And l r ihl ihr =>
    rintro (rfl | ((same | inner) | (same | inner))) count
    · exact count
    · exact ihl (.inl same) count.1
    · exact ihl (.inr inner) count.1
    · exact ihr (.inl same) count.2
    · exact ihr (.inr inner) count.2
  | Or l r ihl ihr =>
    rintro (rfl | ((same | inner) | (same | inner))) count
    · exact count
    · exact ihl (.inl same) count.1
    · exact ihl (.inr inner) count.1
    · exact ihr (.inl same) count.2
    · exact ihr (.inr inner) count.2
  | Exists _ f ih =>
    rintro (rfl | (same | inner)) count
    · exact count
    · exact ih (.inl same) count
    · exact ih (.inr inner) count
  | Forall _ f ih =>
    rintro (rfl | (same | inner)) count
    · exact count
    · exact ih (.inl same) count
    · exact ih (.inr inner) count
  | AtLeast _ _ f ih =>
    rintro (rfl | (same | inner)) count
    · exact count
    · exact ih (.inl same) count.2
    · exact ih (.inr inner) count.2
  | AtMost _ _ f ih =>
    rintro (rfl | (same | inner)) count
    · exact count
    · exact ih (.inl same) count.2
    · exact ih (.inr inner) count.2

/-- A proper part is smaller. -/
theorem within_size {a : concepts.Concept} : ∀ c, Within a c → sizeOf a < sizeOf c := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ | HasSelf _ | NotSelf _ =>
    intro inner; simp [Within] at inner
  | And l r ihl ihr =>
    rintro ((same | inner) | (same | inner))
    · subst same; simp only [concepts.Concept.And.sizeOf_spec]; omega
    · have := ihl inner; simp only [concepts.Concept.And.sizeOf_spec]; omega
    · subst same; simp only [concepts.Concept.And.sizeOf_spec]; omega
    · have := ihr inner; simp only [concepts.Concept.And.sizeOf_spec]; omega
  | Or l r ihl ihr =>
    rintro ((same | inner) | (same | inner))
    · subst same; simp only [concepts.Concept.Or.sizeOf_spec]; omega
    · have := ihl inner; simp only [concepts.Concept.Or.sizeOf_spec]; omega
    · subst same; simp only [concepts.Concept.Or.sizeOf_spec]; omega
    · have := ihr inner; simp only [concepts.Concept.Or.sizeOf_spec]; omega
  | Exists _ f ih =>
    rintro (same | inner)
    · subst same; simp only [concepts.Concept.Exists.sizeOf_spec]; omega
    · have := ih inner; simp only [concepts.Concept.Exists.sizeOf_spec]; omega
  | Forall _ f ih =>
    rintro (same | inner)
    · subst same; simp only [concepts.Concept.Forall.sizeOf_spec]; omega
    · have := ih inner; simp only [concepts.Concept.Forall.sizeOf_spec]; omega
  | AtLeast _ _ f ih =>
    rintro (same | inner)
    · subst same; simp only [concepts.Concept.AtLeast.sizeOf_spec]; omega
    · have := ih inner; simp only [concepts.Concept.AtLeast.sizeOf_spec]; omega
  | AtMost _ _ f ih =>
    rintro (same | inner)
    · subst same; simp only [concepts.Concept.AtMost.sizeOf_spec]; omega
    · have := ih inner; simp only [concepts.Concept.AtMost.sizeOf_spec]; omega

/-- Counting the same predicate counts the same. -/
private theorem atLeast_congr {α : Type u} (n : Nat) (P Q : α → Prop) (same : ∀ y, P y ↔ Q y) :
    Rowl.Owl.AtLeast n P ↔ Rowl.Owl.AtLeast n Q := by
  have : P = Q := funext fun y => propext (same y)
  rw [this]

/-- Once the guess for every atom of a concept is its truth, with the universal
    role relating every pair, the concept under the guess means the concept,
    as long as it counts nowhere along the universal role. -/
theorem fixed_meaning (J : Interpretation Object Value) (atoms : List concepts.Concept) (guess : List Bool) :
    ∀ c, NoTopCount c →
      (∀ a, Occurs a c → Global a → (guess[atomIndex atoms a]? = some true ↔ GlobalTruth (withUniversal J) a)) →
      ∀ x, denote J (fixedOf atoms guess c) x ↔ denote (withUniversal J) c x := by
  intro c
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ => intro _ _ x; exact Iff.rfl
  | HasSelf r =>
    intro _ _ x
    by_cases top : RoleOf r = topObject
    · simp [fixedOf,top,denote,relation_with_universal]
    · simp [fixedOf,top,denote,relation_with_universal]
  | NotSelf r =>
    intro _ _ x
    by_cases top : RoleOf r = topObject
    · simp [fixedOf,top,denote,relation_with_universal]
    · simp [fixedOf,top,denote,relation_with_universal]
  | And l r ihl ihr =>
    intro count exact x
    simp only [fixedOf,denote]
    rw [ihl count.1 (fun a occurs global => exact a (occurs_trans occurs _ (.inr (.inl (occurs_self l))))
        global) x,
      ihr count.2 (fun a occurs global => exact a (occurs_trans occurs _ (.inr (.inr (occurs_self r))))
        global) x]
  | Or l r ihl ihr =>
    intro count exact x
    simp only [fixedOf,denote]
    rw [ihl count.1 (fun a occurs global => exact a (occurs_trans occurs _ (.inr (.inl (occurs_self l))))
        global) x,
      ihr count.2 (fun a occurs global => exact a (occurs_trans occurs _ (.inr (.inr (occurs_self r))))
        global) x]
  | Exists r f ih =>
    intro count exact x
    by_cases top : RoleOf r = topObject
    · have atom : Global (.Exists r f) := top
      rw [global_denote J _ atom x,← exact _ (occurs_self _) atom]
      simp only [fixedOf,top,↓reduceIte,truthOf]
      by_cases guessed : guess[atomIndex atoms (.Exists r f)]? = some true <;> simp [guessed,denote]
    · have inner := ih count (fun a occurs global => exact a (occurs_trans occurs _ (.inr (occurs_self f))) global)
      simp only [fixedOf,top,↓reduceIte,denote,relation_with_universal,false_or,inner]
  | Forall r f ih =>
    intro count exact x
    by_cases top : RoleOf r = topObject
    · have atom : Global (.Forall r f) := top
      rw [global_denote J _ atom x,← exact _ (occurs_self _) atom]
      simp only [fixedOf,top,↓reduceIte,truthOf]
      by_cases guessed : guess[atomIndex atoms (.Forall r f)]? = some true <;> simp [guessed,denote]
    · have inner := ih count (fun a occurs global => exact a (occurs_trans occurs _ (.inr (occurs_self f))) global)
      simp only [fixedOf,top,↓reduceIte,denote,relation_with_universal,false_or,inner]
  | AtLeast n r f ih =>
    intro count exact x
    have inner := ih count.2 (fun a occurs global => exact a (occurs_trans occurs _ (.inr (occurs_self f))) global)
    simp only [fixedOf,denote]
    exact atLeast_congr _ _ _ (fun y => by
      rw [relation_with_universal,inner y]
      simp [count.1])
  | AtMost n r f ih =>
    intro count exact x
    have inner := ih count.2 (fun a occurs global => exact a (occurs_trans occurs _ (.inr (occurs_self f))) global)
    simp only [fixedOf,denote,Rowl.Owl.AtMost]
    exact not_congr (atLeast_congr _ _ _ (fun y => by
      rw [relation_with_universal,inner y]
      simp [count.1]))

/-- What the guess requires of atom `j`, whose further node is `base + j`: under
    the guess, an element in the filler of a true `∃U.C` and outside the filler
    of a false `∀U.C` at that node, the filler of a true `∀U.C` and its
    complement for a false `∃U.C` everywhere. -/
def Required (J : Interpretation Object Value) (π : Nat → Object) (atoms : List concepts.Concept)
    (guess : List Bool) (base j : Nat) : Prop :=
  match atoms[j]? with
  | some (.Exists _ f) =>
    if guess[j]? = some true then denote J (fixedOf atoms guess f) (π (base + j))
    else ∀ y, ¬ denote J (fixedOf atoms guess f) y
  | some (.Forall _ f) =>
    if guess[j]? = some true then ∀ y, denote J (fixedOf atoms guess f) y
    else ¬ denote J (fixedOf atoms guess f) (π (base + j))
  | _ => False

/-- Where every requirement holds, every guess is the truth of its atom once the
    universal role relates every pair: the atoms of a filler first, whose
    guesses give the filler its meaning. -/
theorem requirements_exact (J : Interpretation Object Value) (π : Nat → Object) (atoms : List concepts.Concept)
    (guess : List Bool) (base : Nat) (globals : ∀ a ∈ atoms, Global a ∧ NoTopCount a)
    (closed : ∀ a ∈ atoms, ∀ b, Occurs b a → Global b → b ∈ atoms)
    (required : ∀ j, j < atoms.length → Required J π atoms guess base j) :
    ∀ a ∈ atoms, (guess[atomIndex atoms a]? = some true ↔ GlobalTruth (withUniversal J) a) := by
  suffices bounded : ∀ n, ∀ a ∈ atoms, sizeOf a < n →
      (guess[atomIndex atoms a]? = some true ↔ GlobalTruth (withUniversal J) a) from
    fun a member => bounded (sizeOf a + 1) a member (by omega)
  intro n
  induction n with
  | zero => intro a _ small; omega
  | succ n ih =>
    intro a member small
    have inside : atomIndex atoms a < atoms.length := (atomIndex_lt atoms a).mpr member
    have at_index : atoms[atomIndex atoms a] = a := atomIndex_get atoms a inside
    have req := required _ inside
    obtain ⟨global,count⟩ := globals a member
    cases a with
    | Exists r f =>
      have meaning := fixed_meaning J atoms guess f count (fun b occurs bGlobal => by
        have bIn := closed _ member b (.inr occurs) bGlobal
        have := within_size (.Exists r f) (show Within b (.Exists r f) from occurs)
        exact ih b bIn (by omega))
      simp only [Required,List.getElem?_eq_getElem inside,at_index] at req
      by_cases guessed : guess[atomIndex atoms (.Exists r f)]? = some true
      · rw [if_pos guessed] at req
        simp only [guessed,true_iff,GlobalTruth]
        exact ⟨_,(meaning _).mp req⟩
      · rw [if_neg guessed] at req
        simp only [guessed,false_iff,GlobalTruth,not_exists]
        exact fun y holds => req y ((meaning y).mpr holds)
    | Forall r f =>
      have meaning := fixed_meaning J atoms guess f count (fun b occurs bGlobal => by
        have bIn := closed _ member b (.inr occurs) bGlobal
        have := within_size (.Forall r f) (show Within b (.Forall r f) from occurs)
        exact ih b bIn (by omega))
      simp only [Required,List.getElem?_eq_getElem inside,at_index] at req
      by_cases guessed : guess[atomIndex atoms (.Forall r f)]? = some true
      · rw [if_pos guessed] at req
        simp only [guessed,true_iff,GlobalTruth]
        exact fun y => (meaning y).mp (req y)
      · rw [if_neg guessed] at req
        simp only [guessed,false_iff,GlobalTruth]
        exact fun every => req ((meaning _).mpr (every _))
    | _ => simp [Global] at global

/-- The requirements of the atoms from `index` on: the facts they add are at
    the further nodes, and a model of the resulting TBox concept and query
    facts is exactly a model of the given ones with every requirement. -/
theorem require_correct (atoms : alloc.vec.Vec concepts.Concept) (guess : alloc.vec.Vec Bool) (base index : Usize)
    (axioms : concepts.Concept) (query : alloc.vec.Vec completion.Fact) :
    ∃ r, universal.require atoms guess base index axioms query = .ok r ∧ ∀ axioms' query', r = some (axioms',query') →
      (∀ f ∈ query'.val, f ∈ query.val ∨
        (base.val + index.val ≤ f.node.val ∧ f.node.val < base.val + atoms.val.length)) ∧
      ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        ((∀ y, denote I axioms' y) ∧ ∀ f ∈ query'.val, denote I f.concept (π f.node.val)) ↔
        ((∀ y, denote I axioms y) ∧ (∀ f ∈ query.val, denote I f.concept (π f.node.val)) ∧
          ∀ j, index.val ≤ j → j < atoms.val.length → Required I π atoms.val guess.val base.val j) := by
  rw [universal.require]
  by_cases more : index.val < atoms.val.length
  swap
  · have more' : ¬ index < alloc.vec.Vec.len atoms := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    refine ⟨some (axioms,query),by simp only [more',↓reduceIte],?_⟩
    intro axioms' query' same
    simp only [Option.some.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    refine ⟨fun f m => .inl m,?_⟩
    intro Object Value I π
    constructor
    · rintro ⟨ax,fs⟩
      exact ⟨ax,fs,fun j lo hi => absurd hi (by omega)⟩
    · rintro ⟨ax,fs,_⟩
      exact ⟨ax,fs⟩
  have more' : index < alloc.vec.Vec.len atoms := by
    simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
  by_cases guessed : index.val < guess.val.length
  swap
  · have guessed' : ¬ index < alloc.vec.Vec.len guess := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact guessed
    exact ⟨none,by simp only [more',↓reduceIte,guessed'],by simp⟩
  have guessed' : index < alloc.vec.Vec.len guess := by
    simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact guessed
  obtain ⟨room,roomRun,roomValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := core.num.Usize.MAX) (y := base) (by simp [usize_max_val]; scalar_tac))
  have roomIs : room.val = Usize.max - base.val := by simp [usize_max_val] at roomValue; exact roomValue.1
  by_cases fits : index.val < Usize.max - base.val
  swap
  · have fits' : ¬ index < room := by simp only [UScalar.lt_equiv,roomIs]; exact fits
    exact ⟨none,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits'],by simp⟩
  have fits' : index < room := by simp only [UScalar.lt_equiv,roomIs]; exact fits
  have lookup : atoms.index_usize index = .ok atoms.val[index.val] := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    rfl
  have choice : guess.index_usize index = .ok guess.val[index.val] := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem guessed]
    rfl
  obtain ⟨node,nodeRun,nodeValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := base) (y := index) (by scalar_tac))
  have nodeIs : node.val = base.val + index.val := by simpa using nodeValue
  obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
  have nextIndex : next.val = index.val + 1 := by simpa using nextValue
  have here : atoms.val[index.val]? = some atoms.val[index.val] := List.getElem?_eq_getElem more
  have chosen : guess.val[index.val]? = some guess.val[index.val] := List.getElem?_eq_getElem guessed
  -- The requirements from `index` on: this one and the later ones.
  have split : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
      (∀ j, index.val ≤ j → j < atoms.val.length → Required I π atoms.val guess.val base.val j) ↔
      Required I π atoms.val guess.val base.val index.val ∧
        ∀ j, next.val ≤ j → j < atoms.val.length → Required I π atoms.val guess.val base.val j := by
    intro Object Value I π
    rw [nextIndex]
    constructor
    · intro every
      exact ⟨every _ (le_refl _) more,fun j lo hi => every j (by omega) hi⟩
    · rintro ⟨first,later⟩ j lo hi
      rcases Nat.eq_or_lt_of_le lo with same | after
      · rw [← same]; exact first
      · exact later j (by omega) hi
  cases atom : atoms.val[index.val] with
  | Exists role f =>
    have reqIs : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Required I π atoms.val guess.val base.val index.val ↔
          if guess.val[index.val] = true then denote I (fixedOf atoms.val guess.val f) (π (base.val + index.val))
          else ∀ y, ¬ denote I (fixedOf atoms.val guess.val f) y := by
      intro Object Value I π
      simp only [Required,here,atom,chosen]
      cases guess.val[index.val] <;> simp
    cases yes : guess.val[index.val] with
    | true =>
      obtain ⟨o,wRun,wSpec⟩ := witness_correct query node (fixedOf atoms.val guess.val f)
      cases o with
      | none =>
        exact ⟨none,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
          lookup,atom,fixed_correct,choice,yes,nodeRun,wRun],by simp⟩
      | some query1 =>
      have query1Is := wSpec query1 rfl
      obtain ⟨r,run,spec⟩ := require_correct atoms guess base next axioms query1
      refine ⟨r,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
        lookup,atom,fixed_correct,choice,yes,nodeRun,wRun,advance,run],?_⟩
      intro axioms' query' same
      obtain ⟨nodes,meaning⟩ := spec axioms' query' same
      refine ⟨?_,?_⟩
      · intro f member
        rcases nodes f member with old | ⟨lo,hi⟩
        · rw [query1Is] at old
          rcases List.mem_append.mp old with older | added
          · exact .inl older
          · simp only [List.mem_singleton] at added
            subst added
            exact .inr ⟨by simp [nodeIs],by simp [nodeIs]; omega⟩
        · exact .inr ⟨by omega,hi⟩
      · intro Object Value I π
        rw [meaning Object Value I π,split Object Value I π,reqIs Object Value I π,query1Is,yes]
        simp only [List.mem_append,List.mem_singleton,if_true,nodeIs]
        constructor
        · rintro ⟨ax,fs,later⟩
          refine ⟨ax,fun q m => fs q (.inl m),?_,later⟩
          have added := fs _ (.inr rfl)
          simpa [nodeIs] using added
        · rintro ⟨ax,fs,first,later⟩
          refine ⟨ax,?_,later⟩
          rintro q (m | rfl)
          · exact fs q m
          · simpa [nodeIs] using first
    | false =>
      obtain ⟨o,nRun,nSpec⟩ := Rowl.Concepts.negate_correct.{u,v} (fixedOf atoms.val guess.val f)
      cases o with
      | none =>
        exact ⟨none,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
          lookup,atom,fixed_correct,choice,yes,Bool.false_eq_true,nRun],by simp⟩
      | some outside =>
      have outsideIs := nSpec outside rfl
      obtain ⟨r,run,spec⟩ := require_correct atoms guess base next (.And axioms outside) query
      refine ⟨r,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
        lookup,atom,fixed_correct,choice,yes,Bool.false_eq_true,nRun,advance,run],?_⟩
      intro axioms' query' same
      obtain ⟨nodes,meaning⟩ := spec axioms' query' same
      refine ⟨?_,?_⟩
      · intro f member
        rcases nodes f member with old | ⟨lo,hi⟩
        · exact .inl old
        · exact .inr ⟨by omega,hi⟩
      · intro Object Value I π
        rw [meaning Object Value I π,split Object Value I π,reqIs Object Value I π,yes]
        simp only [denote,Bool.false_eq_true,if_false]
        constructor
        · rintro ⟨ax,fs,later⟩
          exact ⟨fun y => (ax y).1,fs,fun y => (outsideIs Object Value I y).mp (ax y).2,later⟩
        · rintro ⟨ax,fs,first,later⟩
          exact ⟨fun y => ⟨ax y,(outsideIs Object Value I y).mpr (first y)⟩,fs,later⟩
  | Forall role f =>
    have reqIs : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Required I π atoms.val guess.val base.val index.val ↔
          if guess.val[index.val] = true then ∀ y, denote I (fixedOf atoms.val guess.val f) y
          else ¬ denote I (fixedOf atoms.val guess.val f) (π (base.val + index.val)) := by
      intro Object Value I π
      simp only [Required,here,atom,chosen]
      cases guess.val[index.val] <;> simp
    cases yes : guess.val[index.val] with
    | true =>
      obtain ⟨r,run,spec⟩ := require_correct atoms guess base next
        (.And axioms (fixedOf atoms.val guess.val f)) query
      refine ⟨r,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
        lookup,atom,fixed_correct,choice,yes,advance,run],?_⟩
      intro axioms' query' same
      obtain ⟨nodes,meaning⟩ := spec axioms' query' same
      refine ⟨?_,?_⟩
      · intro f member
        rcases nodes f member with old | ⟨lo,hi⟩
        · exact .inl old
        · exact .inr ⟨by omega,hi⟩
      · intro Object Value I π
        rw [meaning Object Value I π,split Object Value I π,reqIs Object Value I π,yes]
        simp only [denote,if_true]
        constructor
        · rintro ⟨ax,fs,later⟩
          exact ⟨fun y => (ax y).1,fs,fun y => (ax y).2,later⟩
        · rintro ⟨ax,fs,first,later⟩
          exact ⟨fun y => ⟨ax y,first y⟩,fs,later⟩
    | false =>
      obtain ⟨o,nRun,nSpec⟩ := Rowl.Concepts.negate_correct.{u,v} (fixedOf atoms.val guess.val f)
      cases o with
      | none =>
        exact ⟨none,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
          lookup,atom,fixed_correct,choice,yes,Bool.false_eq_true,nRun],by simp⟩
      | some outside =>
      have outsideIs := nSpec outside rfl
      obtain ⟨o2,wRun,wSpec⟩ := witness_correct query node outside
      cases o2 with
      | none =>
        exact ⟨none,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
          lookup,atom,fixed_correct,choice,yes,Bool.false_eq_true,nRun,nodeRun,wRun],by simp⟩
      | some query1 =>
      have query1Is := wSpec query1 rfl
      obtain ⟨r,run,spec⟩ := require_correct atoms guess base next axioms query1
      refine ⟨r,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
        lookup,atom,fixed_correct,choice,yes,Bool.false_eq_true,nRun,nodeRun,wRun,advance,run],?_⟩
      intro axioms' query' same
      obtain ⟨nodes,meaning⟩ := spec axioms' query' same
      refine ⟨?_,?_⟩
      · intro f member
        rcases nodes f member with old | ⟨lo,hi⟩
        · rw [query1Is] at old
          rcases List.mem_append.mp old with older | added
          · exact .inl older
          · simp only [List.mem_singleton] at added
            subst added
            exact .inr ⟨by simp [nodeIs],by simp [nodeIs]; omega⟩
        · exact .inr ⟨by omega,hi⟩
      · intro Object Value I π
        rw [meaning Object Value I π,split Object Value I π,reqIs Object Value I π,query1Is,yes]
        simp only [List.mem_append,List.mem_singleton,Bool.false_eq_true,if_false,nodeIs]
        constructor
        · rintro ⟨ax,fs,later⟩
          refine ⟨ax,fun q m => fs q (.inl m),?_,later⟩
          have added := (outsideIs Object Value I _).mp (fs _ (.inr rfl))
          simpa [nodeIs] using added
        · rintro ⟨ax,fs,first,later⟩
          refine ⟨ax,?_,later⟩
          rintro q (m | rfl)
          · exact fs q m
          · exact (outsideIs Object Value I _).mpr (by simpa [nodeIs] using first)
  | _ =>
    exact ⟨none,by simp only [more',↓reduceIte,guessed',roomRun,bind_ok,fits',alloc.vec.Vec.index_slice_index,
      lookup,atom],by simp⟩
termination_by atoms.val.length - index.val
decreasing_by all_goals omega

private theorem new_val_facts : (alloc.vec.Vec.new completion.Fact).val = [] := rfl
private theorem new_val_definitions : (alloc.vec.Vec.new completion.Definition).val = [] := rfl

/-- One guess is decided by the completion forest: an acceptance comes with a
    model of the role axioms, the concepts under the guess and its requirements,
    and a rejection rules out every such model. -/
theorem guessed_correct (count : Usize) (query facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (chs : alloc.vec.Vec role_chains.Chain) (atoms : alloc.vec.Vec concepts.Concept) (guess : alloc.vec.Vec Bool)
    (positive : 0 < count.val)
    (factsIn : ∀ f ∈ query.val ++ facts.val, f.node.val < count.val)
    (linksIn : ∀ l ∈ links.val, l.from.val < count.val ∧ l.to.val < count.val) :
    ∃ r, universal.guessed count query facts links axioms definitions h chs atoms guess = .ok r ∧
      (r = some true → ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
        Respects I h ∧ Chained I chs.val ∧ Constrained I h ∧
        (∀ y, denote I (fixedOf atoms.val guess.val axioms) y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I (fixedOf atoms.val guess.val d.concept) y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I (fixedOf atoms.val guess.val f.concept) (π f.node.val)) ∧
        (∀ j, j < atoms.val.length → Required I π atoms.val guess.val count.val j) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) ∧
      (r = some false → ¬ ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Respects I h ∧ Chained I chs.val ∧ Constrained I h ∧
        (∀ y, denote I (fixedOf atoms.val guess.val axioms) y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I (fixedOf atoms.val guess.val d.concept) y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I (fixedOf atoms.val guess.val f.concept) (π f.node.val)) ∧
        (∀ j, j < atoms.val.length → Required I π atoms.val guess.val count.val j) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) := by
  rw [universal.guessed]
  obtain ⟨room,roomRun,roomValue⟩ := WP.spec_imp_exists
    (Usize.sub_spec (x := core.num.Usize.MAX) (y := count) (by simp [usize_max_val]; scalar_tac))
  have roomIs : room.val = Usize.max - count.val := by simp [usize_max_val] at roomValue; exact roomValue.1
  by_cases fits : atoms.val.length < Usize.max - count.val
  swap
  · have fits' : ¬ alloc.vec.Vec.len atoms < room := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,roomIs]; exact fits
    exact ⟨none,by simp only [roomRun,bind_ok,fits',↓reduceIte],by simp,by simp⟩
  have fits' : alloc.vec.Vec.len atoms < room := by
    simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val,roomIs]; exact fits
  have zero : (0#usize).val = 0 := rfl
  obtain ⟨q0,q0Run,q0Is⟩ := fixed_facts_correct query atoms guess 0#usize (alloc.vec.Vec.new completion.Fact)
    (by simp [new_val_facts])
  rw [new_val_facts,zero,List.drop_zero,List.nil_append] at q0Is
  obtain ⟨rr,rrRun,rrSpec⟩ := require_correct.{u,v} atoms guess count 0#usize (fixedOf atoms.val guess.val axioms) q0
  cases rr with
  | none =>
    exact ⟨none,by simp only [roomRun,bind_ok,fits',↓reduceIte,q0Run,fixed_correct,rrRun],by simp,by simp⟩
  | some pair =>
  obtain ⟨ax',q'⟩ := pair
  obtain ⟨nodes,meaning⟩ := rrSpec ax' q' rfl
  rw [zero] at nodes meaning
  obtain ⟨f0,f0Run,f0Is⟩ := fixed_facts_correct facts atoms guess 0#usize (alloc.vec.Vec.new completion.Fact)
    (by simp [new_val_facts])
  rw [new_val_facts,zero,List.drop_zero,List.nil_append] at f0Is
  obtain ⟨d0,d0Run,d0Is⟩ := fixed_definitions_correct definitions atoms guess 0#usize
    (alloc.vec.Vec.new completion.Definition) (by simp [new_val_definitions])
  rw [new_val_definitions,zero,List.drop_zero,List.nil_append] at d0Is
  obtain ⟨total,totalRun,totalValue⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := count) (y := alloc.vec.Vec.len atoms) (by simp; omega))
  have totalIs : total.val = count.val + atoms.val.length := by simpa using totalValue
  have factsIn' : ∀ f ∈ q'.val ++ f0.val, f.node.val < total.val := by
    intro f member
    rw [totalIs]
    rcases List.mem_append.mp member with given | old
    · rcases nodes f given with fixedQuery | ⟨_,hi⟩
      · rw [q0Is] at fixedQuery
        obtain ⟨g,gIn,rfl⟩ := List.mem_map.mp fixedQuery
        have := factsIn g (List.mem_append_left _ gIn)
        simp only [fixedFact]
        omega
      · omega
    · rw [f0Is] at old
      obtain ⟨g,gIn,rfl⟩ := List.mem_map.mp old
      have := factsIn g (List.mem_append_right _ gIn)
      simp only [fixedFact]
      omega
  have linksIn' : ∀ l ∈ links.val, l.from.val < total.val ∧ l.to.val < total.val := by
    intro l member
    have := linksIn l member
    omega
  obtain ⟨answer,answerRun,sound,complete⟩ := Rowl.Chains.satisfiable_correct.{u,v} total q' f0 links ax' d0 h
    closed chs (by omega) factsIn' linksIn'
  obtain ⟨rr0,rrRun0,rrSpec0⟩ := require_correct.{0,0} atoms guess count 0#usize (fixedOf atoms.val guess.val axioms) q0
  rw [rrRun] at rrRun0
  cases Result.ok_injective rrRun0
  obtain ⟨_,meaning0⟩ := rrSpec0 ax' q' rfl
  rw [zero] at meaning0
  refine ⟨answer,?_,?_,?_⟩
  · simp only [roomRun,bind_ok,fits',↓reduceIte,q0Run,fixed_correct,rrRun,f0Run,d0Run,totalRun]
    exact answerRun
  · intro yes
    obtain ⟨Obj,I,π,resp,chained,cons,axHold,defsHold,factsHold,linksHold⟩ := sound yes
    obtain ⟨axFixed,queryFixed,req⟩ := (meaning0 Obj Unit I π).mp
      ⟨axHold,fun f m => factsHold f (List.mem_append_left _ m)⟩
    refine ⟨Obj,I,π,resp,chained,cons,axFixed,?_,?_,fun j hi => req j (Nat.zero_le _) hi,linksHold⟩
    · intro d member y classes
      have dIn : fixedDefinition atoms.val guess.val d ∈ d0.val := by
        rw [d0Is]; exact List.mem_map_of_mem member
      exact defsHold _ dIn y classes
    · intro f member
      rcases List.mem_append.mp member with given | old
      · have fIn : fixedFact atoms.val guess.val f ∈ q0.val := by
          rw [q0Is]; exact List.mem_map_of_mem given
        exact queryFixed _ fIn
      · have fIn : fixedFact atoms.val guess.val f ∈ f0.val := by
          rw [f0Is]; exact List.mem_map_of_mem old
        exact factsHold _ (List.mem_append_right _ fIn)
  · rintro no ⟨Object,Value,I,π,resp,chained,cons,axFixed,defsFixed,factsFixed,req,linksHold⟩
    apply complete no
    have queryFixed : ∀ f ∈ q0.val, denote I f.concept (π f.node.val) := by
      intro f member
      rw [q0Is] at member
      obtain ⟨g,gIn,rfl⟩ := List.mem_map.mp member
      exact factsFixed g (List.mem_append_left _ gIn)
    obtain ⟨axHold,factsHold⟩ := (meaning Object Value I π).mpr
      ⟨axFixed,queryFixed,fun j _ hi => req j hi⟩
    refine ⟨Object,Value,I,π,resp,chained,cons,axHold,?_,?_,linksHold⟩
    · intro d member y classes
      rw [d0Is] at member
      obtain ⟨e,eIn,rfl⟩ := List.mem_map.mp member
      exact defsFixed e eIn y classes
    · intro f member
      rcases List.mem_append.mp member with given | old
      · exact factsHold f given
      · rw [f0Is] at old
        obtain ⟨g,gIn,rfl⟩ := List.mem_map.mp old
        exact factsFixed g (List.mem_append_right _ gIn)

private theorem new_val_bools : (alloc.vec.Vec.new Bool).val = [] := rfl

/-- A prefix shorter than a list extends by the list's next element. -/
private theorem prefix_next {α : Type} (p l : List α) (starts : p <+: l) (shorter : p.length < l.length) :
    p ++ [l[p.length]] <+: l := by
  obtain ⟨t,rfl⟩ := starts
  cases t with
  | nil => simp at shorter
  | cons b t => exact ⟨t,by simp⟩

/-- The search over the guesses that start with `guess`: an acceptance comes
    from a full guess that the forest accepts, and a rejection from the forest's
    rejection of every full guess that starts with `guess`. -/
theorem guesses_correct (count : Usize) (query facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy)
    (chs : alloc.vec.Vec role_chains.Chain) (atoms : alloc.vec.Vec concepts.Concept)
    (total : ∀ g : alloc.vec.Vec Bool, ∃ r,
      universal.guessed count query facts links axioms definitions h chs atoms g = .ok r)
    (guess : alloc.vec.Vec Bool) (short : guess.val.length ≤ atoms.val.length) :
    ∃ r, universal.guesses count query facts links axioms definitions h chs atoms guess = .ok r ∧
      (r = some true → ∃ g : alloc.vec.Vec Bool, g.val.length = atoms.val.length ∧
        universal.guessed count query facts links axioms definitions h chs atoms g = .ok (some true)) ∧
      (r = some false → ∀ g : alloc.vec.Vec Bool, guess.val <+: g.val → g.val.length = atoms.val.length →
        universal.guessed count query facts links axioms definitions h chs atoms g = .ok (some false)) := by
  rw [universal.guesses]
  by_cases more : guess.val.length < atoms.val.length
  · have more' : alloc.vec.Vec.len guess < alloc.vec.Vec.len atoms := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    have atomsFit := atoms.property
    obtain ⟨copy,copyRun,copyIs⟩ := copy_guess_correct guess 0#usize (alloc.vec.Vec.new Bool)
      (by simp [new_val_bools])
    rw [new_val_bools,show (0#usize).val = 0 from rfl,List.drop_zero,List.nil_append] at copyIs
    obtain ⟨no,noRun,noIs⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec copy false (by rw [copyIs]; scalar_tac))
    rw [copyIs] at noIs
    obtain ⟨r1,run1,sound1,complete1⟩ := guesses_correct count query facts links axioms definitions h chs atoms
      total no (by rw [noIs]; simp; omega)
    cases r1 with
    | none =>
      exact ⟨none,by simp only [more',↓reduceIte,copyRun,bind_ok,noRun,run1],by simp,by simp⟩
    | some b =>
    cases b with
    | true =>
      exact ⟨some true,by simp only [more',↓reduceIte,copyRun,bind_ok,noRun,run1],fun _ => sound1 rfl,by simp⟩
    | false =>
      obtain ⟨yes,yesRun,yesIs⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec guess true (by scalar_tac))
      obtain ⟨r2,run2,sound2,complete2⟩ := guesses_correct count query facts links axioms definitions h chs atoms
        total yes (by rw [yesIs]; simp; omega)
      refine ⟨r2,by simp only [more',↓reduceIte,copyRun,bind_ok,noRun,run1,Bool.false_eq_true,yesRun,run2],
        sound2,?_⟩
      intro rejected g starts length
      have next := prefix_next guess.val g.val starts (by omega)
      cases bit : g.val[guess.val.length] with
      | false =>
        rw [bit] at next
        exact complete1 rfl g (by rw [noIs]; exact next) length
      | true =>
        rw [bit] at next
        exact complete2 rejected g (by rw [yesIs]; exact next) length
  · have more' : ¬ alloc.vec.Vec.len guess < alloc.vec.Vec.len atoms := by
      simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; exact more
    have full : guess.val.length = atoms.val.length := by omega
    obtain ⟨r,run⟩ := total guess
    refine ⟨r,by simp only [more',↓reduceIte,run],fun yes => ⟨guess,full,by rw [run,yes]⟩,?_⟩
    intro rejected g starts length
    have same : g = guess := by
      apply (alloc.vec.Vec.eq_iff _ _).mpr
      exact (starts.eq_of_length (by omega)).symm
    rw [same,run,rejected]
termination_by atoms.val.length - guess.val.length
decreasing_by all_goals (simp_all; omega)

/-- Where the universal role already relates every pair, the truth of an atom
    is unchanged by making it do so. -/
theorem globalTruth_with_total (I : Interpretation Object Value) (full : ∀ x y, I.objectProperties topObject x y)
    (a : concepts.Concept) : GlobalTruth (withUniversal I) a ↔ GlobalTruth I a := by
  cases a with
  | Exists r c => simp only [GlobalTruth,denote_with_total I full]
  | Forall r c => simp only [GlobalTruth,denote_with_total I full]
  | _ => exact Iff.rfl

/-- What a further element of an atom must be: in the filler of `∃U.C`, outside
    the filler of `∀U.C`. -/
def Wanted (I : Interpretation Object Value) : concepts.Concept → Object → Prop
  | .Exists _ f => fun y => denote I f y
  | .Forall _ f => fun y => ¬ denote I f y
  | _ => fun _ => True

/-- The universal role for the completion forest: the case split over the
    truths of the restrictions along it terminates, an acceptance comes with a
    model of the role axioms in which every concept holds once the universal
    role relates every pair, and a rejection rules out every such model in which
    it does, in any universes. Number restrictions must not count along the
    universal role. -/
theorem satisfiable_correct (count : Usize) (query facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (chs : alloc.vec.Vec role_chains.Chain) (positive : 0 < count.val)
    (factsIn : ∀ f ∈ query.val ++ facts.val, f.node.val < count.val)
    (linksIn : ∀ l ∈ links.val, l.from.val < count.val ∧ l.to.val < count.val)
    (counted : NoTopCount axioms ∧ (∀ d ∈ definitions.val, NoTopCount d.concept) ∧
      ∀ f ∈ query.val ++ facts.val, NoTopCount f.concept) :
    ∃ r, universal.satisfiable count query facts links axioms definitions h chs = .ok r ∧
      (r = some true → ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
        Respects I h ∧ Chained I chs.val ∧ Constrained I h ∧ (∀ y, denote (withUniversal I) axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote (withUniversal I) d.concept y) ∧
        (∀ f ∈ query.val ++ facts.val, denote (withUniversal I) f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) ∧
      (r = some false → ¬ ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        (∀ x y, I.objectProperties topObject x y) ∧
        Respects I h ∧ Chained I chs.val ∧ Constrained I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) := by
  have zero : (0#usize).val = 0 := rfl
  rw [universal.satisfiable]
  obtain ⟨r1,run1,spec1⟩ := collect_correct axioms (alloc.vec.Vec.new concepts.Concept)
  cases r1 with
  | none => exact ⟨none,by simp [run1],by simp,by simp⟩
  | some a1 =>
  obtain ⟨_,new1,all1⟩ := spec1 a1 rfl
  obtain ⟨r2,run2,spec2⟩ := collect_definitions_correct definitions 0#usize a1
  cases r2 with
  | none => exact ⟨none,by simp [run1,run2],by simp,by simp⟩
  | some a2 =>
  obtain ⟨kept2,new2,all2⟩ := spec2 a2 rfl
  obtain ⟨r3,run3,spec3⟩ := collect_facts_correct facts 0#usize a2
  cases r3 with
  | none => exact ⟨none,by simp [run1,run2,run3],by simp,by simp⟩
  | some a3 =>
  obtain ⟨kept3,new3,all3⟩ := spec3 a3 rfl
  obtain ⟨r4,run4,spec4⟩ := collect_facts_correct query 0#usize a3
  cases r4 with
  | none => exact ⟨none,by simp [run1,run2,run3,run4],by simp,by simp⟩
  | some atoms =>
  obtain ⟨kept4,new4,all4⟩ := spec4 atoms rfl
  rw [zero,List.drop_zero] at new2 all2 new3 all3 new4 all4
  -- The concepts of the question and their atoms.
  let Input : concepts.Concept → Prop := fun c =>
    c = axioms ∨ (∃ d ∈ definitions.val, c = d.concept) ∨ ∃ f ∈ query.val ++ facts.val, c = f.concept
  have inputCount : ∀ c, Input c → NoTopCount c := by
    rintro c (rfl | ⟨d,dIn,rfl⟩ | ⟨q,qIn,rfl⟩)
    · exact counted.1
    · exact counted.2.1 d dIn
    · exact counted.2.2 q qIn
  have atomsFrom : ∀ a ∈ atoms.val, ∃ c, Input c ∧ Occurs a c ∧ Global a := by
    intro a m
    rcases new4 a m with m3 | ⟨q,qIn,occ,gl⟩
    · rcases new3 a m3 with m2 | ⟨q,qIn,occ,gl⟩
      · rcases new2 a m2 with m1 | ⟨d,dIn,occ,gl⟩
        · rcases new1 a m1 with m0 | ⟨occ,gl⟩
          · simp at m0
          · exact ⟨axioms,.inl rfl,occ,gl⟩
        · exact ⟨d.concept,.inr (.inl ⟨d,dIn,rfl⟩),occ,gl⟩
      · exact ⟨q.concept,.inr (.inr ⟨q,List.mem_append_right _ qIn,rfl⟩),occ,gl⟩
    · exact ⟨q.concept,.inr (.inr ⟨q,List.mem_append_left _ qIn,rfl⟩),occ,gl⟩
  have cover : ∀ c, Input c → ∀ a, Occurs a c → Global a → a ∈ atoms.val := by
    rintro c (rfl | ⟨d,dIn,rfl⟩ | ⟨q,qIn,rfl⟩) a occ gl
    · exact kept4 a (kept3 a (kept2 a (all1 a occ gl)))
    · exact kept4 a (kept3 a (all2 d dIn a occ gl))
    · rcases List.mem_append.mp qIn with inQuery | inFacts
      · exact all4 q inQuery a occ gl
      · exact kept4 a (all3 q inFacts a occ gl)
  have globals : ∀ a ∈ atoms.val, Global a ∧ NoTopCount a := by
    intro a m
    obtain ⟨c,input,occ,gl⟩ := atomsFrom a m
    exact ⟨gl,occurs_count c occ (inputCount c input)⟩
  have closedAtoms : ∀ a ∈ atoms.val, ∀ b, Occurs b a → Global b → b ∈ atoms.val := by
    intro a m b occ gl
    obtain ⟨c,input,occA,_⟩ := atomsFrom a m
    exact cover c input b (occurs_trans occ c occA) gl
  have total : ∀ g : alloc.vec.Vec Bool, ∃ r,
      universal.guessed count query facts links axioms definitions h chs atoms g = .ok r := by
    intro g
    obtain ⟨r,run,_,_⟩ := guessed_correct.{0,0} count query facts links axioms definitions h closed chs atoms g
      positive factsIn linksIn
    exact ⟨r,run⟩
  by_cases few : atoms.val.length ≤ 16
  swap
  · have few' : ¬ alloc.vec.Vec.len atoms ≤ universal.GUESSES := by
      simp only [universal.GUESSES,UScalar.le_equiv,alloc.vec.Vec.len_val]; simpa using few
    exact ⟨none,by simp only [run1,run2,run3,run4,bind_ok,few',↓reduceIte],by simp,by simp⟩
  have few' : alloc.vec.Vec.len atoms ≤ universal.GUESSES := by
    simp only [universal.GUESSES,UScalar.le_equiv,alloc.vec.Vec.len_val]; simpa using few
  obtain ⟨r,run,sound,complete⟩ := guesses_correct count query facts links axioms definitions h chs atoms total
    (alloc.vec.Vec.new Bool) (by simp [new_val_bools])
  refine ⟨r,by simp only [run1,run2,run3,run4,bind_ok,few',↓reduceIte,run],?_,?_⟩
  · intro yes
    obtain ⟨g,_,gRun⟩ := sound yes
    obtain ⟨_,gRun',gSound,_⟩ := guessed_correct.{0,0} count query facts links axioms definitions h closed chs
      atoms g positive factsIn linksIn
    rw [gRun] at gRun'
    cases Result.ok_injective gRun'
    obtain ⟨Obj,I,π,resp,chained,cons,axFixed,defsFixed,factsFixed,req,linksHold⟩ := gSound rfl
    have right := requirements_exact I π atoms.val g.val count.val globals closedAtoms req
    have meaning : ∀ c, Input c → ∀ x, denote I (fixedOf atoms.val g.val c) x ↔ denote (withUniversal I) c x :=
      fun c input => fixed_meaning I atoms.val g.val c (inputCount c input)
        (fun a occ gl => right a (cover c input a occ gl))
    refine ⟨Obj,I,π,resp,chained,cons,fun y => (meaning axioms (.inl rfl) y).mp (axFixed y),?_,?_,linksHold⟩
    · intro d dIn y classes
      exact (meaning d.concept (.inr (.inl ⟨d,dIn,rfl⟩)) y).mp (defsFixed d dIn y classes)
    · intro f fIn
      exact (meaning f.concept (.inr (.inr ⟨f,fIn,rfl⟩)) _).mp (factsFixed f fIn)
  · rintro no ⟨Object,Value,I,π,full,resp,chained,cons,axHold,defsHold,factsHold,linksHold⟩
    haveI : Nonempty Object := I.objectsNonempty
    -- The guess of the atoms' truths in the model.
    let truths : List Bool := atoms.val.map (fun a => decide (GlobalTruth I a))
    have truthsFit : truths.length ≤ Usize.max := by
      simp only [truths,List.length_map]; exact atoms.property
    let g : alloc.vec.Vec Bool := alloc.vec.Vec.from truths truthsFit
    have gIs : g.val = truths := alloc.vec.Vec.from_val truths truthsFit
    have rejected := complete no g (by rw [new_val_bools]; exact List.nil_prefix)
      (by rw [gIs]; simp [truths])
    obtain ⟨_,gRun',_,gComplete⟩ := guessed_correct.{u,v} count query facts links axioms definitions h closed chs
      atoms g positive factsIn linksIn
    rw [rejected] at gRun'
    cases Result.ok_injective gRun'
    apply gComplete rfl
    -- Every guess is right in the model.
    have right : ∀ a ∈ atoms.val,
        (g.val[atomIndex atoms.val a]? = some true ↔ GlobalTruth (withUniversal I) a) := by
      intro a m
      have inside : atomIndex atoms.val a < atoms.val.length := (atomIndex_lt atoms.val a).mpr m
      have at_index := atomIndex_get atoms.val a inside
      have lookup : g.val[atomIndex atoms.val a]? = some (decide (GlobalTruth I a)) := by
        rw [gIs]
        simp only [truths,List.getElem?_map,List.getElem?_eq_getElem inside,at_index,Option.map_some]
      rw [lookup,globalTruth_with_total I full]
      simp
    have meaning : ∀ c, NoTopCount c → (∀ a, Occurs a c → Global a → a ∈ atoms.val) →
        ∀ x, denote I (fixedOf atoms.val g.val c) x ↔ denote I c x :=
      fun c count inAtoms x => (fixed_meaning I atoms.val g.val c count
        (fun a occ gl => right a (inAtoms a occ gl)) x).trans (denote_with_total I full c x)
    have inputMeaning : ∀ c, Input c → ∀ x, denote I (fixedOf atoms.val g.val c) x ↔ denote I c x :=
      fun c input => meaning c (inputCount c input) (cover c input)
    -- The further elements: one in or out of each atom's filler, as it needs.
    let witness : Nat → Object := fun j => Classical.epsilon (Wanted I (atoms.val.getD j .Top))
    let π' : Nat → Object := fun n => if count.val ≤ n then witness (n - count.val) else π n
    have early : ∀ n, n < count.val → π' n = π n := by
      intro n lt
      simp only [π',show ¬ count.val ≤ n by omega,↓reduceIte]
    refine ⟨Object,Value,I,π',resp,chained,cons,fun y => (inputMeaning axioms (.inl rfl) y).mpr (axHold y),
      ?_,?_,?_,?_⟩
    · intro d dIn y classes
      exact (inputMeaning d.concept (.inr (.inl ⟨d,dIn,rfl⟩)) y).mpr (defsHold d dIn y classes)
    · intro f fIn
      rw [early f.node.val (factsIn f fIn)]
      exact (inputMeaning f.concept (.inr (.inr ⟨f,fIn,rfl⟩)) _).mpr (factsHold f fIn)
    · intro j hi
      have here : atoms.val[j]? = some atoms.val[j] := List.getElem?_eq_getElem hi
      have member : atoms.val[j] ∈ atoms.val := List.getElem_mem hi
      have chosen : g.val[j]? = some (decide (GlobalTruth I atoms.val[j])) := by
        rw [gIs]
        simp only [truths,List.getElem?_map,here,Option.map_some]
      have at_node : π' (count.val + j) = Classical.epsilon (Wanted I atoms.val[j]) := by
        simp only [π',witness,show count.val ≤ count.val + j by omega,↓reduceIte,Nat.add_sub_cancel_left,
          List.getD_eq_getElem _ _ hi]
      obtain ⟨global,countA⟩ := globals _ member
      unfold Required
      rw [here,chosen,at_node]
      cases atom : atoms.val[j] with
      | Exists r f =>
        have countF : NoTopCount f := by rw [atom] at countA; exact countA
        have fMeaning := meaning f countF (fun b occ gl => closedAtoms _ member b (by rw [atom]; exact .inr occ) gl)
        by_cases some : ∃ y, denote I f y
        · have truth : GlobalTruth I (.Exists r f) := some
          rw [decide_eq_true truth]
          dsimp only
          rw [if_pos rfl]
          exact (fMeaning _).mpr (Classical.epsilon_spec (p := Wanted I (.Exists r f)) some)
        · have untrue : ¬ GlobalTruth I (.Exists r f) := some
          rw [decide_eq_false untrue]
          dsimp only
          rw [if_neg (by simp)]
          exact fun y holds => some ⟨y,(fMeaning y).mp holds⟩
      | Forall r f =>
        have countF : NoTopCount f := by rw [atom] at countA; exact countA
        have fMeaning := meaning f countF (fun b occ gl => closedAtoms _ member b (by rw [atom]; exact .inr occ) gl)
        by_cases every : ∀ y, denote I f y
        · have truth : GlobalTruth I (.Forall r f) := every
          rw [decide_eq_true truth]
          dsimp only
          rw [if_pos rfl]
          exact fun y => (fMeaning y).mpr (every y)
        · have untrue : ¬ GlobalTruth I (.Forall r f) := every
          rw [decide_eq_false untrue]
          dsimp only
          rw [if_neg (by simp)]
          have outside : ∃ y, Wanted I (.Forall r f) y := by
            simp only [Wanted]
            exact not_forall.mp every
          exact fun holds => Classical.epsilon_spec outside ((fMeaning _).mp holds)
      | _ => rw [atom] at global; simp [Global] at global
    · intro l lIn
      rw [early _ (linksIn l lIn).1,early _ (linksIn l lIn).2]
      exact linksHold l lIn

end Rowl.Universal
