import Rowl.Internalization

/-!
The role box of an axiom closure, proved against the independent Direct
Semantics. The kernel reads every inclusion and equivalence between named object
properties and every transitive named object property. Each inclusion is added
together with its compositions with the inclusions already listed: everything
below its sub-property becomes included in everything above its
super-property. The result is closed under composition, and an interpretation
respects it exactly when it satisfies every role axiom of the closure.
-/
namespace Rowl.OntologyRoles
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation)
open Rowl.RoleBox (Below Closed Respects inclusionList transitives below_refl respects_below closed_of_empty
  respects_of_empty)
open Rowl.Internalization (RoleAxiom)
open Rowl.Tableau (property_eq_iff)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- What the role axioms of a closure require: every role axiom holds. -/
def RolesHold {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (items : List AnnotatedAxiom) :
    Prop :=
  ∀ a ∈ items, RoleAxiom a.axiom → Rowl.Owl.satisfies I a.axiom

theorem copy_property_identity (r : ObjectProperty) : alc_ontology.copy_property r = .ok r := by
  rw [alc_ontology.copy_property]
  simp [Rowl.Nnf.copy_iri_identity]

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The properties listed below `sup` from `index` are found, after `found`. -/
theorem subs_from_correct (inclusions : alloc.vec.Vec role_box.RoleInclusion) (index : Usize) (sup : ObjectProperty)
    (found : alloc.vec.Vec ObjectProperty) :
    ∃ result, alc_ontology.subs_from inclusions index sup found = .ok result ∧
      ∀ out, result = some out → ∀ x, x ∈ out.val ↔
        x ∈ found.val ∨ ∃ i ∈ inclusions.val.drop index.val, i.sup = sup ∧ i.sub = x := by
  rw [alc_ontology.subs_from]
  by_cases more : index.val < inclusions.val.length
  · have lookup : inclusions.index_usize index = .ok inclusions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : inclusions.val.drop index.val = inclusions.val[index.val] :: inclusions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases hit : inclusions.val[index.val].sup = sup
    · have bytes := (property_eq_iff _ _).mp hit
      by_cases room : found.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec found inclusions.val[index.val].sub room)
        obtain ⟨result,run,spec⟩ := subs_from_correct inclusions next sup appended
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,bytes,decide_true,usize_max_val,room,
            copy_property_identity,push,advance,run]
        · intro out same x
          rw [spec out same x,contents,nextIndex,split]
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
          constructor
          · rintro ((old | rfl) | ⟨i,member,rest⟩)
            · exact .inl old
            · exact .inr ⟨_,.inl rfl,hit,rfl⟩
            · exact .inr ⟨i,.inr member,rest⟩
          · rintro (old | ⟨i,(rfl | member),first,second⟩)
            · exact .inl (.inl old)
            · exact .inl (.inr second.symm)
            · exact .inr ⟨i,member,first,second⟩
      · refine ⟨none,?_,by intro out impossible; cases impossible⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,bytes,decide_true,usize_max_val,room]
    · have bytes : ¬ inclusions.val[index.val].sup.iri.spelling.val = sup.iri.spelling.val :=
        fun h => hit ((property_eq_iff _ _).mpr h)
      obtain ⟨result,run,spec⟩ := subs_from_correct inclusions next sup found
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,bytes,decide_false,Bool.false_eq_true,advance,run]
      · intro out same x
        rw [spec out same x,nextIndex,split]
        simp only [List.mem_cons]
        constructor
        · rintro (old | ⟨i,member,rest⟩)
          · exact .inl old
          · exact .inr ⟨i,.inr member,rest⟩
        · rintro (old | ⟨i,(rfl | member),first,second⟩)
          · exact .inl old
          · exact absurd first hit
          · exact .inr ⟨i,member,first,second⟩
  · have empty : inclusions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some found,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out same x
    cases same
    simp [empty]
termination_by inclusions.val.length - index.val
decreasing_by all_goals omega

/-- The properties listed above `sub` from `index` are found, after `found`. -/
theorem sups_from_correct (inclusions : alloc.vec.Vec role_box.RoleInclusion) (index : Usize) (sub : ObjectProperty)
    (found : alloc.vec.Vec ObjectProperty) :
    ∃ result, alc_ontology.sups_from inclusions index sub found = .ok result ∧
      ∀ out, result = some out → ∀ x, x ∈ out.val ↔
        x ∈ found.val ∨ ∃ i ∈ inclusions.val.drop index.val, i.sub = sub ∧ i.sup = x := by
  rw [alc_ontology.sups_from]
  by_cases more : index.val < inclusions.val.length
  · have lookup : inclusions.index_usize index = .ok inclusions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : inclusions.val.drop index.val = inclusions.val[index.val] :: inclusions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases hit : inclusions.val[index.val].sub = sub
    · have bytes := (property_eq_iff _ _).mp hit
      by_cases room : found.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec found inclusions.val[index.val].sup room)
        obtain ⟨result,run,spec⟩ := sups_from_correct inclusions next sub appended
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,bytes,decide_true,usize_max_val,room,
            copy_property_identity,push,advance,run]
        · intro out same x
          rw [spec out same x,contents,nextIndex,split]
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
          constructor
          · rintro ((old | rfl) | ⟨i,member,rest⟩)
            · exact .inl old
            · exact .inr ⟨_,.inl rfl,hit,rfl⟩
            · exact .inr ⟨i,.inr member,rest⟩
          · rintro (old | ⟨i,(rfl | member),first,second⟩)
            · exact .inl (.inl old)
            · exact .inl (.inr second.symm)
            · exact .inr ⟨i,member,first,second⟩
      · refine ⟨none,?_,by intro out impossible; cases impossible⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,bytes,decide_true,usize_max_val,room]
    · have bytes : ¬ inclusions.val[index.val].sub.iri.spelling.val = sub.iri.spelling.val :=
        fun h => hit ((property_eq_iff _ _).mpr h)
      obtain ⟨result,run,spec⟩ := sups_from_correct inclusions next sub found
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,Rowl.Symbols.same_spelling_total_correct,bytes,decide_false,Bool.false_eq_true,advance,run]
      · intro out same x
        rw [spec out same x,nextIndex,split]
        simp only [List.mem_cons]
        constructor
        · rintro (old | ⟨i,member,rest⟩)
          · exact .inl old
          · exact .inr ⟨i,.inr member,rest⟩
        · rintro (old | ⟨i,(rfl | member),first,second⟩)
          · exact .inl old
          · exact absurd first hit
          · exact .inr ⟨i,member,first,second⟩
  · have empty : inclusions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some found,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out same x
    cases same
    simp [empty]
termination_by inclusions.val.length - index.val
decreasing_by all_goals omega

/-- One row of inclusions: `sub` below every listed property from `index`. -/
theorem row_from_correct (sub : ObjectProperty) (above : alloc.vec.Vec ObjectProperty) (index : Usize)
    (out : alloc.vec.Vec role_box.RoleInclusion) :
    ∃ result, alc_ontology.row_from sub above index out = .ok result ∧
      ∀ out', result = some out' → ∀ i, i ∈ out'.val ↔ i ∈ out.val ∨ (i.sub = sub ∧ i.sup ∈ above.val.drop index.val) := by
  rw [alc_ontology.row_from]
  by_cases more : index.val < above.val.length
  · have lookup : above.index_usize index = .ok above.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : above.val.drop index.val = above.val[index.val] :: above.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases room : out.val.length < Usize.max
    · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out ⟨sub,above.val[index.val]⟩ room)
      obtain ⟨result,run,spec⟩ := row_from_correct sub above next appended
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room,copy_property_identity,
          bind_ok,alloc.vec.Vec.index_slice_index,lookup,push,advance,run]
      · intro out' same i
        rw [spec out' same i,contents,nextIndex,split]
        obtain ⟨isub,isup⟩ := i
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,role_box.RoleInclusion.mk.injEq]
        tauto
    · refine ⟨none,?_,by intro out' impossible; cases impossible⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room]
  · have empty : above.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same i
    cases same
    simp [empty]
termination_by above.val.length - index.val
decreasing_by all_goals omega

/-- Every property listed below, from `index`, below every property listed above. -/
theorem pairs_from_correct (below : alloc.vec.Vec ObjectProperty) (index : Usize) (above : alloc.vec.Vec ObjectProperty)
    (out : alloc.vec.Vec role_box.RoleInclusion) :
    ∃ result, alc_ontology.pairs_from below index above out = .ok result ∧
      ∀ out', result = some out' → ∀ i, i ∈ out'.val ↔
        i ∈ out.val ∨ (i.sub ∈ below.val.drop index.val ∧ i.sup ∈ above.val) := by
  rw [alc_ontology.pairs_from]
  by_cases more : index.val < below.val.length
  · have lookup : below.index_usize index = .ok below.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : below.val.drop index.val = below.val[index.val] :: below.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨row,rowRun,rowSpec⟩ := row_from_correct below.val[index.val] above 0#usize out
    cases row with
    | none =>
      exact ⟨none,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,rowRun],by intro out' impossible; cases impossible⟩
    | some rowOut =>
      obtain ⟨result,run,spec⟩ := pairs_from_correct below next above rowOut
      refine ⟨result,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,rowRun,advance,run],?_⟩
      intro out' same i
      rw [spec out' same i,rowSpec rowOut rfl i,nextIndex,split]
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero,List.mem_cons]
      constructor
      · rintro ((old | ⟨first,second⟩) | ⟨first,second⟩)
        · exact .inl old
        · exact .inr ⟨.inl first,second⟩
        · exact .inr ⟨.inr first,second⟩
      · rintro (old | ⟨(first | first),second⟩)
        · exact .inl (.inl old)
        · exact .inl (.inr ⟨first,second⟩)
        · exact .inr ⟨first,second⟩
  · have empty : below.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same i
    cases same
    simp [empty]
termination_by below.val.length - index.val
decreasing_by all_goals omega

/-- Adding an inclusion lists exactly the old inclusions and every property
    below its sub-property below every property above its super-property. -/
theorem add_inclusion_correct (rb : role_box.RoleBox) (sub sup : ObjectProperty) :
    ∃ result, alc_ontology.add_inclusion rb sub sup = .ok result ∧
      ∀ rb', result = some rb' → rb'.transitive = rb.transitive ∧
        ∀ a b, (a,b) ∈ inclusionList rb' ↔ (a,b) ∈ inclusionList rb ∨ (Below rb a sub ∧ Below rb sup b) := by
  rw [alc_ontology.add_inclusion]
  obtain ⟨start,startPush,startContents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectProperty) sub (by simp; scalar_tac))
  obtain ⟨belowResult,belowRun,belowSpec⟩ := subs_from_correct rb.inclusions 0#usize sub start
  cases belowResult with
  | none => exact ⟨none,by simp [copy_property_identity,startPush,belowRun],by intro rb' impossible; cases impossible⟩
  | some below =>
    obtain ⟨finish,finishPush,finishContents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectProperty) sup (by simp; scalar_tac))
    obtain ⟨aboveResult,aboveRun,aboveSpec⟩ := sups_from_correct rb.inclusions 0#usize sup finish
    cases aboveResult with
    | none =>
      exact ⟨none,by simp [copy_property_identity,startPush,belowRun,finishPush,aboveRun],
        by intro rb' impossible; cases impossible⟩
    | some above =>
      obtain ⟨pairsResult,pairsRun,pairsSpec⟩ := pairs_from_correct below 0#usize above rb.inclusions
      cases pairsResult with
      | none =>
        exact ⟨none,by simp [copy_property_identity,startPush,belowRun,finishPush,aboveRun,pairsRun],
          by intro rb' impossible; cases impossible⟩
      | some inclusions =>
        refine ⟨some { rb with inclusions },by simp [copy_property_identity,startPush,belowRun,finishPush,aboveRun,
          pairsRun],?_⟩
        intro rb' same
        cases same
        refine ⟨rfl,?_⟩
        intro a b
        have belowIff : ∀ x, x ∈ below.val ↔ Below rb x sub := by
          intro x
          rw [belowSpec below rfl x,startContents]
          simp only [show (0#usize).val = 0 from rfl,List.drop_zero,Below,inclusionList,List.mem_map]
          constructor
          · rintro (same | ⟨i,member,first,second⟩)
            · simp at same; exact .inl same
            · exact .inr ⟨i,member,by rw [first,second]⟩
          · rintro (same | ⟨i,member,pair⟩)
            · exact .inl (by simp [same])
            · simp only [Prod.mk.injEq] at pair
              exact .inr ⟨i,member,pair.2,pair.1⟩
        have aboveIff : ∀ y, y ∈ above.val ↔ Below rb sup y := by
          intro y
          rw [aboveSpec above rfl y,finishContents]
          simp only [show (0#usize).val = 0 from rfl,List.drop_zero,Below,inclusionList,List.mem_map]
          constructor
          · rintro (same | ⟨i,member,first,second⟩)
            · simp at same; exact .inl same.symm
            · exact .inr ⟨i,member,by rw [first,second]⟩
          · rintro (same | ⟨i,member,pair⟩)
            · exact .inl (by simp [same])
            · simp only [Prod.mk.injEq] at pair
              exact .inr ⟨i,member,pair.1,pair.2⟩
        simp only [inclusionList,List.mem_map]
        constructor
        · rintro ⟨i,member,pair⟩
          rcases (pairsSpec inclusions rfl i).mp member with old | ⟨first,second⟩
          · exact .inl ⟨i,old,pair⟩
          · simp only [Prod.mk.injEq] at pair
            simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at first
            exact .inr ⟨by rw [← pair.1]; exact (belowIff _).mp first,by rw [← pair.2]; exact (aboveIff _).mp second⟩
        · rintro (⟨i,member,pair⟩ | ⟨first,second⟩)
          · exact ⟨i,(pairsSpec inclusions rfl i).mpr (.inl member),pair⟩
          · refine ⟨⟨a,b⟩,(pairsSpec inclusions rfl _).mpr (.inr ⟨?_,(aboveIff b).mpr second⟩),rfl⟩
            simpa using (belowIff a).mpr first

/-- After adding an inclusion, a property is below another when it was, or when
    it was below the new sub-property and the new super-property below the other. -/
theorem below_added {rb rb' : role_box.RoleBox} {sub sup : ObjectProperty}
    (spec : ∀ a b, (a,b) ∈ inclusionList rb' ↔ (a,b) ∈ inclusionList rb ∨ (Below rb a sub ∧ Below rb sup b))
    (a b : ObjectProperty) : Below rb' a b ↔ Below rb a b ∨ (Below rb a sub ∧ Below rb sup b) := by
  simp only [Below,spec]
  tauto
/-- Adding an inclusion to a closed role box keeps it closed. -/
theorem closed_added {rb rb' : role_box.RoleBox} {sub sup : ObjectProperty} (closed : Closed rb)
    (spec : ∀ a b, (a,b) ∈ inclusionList rb' ↔ (a,b) ∈ inclusionList rb ∨ (Below rb a sub ∧ Below rb sup b)) :
    Closed rb' := by
  intro a b c first second
  rw [below_added spec] at first second ⊢
  rcases first with old | ⟨aBelow,bAbove⟩ <;> rcases second with old' | ⟨bBelow,cAbove⟩
  · exact .inl (closed a b c old old')
  · exact .inr ⟨closed a b sub old bBelow,cAbove⟩
  · exact .inr ⟨aBelow,closed sup b c bAbove old'⟩
  · exact .inr ⟨aBelow,cAbove⟩
/-- An interpretation respects the role box with an added inclusion exactly when
    it respects the old role box and the inclusion. -/
theorem respects_added {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    {rb rb' : role_box.RoleBox} {sub sup : ObjectProperty} (sameTransitive : rb'.transitive = rb.transitive)
    (spec : ∀ a b, (a,b) ∈ inclusionList rb' ↔ (a,b) ∈ inclusionList rb ∨ (Below rb a sub ∧ Below rb sup b)) :
    Respects I rb' ↔ Respects I rb ∧ ∀ x y, I.objectProperties sub x y → I.objectProperties sup x y := by
  have transitivesSame : transitives rb' = transitives rb := by simp [transitives,sameTransitive]
  constructor
  · rintro ⟨inclusions,transitive⟩
    refine ⟨⟨fun s r listed => inclusions s r ((spec s r).mpr (.inl listed)),by rwa [transitivesSame] at transitive⟩,?_⟩
    exact inclusions sub sup ((spec sub sup).mpr (.inr ⟨below_refl rb sub,below_refl rb sup⟩))
  · rintro ⟨⟨inclusions,transitive⟩,added⟩
    refine ⟨?_,by rwa [transitivesSame]⟩
    intro s r listed x y edge
    rcases (spec s r).mp listed with old | ⟨below,above⟩
    · exact inclusions s r old x y edge
    · have respects : Respects I rb := ⟨inclusions,transitive⟩
      exact respects_below respects above (added x y (respects_below respects below edge))

/-- Adding a transitive property keeps the inclusions. -/
theorem add_transitive_correct (rb : role_box.RoleBox) (role : ObjectProperty) :
    ∃ result, alc_ontology.add_transitive rb role = .ok result ∧
      ∀ rb', result = some rb' → rb'.inclusions = rb.inclusions ∧ transitives rb' = transitives rb ++ [role] := by
  rw [alc_ontology.add_transitive]
  by_cases room : rb.transitive.val.length < Usize.max
  · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec rb.transitive role room)
    refine ⟨some { rb with transitive := appended },?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room,copy_property_identity,push]
    · intro rb' same
      cases same
      exact ⟨rfl,by simp [transitives,contents]⟩
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room],?_⟩
    intro rb' impossible
    cases impossible
/-- An interpretation respects the role box with an added transitive property
    exactly when it respects the old role box and the property is transitive. -/
theorem respects_transitive_added {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    {rb rb' : role_box.RoleBox} {role : ObjectProperty} (sameInclusions : rb'.inclusions = rb.inclusions)
    (spec : transitives rb' = transitives rb ++ [role]) :
    Respects I rb' ↔ Respects I rb ∧ ∀ x y z, I.objectProperties role x y → I.objectProperties role y z →
      I.objectProperties role x z := by
  have listed : inclusionList rb' = inclusionList rb := by simp [inclusionList,sameInclusions]
  simp only [Respects,listed,spec,List.mem_append,List.mem_singleton]
  constructor
  · rintro ⟨inclusions,transitive⟩
    exact ⟨⟨inclusions,fun t member => transitive t (.inl member)⟩,transitive role (.inr rfl)⟩
  · rintro ⟨⟨inclusions,transitive⟩,added⟩
    refine ⟨inclusions,?_⟩
    rintro t (member | rfl)
    · exact transitive t member
    · exact added
/-- The named properties after `index`, after `roles`; none for an inverse member. -/
theorem rest_roles_correct (values : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (roles : alloc.vec.Vec ObjectProperty) :
    ∃ result, alc_ontology.rest_roles values index roles = .ok result ∧
      ∀ out, result = some out → (∀ p ∈ values.val.drop index.val, ∃ q, p = .Property q) ∧
        ∀ r, r ∈ out.val ↔ r ∈ roles.val ∨ ObjectPropertyExpression.Property r ∈ values.val.drop index.val := by
  rw [alc_ontology.rest_roles]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    cases here : values.val[index.val] with
    | Property role =>
      by_cases room : roles.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec roles role room)
        obtain ⟨result,run,spec⟩ := rest_roles_correct values next appended
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,here,usize_max_val,room,copy_property_identity,push,advance,run]
        · intro out same
          obtain ⟨named,members⟩ := spec out same
          rw [nextIndex] at named members
          rw [split,here]
          refine ⟨?_,?_⟩
          · simp only [List.forall_mem_cons]
            exact ⟨⟨role,rfl⟩,named⟩
          · intro r
            rw [members r,contents]
            simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,ObjectPropertyExpression.Property.injEq]
            tauto
      · refine ⟨none,?_,by intro out impossible; cases impossible⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,here,usize_max_val,room]
    | Inverse role =>
      refine ⟨none,?_,by intro out impossible; cases impossible⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,here]
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some roles,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out same
    cases same
    simp [empty]
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- The named properties of an equivalence; none for an inverse member. -/
theorem member_roles_correct (members : AtLeastTwo ObjectPropertyExpression) :
    ∃ result, alc_ontology.member_roles members = .ok result ∧
      ∀ out, result = some out → (∀ p ∈ members.elements, ∃ q, p = .Property q) ∧
        ∀ r, r ∈ out.val ↔ ObjectPropertyExpression.Property r ∈ members.elements := by
  rw [alc_ontology.member_roles]
  cases first : members.first with
  | Inverse role => exact ⟨none,by simp,by intro out impossible; cases impossible⟩
  | Property one =>
    obtain ⟨start,startPush,startContents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectProperty) one (by simp; scalar_tac))
    cases second : members.second with
    | Inverse role =>
      exact ⟨none,by simp [copy_property_identity,startPush],by intro out impossible; cases impossible⟩
    | Property two =>
      obtain ⟨pair,pairPush,pairContents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec start two (by rw [startContents]; simp; scalar_tac))
      obtain ⟨result,run,spec⟩ := rest_roles_correct members.rest 0#usize pair
      refine ⟨result,by simp [copy_property_identity,startPush,pairPush,run],?_⟩
      intro out same
      obtain ⟨named,listed⟩ := spec out same
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at named listed
      refine ⟨?_,?_⟩
      · intro p member
        simp only [AtLeastTwo.elements,first,second,List.mem_cons] at member
        rcases member with rfl | rfl | rest
        · exact ⟨one,rfl⟩
        · exact ⟨two,rfl⟩
        · exact named p rest
      · intro r
        rw [listed r,pairContents,startContents]
        simp only [AtLeastTwo.elements,first,second,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
          ObjectPropertyExpression.Property.injEq]
        simp [alloc.vec.Vec.new]
        tauto

/-- `member` below every listed property from `index`, keeping the role box closed. -/
theorem includes_from_correct (rb : role_box.RoleBox) (member : ObjectProperty) (members : alloc.vec.Vec ObjectProperty)
    (index : Usize) (closed : Closed rb) :
    ∃ result, alc_ontology.includes_from rb member members index = .ok result ∧
      ∀ rb', result = some rb' → Closed rb' ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (Respects I rb' ↔ Respects I rb ∧ ∀ b ∈ members.val.drop index.val, ∀ x y,
          I.objectProperties member x y → I.objectProperties b x y) := by
  rw [alc_ontology.includes_from]
  by_cases more : index.val < members.val.length
  · have lookup : members.index_usize index = .ok members.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : members.val.drop index.val = members.val[index.val] :: members.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨added,addRun,addSpec⟩ := add_inclusion_correct rb member members.val[index.val]
    cases added with
    | none =>
      exact ⟨none,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,addRun],by intro rb' impossible; cases impossible⟩
    | some middle =>
      obtain ⟨sameTransitive,inclusions⟩ := addSpec middle rfl
      have middleClosed := closed_added closed inclusions
      obtain ⟨result,run,spec⟩ := includes_from_correct middle member members next middleClosed
      refine ⟨result,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,addRun,advance,run],?_⟩
      intro rb' same
      obtain ⟨finalClosed,meaning⟩ := spec rb' same
      refine ⟨finalClosed,?_⟩
      intro Object Value I
      rw [meaning,respects_added I sameTransitive inclusions,nextIndex,split]
      simp only [List.forall_mem_cons]
      tauto
  · have empty : members.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some rb,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro rb' same
    cases same
    exact ⟨closed,by simp [empty]⟩
termination_by members.val.length - index.val
decreasing_by all_goals omega

/-- Every listed property from `index` below every listed property. -/
theorem equivalent_from_correct (rb : role_box.RoleBox) (members : alloc.vec.Vec ObjectProperty) (index : Usize)
    (closed : Closed rb) :
    ∃ result, alc_ontology.equivalent_from rb members index = .ok result ∧
      ∀ rb', result = some rb' → Closed rb' ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (Respects I rb' ↔ Respects I rb ∧ ∀ a ∈ members.val.drop index.val, ∀ b ∈ members.val, ∀ x y,
          I.objectProperties a x y → I.objectProperties b x y) := by
  rw [alc_ontology.equivalent_from]
  by_cases more : index.val < members.val.length
  · have lookup : members.index_usize index = .ok members.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : members.val.drop index.val = members.val[index.val] :: members.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨included,includeRun,includeSpec⟩ :=
      includes_from_correct.{u,v} rb members.val[index.val] members 0#usize closed
    cases included with
    | none =>
      exact ⟨none,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,includeRun],by intro rb' impossible; cases impossible⟩
    | some middle =>
      obtain ⟨middleClosed,middleMeaning⟩ := includeSpec middle rfl
      obtain ⟨result,run,spec⟩ := equivalent_from_correct middle members next middleClosed
      refine ⟨result,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,includeRun,advance,run],?_⟩
      intro rb' same
      obtain ⟨finalClosed,meaning⟩ := spec rb' same
      refine ⟨finalClosed,?_⟩
      intro Object Value I
      rw [meaning,middleMeaning,nextIndex,split]
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero,List.forall_mem_cons]
      tauto
  · have empty : members.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some rb,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro rb' same
    cases same
    exact ⟨closed,by simp [empty]⟩
termination_by members.val.length - index.val
decreasing_by all_goals omega

/-- Equal relations for every pair of members, read as inclusions both ways. -/
theorem equal_iff_included {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (members : List ObjectProperty) :
    (∀ a ∈ members, ∀ b ∈ members, ∀ x y, I.objectProperties a x y → I.objectProperties b x y) ↔
      ∀ a ∈ members, ∀ b ∈ members, I.objectProperties a = I.objectProperties b := by
  constructor
  · intro included a aIn b bIn
    funext x y
    exact propext ⟨included a aIn b bIn x y,included b bIn a aIn x y⟩
  · intro equal a aIn b bIn x y edge
    rw [← equal a aIn b bIn]
    exact edge

/-- An equivalence of named properties adds exactly their mutual inclusions. -/
theorem add_equivalent_correct (rb : role_box.RoleBox) (members : AtLeastTwo ObjectPropertyExpression)
    (closed : Closed rb) :
    ∃ result, alc_ontology.add_equivalent rb members = .ok result ∧
      ∀ rb', result = some rb' → (∀ p ∈ members.elements, ∃ q, p = .Property q) ∧ Closed rb' ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I rb' ↔ Respects I rb ∧ Rowl.Owl.satisfies I (.EquivalentObjectProperties members)) := by
  rw [alc_ontology.add_equivalent]
  obtain ⟨roles,rolesRun,rolesSpec⟩ := member_roles_correct members
  cases roles with
  | none => exact ⟨none,by simp [rolesRun],by intro rb' impossible; cases impossible⟩
  | some list =>
    obtain ⟨named,listed⟩ := rolesSpec list rfl
    obtain ⟨result,run,spec⟩ := equivalent_from_correct.{u,v} rb list 0#usize closed
    refine ⟨result,by simp [rolesRun,run],?_⟩
    intro rb' same
    obtain ⟨finalClosed,meaning⟩ := spec rb' same
    refine ⟨named,finalClosed,?_⟩
    intro Object Value I
    rw [meaning]
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero]
    rw [equal_iff_included I list.val]
    simp only [Rowl.Owl.satisfies,Rowl.Owl.allEqual]
    constructor
    · rintro ⟨respects,equal⟩
      refine ⟨respects,?_⟩
      intro a aIn b bIn
      obtain ⟨p,rfl⟩ := named a aIn
      obtain ⟨q,rfl⟩ := named b bIn
      exact equal p ((listed p).mpr aIn) q ((listed q).mpr bIn)
    · rintro ⟨respects,equal⟩
      refine ⟨respects,?_⟩
      intro p pIn q qIn
      exact equal _ ((listed p).mp pIn) _ ((listed q).mp qIn)

/-- The role box of the role axioms from `index`, after a closed role box. -/
theorem role_box_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (rb : role_box.RoleBox)
    (closed : Closed rb) :
    ∃ result, alc_ontology.role_box_from items index rb = .ok result ∧
      ∀ rb', result = some rb' → Closed rb' ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (Respects I rb' ↔ Respects I rb ∧ RolesHold I (items.val.drop index.val)) := by
  rw [alc_ontology.role_box_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    -- After this axiom's step, the rest of the role axioms follow by recursion.
    have continuation : ∀ middle : Option role_box.RoleBox,
        (∀ mid, middle = some mid → Closed mid ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I mid ↔ Respects I rb ∧ (RoleAxiom items.val[index.val].axiom →
            Rowl.Owl.satisfies I items.val[index.val].axiom))) →
        ∃ result, (match middle with
          | none => (ok none : Result (Option role_box.RoleBox))
          | some roles2 => alc_ontology.role_box_from items next roles2) = .ok result ∧
          ∀ rb', result = some rb' → Closed rb' ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
            (Respects I rb' ↔ Respects I rb ∧ RolesHold I (items.val.drop index.val)) := by
      intro middle middleSpec
      cases middle with
      | none => exact ⟨none,rfl,by intro rb' impossible; cases impossible⟩
      | some mid =>
        obtain ⟨midClosed,midMeaning⟩ := middleSpec mid rfl
        obtain ⟨result,run,spec⟩ := role_box_from_correct items next mid midClosed
        refine ⟨result,run,?_⟩
        intro rb' same
        obtain ⟨finalClosed,meaning⟩ := spec rb' same
        refine ⟨finalClosed,?_⟩
        intro Object Value I
        rw [meaning,midMeaning,nextIndex,split]
        simp only [RolesHold,List.forall_mem_cons]
        tauto
    have unchanged : ∀ (_ : ¬ RoleAxiom items.val[index.val].axiom), ∃ result,
        (match (some rb : Option role_box.RoleBox) with
          | none => (ok none : Result (Option role_box.RoleBox))
          | some roles2 => alc_ontology.role_box_from items next roles2) = .ok result ∧
          ∀ rb', result = some rb' → Closed rb' ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
            (Respects I rb' ↔ Respects I rb ∧ RolesHold I (items.val.drop index.val)) := by
      intro notRole
      apply continuation (some rb)
      intro mid same
      cases same
      exact ⟨closed,fun Object Value I => by simp [notRole]⟩
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,advance]
    cases here : items.val[index.val].axiom with
    | SubObjectPropertyOf sub sup =>
      cases sub with
      | Single p =>
        cases p with
        | Property s =>
          cases sup with
          | Property r =>
            obtain ⟨added,addRun,addSpec⟩ := add_inclusion_correct rb s r
            simp only [addRun,bind_ok]
            apply continuation added
            intro rb' same
            obtain ⟨sameTransitive,inclusions⟩ := addSpec rb' same
            refine ⟨closed_added closed inclusions,?_⟩
            intro Object Value I
            rw [respects_added I sameTransitive inclusions,here]
            simp [RoleAxiom,Rowl.Owl.satisfies,Rowl.Owl.subRelation,Rowl.Owl.objectRelation]
          | Inverse r => simp only [bind_ok]; exact unchanged (by simp [here,RoleAxiom])
        | Inverse s => cases sup <;> (simp only [bind_ok]; exact unchanged (by simp [here,RoleAxiom]))
      | Chain c => simp only [bind_ok]; exact unchanged (by simp [here,RoleAxiom])
    | EquivalentObjectProperties members =>
      obtain ⟨added,addRun,addSpec⟩ := add_equivalent_correct.{u,v} rb members closed
      simp only [addRun,bind_ok]
      apply continuation added
      intro rb' same
      obtain ⟨named,finalClosed,meaning⟩ := addSpec rb' same
      refine ⟨finalClosed,?_⟩
      intro Object Value I
      rw [meaning,here]
      simp only [RoleAxiom]
      constructor
      · rintro ⟨respects,holds⟩
        exact ⟨respects,fun _ => holds⟩
      · rintro ⟨respects,holds⟩
        exact ⟨respects,holds named⟩
    | TransitiveObjectProperty p =>
      cases p with
      | Property role =>
        obtain ⟨added,addRun,addSpec⟩ := add_transitive_correct rb role
        simp only [addRun,bind_ok]
        apply continuation added
        intro rb' same
        obtain ⟨sameInclusions,transitiveSpec⟩ := addSpec rb' same
        have closed' : Closed rb' := by
          intro a b c first second
          simp only [Below,inclusionList,sameInclusions] at first second ⊢
          exact closed a b c first second
        refine ⟨closed',?_⟩
        intro Object Value I
        rw [respects_transitive_added I sameInclusions transitiveSpec,here]
        simp [RoleAxiom,Rowl.Owl.satisfies,Rowl.Owl.objectRelation]
      | Inverse role => simp only [bind_ok]; exact unchanged (by simp [here,RoleAxiom])
    | _ => simp only [bind_ok]; exact unchanged (by simp [here,RoleAxiom])
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some rb,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro rb' same
    cases same
    exact ⟨closed,by simp [empty,RolesHold]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The role box of a closure is closed under composition, and an interpretation
    respects it exactly when it satisfies every role axiom of the closure. -/
theorem role_box_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, alc_ontology.role_box items = .ok result ∧
      ∀ rb, result = some rb → Closed rb ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (Respects I rb ↔ RolesHold I items.val) := by
  rw [alc_ontology.role_box]
  obtain ⟨result,run,spec⟩ := role_box_from_correct.{u,v} items 0#usize
    ⟨alloc.vec.Vec.new role_box.RoleInclusion,alloc.vec.Vec.new ObjectProperty⟩ (closed_of_empty _ rfl)
  refine ⟨result,run,?_⟩
  intro rb same
  obtain ⟨closed,meaning⟩ := spec rb same
  refine ⟨closed,?_⟩
  intro Object Value I
  rw [meaning]
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero]
  exact ⟨fun both => both.2,fun holds => ⟨respects_of_empty I _ rfl rfl,holds⟩⟩
end Rowl.OntologyRoles
