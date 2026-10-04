import Rowl.ChainSemantics
import Rowl.Nnf

/-!
The actual operations of `role_chains` on roles and automata: equivalence and
complexity of roles, the segments of chains and the transitions of the
automata, which the actual code produces exactly as `Trans` describes them.
-/
namespace Rowl.ChainOps
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv inverse_correct copy_role_identity same_role_correct copy_concept_identity negate_correct denote)
open Rowl.Hierarchy (Below Closed inclusionList transitives below_correct below_refl)
open Rowl.ChainSemantics
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

theorem equivalent_correct (h : hierarchy.RoleHierarchy) (a b : ObjectPropertyExpression) :
    role_chains.equivalent h a b = .ok (decide (Equivalent h a b)) := by
  rw [role_chains.equivalent,below_correct]
  by_cases ab : Below h a b
  · simp [ab,below_correct,Equivalent]
  · simp [ab,Equivalent]

private theorem complex_from_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (r : ObjectPropertyExpression) (index : Usize) :
    role_chains.complex_from h chs r index =
      .ok (decide (∃ ch ∈ chs.val.drop index.val, Below h ch.sup r)) := by
  rw [role_chains.complex_from]
  by_cases more : index.val < chs.val.length
  · have lookup : chs.index_usize index = .ok chs.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : chs.val.drop index.val = chs.val[index.val] :: chs.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := complex_from_correct h chs r index'
    rw [nextIndex] at rest
    rw [split]
    by_cases here : Below h chs.val[index.val].sup r
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,below_correct,here,decide_true]
      simp only [List.mem_cons,exists_eq_or_imp,here,true_or,decide_true]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,below_correct,here,decide_false,Bool.false_eq_true,advance,rest]
      have iff : (∃ ch ∈ chs.val[index.val] :: chs.val.drop (index.val+1), Below h ch.sup r) ↔
          (∃ ch ∈ chs.val.drop (index.val+1), Below h ch.sup r) := by
        constructor
        · rintro ⟨ch,mem,below⟩
          rcases List.mem_cons.mp mem with same | later
          · rw [same] at below; exact absurd below here
          · exact ⟨ch,later,below⟩
        · rintro ⟨ch,mem,below⟩
          exact ⟨ch,List.mem_cons_of_mem _ mem,below⟩
      simp only [iff]
  · have empty : chs.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by chs.val.length - index.val
decreasing_by omega

/-- The actual test decides whether the role is complex. -/
theorem complex_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (r : ObjectPropertyExpression) :
    role_chains.complex h chs r = .ok (decide (Complex h chs.val r)) := by
  rw [role_chains.complex,complex_from_correct]
  simp [Complex]

theorem copy_state_identity (s : role_chains.State) : role_chains.copy_state s = .ok s := by
  cases s <;> rfl

theorem same_state_correct (a b : role_chains.State) : role_chains.same_state a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;> simp [role_chains.same_state]
  rename_i k j k' j'
  by_cases same : k = k'
  · simp [same]
  · simp [same]

theorem copy_filler_identity (f : role_chains.Filler) : role_chains.copy_filler f = .ok f := by
  cases f <;> rfl

theorem same_filler_correct (a b : role_chains.Filler) : role_chains.same_filler a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;> simp [role_chains.same_filler]

/-- The actual test decides whether a chain is a twin. -/
theorem twin_correct (h : hierarchy.RoleHierarchy) (ch : role_chains.Chain) (c : ObjectPropertyExpression) :
    role_chains.twin h ch c = .ok (decide (Twin h ch c)) := by
  rw [role_chains.twin]
  by_cases two : ch.roles.val.length = 2
  · obtain ⟨a,b,roles⟩ : ∃ a b, ch.roles.val = [a,b] := by
      match roles : ch.roles.val, two with
      | [a,b], _ => exact ⟨a,b,rfl⟩
    have len : (alloc.vec.Vec.len ch.roles) = 2#usize := by
      apply UScalar.eq_of_val_eq
      simp [alloc.vec.Vec.len_val,roles]
    have first : ch.roles.index_usize 0#usize = .ok a := by
      simp [alloc.vec.Vec.index_usize,roles]
    have second : ch.roles.index_usize 1#usize = .ok b := by
      simp [alloc.vec.Vec.index_usize,roles]
    simp only [len,↓reduceIte,equivalent_correct,alloc.vec.Vec.index_slice_index,first,second,bind_ok]
    by_cases sup : Equivalent h ch.sup c
    · by_cases ea : Equivalent h a c
      · by_cases eb : Equivalent h b c
        · simp [sup,ea,eb,Twin,roles]
        · simp [sup,ea,eb,Twin,roles]
      · simp [sup,ea,Twin,roles]
    · simp [sup,Twin,roles]
  · have len : ¬ (alloc.vec.Vec.len ch.roles) = 2#usize := by
      intro same
      have := congrArg UScalar.val same
      simp [alloc.vec.Vec.len_val] at this
      exact two this
    have notTwin : ¬ Twin h ch c := by
      rintro ⟨a,b,roles,_⟩
      rw [roles] at two
      simp at two
    simp [len,notTwin]

/-- The segment of the actual code as a `Seg`. -/
def toSeg (s : role_chains.Segment) : Seg := ⟨s.start,s.end,s.offset.val,s.length.val⟩

/-- The actual segment is the one that `segOf` describes. -/
theorem segment_correct (h : hierarchy.RoleHierarchy) (ch : role_chains.Chain) (c : ObjectPropertyExpression) :
    ∃ o, role_chains.segment h ch c = .ok o ∧ o.map toSeg = segOf h ch c := by
  have small : ch.roles.val.length ≤ Usize.max := ch.roles.property
  rw [role_chains.segment]
  match roles : ch.roles.val with
  | [] =>
    have short : (alloc.vec.Vec.len ch.roles) < 2#usize := by
      simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,roles]
    exact ⟨none,by simp [short],by simp [segOf,roles]⟩
  | [a] =>
    have short : (alloc.vec.Vec.len ch.roles) < 2#usize := by
      simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,roles]
    exact ⟨none,by simp [short],by simp [segOf,roles]⟩
  | a :: b :: rest =>
    have long : ¬ (alloc.vec.Vec.len ch.roles) < 2#usize := by
      simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,roles]
    have first : ch.roles.index_usize 0#usize = .ok a := by
      simp [alloc.vec.Vec.index_usize,roles]
    rw [roles] at small
    simp only [List.length_cons] at small
    obtain ⟨less,lessRun,lessVal⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := alloc.vec.Vec.len ch.roles) (y := 1#usize)
        (by simp [alloc.vec.Vec.len_val,roles]))
    have lessIs : less.val = rest.length + 1 := by
      simp [alloc.vec.Vec.len_val,roles] at lessVal; omega
    have described : segOf h ch c =
        if Equivalent h ch.sup c then
          if Equivalent h a c then
            if rest = [] ∧ Equivalent h b c then none
            else some ⟨.Final,.Final,1,rest.length+1⟩
          else if Equivalent h ((b :: rest).getLast (by simp)) c then
            some ⟨.Initial,.Initial,0,rest.length+1⟩
          else some ⟨.Initial,.Final,0,rest.length+2⟩
        else none := by
      simp only [segOf,roles]
    rw [described]
    simp only [long,↓reduceIte,equivalent_correct,alloc.vec.Vec.index_slice_index,first,bind_ok]
    by_cases sup : Equivalent h ch.sup c
    · simp only [sup,decide_true,↓reduceIte]
      by_cases ea : Equivalent h a c
      · simp only [ea,decide_true,↓reduceIte]
        by_cases short : rest = []
        · subst short
          have two : (alloc.vec.Vec.len ch.roles) = 2#usize := by
            apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len_val,roles]
          have second : ch.roles.index_usize 1#usize = .ok b := by
            simp [alloc.vec.Vec.index_usize,roles]
          rw [two] at lessRun
          simp only [two,↓reduceIte,second,bind_ok,equivalent_correct]
          by_cases eb : Equivalent h b c
          · exact ⟨none,by simp [eb],by simp [eb]⟩
          · refine ⟨some ⟨.Final,.Final,1#usize,less⟩,by simp [eb,lessRun],?_⟩
            simp [eb,toSeg,lessIs]
        · have notTwo : ¬ (alloc.vec.Vec.len ch.roles) = 2#usize := by
            intro same
            have := congrArg UScalar.val same
            simp [alloc.vec.Vec.len_val,roles] at this
            exact short this
          refine ⟨some ⟨.Final,.Final,1#usize,less⟩,by simp [notTwo,lessRun],?_⟩
          simp [short,toSeg,lessIs]
      · simp only [ea,decide_false,Bool.false_eq_true,↓reduceIte,lessRun,bind_ok]
        have last : ch.roles.index_usize less = .ok ((b :: rest).getLast (by simp)) := by
          have get : ch.roles.val[less.val]? = some ((b :: rest).getLast (by simp)) := by
            rw [roles,lessIs,List.getLast_eq_getElem]; simp
          simp [alloc.vec.Vec.index_usize,get]
        simp only [last,bind_ok,equivalent_correct]
        by_cases el : Equivalent h ((b :: rest).getLast (by simp)) c
        · refine ⟨some ⟨.Initial,.Initial,0#usize,less⟩,by simp [el],?_⟩
          simp [el,toSeg,lessIs]
        · refine ⟨some ⟨.Initial,.Final,0#usize,alloc.vec.Vec.len ch.roles⟩,by simp [el],?_⟩
          simp [el,toSeg,alloc.vec.Vec.len_val,roles]
    · exact ⟨none,by simp [sup],by simp [sup]⟩


/-- The bounds of a segment: its roles lie inside the chain. -/
theorem segment_fits {h : hierarchy.RoleHierarchy} {ch : role_chains.Chain} {c : ObjectPropertyExpression}
    {s : role_chains.Segment} (found : segOf h ch c = some (toSeg s)) :
    s.offset.val + s.length.val ≤ ch.roles.val.length ∧ 1 ≤ s.length.val := by
  obtain ⟨_,_,positive,shape⟩ := segOf_shape found
  simp only [toSeg] at positive shape
  refine ⟨?_,positive⟩
  rcases shape with ⟨_,_,_,length,_⟩ | ⟨_,_,_,length,_⟩ | ⟨_,_,_,length⟩ <;> omega

/-- The actual transition of a segment after `j` of its roles. -/
theorem step_correct (ch : role_chains.Chain) (k : Usize) (s : role_chains.Segment) (j : Usize)
    (fits : s.offset.val + s.length.val ≤ ch.roles.val.length) (lt : j.val < s.length.val) :
    ∃ (l : ObjectPropertyExpression) (j' : Usize), ch.roles.val[s.offset.val + j.val]? = some l ∧
      j'.val = j.val + 1 ∧ role_chains.step ch k s j = .ok ⟨.Role l,after (toSeg s) k j'⟩ := by
  have small : ch.roles.val.length ≤ Usize.max := ch.roles.property
  obtain ⟨i,iRun,iVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := s.offset) (y := j) (by scalar_tac))
  obtain ⟨j',jRun,jVal⟩ := WP.spec_imp_exists (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
  have iIs : i.val = s.offset.val + j.val := by simpa using iVal
  have jIs : j'.val = j.val + 1 := by simpa using jVal
  have within : i.val < ch.roles.val.length := by omega
  refine ⟨ch.roles.val[i.val],j',by rw [← iIs]; exact List.getElem?_eq_getElem within,jIs,?_⟩
  rw [role_chains.step]
  have lookup : ch.roles.index_usize i = .ok ch.roles.val[i.val] := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem within]
  simp only [iRun,bind_ok,alloc.vec.Vec.len_val,UScalar.lt_equiv,within,↓reduceIte,
    alloc.vec.Vec.index_slice_index,lookup,copy_role_identity,jRun]
  unfold after toSeg
  by_cases last : j'.val = s.length.val
  · have same : j' = s.length := UScalar.eq_of_val_eq last
    simp [same,copy_state_identity]
  · have differ : ¬ j' = s.length := fun same => last (by rw [same])
    simp [differ,last]

private theorem transitive_from_correct (h : hierarchy.RoleHierarchy) (c : ObjectPropertyExpression)
    (index : Usize) :
    role_chains.transitive_from h c index =
      .ok (decide (∃ t ∈ h.transitive.val.drop index.val, Equivalent h t c)) := by
  rw [role_chains.transitive_from]
  by_cases more : index.val < h.transitive.val.length
  · have lookup : h.transitive.index_usize index = .ok h.transitive.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : h.transitive.val.drop index.val =
        h.transitive.val[index.val] :: h.transitive.val.drop (index.val+1) := List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := transitive_from_correct h c index'
    rw [nextIndex] at rest
    rw [split]
    by_cases here : Equivalent h h.transitive.val[index.val] c
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,equivalent_correct,here,decide_true]
      have yes : ∃ t ∈ h.transitive.val[index.val] :: h.transitive.val.drop (index.val+1), Equivalent h t c :=
        ⟨_,List.mem_cons_self,here⟩
      simp only [yes,decide_true]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,equivalent_correct,here,decide_false,Bool.false_eq_true,advance,rest]
      have iff : (∃ t ∈ h.transitive.val[index.val] :: h.transitive.val.drop (index.val+1), Equivalent h t c) ↔
          (∃ t ∈ h.transitive.val.drop (index.val+1), Equivalent h t c) := by
        constructor
        · rintro ⟨t,mem,e⟩
          rcases List.mem_cons.mp mem with same | later
          · rw [same] at e; exact absurd e here
          · exact ⟨t,later,e⟩
        · rintro ⟨t,mem,e⟩
          exact ⟨t,List.mem_cons_of_mem _ mem,e⟩
      simp only [iff]
  · have empty : h.transitive.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by h.transitive.val.length - index.val
decreasing_by omega

private theorem sub_transitions_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (c : ObjectPropertyExpression) (index : Usize) (out : alloc.vec.Vec role_chains.Transition) :
    ∃ o, role_chains.sub_transitions h chs c index out = .ok o ∧ ∀ out', o = some out' →
      ∀ t, t ∈ out'.val ↔ t ∈ out.val ∨ ∃ s, (s,c) ∈ (h.inclusions.val.drop index.val).map (fun i => (i.sub,i.sup)) ∧
        Complex h chs.val s ∧ ¬ Below h c s ∧ t = ⟨.Role s,.Final⟩ := by
  rw [role_chains.sub_transitions]
  by_cases more : index.val < h.inclusions.val.length
  · have lookup : h.inclusions.index_usize index = .ok h.inclusions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : h.inclusions.val.drop index.val =
        h.inclusions.val[index.val] :: h.inclusions.val.drop (index.val+1) := List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
      lookup,bind_ok,same_role_correct,complex_correct,below_correct,advance]
    set i := h.inclusions.val[index.val] with iIs
    -- What the rest adds, and the list with this inclusion first.
    have tail : ∀ t : role_chains.Transition, (∃ s, (s,c) ∈ (h.inclusions.val.drop index.val).map (fun i => (i.sub,i.sup)) ∧
        Complex h chs.val s ∧ ¬ Below h c s ∧ t = ⟨.Role s,.Final⟩) ↔
        ((i.sup = c ∧ Complex h chs.val i.sub ∧ ¬ Below h c i.sub ∧ t = ⟨.Role i.sub,.Final⟩) ∨
          ∃ s, (s,c) ∈ (h.inclusions.val.drop index'.val).map (fun i => (i.sub,i.sup)) ∧
            Complex h chs.val s ∧ ¬ Below h c s ∧ t = ⟨.Role s,.Final⟩) := by
      intro t
      rw [split,nextIndex,List.map_cons]
      constructor
      · rintro ⟨s,mem,complex,above,same⟩
        rcases List.mem_cons.mp mem with pair | later
        · simp only [Prod.mk.injEq] at pair
          obtain ⟨rfl,sup⟩ := pair
          exact .inl ⟨sup.symm,complex,above,same⟩
        · exact .inr ⟨s,later,complex,above,same⟩
      · rintro (⟨sup,complex,above,same⟩ | ⟨s,later,complex,above,same⟩)
        · exact ⟨i.sub,List.mem_cons.mpr (.inl (by rw [sup])),complex,above,same⟩
        · exact ⟨s,List.mem_cons_of_mem _ later,complex,above,same⟩
    by_cases sup : i.sup = c
    · by_cases complex : Complex h chs.val i.sub
      · by_cases above : Below h c i.sub
        · obtain ⟨o,run,spec⟩ := sub_transitions_correct h chs c index' out
          refine ⟨o,?_,?_⟩
          · simp only [sup,complex,above,decide_true,↓reduceIte,run]
          · intro out' same t
            rw [spec out' same t,tail t]
            simp [above]
        · by_cases room : out.val.length < Usize.max
          · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.push_spec out (⟨.Role i.sub,.Final⟩ : role_chains.Transition) room)
            obtain ⟨o,run,spec⟩ := sub_transitions_correct h chs c index' pushed
            refine ⟨o,?_,?_⟩
            · simp only [sup,complex,above,decide_true,decide_false,Bool.false_eq_true,↓reduceIte,
                alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,
                copy_role_identity,bind_ok,push,run]
            · intro out' same t
              rw [spec out' same t,contents,tail t,List.mem_append,List.mem_singleton]
              constructor
              · rintro ((old | new) | later)
                · exact .inl old
                · exact .inr (.inl ⟨sup,complex,above,new⟩)
                · exact .inr (.inr later)
              · rintro (old | (⟨_,_,_,new⟩ | later))
                · exact .inl (.inl old)
                · exact .inl (.inr new)
                · exact .inr later
          · refine ⟨none,?_,by simp⟩
            simp only [sup,complex,above,decide_true,decide_false,Bool.false_eq_true,↓reduceIte,
              alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room]
      · obtain ⟨o,run,spec⟩ := sub_transitions_correct h chs c index' out
        refine ⟨o,?_,?_⟩
        · simp only [sup,complex,decide_true,decide_false,Bool.false_eq_true,↓reduceIte,run]
        · intro out' same t
          rw [spec out' same t,tail t]
          simp [complex]
    · obtain ⟨o,run,spec⟩ := sub_transitions_correct h chs c index' out
      refine ⟨o,?_,?_⟩
      · simp only [sup,decide_false,Bool.false_eq_true,↓reduceIte,run]
      · intro out' same t
        rw [spec out' same t,tail t]
        simp [sup]
  · have empty : h.inclusions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same t
    simp only [Option.some.injEq] at same
    subst same
    simp [empty]
termination_by h.inclusions.val.length - index.val
decreasing_by all_goals omega


/-- A segment's chain is no twin. -/
theorem segOf_not_twin {h : hierarchy.RoleHierarchy} {ch : role_chains.Chain} {c : ObjectPropertyExpression}
    {g : Seg} (found : segOf h ch c = some g) : ¬ Twin h ch c := by
  rintro ⟨a,b,roles,sup,first,second⟩
  unfold segOf at found
  simp only [roles,sup,first,second,↓reduceIte,and_self] at found
  simp at found

/-- The transitions of an automaton, by kind. -/
theorem trans_iff {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} {c : ObjectPropertyExpression}
    {q : role_chains.State} {l : role_chains.Label} {q' : role_chains.State} :
    Trans h chs c q l q' ↔
      (q = .Initial ∧ l = .Direct ∧ q' = .Final) ∨
      (q = .Initial ∧ q' = .Final ∧ ∃ s, (s,c) ∈ inclusionList h ∧ Complex h chs s ∧ ¬ Below h c s ∧ l = .Role s) ∨
      (q = .Final ∧ l = .Empty ∧ q' = .Initial ∧
        ((∃ t ∈ transitives h, Equivalent h t c) ∨ ∃ (k : Nat) (ch : role_chains.Chain), chs[k]? = some ch ∧ Twin h ch c)) ∨
      (∃ (k j j' : Usize) (ch : role_chains.Chain) (g : Seg) (r : ObjectPropertyExpression),
        chs[k.val]? = some ch ∧ segOf h ch c = some g ∧ j.val < g.length ∧ j'.val = j.val + 1 ∧
        ch.roles.val[g.offset + j.val]? = some r ∧ q = before g k j ∧ l = .Role r ∧ q' = after g k j') := by
  constructor
  · intro trans
    cases trans with
    | direct => exact .inl ⟨rfl,rfl,rfl⟩
    | sub listed complex above => exact .inr (.inl ⟨rfl,rfl,_,listed,complex,above,rfl⟩)
    | loop transitive => exact .inr (.inr (.inl ⟨rfl,rfl,rfl,.inl transitive⟩))
    | twin get twin => exact .inr (.inr (.inl ⟨rfl,rfl,rfl,.inr ⟨_,_,get,twin⟩⟩))
    | segment get found lt next role => exact .inr (.inr (.inr ⟨_,_,_,_,_,_,get,found,lt,next,role,rfl,rfl,rfl⟩))
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,s,listed,complex,above,rfl⟩ | ⟨rfl,rfl,rfl,transitive | ⟨k,ch,get,twin⟩⟩ |
      ⟨k,j,j',ch,g,r,get,found,lt,next,role,rfl,rfl,rfl⟩)
    · exact .direct
    · exact .sub listed complex above
    · exact .loop transitive
    · exact .twin get twin
    · exact .segment get found lt next role

/-- What the chain at `k` adds to the transitions from `q`. -/
def Adds (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) (c : ObjectPropertyExpression)
    (q : role_chains.State) (k : Usize) (t : role_chains.Transition) : Prop :=
  ∃ ch, chs[k.val]? = some ch ∧
    ((Twin h ch c ∧ q = .Final ∧ t = ⟨.Empty,.Initial⟩) ∨
      (∃ (g : Seg) (r : ObjectPropertyExpression) (j' : Usize), segOf h ch c = some g ∧ g.start = q ∧
        j'.val = 1 ∧ ch.roles.val[g.offset]? = some r ∧ t = ⟨.Role r,after g k j'⟩))

private theorem chain_transitions_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (c : ObjectPropertyExpression) (q : role_chains.State) (index : Usize) (out : alloc.vec.Vec role_chains.Transition) :
    ∃ o, role_chains.chain_transitions h chs c q index out = .ok o ∧ ∀ out', o = some out' →
      ∀ t, t ∈ out'.val ↔ t ∈ out.val ∨ ∃ k : Usize, index.val ≤ k.val ∧ Adds h chs.val c q k t := by
  rw [role_chains.chain_transitions.eq_def]
  by_cases more : index.val < chs.val.length
  · have lookup : chs.index_usize index = .ok chs.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    set ch := chs.val[index.val] with chIs
    have get : chs.val[index.val]? = some ch := List.getElem?_eq_getElem more
    have split : ∀ t, (∃ k : Usize, index.val ≤ k.val ∧ Adds h chs.val c q k t) ↔
        Adds h chs.val c q index t ∨ ∃ k : Usize, index'.val ≤ k.val ∧ Adds h chs.val c q k t := by
      intro t
      constructor
      · rintro ⟨k,le,adds⟩
        by_cases same : k.val = index.val
        · have : k = index := UScalar.eq_of_val_eq same
          subst this
          exact .inl adds
        · exact .inr ⟨k,by omega,adds⟩
      · rintro (adds | ⟨k,le,adds⟩)
        · exact ⟨index,le_refl _,adds⟩
        · exact ⟨k,by omega,adds⟩
    have here : ∀ t, Adds h chs.val c q index t ↔
        ((Twin h ch c ∧ q = .Final ∧ t = ⟨.Empty,.Initial⟩) ∨
          (∃ (g : Seg) (r : ObjectPropertyExpression) (j' : Usize), segOf h ch c = some g ∧ g.start = q ∧
            j'.val = 1 ∧ ch.roles.val[g.offset]? = some r ∧ t = ⟨.Role r,after g index j'⟩)) := by
      intro t
      simp only [Adds,get,Option.some.injEq,exists_eq_left']
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
      lookup,bind_ok,twin_correct]
    -- Continue with the rest of the chains from `next`.
    have continue_ : ∀ (next : alloc.vec.Vec role_chains.Transition),
        (∀ t, t ∈ next.val ↔ t ∈ out.val ∨ Adds h chs.val c q index t) →
        ∃ o, role_chains.chain_transitions h chs c q index' next = .ok o ∧ ∀ out', o = some out' →
          ∀ t, t ∈ out'.val ↔ t ∈ out.val ∨ ∃ k : Usize, index.val ≤ k.val ∧ Adds h chs.val c q k t := by
      intro next contents
      obtain ⟨o,run,spec⟩ := chain_transitions_correct h chs c q index' next
      refine ⟨o,run,?_⟩
      intro out' same t
      rw [spec out' same t,contents t,split t]
      tauto
    by_cases twin : Twin h ch c
    · simp only [twin,decide_true,↓reduceIte]
      cases q with
      | Final =>
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec out (⟨.Empty,.Initial⟩ : role_chains.Transition) room)
          obtain ⟨o,run,spec⟩ := continue_ pushed (by
            intro t
            rw [contents,List.mem_append,List.mem_singleton,here t]
            constructor
            · rintro (old | new)
              · exact .inl old
              · exact .inr (.inl ⟨twin,rfl,new⟩)
            · rintro (old | ⟨_,_,new⟩ | ⟨g,_,_,found,_⟩)
              · exact .inl old
              · exact .inr new
              · exact absurd twin (segOf_not_twin found))
          refine ⟨o,?_,spec⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,↓reduceIte,
            push,bind_ok,advance,run]
        · refine ⟨none,?_,by simp⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,↓reduceIte]
      | Initial =>
        obtain ⟨o,run,spec⟩ := continue_ out (by
          intro t; rw [here t]
          constructor
          · intro member; exact .inl member
          · rintro (member | ⟨_,bad,_⟩ | ⟨g,_,_,found,_⟩)
            · exact member
            · cases bad
            · exact absurd twin (segOf_not_twin found))
        exact ⟨o,by simp only [advance,bind_ok,run],spec⟩
      | Inside a b =>
        obtain ⟨o,run,spec⟩ := continue_ out (by
          intro t; rw [here t]
          constructor
          · intro member; exact .inl member
          · rintro (member | ⟨_,bad,_⟩ | ⟨g,_,_,found,_⟩)
            · exact member
            · cases bad
            · exact absurd twin (segOf_not_twin found))
        exact ⟨o,by simp only [advance,bind_ok,run],spec⟩
    · simp only [twin,decide_false,Bool.false_eq_true,↓reduceIte]
      obtain ⟨o0,segRun,segMap⟩ := segment_correct h ch c
      simp only [segRun,bind_ok]
      cases o0 with
      | none =>
        obtain ⟨o,run,spec⟩ := continue_ out (by
          intro t; rw [here t]
          constructor
          · intro member; exact .inl member
          · rintro (member | ⟨bad,_⟩ | ⟨g,_,_,found,_⟩)
            · exact member
            · exact absurd bad twin
            · simp only [Option.map_none] at segMap; rw [← segMap] at found; cases found)
        exact ⟨o,by simp only [advance,bind_ok,run],spec⟩
      | some seg =>
        simp only [Option.map_some] at segMap
        have found := segMap.symm
        obtain ⟨fits,positive⟩ := segment_fits found
        simp only [same_state_correct]
        by_cases starts : seg.start = q
        · obtain ⟨r,j',role,j'Val,stepRun⟩ := step_correct ch index seg 0#usize fits (by simp; omega)
          by_cases room : out.val.length < Usize.max
          · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.push_spec out (⟨.Role r,after (toSeg seg) index j'⟩ : role_chains.Transition) room)
            obtain ⟨o,run,spec⟩ := continue_ pushed (by
              intro t
              rw [contents,List.mem_append,List.mem_singleton,here t]
              constructor
              · rintro (old | new)
                · exact .inl old
                · exact .inr (.inr ⟨toSeg seg,r,j',found,starts,by simpa using j'Val,by simpa [toSeg] using role,new⟩)
              · rintro (old | ⟨bad,_⟩ | ⟨g,r',j'',found',start',j''Val,role',new⟩)
                · exact .inl old
                · exact absurd bad twin
                · rw [found] at found'
                  simp only [Option.some.injEq] at found'
                  subst found'
                  have sameJ : j'' = j' := UScalar.eq_of_val_eq (by simp at j'Val; omega)
                  subst sameJ
                  have sameR : r' = r := by
                    simp only [toSeg] at role'
                    simp at role
                    rw [role] at role'
                    exact (Option.some.inj role').symm
                  subst sameR
                  exact .inr new)
            refine ⟨o,?_,spec⟩
            simp only [starts,decide_true,↓reduceIte,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,
              alloc.vec.Vec.length,room,stepRun,bind_ok,push,advance,run]
          · refine ⟨none,?_,by simp⟩
            simp only [starts,decide_true,bind_ok,↓reduceIte,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,
              alloc.vec.Vec.length,room]
        · obtain ⟨o,run,spec⟩ := continue_ out (by
            intro t; rw [here t]
            constructor
            · intro member; exact .inl member
            · rintro (member | ⟨bad,_⟩ | ⟨g,_,_,found',start',_⟩)
              · exact member
              · exact absurd bad twin
              · rw [found] at found'
                simp only [Option.some.injEq] at found'
                subst found'
                exact absurd start' starts)
          refine ⟨o,?_,spec⟩
          simp only [starts,decide_false,Bool.false_eq_true,↓reduceIte,advance,bind_ok,run]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same t
    simp only [Option.some.injEq] at same
    subst same
    constructor
    · intro member; exact .inl member
    · rintro (member | ⟨k,le,ch,get,_⟩)
      · exact member
      · have := (List.getElem?_eq_some_iff.mp get).1
        omega
termination_by chs.val.length - index.val
decreasing_by all_goals omega


/-- A segment starts at the initial or the final state. -/
theorem segOf_start {h : hierarchy.RoleHierarchy} {ch : role_chains.Chain} {c : ObjectPropertyExpression}
    {g : Seg} (found : segOf h ch c = some g) : g.start = .Initial ∨ g.start = .Final := by
  obtain ⟨_,_,_,shape⟩ := segOf_shape found
  rcases shape with ⟨start,_⟩ | ⟨start,_⟩ | ⟨start,_⟩
  · exact .inr start
  · exact .inl start
  · exact .inl start

/-- Only the first role of a segment leaves from the initial or final state. -/
theorem before_outer {g : Seg} {k j : Usize} {st : role_chains.State}
    (outer : st = .Initial ∨ st = .Final) (same : st = before g k j) : j.val = 0 ∧ g.start = st := by
  unfold before at same
  by_cases zero : j.val = 0
  · simp only [zero,↓reduceIte] at same
    exact ⟨zero,same.symm⟩
  · simp only [zero,↓reduceIte] at same
    rcases outer with rfl | rfl <;> cases same

/-- The transitions from the initial or final state that the chains add. -/
private theorem adds_outer (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (c : ObjectPropertyExpression) (st : role_chains.State) (outer : st = .Initial ∨ st = .Final)
    (t : role_chains.Transition) :
    (∃ k : Usize, (0#usize).val ≤ k.val ∧ Adds h chs.val c st k t) ↔
      ((st = .Final ∧ t = ⟨.Empty,.Initial⟩ ∧ ∃ (k : Nat) (ch : role_chains.Chain), chs.val[k]? = some ch ∧ Twin h ch c) ∨
        ∃ (k j j' : Usize) (ch : role_chains.Chain) (g : Seg) (r : ObjectPropertyExpression),
          chs.val[k.val]? = some ch ∧ segOf h ch c = some g ∧ j.val < g.length ∧ j'.val = j.val + 1 ∧
          ch.roles.val[g.offset + j.val]? = some r ∧ st = before g k j ∧ t.label = .Role r ∧ t.target = after g k j') := by
  have small : chs.val.length ≤ Usize.max := chs.property
  constructor
  · rintro ⟨k,_,ch,get,⟨twin,final,same⟩ | ⟨g,r,j',found,start,j'Val,role,same⟩⟩
    · exact .inl ⟨final,same,k.val,ch,get,twin⟩
    · refine .inr ⟨k,0#usize,j',ch,g,r,get,found,?_,by simpa using j'Val,by simpa using role,?_,by rw [same],
        by rw [same]⟩
      · obtain ⟨_,_,positive,_⟩ := segOf_shape found
        simp; omega
      · unfold before; simp [start]
  · rintro (⟨final,same,k,ch,get,twin⟩ | ⟨k,j,j',ch,g,r,get,found,lt,next,role,start,label,target⟩)
    · have bound : k < chs.val.length := (List.getElem?_eq_some_iff.mp get).1
      obtain ⟨u,uVal⟩ := usize_of (n := k) (by omega)
      exact ⟨u,by simp,ch,by rw [uVal]; exact get,.inl ⟨twin,final,same⟩⟩
    · obtain ⟨zero,starts⟩ := before_outer outer start
      refine ⟨k,by simp,ch,get,.inr ⟨g,r,j',found,starts,by omega,by rw [zero] at role; simpa using role,?_⟩⟩
      cases t
      simp only at label target
      rw [label,target]

theorem new_val (T : Type) : (alloc.vec.Vec.new T).val = [] := rfl
theorem zero_val : (0#usize).val = 0 := by simp

/-- The actual transitions of a state are exactly those of `Trans`. -/
theorem transitions_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (c : ObjectPropertyExpression) (q : role_chains.State) :
    ∃ o, role_chains.transitions h chs c q = .ok o ∧ ∀ ts, o = some ts →
      ∀ t : role_chains.Transition, t ∈ ts.val ↔ Trans h chs.val c q t.label t.target := by
  have room : (alloc.vec.Vec.new role_chains.Transition).val.length < Usize.max := by
    rw [new_val]; simp only [List.length_nil]; scalar_tac
  cases q with
  | Initial =>
    obtain ⟨first,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new role_chains.Transition) (⟨.Direct,.Final⟩ : role_chains.Transition)
        room)
    rw [new_val,List.nil_append] at contents
    obtain ⟨o1,run1,spec1⟩ := sub_transitions_correct h chs c 0#usize first
    rw [role_chains.transitions]
    simp only [push,bind_ok,run1]
    cases o1 with
    | none => exact ⟨none,rfl,by simp⟩
    | some out1 =>
      obtain ⟨o2,run2,spec2⟩ := chain_transitions_correct h chs c .Initial 0#usize out1
      refine ⟨o2,by simp only [run2],?_⟩
      intro ts same t
      rw [spec2 ts same t,spec1 out1 rfl t,contents,adds_outer h chs c .Initial (.inl rfl) t,trans_iff]
      simp only [List.mem_singleton,zero_val,List.drop_zero]
      rw [show (h.inclusions.val.map (fun i => (i.sub,i.sup))) = inclusionList h from rfl]
      obtain ⟨l,q'⟩ := t
      simp only [role_chains.Transition.mk.injEq,reduceCtorEq,false_and,false_or,true_and]
      constructor
      · rintro ((direct | ⟨s,listed,complex,above,label,target⟩) | segment)
        · exact .inl direct
        · exact .inr (.inl ⟨target,s,listed,complex,above,label⟩)
        · exact .inr (.inr segment)
      · rintro (direct | ⟨target,s,listed,complex,above,label⟩ | segment)
        · exact .inl (.inl direct)
        · exact .inl (.inr ⟨s,listed,complex,above,label,target⟩)
        · exact .inr segment
  | Final =>
    obtain ⟨first,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new role_chains.Transition) (⟨.Empty,.Initial⟩ : role_chains.Transition)
        room)
    rw [new_val,List.nil_append] at contents
    rw [role_chains.transitions,transitive_from_correct]
    simp only [bind_ok,zero_val,List.drop_zero]
    by_cases transitive : ∃ t ∈ h.transitive.val, Equivalent h t c
    · simp only [transitive,decide_true,↓reduceIte,push,bind_ok]
      obtain ⟨o2,run2,spec2⟩ := chain_transitions_correct h chs c .Final 0#usize first
      refine ⟨o2,run2,?_⟩
      intro ts same t
      rw [spec2 ts same t,contents,adds_outer h chs c .Final (.inr rfl) t,trans_iff]
      simp only [List.mem_singleton]
      obtain ⟨l,q'⟩ := t
      simp only [role_chains.Transition.mk.injEq,reduceCtorEq,false_and,false_or,true_and]
      constructor
      · rintro (⟨label,target⟩ | ⟨⟨label,target⟩,twin⟩ | segment)
        · exact .inl ⟨label,target,.inl transitive⟩
        · exact .inl ⟨label,target,.inr twin⟩
        · exact .inr segment
      · rintro (⟨label,target,_⟩ | segment)
        · exact .inl ⟨label,target⟩
        · exact .inr (.inr segment)
    · simp only [transitive,decide_false,Bool.false_eq_true,↓reduceIte]
      obtain ⟨o2,run2,spec2⟩ := chain_transitions_correct h chs c .Final 0#usize (alloc.vec.Vec.new _)
      refine ⟨o2,by simp only [bind_ok,run2],?_⟩
      intro ts same t
      rw [spec2 ts same t,adds_outer h chs c .Final (.inr rfl) t,trans_iff,new_val]
      simp only [List.not_mem_nil,false_or]
      obtain ⟨l,q'⟩ := t
      simp only [role_chains.Transition.mk.injEq,reduceCtorEq,false_and,false_or,true_and]
      constructor
      · rintro (⟨⟨label,target⟩,twin⟩ | segment)
        · exact .inl ⟨label,target,.inr twin⟩
        · exact .inr segment
      · rintro (⟨label,target,transitive' | twin⟩ | segment)
        · exact absurd transitive' transitive
        · exact .inl ⟨⟨label,target⟩,twin⟩
        · exact .inr segment
  | Inside k j =>
    rw [role_chains.transitions]
    -- No transition of another kind leaves a state inside a segment.
    have inside : ∀ (l : role_chains.Label) (q' : role_chains.State), Trans h chs.val c (.Inside k j) l q' ↔
        ∃ (j' : Usize) (ch : role_chains.Chain) (g : Seg) (r : ObjectPropertyExpression),
          chs.val[k.val]? = some ch ∧ segOf h ch c = some g ∧ 0 < j.val ∧ j.val < g.length ∧
          j'.val = j.val + 1 ∧ ch.roles.val[g.offset + j.val]? = some r ∧ l = .Role r ∧ q' = after g k j' := by
      intro l q'
      rw [trans_iff]
      simp only [reduceCtorEq,false_and,false_or]
      constructor
      · rintro ⟨k',j0,j',ch,g,r,get,found,lt,next,role,start,label,target⟩
        unfold before at start
        by_cases zero : j0.val = 0
        · simp only [zero,↓reduceIte] at start
          rcases segOf_start found with first | first <;> rw [first] at start <;> cases start
        · simp only [zero,↓reduceIte,role_chains.State.Inside.injEq] at start
          obtain ⟨rfl,rfl⟩ := start
          exact ⟨j',ch,g,r,get,found,by omega,lt,next,role,label,target⟩
      · rintro ⟨j',ch,g,r,get,found,positive,lt,next,role,label,target⟩
        refine ⟨k,j,j',ch,g,r,get,found,lt,next,role,?_,label,target⟩
        unfold before; simp [show j.val ≠ 0 by omega]
    have none_ : ∀ (ts : alloc.vec.Vec role_chains.Transition), ts.val = [] →
        (∀ (j' : Usize) (ch : role_chains.Chain) (g : Seg), chs.val[k.val]? = some ch → segOf h ch c = some g →
          0 < j.val → ¬ j.val < g.length) →
        ∀ t : role_chains.Transition, t ∈ ts.val ↔ Trans h chs.val c (.Inside k j) t.label t.target := by
      intro ts empty never t
      rw [inside,empty]
      simp only [List.not_mem_nil,false_iff,not_exists,not_and]
      intro j' ch g r get found positive lt
      exact absurd lt (never j' ch g get found positive)
    by_cases more : k.val < chs.val.length
    · have lookup : chs.index_usize k = .ok chs.val[k.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      have get : chs.val[k.val]? = some chs.val[k.val] := List.getElem?_eq_getElem more
      obtain ⟨o0,segRun,segMap⟩ := segment_correct h chs.val[k.val] c
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,segRun]
      cases o0 with
      | none =>
        refine ⟨_,rfl,?_⟩
        intro ts same
        simp only [Option.some.injEq] at same
        subst same
        refine none_ _ (new_val _) ?_
        intro j' ch g get' found
        rw [get] at get'
        simp only [Option.some.injEq] at get'
        subst get'
        simp only [Option.map_none] at segMap
        rw [← segMap] at found
        cases found
      | some seg =>
        simp only [Option.map_some] at segMap
        have found := segMap.symm
        obtain ⟨fits,_⟩ := segment_fits found
        have same_seg : ∀ (ch : role_chains.Chain) (g : Seg), chs.val[k.val]? = some ch → segOf h ch c = some g →
            ch = chs.val[k.val] ∧ g = toSeg seg := by
          intro ch g get' found'
          rw [get] at get'
          simp only [Option.some.injEq] at get'
          subst get'
          rw [found] at found'
          simp only [Option.some.injEq] at found'
          exact ⟨rfl,found'.symm⟩
        by_cases positive : 0 < j.val
        · by_cases lt : j.val < seg.length.val
          · obtain ⟨r,j',role,j'Val,stepRun⟩ := step_correct chs.val[k.val] k seg j fits lt
            obtain ⟨single,push,contents⟩ := WP.spec_imp_exists
              (alloc.vec.Vec.push_spec (alloc.vec.Vec.new role_chains.Transition)
                (⟨.Role r,after (toSeg seg) k j'⟩ : role_chains.Transition) room)
            rw [new_val,List.nil_append] at contents
            refine ⟨some single,?_,?_⟩
            · simp only [zero_val,positive,lt,↓reduceIte,stepRun,bind_ok,push]
            · intro ts same t
              simp only [Option.some.injEq] at same
              subst same
              rw [inside,contents,List.mem_singleton]
              constructor
              · intro same
                subst same
                exact ⟨j',_,toSeg seg,r,get,found,positive,lt,j'Val,role,rfl,rfl⟩
              · rintro ⟨j'',ch,g,r',get',found',_,_,j''Val,role',label,target⟩
                obtain ⟨rfl,rfl⟩ := same_seg ch g get' found'
                have sameJ : j'' = j' := UScalar.eq_of_val_eq (by omega)
                subst sameJ
                have sameR : r' = r := by
                  simp only [toSeg] at role'
                  rw [role] at role'
                  exact (Option.some.inj role').symm
                subst sameR
                cases t
                simp only at label target
                rw [label,target]
          · refine ⟨some (alloc.vec.Vec.new _),by simp only [zero_val,positive,lt,↓reduceIte],?_⟩
            intro ts same
            simp only [Option.some.injEq] at same
            subst same
            refine none_ _ (new_val _) ?_
            intro j' ch g get' found' _
            obtain ⟨rfl,rfl⟩ := same_seg ch g get' found'
            exact lt
        · refine ⟨some (alloc.vec.Vec.new _),by simp only [zero_val,positive,↓reduceIte],?_⟩
          intro ts same
          simp only [Option.some.injEq] at same
          subst same
          refine none_ _ (new_val _) ?_
          intro j' ch g _ _ positive'
          exact absurd positive' positive
    · refine ⟨some (alloc.vec.Vec.new _),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
      intro ts same
      simp only [Option.some.injEq] at same
      subst same
      refine none_ _ (new_val _) ?_
      intro j' ch g get'
      have := (List.getElem?_eq_some_iff.mp get').1
      omega


/-! ### The classes of the atoms -/

/-- The byte of a value: its remainder by 256. -/
def octet (v : Nat) : U8 := UScalar.ofNatCore (v % 256) (by
  have : v % 256 < 256 := Nat.mod_lt _ (by decide)
  simpa [UScalarTy.numBits] using this)

theorem octet_val (v : Nat) : (octet v).val = v % 256 := UScalar.ofNatCore_val_eq _

/-- `n` bytes of a value, least significant first. -/
def octets : Nat → Nat → List U8
  | 0, _ => []
  | n+1, v => octet v :: octets n (v / 256)

theorem octets_length : ∀ (n v : Nat), (octets n v).length = n
  | 0, _ => rfl
  | n+1, v => by simp [octets,octets_length n]

/-- Values below `256^n` have distinct bytes. -/
theorem octets_injective : ∀ (n a b : Nat), a < 256^n → b < 256^n → octets n a = octets n b → a = b
  | 0, a, b, ha, hb, _ => by simp at ha hb; omega
  | n+1, a, b, ha, hb, same => by
    simp only [octets,List.cons.injEq] at same
    obtain ⟨first,rest⟩ := same
    have low : a % 256 = b % 256 := by
      have := congrArg UScalar.val first
      rwa [octet_val,octet_val] at this
    have ha' : a / 256 < 256^n := by rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [pow_succ] at ha; exact ha
    have hb' : b / 256 < 256^n := by rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [pow_succ] at hb; exact hb
    have high := octets_injective n (a/256) (b/256) ha' hb' rest
    omega

/-- The spelling of the class of the atom at `k`: a space and the eight bytes
    of `k`. -/
def spellingOf (k : Usize) : alloc.vec.Vec U8 :=
  alloc.vec.Vec.from (32#u8 :: octets 8 k.val) (by simp only [List.length_cons,octets_length]; scalar_tac)

theorem spellingOf_val (k : Usize) : (spellingOf k).val = 32#u8 :: octets 8 k.val := by
  simp [spellingOf]

/-- The class of the atom at `k`. -/
def nameOf (k : Usize) : model.Class := ⟨⟨spellingOf k⟩⟩

theorem nameOf_injective {a b : Usize} (same : nameOf a = nameOf b) : a = b := by
  have spelling : (spellingOf a).val = (spellingOf b).val := by
    simp only [nameOf,model.Class.mk.injEq,model.Iri.mk.injEq] at same
    rw [same]
  simp only [spellingOf_val,List.cons.injEq,true_and] at spelling
  have bound : ∀ x : Usize, x.val < 256^8 := by
    intro x
    have := x.hBounds
    simp only [UScalarTy.numBits] at this
    have platform : System.Platform.numBits ≤ 64 := by
      rcases System.Platform.numBits_eq with h | h <;> omega
    calc x.val < 2 ^ System.Platform.numBits := this
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) platform
      _ = 256^8 := by norm_num
  exact UScalar.eq_of_val_eq (octets_injective 8 _ _ (bound a) (bound b) spelling)

private theorem bytes_correct (value count : Usize) (out : alloc.vec.Vec U8)
    (len : out.val.length = count.val + 1) (le : count.val ≤ 8) :
    ∃ result, role_chains.bytes value count out = .ok result ∧
      result.val = out.val ++ octets (8 - count.val) value.val := by
  rw [role_chains.bytes]
  by_cases more : count.val < 8
  · have more' : count < 8#usize := by simp only [UScalar.lt_equiv]; simpa using more
    have room : out.val.length < Usize.max := by rw [len]; scalar_tac
    obtain ⟨low,lowRun,lowVal⟩ := WP.spec_imp_exists (UScalar.rem_spec value (y := 256#usize) (by simp))
    obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (UScalar.cast .U8 low) room)
    obtain ⟨high,highRun,highVal⟩ := UScalar.div_spec value (y := 256#usize) (by simp)
    obtain ⟨count',countRun,countVal⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := count) (y := 1#usize) (by scalar_tac))
    have countIs : count'.val = count.val + 1 := by simpa using countVal
    obtain ⟨result,run,spec⟩ := bytes_correct high count' pushed
      (by rw [contents,countIs]; simp [len]) (by omega)
    refine ⟨result,?_,?_⟩
    · simp only [more',↓reduceIte,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,
        room,lowRun,bind_ok,lift,push,highRun,countRun,run]
    · rw [spec,contents,countIs,highVal]
      have steps : 8 - count.val = (8 - (count.val + 1)) + 1 := by omega
      rw [steps,octets]
      have same : UScalar.cast .U8 low = octet value.val := by
        apply UScalar.eq_of_val_eq
        rw [UScalar.cast_val_eq,octet_val,lowVal]
        simp [UScalarTy.numBits]
      simp [same]
  · have done : count.val = 8 := by omega
    have more' : ¬ count < 8#usize := by simp only [UScalar.lt_equiv]; simpa using more
    refine ⟨out,by simp only [more',↓reduceIte],?_⟩
    simp [done,octets]
termination_by 8 - count.val
decreasing_by omega

/-- The actual class of an atom is `nameOf`. -/
theorem name_correct (k : Usize) : role_chains.name k = .ok (nameOf k) := by
  obtain ⟨first,push,contents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new U8) 32#u8 (by rw [new_val]; simp only [List.length_nil]; scalar_tac))
  rw [new_val,List.nil_append] at contents
  obtain ⟨result,run,spec⟩ := bytes_correct k 0#usize first (by rw [contents]; simp) (by simp)
  rw [role_chains.name]
  simp only [push,bind_ok,run]
  congr
  apply alloc.vec.Vec.ext
  rw [spec,contents,spellingOf_val]
  simp

/-- The class starts with a space. -/
def Spaced (cl : model.Class) : Prop := cl.iri.spelling.val.head? = some 32#u8

theorem spaced_correct (cl : model.Class) : role_chains.spaced cl = .ok (decide (Spaced cl)) := by
  rw [role_chains.spaced]
  match spelling : cl.iri.spelling.val with
  | [] =>
    have empty : ¬ 0#usize < alloc.vec.Vec.len cl.iri.spelling := by
      simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,spelling]
    simp [empty,Spaced,spelling]
  | b :: rest =>
    have some_ : 0#usize < alloc.vec.Vec.len cl.iri.spelling := by
      simp [UScalar.lt_equiv,alloc.vec.Vec.len_val,spelling]
    have first : cl.iri.spelling.index_usize 0#usize = .ok b := by
      simp [alloc.vec.Vec.index_usize,spelling]
    simp only [some_,↓reduceIte,alloc.vec.Vec.index_slice_index,first,bind_ok,Spaced,spelling,
      List.head?_cons,Option.some.injEq]

theorem nameOf_spaced (k : Usize) : Spaced (nameOf k) := by
  simp [Spaced,nameOf,spellingOf_val]


/-! ### Checks and the table of atoms -/

/-- No class of the concept starts with a space, and its number restrictions,
    self restrictions and their complements are on roles that are not
    complex. -/
def Fits (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) : concepts.Concept → Prop
  | .Top => True
  | .Bottom => True
  | .Atom cl => ¬ Spaced cl
  | .NotAtom cl => ¬ Spaced cl
  | .One _ => True
  | .NotOne _ => True
  | .HasSelf r => ¬ Complex h chs r
  | .NotSelf r => ¬ Complex h chs r
  | .And a b => Fits h chs a ∧ Fits h chs b
  | .Or a b => Fits h chs a ∧ Fits h chs b
  | .Exists _ f => Fits h chs f
  | .Forall _ f => Fits h chs f
  | .AtLeast _ r f => ¬ Complex h chs r ∧ Fits h chs f
  | .AtMost _ r f => ¬ Complex h chs r ∧ Fits h chs f

theorem fits_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain) (D : concepts.Concept) :
    role_chains.fits h chs D = .ok (decide (Fits h chs.val D)) := by
  induction D with
  | Top => rw [role_chains.fits]; simp [Fits]
  | Bottom => rw [role_chains.fits]; simp [Fits]
  | Atom cl => rw [role_chains.fits]; simp [Fits,spaced_correct]
  | NotAtom cl => rw [role_chains.fits]; simp [Fits,spaced_correct]
  | One a => rw [role_chains.fits]; simp [Fits]
  | NotOne a => rw [role_chains.fits]; simp [Fits]
  | HasSelf r => rw [role_chains.fits]; simp [Fits,complex_correct]
  | NotSelf r => rw [role_chains.fits]; simp [Fits,complex_correct]
  | And a b iha ihb =>
    rw [role_chains.fits,iha]
    by_cases fa : Fits h chs.val a
    · simp [fa,ihb,Fits]
    · simp [fa,Fits]
  | Or a b iha ihb =>
    rw [role_chains.fits,iha]
    by_cases fa : Fits h chs.val a
    · simp [fa,ihb,Fits]
    · simp [fa,Fits]
  | Exists r f ih => rw [role_chains.fits,ih]; simp [Fits]
  | Forall r f ih => rw [role_chains.fits,ih]; simp [Fits]
  | AtLeast n r f ih =>
    rw [role_chains.fits,complex_correct]
    by_cases complex : Complex h chs.val r
    · simp [complex,Fits]
    · simp [complex,ih,Fits]
  | AtMost n r f ih =>
    rw [role_chains.fits,complex_correct]
    by_cases complex : Complex h chs.val r
    · simp [complex,Fits]
    · simp [complex,ih,Fits]

private theorem find_from_correct (atoms : alloc.vec.Vec role_chains.Atom) (role : ObjectPropertyExpression)
    (state : role_chains.State) (filler : role_chains.Filler) (index : Usize) :
    ∃ p : Usize, role_chains.find_from atoms role state filler index = .ok p ∧
      (p.val < atoms.val.length → atoms.val[p.val]? = some ⟨role,state,filler⟩) ∧
      (¬ p.val < atoms.val.length → p.val = atoms.val.length ∧
        (⟨role,state,filler⟩ : role_chains.Atom) ∉ atoms.val.drop index.val) := by
  rw [role_chains.find_from]
  by_cases more : index.val < atoms.val.length
  · have lookup : atoms.index_usize index = .ok atoms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : atoms.val.drop index.val = atoms.val[index.val] :: atoms.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨p,run,hit,miss⟩ := find_from_correct atoms role state filler index'
    set a := atoms.val[index.val] with aIs
    by_cases found : a = ⟨role,state,filler⟩
    · refine ⟨index,?_,fun _ => by rw [List.getElem?_eq_getElem more,← aIs,found],fun outside => absurd more outside⟩
      have r : a.role = role := by rw [found]
      have st : a.state = state := by rw [found]
      have fi : a.filler = filler := by rw [found]
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,same_role_correct,same_state_correct,same_filler_correct,r,st,fi,decide_true]
    · refine ⟨p,?_,hit,?_⟩
      · have differ : ¬ (a.role = role ∧ a.state = state ∧ a.filler = filler) := by
          rintro ⟨r,st,fi⟩
          apply found
          rw [← r,← st,← fi]
        by_cases r : a.role = role
        · by_cases st : a.state = state
          · have fi : ¬ a.filler = filler := fun fi => differ ⟨r,st,fi⟩
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,same_role_correct,same_state_correct,same_filler_correct,r,st,fi,decide_true,
              decide_false,Bool.false_eq_true,advance,run]
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,same_role_correct,same_state_correct,r,st,decide_true,decide_false,
              Bool.false_eq_true,advance,run]
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,same_role_correct,r,decide_false,Bool.false_eq_true,advance,run]
      · intro outside
        refine ⟨(miss outside).1,?_⟩
        intro member
        rw [split] at member
        rcases List.mem_cons.mp member with same | later
        · exact found same.symm
        · exact (miss outside).2 (by rw [nextIndex]; exact later)
  · refine ⟨alloc.vec.Vec.len atoms,?_,?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · simp
    · intro _
      refine ⟨by simp,?_⟩
      simp [List.drop_eq_nil_iff.mpr (show atoms.val.length ≤ index.val by omega)]
termination_by atoms.val.length - index.val
decreasing_by omega

/-- The atom with a role, state and filler: an existing one, or one added at
    the end of the table. -/
theorem atom_for_correct (atoms : alloc.vec.Vec role_chains.Atom) (role : ObjectPropertyExpression)
    (state : role_chains.State) (filler : role_chains.Filler) :
    ∃ o, role_chains.atom_for atoms role state filler = .ok o ∧ ∀ atoms' j, o = some (atoms',j) →
      atoms'.val[j.val]? = some ⟨role,state,filler⟩ ∧
      (atoms'.val = atoms.val ∨
        (atoms'.val = atoms.val ++ [⟨role,state,filler⟩] ∧ (⟨role,state,filler⟩ : role_chains.Atom) ∉ atoms.val)) := by
  obtain ⟨p,run,hit,miss⟩ := find_from_correct atoms role state filler 0#usize
  rw [role_chains.atom_for]
  by_cases found : p.val < atoms.val.length
  · refine ⟨some (atoms,p),?_,?_⟩
    · simp [run,alloc.vec.Vec.len_val,UScalar.lt_equiv,found]
    · intro atoms' j same
      simp only [Option.some.injEq,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      exact ⟨hit found,.inl rfl⟩
  · by_cases room : atoms.val.length < Usize.max
    · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec atoms (⟨role,state,filler⟩ : role_chains.Atom) room)
      refine ⟨some (pushed,p),?_,?_⟩
      · simp [run,alloc.vec.Vec.len_val,UScalar.lt_equiv,found,usize_max_val,room,copy_role_identity,
          copy_state_identity,copy_filler_identity,push]
      · intro atoms' j same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        obtain ⟨at_end,outside⟩ := miss found
        simp only [zero_val,List.drop_zero] at outside
        refine ⟨by rw [contents,at_end]; simp,.inr ⟨contents,outside⟩⟩
    · refine ⟨none,?_,by simp⟩
      simp [run,alloc.vec.Vec.len_val,UScalar.lt_equiv,found,usize_max_val,room]


/-- The class occurs in the concept, positively or negated. -/
def Mentions (cl : model.Class) : concepts.Concept → Prop
  | .Atom c => c = cl
  | .NotAtom c => c = cl
  | .And a b => Mentions cl a ∨ Mentions cl b
  | .Or a b => Mentions cl a ∨ Mentions cl b
  | .Exists _ f => Mentions cl f
  | .Forall _ f => Mentions cl f
  | .AtLeast _ _ f => Mentions cl f
  | .AtMost _ _ f => Mentions cl f
  | _ => False

/-- A complement mentions only classes of the concept. -/
theorem negate_mentions (c : concepts.Concept) :
    ∀ n, concepts.negate c = .ok (some n) → ∀ cl, Mentions cl n → Mentions cl c := by
  induction c with
  | Top =>
    intro n run; rw [concepts.negate] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | Bottom =>
    intro n run; rw [concepts.negate] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | Atom k =>
    intro n run; rw [concepts.negate] at run; simp only [Rowl.Nnf.copy_iri_identity,bind_ok] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | NotAtom k =>
    intro n run; rw [concepts.negate] at run; simp only [Rowl.Nnf.copy_iri_identity,bind_ok] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | One a =>
    intro n run; rw [concepts.negate] at run; simp only [Rowl.Concepts.copy_individual_identity,bind_ok] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | NotOne a =>
    intro n run; rw [concepts.negate] at run; simp only [Rowl.Concepts.copy_individual_identity,bind_ok] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | HasSelf r =>
    intro n run; rw [concepts.negate] at run; simp only [copy_role_identity,bind_ok] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | NotSelf r =>
    intro n run; rw [concepts.negate] at run; simp only [copy_role_identity,bind_ok] at run
    have := Option.some.inj (Result.ok_injective run); subst this; simp [Mentions]
  | And a b iha ihb | Or a b iha ihb =>
    intro n run
    obtain ⟨ra,runA,_⟩ := negate_correct.{0,0} a
    obtain ⟨rb,runB,_⟩ := negate_correct.{0,0} b
    rw [concepts.negate,concepts.negate_pair,runA] at run
    cases ra with
    | none => simp at run
    | some a' =>
      rw [runB] at run
      cases rb with
      | none => simp at run
      | some b' =>
        simp only [bind_ok,concepts.join,Bool.false_eq_true,↓reduceIte] at run
        have := Option.some.inj (Result.ok_injective run)
        subst this
        intro cl mentions
        rcases mentions with ma | mb
        · exact .inl (iha a' runA cl ma)
        · exact .inr (ihb b' runB cl mb)
  | Exists r c ih =>
    intro n run
    obtain ⟨rc,runC,_⟩ := negate_correct.{0,0} c
    rw [concepts.negate,runC] at run
    cases rc with
    | none => simp at run
    | some c' =>
      simp only [bind_ok,copy_role_identity] at run
      have := Option.some.inj (Result.ok_injective run)
      subst this
      exact ih c' runC
  | Forall r c ih =>
    intro n run
    obtain ⟨rc,runC,_⟩ := negate_correct.{0,0} c
    rw [concepts.negate,runC] at run
    cases rc with
    | none => simp at run
    | some c' =>
      simp only [bind_ok,copy_role_identity] at run
      have := Option.some.inj (Result.ok_injective run)
      subst this
      exact ih c' runC
  | AtLeast m r c _ =>
    intro n run cl mentions
    rw [concepts.negate] at run
    by_cases zero : m = 0#usize
    · simp only [zero,↓reduceIte] at run
      have := Option.some.inj (Result.ok_injective run)
      subst this
      simp [Mentions] at mentions
    · obtain ⟨less,lessRun,_⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := m) (y := 1#usize) (by
          have : m.val ≠ 0 := fun same => zero (UScalar.eq_of_val_eq (by simpa using same))
          simp; omega))
      simp only [zero,↓reduceIte,lessRun,bind_ok,copy_role_identity,copy_concept_identity] at run
      have := Option.some.inj (Result.ok_injective run)
      subst this
      exact mentions
  | AtMost m r c _ =>
    intro n run cl mentions
    rw [concepts.negate] at run
    by_cases room : m < core.num.Usize.MAX
    · obtain ⟨more,moreRun,_⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := m) (y := 1#usize) (by
          have := room
          simp only [UScalar.lt_equiv,usize_max_val] at this
          simp; omega))
      simp only [room,↓reduceIte,moreRun,bind_ok,copy_role_identity,copy_concept_identity] at run
      have := Option.some.inj (Result.ok_injective run)
      subst this
      exact mentions
    · simp [room] at run

theorem prefix_get {α : Type} {l l' : List α} (p : l <+: l') {n : Nat} {x : α} (h : l[n]? = some x) :
    l'[n]? = some x := by
  obtain ⟨t,rfl⟩ := p
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- The class of an atom before `n`, or a class that starts no space. -/
def Before (n : Nat) (cl : model.Class) : Prop := ¬ Spaced cl ∨ ∃ j : Usize, cl = nameOf j ∧ j.val < n

theorem before_mono {n m : Nat} (le : n ≤ m) {cl : model.Class} (before : Before n cl) : Before m cl := by
  rcases before with plain | ⟨j,same,lt⟩
  · exact .inl plain
  · exact .inr ⟨j,same,by omega⟩

/-- A filler refers to an atom before `n` or to a base whose classes come
    before `n`. -/
def FillerOk (B : List concepts.Concept) (n : Nat) : role_chains.Filler → Prop
  | .Atom j => j.val < n
  | .Base b => ∃ D, B[b.val]? = some D ∧ ∀ cl, Mentions cl D → Before n cl

/-- Distinct atoms whose fillers come before them. -/
def TableOk (T : List role_chains.Atom) (B : List concepts.Concept) : Prop :=
  T.Nodup ∧ ∀ (k : Nat) (a : role_chains.Atom), T[k]? = some a → FillerOk B k a.filler

theorem fillerOk_mono {B B' : List concepts.Concept} (prefix_ : B <+: B') {n m : Nat} (le : n ≤ m)
    {F : role_chains.Filler} (ok : FillerOk B n F) : FillerOk B' m F := by
  cases F with
  | Atom j => exact Nat.lt_of_lt_of_le ok le
  | Base b =>
    obtain ⟨D,at_b,classes⟩ := ok
    exact ⟨D,prefix_get prefix_ at_b,fun cl mentions => before_mono le (classes cl mentions)⟩

theorem tableOk_bases {T : List role_chains.Atom} {B B' : List concepts.Concept} (ok : TableOk T B)
    (prefix_ : B <+: B') : TableOk T B' :=
  ⟨ok.1,fun k a at_k => fillerOk_mono prefix_ (le_refl _) (ok.2 k a at_k)⟩

/-- Adding a new atom whose filler comes before it keeps the table in order. -/
theorem tableOk_push {T : List role_chains.Atom} {B : List concepts.Concept} (ok : TableOk T B)
    {a : role_chains.Atom} (fresh : a ∉ T) (filler : FillerOk B T.length a.filler) : TableOk (T ++ [a]) B := by
  refine ⟨List.nodup_append.mpr ⟨ok.1,List.nodup_singleton a,?_⟩,?_⟩
  · intro x member y same; simp at same; subst same; exact fun eq => fresh (eq ▸ member)
  · intro k b at_k
    by_cases old : k < T.length
    · rw [List.getElem?_append_left old] at at_k
      exact ok.2 k b at_k
    · rw [List.getElem?_append_right (by omega)] at at_k
      have bound := (List.getElem?_eq_some_iff.mp at_k).1
      simp only [List.length_singleton] at bound
      have same : k = T.length := by omega
      subst same
      simp only [Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at at_k
      subst at_k
      exact filler


/-- Adding an atom whose filler comes before the end keeps the table in order. -/
theorem atom_for_ok {atoms : alloc.vec.Vec role_chains.Atom} {B : List concepts.Concept} (ok : TableOk atoms.val B)
    {role : ObjectPropertyExpression} {state : role_chains.State} {filler : role_chains.Filler}
    (fill : FillerOk B atoms.val.length filler) {atoms' : alloc.vec.Vec role_chains.Atom} {j : Usize}
    (run : role_chains.atom_for atoms role state filler = .ok (some (atoms',j))) :
    TableOk atoms'.val B ∧ atoms.val <+: atoms'.val ∧ atoms'.val[j.val]? = some ⟨role,state,filler⟩ := by
  obtain ⟨o,run',spec⟩ := atom_for_correct atoms role state filler
  rw [run] at run'
  obtain ⟨at_j,same | ⟨grown,fresh⟩⟩ := spec atoms' j (Result.ok_injective run').symm
  · rw [same]; exact ⟨ok,List.prefix_refl _,by rw [← same]; exact at_j⟩
  · rw [grown]
    exact ⟨tableOk_push ok fresh fill,List.prefix_append _ _,by rw [← grown]; exact at_j⟩

/-- The atom of the initial state of a role with a new base filler. -/
theorem universal_correct (atoms : alloc.vec.Vec role_chains.Atom) (bases : alloc.vec.Vec concepts.Concept)
    (role : ObjectPropertyExpression) (filler : concepts.Concept) (ok : TableOk atoms.val bases.val)
    (classes : ∀ cl, Mentions cl filler → Before atoms.val.length cl) :
    ∃ o, role_chains.universal atoms bases role filler = .ok o ∧ ∀ atoms' bases' k, o = some (atoms',bases',k) →
      bases'.val = bases.val ++ [filler] ∧ TableOk atoms'.val bases'.val ∧ atoms.val <+: atoms'.val ∧
      ∃ b : Usize, atoms'.val[k.val]? = some ⟨role,.Initial,.Base b⟩ ∧ bases'.val[b.val]? = some filler := by
  rw [role_chains.universal]
  by_cases room : bases.val.length < Usize.max
  · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec bases filler room)
    have ok' : TableOk atoms.val pushed.val := tableOk_bases ok (by rw [contents]; exact List.prefix_append _ _)
    have fill : FillerOk pushed.val atoms.val.length (.Base (alloc.vec.Vec.len bases)) :=
      ⟨filler,by rw [contents]; simp,classes⟩
    obtain ⟨o,run,_⟩ := atom_for_correct atoms role .Initial (.Base (alloc.vec.Vec.len bases))
    cases o with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,↓reduceIte,
        push,bind_ok,run]
    | some pair =>
      obtain ⟨atoms1,k⟩ := pair
      obtain ⟨ok1,grows,at_k⟩ := atom_for_ok ok' fill run
      refine ⟨some (atoms1,pushed,k),?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,↓reduceIte,
          push,bind_ok,run]
        rfl
      · intro atoms' bases' k' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl,rfl⟩ := same
        exact ⟨contents,ok1,grows,_,at_k,by rw [contents]; simp⟩
  · refine ⟨none,?_,by simp⟩
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,↓reduceIte]

/-- `D'` encodes `D` in a positive (`true`) or negative position, with the
    atoms of `T` and the base fillers of `B`. -/
inductive Enc (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) (T : List role_chains.Atom)
    (B : List concepts.Concept) : Bool → concepts.Concept → concepts.Concept → Prop
  | top (p : Bool) : Enc h chs T B p .Top .Top
  | bottom (p : Bool) : Enc h chs T B p .Bottom .Bottom
  | atom (p : Bool) (cl : model.Class) : Enc h chs T B p (.Atom cl) (.Atom cl)
  | notAtom (p : Bool) (cl : model.Class) : Enc h chs T B p (.NotAtom cl) (.NotAtom cl)
  | one (p : Bool) (a : Individual) : Enc h chs T B p (.One a) (.One a)
  | notOne (p : Bool) (a : Individual) : Enc h chs T B p (.NotOne a) (.NotOne a)
  | hasSelf (p : Bool) (r : ObjectPropertyExpression) : Enc h chs T B p (.HasSelf r) (.HasSelf r)
  | notSelf (p : Bool) (r : ObjectPropertyExpression) : Enc h chs T B p (.NotSelf r) (.NotSelf r)
  | and {p : Bool} {a b a' b' : concepts.Concept} : Enc h chs T B p a a' → Enc h chs T B p b b' →
      Enc h chs T B p (.And a b) (.And a' b')
  | or {p : Bool} {a b a' b' : concepts.Concept} : Enc h chs T B p a a' → Enc h chs T B p b b' →
      Enc h chs T B p (.Or a b) (.Or a' b')
  | existsPos {r : ObjectPropertyExpression} {e e' : concepts.Concept} : Enc h chs T B true e e' →
      Enc h chs T B true (.Exists r e) (.Exists r e')
  | existsSimple {r : ObjectPropertyExpression} {e e' : concepts.Concept} : ¬ Complex h chs r →
      Enc h chs T B false e e' → Enc h chs T B false (.Exists r e) (.Exists r e')
  | existsComplex {r : ObjectPropertyExpression} {e e' n : concepts.Concept} {k b : Usize} : Complex h chs r →
      Enc h chs T B false e e' → concepts.negate e' = .ok (some n) → T[k.val]? = some ⟨r,.Initial,.Base b⟩ →
      B[b.val]? = some n → Enc h chs T B false (.Exists r e) (.NotAtom (nameOf k))
  | forallComplex {r : ObjectPropertyExpression} {e e' : concepts.Concept} {k b : Usize} : Complex h chs r →
      Enc h chs T B true e e' → T[k.val]? = some ⟨r,.Initial,.Base b⟩ → B[b.val]? = some e' →
      Enc h chs T B true (.Forall r e) (.Atom (nameOf k))
  | forallSimple {r : ObjectPropertyExpression} {e e' : concepts.Concept} : ¬ Complex h chs r →
      Enc h chs T B true e e' → Enc h chs T B true (.Forall r e) (.Forall r e')
  | forallNeg {r : ObjectPropertyExpression} {e e' : concepts.Concept} : Enc h chs T B false e e' →
      Enc h chs T B false (.Forall r e) (.Forall r e')
  | atLeast {p : Bool} {n : Usize} {r : ObjectPropertyExpression} {e e' : concepts.Concept} :
      Enc h chs T B p e e' → Enc h chs T B p (.AtLeast n r e) (.AtLeast n r e')
  | atMost {p : Bool} {n : Usize} {r : ObjectPropertyExpression} {e e' : concepts.Concept} :
      Enc h chs T B (!p) e e' → Enc h chs T B p (.AtMost n r e) (.AtMost n r e')

theorem enc_mono {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} {T T' : List role_chains.Atom}
    {B B' : List concepts.Concept} (pt : T <+: T') (pb : B <+: B') {p : Bool} {D D' : concepts.Concept}
    (enc : Enc h chs T B p D D') : Enc h chs T' B' p D D' := by
  induction enc with
  | top p => exact .top p
  | bottom p => exact .bottom p
  | atom p cl => exact .atom p cl
  | notAtom p cl => exact .notAtom p cl
  | one p a => exact .one p a
  | notOne p a => exact .notOne p a
  | hasSelf p r => exact .hasSelf p r
  | notSelf p r => exact .notSelf p r
  | and _ _ iha ihb => exact .and iha ihb
  | or _ _ iha ihb => exact .or iha ihb
  | existsPos _ ih => exact .existsPos ih
  | existsSimple simple _ ih => exact .existsSimple simple ih
  | existsComplex complex _ neg at_k at_b ih =>
    exact .existsComplex complex ih neg (prefix_get pt at_k) (prefix_get pb at_b)
  | forallComplex complex _ at_k at_b ih => exact .forallComplex complex ih (prefix_get pt at_k) (prefix_get pb at_b)
  | forallSimple simple _ ih => exact .forallSimple simple ih
  | forallNeg _ ih => exact .forallNeg ih
  | atLeast _ ih => exact .atLeast ih
  | atMost _ ih => exact .atMost ih


private theorem before_atom {T : List role_chains.Atom} {k : Usize} {a : role_chains.Atom}
    (at_k : T[k.val]? = some a) : Before T.length (nameOf k) :=
  .inr ⟨k,rfl,(List.getElem?_eq_some_iff.mp at_k).1⟩

/-- The actual encoding extends the tables, keeps them in order, and its result
    encodes the concept, mentioning only the concept's classes and atoms of the
    table. -/
theorem encode_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain) (D : concepts.Concept)
    (fits : Fits h chs.val D) :
    ∀ (p : Bool) (atoms : alloc.vec.Vec role_chains.Atom) (bases : alloc.vec.Vec concepts.Concept),
      TableOk atoms.val bases.val →
      ∃ o, role_chains.encode h chs D p atoms bases = .ok o ∧ ∀ atoms' bases' D', o = some (atoms',bases',D') →
        atoms.val <+: atoms'.val ∧ bases.val <+: bases'.val ∧ TableOk atoms'.val bases'.val ∧
        Enc h chs.val atoms'.val bases'.val p D D' ∧ ∀ cl, Mentions cl D' → Before atoms'.val.length cl := by
  -- Concepts the encoding copies.
  have copied : ∀ (D : concepts.Concept) (p : Bool) (atoms : alloc.vec.Vec role_chains.Atom)
      (bases : alloc.vec.Vec concepts.Concept), TableOk atoms.val bases.val → Enc h chs.val atoms.val bases.val p D D →
      (∀ cl, Mentions cl D → Before atoms.val.length cl) →
      role_chains.encode h chs D p atoms bases = .ok (some (atoms,bases,D)) →
      ∃ o, role_chains.encode h chs D p atoms bases = .ok o ∧ ∀ atoms' bases' D', o = some (atoms',bases',D') →
        atoms.val <+: atoms'.val ∧ bases.val <+: bases'.val ∧ TableOk atoms'.val bases'.val ∧
        Enc h chs.val atoms'.val bases'.val p D D' ∧ ∀ cl, Mentions cl D' → Before atoms'.val.length cl := by
    intro D p atoms bases ok enc classes run
    refine ⟨_,run,?_⟩
    intro atoms' bases' D' same
    simp only [Option.some.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl,rfl⟩ := same
    exact ⟨List.prefix_refl _,List.prefix_refl _,ok,enc,classes⟩
  induction D with
  | Top =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.top p) (by simp [Mentions])
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | Bottom =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.bottom p) (by simp [Mentions])
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | Atom cl =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.atom p cl)
      (by intro c same; simp only [Mentions] at same; subst same; exact .inl fits)
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | NotAtom cl =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.notAtom p cl)
      (by intro c same; simp only [Mentions] at same; subst same; exact .inl fits)
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | One a =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.one p a) (by simp [Mentions])
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | NotOne a =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.notOne p a) (by simp [Mentions])
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | HasSelf r =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.hasSelf p r) (by simp [Mentions])
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | NotSelf r =>
    intro p atoms bases ok
    exact copied _ p atoms bases ok (.notSelf p r) (by simp [Mentions])
      (by rw [role_chains.encode]; simp [copy_concept_identity])
  | And a b iha ihb | Or a b iha ihb =>
    intro p atoms bases ok
    obtain ⟨oa,runA,specA⟩ := iha fits.1 p atoms bases ok
    cases oa with
    | none => exact ⟨none,by rw [role_chains.encode]; simp [runA],by simp⟩
    | some triple =>
      obtain ⟨atoms1,bases1,a'⟩ := triple
      obtain ⟨pa1,pb1,ok1,encA,mentA⟩ := specA _ _ _ rfl
      obtain ⟨ob,runB,specB⟩ := ihb fits.2 p atoms1 bases1 ok1
      cases ob with
      | none => exact ⟨none,by rw [role_chains.encode]; simp [runA,runB],by simp⟩
      | some triple =>
        obtain ⟨atoms2,bases2,b'⟩ := triple
        obtain ⟨pa2,pb2,ok2,encB,mentB⟩ := specB _ _ _ rfl
        first
        | refine ⟨some (atoms2,bases2,.And a' b'),by rw [role_chains.encode]; simp [runA,runB],?_⟩
          intro atoms' bases' D' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl,rfl⟩ := same
          refine ⟨pa1.trans pa2,pb1.trans pb2,ok2,.and (enc_mono pa2 pb2 encA) encB,?_⟩
          rintro cl (ma | mb)
          · exact before_mono pa2.length_le (mentA cl ma)
          · exact mentB cl mb
        | refine ⟨some (atoms2,bases2,.Or a' b'),by rw [role_chains.encode]; simp [runA,runB],?_⟩
          intro atoms' bases' D' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl,rfl⟩ := same
          refine ⟨pa1.trans pa2,pb1.trans pb2,ok2,.or (enc_mono pa2 pb2 encA) encB,?_⟩
          rintro cl (ma | mb)
          · exact before_mono pa2.length_le (mentA cl ma)
          · exact mentB cl mb
  | Exists r e ih =>
    intro p atoms bases ok
    obtain ⟨oe,runE,specE⟩ := ih fits p atoms bases ok
    cases oe with
    | none => exact ⟨none,by rw [role_chains.encode]; simp [runE],by simp⟩
    | some triple =>
      obtain ⟨atoms1,bases1,e'⟩ := triple
      obtain ⟨pa1,pb1,ok1,encE,mentE⟩ := specE _ _ _ rfl
      cases p with
      | true =>
        refine ⟨some (atoms1,bases1,.Exists r e'),by rw [role_chains.encode]; simp [runE,copy_role_identity],?_⟩
        intro atoms' bases' D' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl,rfl⟩ := same
        exact ⟨pa1,pb1,ok1,.existsPos encE,mentE⟩
      | false =>
        by_cases complex : Complex h chs.val r
        · obtain ⟨on,runN,_⟩ := negate_correct.{0,0} e'
          cases on with
          | none =>
            exact ⟨none,by rw [role_chains.encode]; simp [runE,complex_correct,complex,runN],by simp⟩
          | some n =>
            have nClasses : ∀ cl, Mentions cl n → Before atoms1.val.length cl :=
              fun cl mn => mentE cl (negate_mentions e' n runN cl mn)
            obtain ⟨ou,runU,specU⟩ := universal_correct atoms1 bases1 r n ok1 nClasses
            cases ou with
            | none =>
              exact ⟨none,by rw [role_chains.encode]; simp [runE,complex_correct,complex,runN,runU],by simp⟩
            | some triple =>
              obtain ⟨atoms2,bases2,k⟩ := triple
              obtain ⟨contents,ok2,pa2,b,at_k,at_b⟩ := specU _ _ _ rfl
              have pb2 : bases1.val <+: bases2.val := by rw [contents]; exact List.prefix_append _ _
              refine ⟨some (atoms2,bases2,.NotAtom (nameOf k)),
                by rw [role_chains.encode]; simp [runE,complex_correct,complex,runN,runU,name_correct],?_⟩
              intro atoms' bases' D' same
              simp only [Option.some.injEq,Prod.mk.injEq] at same
              obtain ⟨rfl,rfl,rfl⟩ := same
              refine ⟨pa1.trans pa2,pb1.trans pb2,ok2,.existsComplex complex (enc_mono pa2 pb2 encE) runN at_k at_b,?_⟩
              intro cl same
              simp only [Mentions] at same
              subst same
              exact before_atom at_k
        · refine ⟨some (atoms1,bases1,.Exists r e'),
            by rw [role_chains.encode]; simp [runE,complex_correct,complex,copy_role_identity],?_⟩
          intro atoms' bases' D' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl,rfl⟩ := same
          exact ⟨pa1,pb1,ok1,.existsSimple complex encE,mentE⟩
  | Forall r e ih =>
    intro p atoms bases ok
    obtain ⟨oe,runE,specE⟩ := ih fits p atoms bases ok
    cases oe with
    | none => exact ⟨none,by rw [role_chains.encode]; simp [runE],by simp⟩
    | some triple =>
      obtain ⟨atoms1,bases1,e'⟩ := triple
      obtain ⟨pa1,pb1,ok1,encE,mentE⟩ := specE _ _ _ rfl
      cases p with
      | false =>
        refine ⟨some (atoms1,bases1,.Forall r e'),by rw [role_chains.encode]; simp [runE,copy_role_identity],?_⟩
        intro atoms' bases' D' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl,rfl⟩ := same
        exact ⟨pa1,pb1,ok1,.forallNeg encE,mentE⟩
      | true =>
        by_cases complex : Complex h chs.val r
        · obtain ⟨ou,runU,specU⟩ := universal_correct atoms1 bases1 r e' ok1 mentE
          cases ou with
          | none =>
            exact ⟨none,by rw [role_chains.encode]; simp [runE,complex_correct,complex,runU],by simp⟩
          | some triple =>
            obtain ⟨atoms2,bases2,k⟩ := triple
            obtain ⟨contents,ok2,pa2,b,at_k,at_b⟩ := specU _ _ _ rfl
            have pb2 : bases1.val <+: bases2.val := by rw [contents]; exact List.prefix_append _ _
            refine ⟨some (atoms2,bases2,.Atom (nameOf k)),
              by rw [role_chains.encode]; simp [runE,complex_correct,complex,runU,name_correct],?_⟩
            intro atoms' bases' D' same
            simp only [Option.some.injEq,Prod.mk.injEq] at same
            obtain ⟨rfl,rfl,rfl⟩ := same
            refine ⟨pa1.trans pa2,pb1.trans pb2,ok2,.forallComplex complex (enc_mono pa2 pb2 encE) at_k at_b,?_⟩
            intro cl same
            simp only [Mentions] at same
            subst same
            exact before_atom at_k
        · refine ⟨some (atoms1,bases1,.Forall r e'),
            by rw [role_chains.encode]; simp [runE,complex_correct,complex,copy_role_identity],?_⟩
          intro atoms' bases' D' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl,rfl⟩ := same
          exact ⟨pa1,pb1,ok1,.forallSimple complex encE,mentE⟩
  | AtLeast n r e ih =>
    intro p atoms bases ok
    obtain ⟨oe,runE,specE⟩ := ih fits.2 p atoms bases ok
    cases oe with
    | none => exact ⟨none,by rw [role_chains.encode]; simp [runE],by simp⟩
    | some triple =>
      obtain ⟨atoms1,bases1,e'⟩ := triple
      obtain ⟨pa1,pb1,ok1,encE,mentE⟩ := specE _ _ _ rfl
      refine ⟨some (atoms1,bases1,.AtLeast n r e'),by rw [role_chains.encode]; simp [runE,copy_role_identity],?_⟩
      intro atoms' bases' D' same
      simp only [Option.some.injEq,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl,rfl⟩ := same
      exact ⟨pa1,pb1,ok1,.atLeast encE,mentE⟩
  | AtMost n r e ih =>
    intro p atoms bases ok
    have flip : decide (¬ p = true) = !p := by cases p <;> rfl
    obtain ⟨oe,runE,specE⟩ := ih fits.2 (!p) atoms bases ok
    cases oe with
    | none => exact ⟨none,by rw [role_chains.encode,flip]; simp [runE],by simp⟩
    | some triple =>
      obtain ⟨atoms1,bases1,e'⟩ := triple
      obtain ⟨pa1,pb1,ok1,encE,mentE⟩ := specE _ _ _ rfl
      refine ⟨some (atoms1,bases1,.AtMost n r e'),by rw [role_chains.encode,flip]; simp [runE,copy_role_identity],?_⟩
      intro atoms' bases' D' same
      simp only [Option.some.injEq,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl,rfl⟩ := same
      exact ⟨pa1,pb1,ok1,.atMost encE,mentE⟩


/-! ### Definitions of the atoms -/

/-- The concept of a filler. -/
def fillerConcept (B : List concepts.Concept) : role_chains.Filler → concepts.Concept
  | .Base b => (B[b.val]?).getD .Top
  | .Atom j => .Atom (nameOf j)

theorem filler_concept_correct (B : alloc.vec.Vec concepts.Concept) (F : role_chains.Filler) :
    role_chains.filler_concept B F = .ok (fillerConcept B.val F) := by
  cases F with
  | Base b =>
    rw [role_chains.filler_concept]
    by_cases inside : b.val < B.val.length
    · have lookup : B.index_usize b = .ok B.val[b.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,copy_concept_identity,fillerConcept,
        List.getElem?_eq_getElem inside]
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,fillerConcept,List.getElem?_eq_none (by omega : B.val.length ≤ b.val)]
  | Atom j => rw [role_chains.filler_concept]; simp [name_correct,fillerConcept]

/-- Distinct atoms have distinct indices. -/
theorem nodup_unique {T : List role_chains.Atom} (nd : T.Nodup) {i j : Usize} {a : role_chains.Atom}
    (hi : T[i.val]? = some a) (hj : T[j.val]? = some a) : i = j := by
  obtain ⟨ilt,iget⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨jlt,jget⟩ := List.getElem?_eq_some_iff.mp hj
  apply UScalar.eq_of_val_eq
  exact (List.Nodup.getElem_inj_iff nd).mp (iget.trans jget.symm)

/-- What an atom of `T` requires for the transition `t`, read through the
    classes of the atoms. -/
abbrev Needs {Object : Type u} {Value : Type v} (J : Interpretation Object Value) (h : hierarchy.RoleHierarchy)
    (chs : List role_chains.Chain) (T : List role_chains.Atom) (c : ObjectPropertyExpression)
    (F : role_chains.Filler) (t : role_chains.Transition) (y : Object) : Prop :=
  ∃ j : Usize, T[j.val]? = some ⟨c,t.target,F⟩ ∧ Requires J h chs T (fun j y => J.classes (nameOf j) y) c t.label j y

/-- The table has the atom of the target of a transition, and for a complex
    role the atom of its initial state with that atom as filler. -/
def Present (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) (T : List role_chains.Atom)
    (c : ObjectPropertyExpression) (F : role_chains.Filler) (t : role_chains.Transition) : Prop :=
  ∃ j : Usize, T[j.val]? = some ⟨c,t.target,F⟩ ∧
    ∀ s, t.label = .Role s → Complex h chs s → ∃ j2 : Usize, T[j2.val]? = some ⟨s,.Initial,.Atom j⟩

theorem present_mono {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} {T T' : List role_chains.Atom}
    (p : T <+: T') {c : ObjectPropertyExpression} {F : role_chains.Filler} {t : role_chains.Transition}
    (present : Present h chs T c F t) : Present h chs T' c F t := by
  obtain ⟨j,at_j,nested⟩ := present
  refine ⟨j,prefix_get p at_j,?_⟩
  intro s label complex
  obtain ⟨j2,at_j2⟩ := nested s label complex
  exact ⟨j2,prefix_get p at_j2⟩

private theorem unfold_from_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (ts : alloc.vec.Vec role_chains.Transition) (c : ObjectPropertyExpression) (F : role_chains.Filler)
    (B : List concepts.Concept) (i : Usize) (T : alloc.vec.Vec role_chains.Atom) (acc : concepts.Concept)
    (ok : TableOk T.val B) (fill : FillerOk B T.val.length F) :
      ∃ o, role_chains.unfold_from h chs ts c F i T acc = .ok o ∧ ∀ T' D, o = some (T',D) →
        T.val <+: T'.val ∧ TableOk T'.val B ∧ (∀ t ∈ ts.val.drop i.val, Present h chs.val T'.val c F t) ∧
        ∀ (T'' : List role_chains.Atom), T'.val <+: T'' → T''.Nodup →
          ∀ {Object : Type u} {Value : Type v} (J : Interpretation Object Value) (y : Object),
            denote J D y ↔ denote J acc y ∧ ∀ t ∈ ts.val.drop i.val, Needs J h chs.val T'' c F t y := by
  rw [role_chains.unfold_from]
  by_cases more : i.val < ts.val.length
  · have lookup : ts.index_usize i = .ok ts.val[i.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : ts.val.drop i.val = ts.val[i.val] :: ts.val.drop (i.val+1) := List.drop_eq_getElem_cons more
    obtain ⟨i',advance,iValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have nextI : i'.val = i.val+1 := by simpa using iValue
    set t := ts.val[i.val] with tIs
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok]
    obtain ⟨o1,run1,_⟩ := atom_for_correct T c t.target F
    cases o1 with
    | none => exact ⟨none,by simp [run1],by simp⟩
    | some pair =>
      obtain ⟨T1,target⟩ := pair
      obtain ⟨ok1,p1,at_target⟩ := atom_for_ok ok fill run1
      have fill1 : FillerOk B T1.val.length F := fillerOk_mono (List.prefix_refl _) p1.length_le fill
      have targetIn : target.val < T1.val.length := (List.getElem?_eq_some_iff.mp at_target).1
      -- The rest of the transitions, after this one's part.
      have rest : ∀ (T2 : alloc.vec.Vec role_chains.Atom) (part : concepts.Concept), TableOk T2.val B →
          T1.val <+: T2.val → Present h chs.val T2.val c F t →
          (∀ (T'' : List role_chains.Atom), T2.val <+: T'' → T''.Nodup →
            ∀ {Object : Type u} {Value : Type v} (J : Interpretation Object Value) (y : Object),
              denote J part y ↔ Needs J h chs.val T'' c F t y) →
          ∃ o, role_chains.unfold_from h chs ts c F i' T2 (.And acc part) = .ok o ∧ ∀ T' D, o = some (T',D) →
            T.val <+: T'.val ∧ TableOk T'.val B ∧ (∀ t ∈ ts.val.drop i.val, Present h chs.val T'.val c F t) ∧
            ∀ (T'' : List role_chains.Atom), T'.val <+: T'' → T''.Nodup →
              ∀ {Object : Type u} {Value : Type v} (J : Interpretation Object Value) (y : Object),
                denote J D y ↔ denote J acc y ∧ ∀ t ∈ ts.val.drop i.val, Needs J h chs.val T'' c F t y := by
        intro T2 part ok2 p2 here means
        obtain ⟨o,run,spec⟩ := unfold_from_correct h chs ts c F B i' T2 (.And acc part) ok2
          (fillerOk_mono (List.prefix_refl _) p2.length_le fill1)
        refine ⟨o,run,?_⟩
        intro T' D same
        obtain ⟨p3,ok3,present,meaning⟩ := spec T' D same
        refine ⟨p1.trans (p2.trans p3),ok3,?_,?_⟩
        · rw [split]
          intro t' member
          rcases List.mem_cons.mp member with same | later
          · rw [same]; exact present_mono p3 here
          · exact present t' (by rw [nextI]; exact later)
        intro T'' p4 nd Object Value J y
        rw [meaning T'' p4 nd J y,split,nextI]
        simp only [denote,List.forall_mem_cons]
        rw [means T'' (p3.trans p4) nd J y]
        tauto
      -- The part of this transition.
      have key : ∀ (T'' : List role_chains.Atom), T1.val <+: T'' → T''[target.val]? = some ⟨c,t.target,F⟩ :=
        fun T'' p => prefix_get p at_target
      cases label : t.label with
      | Direct =>
        obtain ⟨o,run,spec⟩ := rest T1 (.Forall c (.Atom (nameOf target))) ok1 (List.prefix_refl _)
          ⟨target,at_target,by intro s same; rw [label] at same; cases same⟩ (by
          intro T'' p nd Object Value J y
          simp only [Needs,label,Requires,denote]
          constructor
          · intro all; exact ⟨target,key T'' p,all⟩
          · rintro ⟨j,at_j,all⟩
            rw [nodup_unique nd (key T'' p) at_j]; exact all)
        refine ⟨o,?_,spec⟩
        simp only [run1,bind_ok,label,copy_role_identity,name_correct,advance]
        exact run
      | Empty =>
        obtain ⟨o,run,spec⟩ := rest T1 (.Atom (nameOf target)) ok1 (List.prefix_refl _)
          ⟨target,at_target,by intro s same; rw [label] at same; cases same⟩ (by
          intro T'' p nd Object Value J y
          simp only [Needs,label,Requires,denote]
          constructor
          · intro holds; exact ⟨target,key T'' p,holds⟩
          · rintro ⟨j,at_j,holds⟩
            rw [nodup_unique nd (key T'' p) at_j]; exact holds)
        refine ⟨o,?_,spec⟩
        simp only [run1,bind_ok,label,name_correct,advance]
        exact run
      | Role along =>
        by_cases complex : Complex h chs.val along
        · obtain ⟨o2,run2,_⟩ := atom_for_correct T1 along .Initial (.Atom target)
          cases o2 with
          | none => exact ⟨none,by simp [run1,label,complex_correct,complex,run2],by simp⟩
          | some pair =>
            obtain ⟨T2,nested⟩ := pair
            obtain ⟨ok2,p2,at_nested⟩ := atom_for_ok ok1 (show FillerOk B T1.val.length (.Atom target) from targetIn) run2
            obtain ⟨o,run,spec⟩ := rest T2 (.Atom (nameOf nested)) ok2 p2
              ⟨target,prefix_get p2 at_target,by
                intro s same _
                rw [label] at same
                cases same
                exact ⟨nested,at_nested⟩⟩ (by
              intro T'' p nd Object Value J y
              simp only [Needs,label,Requires,denote,complex,true_implies,not_true_eq_false,false_implies,and_true]
              constructor
              · intro holds
                exact ⟨target,key T'' (p2.trans p),nested,prefix_get p at_nested,holds⟩
              · rintro ⟨j,at_j,j2,at_j2,holds⟩
                have same := nodup_unique nd (key T'' (p2.trans p)) at_j
                subst same
                rw [nodup_unique nd (prefix_get p at_nested) at_j2]
                exact holds)
            refine ⟨o,?_,spec⟩
            simp only [run1,bind_ok,label,complex_correct,complex,decide_true,↓reduceIte]
            show (do
              let o1 ← role_chains.atom_for T1 along role_chains.State.Initial (role_chains.Filler.Atom target)
              match o1 with
                | none => Result.ok none
                | some p1 =>
                  let (atoms2, nested) := p1
                  do
                  let cl ← role_chains.name nested
                  let i1 ← i + 1#usize
                  role_chains.unfold_from h chs ts c F i1 atoms2 (concepts.Concept.And acc (concepts.Concept.Atom cl))) =
              Result.ok o
            simp only [run2,bind_ok,name_correct,advance]
            exact run
        · obtain ⟨o,run,spec⟩ := rest T1 (.Forall along (.Atom (nameOf target))) ok1 (List.prefix_refl _)
            ⟨target,at_target,by
              intro s same complex'
              rw [label] at same
              cases same
              exact absurd complex' complex⟩ (by
            intro T'' p nd Object Value J y
            simp only [Needs,label,Requires,denote,complex,false_implies,not_false_eq_true,true_implies,true_and]
            constructor
            · intro all; exact ⟨target,key T'' p,all⟩
            · rintro ⟨j,at_j,all⟩
              rw [nodup_unique nd (key T'' p) at_j]; exact all)
          refine ⟨o,?_,spec⟩
          simp only [run1,bind_ok,label,complex_correct,complex,decide_false,Bool.false_eq_true,↓reduceIte,
            copy_role_identity,name_correct,advance]
          exact run
  · refine ⟨some (T,acc),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro T' D same
    simp only [Option.some.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    have empty : ts.val.drop i.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨List.prefix_refl _,ok,by simp [empty],?_⟩
    intro T'' _ _ Object Value J y
    simp [empty]
termination_by ts.val.length - i.val
decreasing_by all_goals omega


/-- What the definition `D` of the atom `a` says, read with any table that
    extends `T` and has distinct atoms: the filler at the final state, and for
    every transition what the atom requires. -/
def Defines (h : hierarchy.RoleHierarchy) (chs : List role_chains.Chain) (B : List concepts.Concept)
    (T : List role_chains.Atom) (a : role_chains.Atom) (D : concepts.Concept) : Prop :=
  (∀ (l : role_chains.Label) (q' : role_chains.State), Trans h chs a.role a.state l q' →
    Present h chs T a.role a.filler ⟨l,q'⟩) ∧
  ∀ (T'' : List role_chains.Atom), T <+: T'' → T''.Nodup →
    ∀ {Object : Type u} {Value : Type v} (J : Interpretation Object Value) (y : Object),
      denote J D y ↔ (a.state = .Final → denote J (fillerConcept B a.filler) y) ∧
        ∀ (l : role_chains.Label) (q' : role_chains.State), Trans h chs a.role a.state l q' →
          Needs J h chs T'' a.role a.filler ⟨l,q'⟩ y

theorem defines_mono {h : hierarchy.RoleHierarchy} {chs : List role_chains.Chain} {B : List concepts.Concept}
    {T T' : List role_chains.Atom} {a : role_chains.Atom} {D : concepts.Concept} (defines : Defines.{u,v} h chs B T a D)
    (p : T <+: T') : Defines.{u,v} h chs B T' a D :=
  ⟨fun l q' trans => present_mono p (defines.1 l q' trans),fun T'' p' nd => defines.2 T'' (p.trans p') nd⟩

/-- The actual definition of the atom at `k`. -/
theorem unfold_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (B : alloc.vec.Vec concepts.Concept) (T : alloc.vec.Vec role_chains.Atom) (k : Usize) (ok : TableOk T.val B.val) :
    ∃ o, role_chains.unfold h chs B T k = .ok o ∧ ∀ T' D, o = some (T',D) →
      T.val <+: T'.val ∧ TableOk T'.val B.val ∧ ∃ a, T.val[k.val]? = some a ∧ Defines.{u,v} h chs.val B.val T'.val a D := by
  rw [role_chains.unfold]
  by_cases inside : k.val < T.val.length
  · have lookup : T.index_usize k = .ok T.val[k.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    set a := T.val[k.val] with aIs
    have get : T.val[k.val]? = some a := List.getElem?_eq_getElem inside
    have fill : FillerOk B.val T.val.length a.filler :=
      fillerOk_mono (List.prefix_refl _) (by omega) (ok.2 k.val a get)
    obtain ⟨ot,runT,specT⟩ := transitions_correct h chs a.role a.state
    have common : ∀ (start : concepts.Concept) (ts : alloc.vec.Vec role_chains.Transition), ot = some ts →
        (∀ {Object : Type u} {Value : Type v} (J : Interpretation Object Value) (y : Object),
          denote J start y ↔ (a.state = .Final → denote J (fillerConcept B.val a.filler) y)) →
        ∃ o, role_chains.unfold_from h chs ts a.role a.filler 0#usize T start = .ok o ∧ ∀ T' D, o = some (T',D) →
          T.val <+: T'.val ∧ TableOk T'.val B.val ∧ ∃ a', T.val[k.val]? = some a' ∧
            Defines.{u,v} h chs.val B.val T'.val a' D := by
      intro start ts same startMeans
      obtain ⟨o,run,spec⟩ := unfold_from_correct.{u,v} h chs ts a.role a.filler B.val 0#usize T start ok fill
      refine ⟨o,run,?_⟩
      intro T' D result
      obtain ⟨p,ok',present,means⟩ := spec T' D result
      refine ⟨p,ok',a,get,?_,?_⟩
      · intro l q' trans
        rw [zero_val,List.drop_zero] at present
        exact present ⟨l,q'⟩ ((specT ts same ⟨l,q'⟩).mpr trans)
      intro T'' p' nd Object Value J y
      rw [means T'' p' nd J y,startMeans J y,zero_val,List.drop_zero]
      apply and_congr_right
      intro _
      constructor
      · intro all l q' trans
        exact all ⟨l,q'⟩ ((specT ts same ⟨l,q'⟩).mpr trans)
      · intro all t member
        exact all t.label t.target ((specT ts same t).mp member)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,copy_role_identity,copy_state_identity,copy_filler_identity,runT]
    cases state : a.state with
    | Initial =>
      cases ot with
      | none => exact ⟨none,by simp,by simp⟩
      | some ts =>
        obtain ⟨o,run,spec⟩ := common .Top ts rfl (by intro _ _ J y; simp [denote,state])
        exact ⟨o,by simp [run],spec⟩
    | Final =>
      cases ot with
      | none => exact ⟨none,by simp [filler_concept_correct],by simp⟩
      | some ts =>
        obtain ⟨o,run,spec⟩ := common (fillerConcept B.val a.filler) ts rfl (by intro _ _ J y; simp [state])
        exact ⟨o,by simp [filler_concept_correct,run],spec⟩
    | Inside _ _ =>
      cases ot with
      | none => exact ⟨none,by simp,by simp⟩
      | some ts =>
        obtain ⟨o,run,spec⟩ := common .Top ts rfl (by intro _ _ J y; simp [denote,state])
        exact ⟨o,by simp [run],spec⟩
  · refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]

theorem limit_val : role_chains.LIMIT.val = 1048576 := by
  unfold role_chains.LIMIT; rfl

/-- The actual definitions of the atoms from `i` on: the table grows in order,
    and every atom from `i` on gets one definition that defines it. -/
theorem generate_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (B : alloc.vec.Vec concepts.Concept) (T : alloc.vec.Vec role_chains.Atom) (i : Usize)
    (out : alloc.vec.Vec completion.Definition) (ok : TableOk T.val B.val) (iLe : i.val ≤ T.val.length) :
    ∃ o, role_chains.generate h chs B T i out = .ok o ∧ ∀ T' out', o = some (T',out') →
      T.val <+: T'.val ∧ TableOk T'.val B.val ∧ ∃ defs, out'.val = out.val ++ defs ∧
        (∀ d ∈ defs, ∃ (k : Usize) (a : role_chains.Atom), i.val ≤ k.val ∧ T'.val[k.val]? = some a ∧
          d.class = nameOf k ∧ Defines.{u,v} h chs.val B.val T'.val a d.concept) ∧
        (∀ (k : Usize) (a : role_chains.Atom), i.val ≤ k.val → T'.val[k.val]? = some a →
          ∃ d ∈ defs, d.class = nameOf k ∧ Defines.{u,v} h chs.val B.val T'.val a d.concept) := by
  rw [role_chains.generate]
  by_cases more : i.val < T.val.length
  · by_cases over : role_chains.LIMIT < alloc.vec.Vec.len T
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,over]
    · have small : T.val.length ≤ 1048576 := by
        simp only [UScalar.lt_equiv,limit_val,alloc.vec.Vec.len_val] at over; simp at over; omega
      obtain ⟨ou,runU,specU⟩ := unfold_correct.{u,v} h chs B T i ok
      cases ou with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,over,runU]
      | some pair =>
        obtain ⟨T1,D⟩ := pair
        obtain ⟨p1,ok1,a,get,defines⟩ := specU T1 D rfl
        by_cases room : out.val.length < Usize.max
        · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec out (⟨nameOf i,D⟩ : completion.Definition) room)
          obtain ⟨i',advance,iValue⟩ := WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
          have nextI : i'.val = i.val+1 := by simpa using iValue
          obtain ⟨o,run,spec⟩ := generate_correct h chs B T1 i' pushed ok1 (by
            have := p1.length_le; omega)
          refine ⟨o,?_,?_⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,over,↓reduceIte,runU,bind_ok,
              usize_max_val,alloc.vec.Vec.length,room,name_correct,advance]
            show (do
              let out1 ← out.push { «class» := nameOf i, concept := D }
              role_chains.generate h chs B T1 i' out1) = Result.ok o
            simp only [push,bind_ok]
            exact run
          · intro T' out' same
            obtain ⟨p2,ok2,defs,outIs,sound,complete⟩ := spec T' out' same
            refine ⟨p1.trans p2,ok2,⟨nameOf i,D⟩ :: defs,by rw [outIs,contents]; simp,?_,?_⟩
            · intro d member
              rcases List.mem_cons.mp member with same | later
              · subst same
                exact ⟨i,a,le_refl _,prefix_get (p1.trans p2) get,rfl,defines_mono defines p2⟩
              · obtain ⟨k,b,le,at_k,cls,defs'⟩ := sound d later
                exact ⟨k,b,by omega,at_k,cls,defs'⟩
            · intro k b le at_k
              by_cases here : k.val = i.val
              · have : k = i := UScalar.eq_of_val_eq here
                subst this
                rw [prefix_get (p1.trans p2) get] at at_k
                simp only [Option.some.injEq] at at_k
                subst at_k
                exact ⟨⟨nameOf k,D⟩,List.mem_cons_self,rfl,defines_mono defines p2⟩
              · obtain ⟨d,member,cls,defs'⟩ := complete k b (by omega) at_k
                exact ⟨d,List.mem_cons_of_mem _ member,cls,defs'⟩
        · refine ⟨none,?_,by simp⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,over,↓reduceIte,runU,bind_ok,
            usize_max_val,alloc.vec.Vec.length,room]
          rfl
  · refine ⟨some (T,out),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro T' out' same
    simp only [Option.some.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    refine ⟨List.prefix_refl _,ok,[],by simp,by simp,?_⟩
    intro k a le at_k
    have := (List.getElem?_eq_some_iff.mp at_k).1
    omega
termination_by 1048577 - i.val
decreasing_by
  have := p1.length_le
  omega


/-! ### The chains with their mirrors -/

private theorem copied_correct (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (out : alloc.vec.Vec ObjectPropertyExpression) (len : out.val.length = index.val) :
    ∃ v, role_chains.copied roles index out = .ok v ∧ v.val = out.val ++ roles.val.drop index.val := by
  rw [role_chains.copied]
  by_cases more : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have room : out.val.length < Usize.max := by have := roles.property; omega
    obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out roles.val[index.val] room)
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨v,run,spec⟩ := copied_correct roles index' pushed (by rw [contents,nextIndex]; simp [len])
    refine ⟨v,?_,?_⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,alloc.vec.Vec.length,room,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,copy_role_identity,push,advance,run]
    · rw [spec,contents,nextIndex,List.drop_eq_getElem_cons more]
      simp
  · refine ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    simp [List.drop_eq_nil_iff.mpr (show roles.val.length ≤ index.val by omega)]
termination_by roles.val.length - index.val
decreasing_by omega

private theorem reversed_correct (roles : alloc.vec.Vec ObjectPropertyExpression) (count : Usize)
    (out : alloc.vec.Vec ObjectPropertyExpression) (room : out.val.length + count.val ≤ roles.val.length) :
    ∃ v, role_chains.reversed roles count out = .ok v ∧
      v.val = out.val ++ ((roles.val.take count.val).map inv).reverse := by
  rw [role_chains.reversed]
  by_cases positive : 0 < count.val
  · obtain ⟨less,lessRun,lessVal⟩ := WP.spec_imp_exists
      (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have lessIs : less.val = count.val - 1 := by simp at lessVal; omega
    have within : less.val < roles.val.length := by omega
    have lookup : roles.index_usize less = .ok roles.val[less.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem within]
    have space : out.val.length < Usize.max := by have := roles.property; omega
    obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (inv roles.val[less.val]) space)
    obtain ⟨v,run,spec⟩ := reversed_correct roles less pushed (by rw [contents]; simp; omega)
    have positive' : 0#usize < count := by simp only [UScalar.lt_equiv]; simpa using positive
    refine ⟨v,?_,?_⟩
    · simp only [positive',↓reduceIte,lessRun,bind_ok,alloc.vec.Vec.len_val,UScalar.lt_equiv,within,
        usize_max_val,alloc.vec.Vec.length,space,alloc.vec.Vec.index_slice_index,lookup,inverse_correct,push,run]
    · have take : roles.val.take count.val = roles.val.take less.val ++ [roles.val[less.val]] := by
        rw [show count.val = less.val + 1 by omega,List.take_add_one,List.getElem?_eq_getElem within]
        rfl
      rw [spec,contents,take,List.map_append,List.reverse_append]
      simp only [List.map_cons,List.map_nil,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,
        List.singleton_append]
  · have zero : count.val = 0 := by omega
    have positive' : ¬ 0#usize < count := by simp only [UScalar.lt_equiv]; simpa using positive
    refine ⟨out,by simp only [positive',↓reduceIte],?_⟩
    simp [zero]
termination_by count.val
decreasing_by omega

/-- The chain read backwards along the inverses. -/
def mirrorOf (ch : role_chains.Chain) (roles : alloc.vec.Vec ObjectPropertyExpression) : Prop :=
  roles.val = (ch.roles.val.map inv).reverse

theorem copy_chains_correct (chains : alloc.vec.Vec role_chains.Chain) (mirror : Bool) (index : Usize)
    (out : alloc.vec.Vec role_chains.Chain) :
    ∃ o, role_chains.copy_chains chains mirror index out = .ok o ∧ ∀ v, o = some v →
      ∃ added, v.val = out.val ++ added ∧
        List.Forall₂ (fun ch ch' => (if mirror then ch'.roles.val = (ch.roles.val.map inv).reverse ∧ ch'.sup = inv ch.sup
          else ch' = ch)) (chains.val.drop index.val) added := by
  rw [role_chains.copy_chains]
  by_cases more : index.val < chains.val.length
  · have lookup : chains.index_usize index = .ok chains.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    set ch := chains.val[index.val] with chIs
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    -- What follows the copy of this chain.
    have after_ : ∀ (copy : role_chains.Chain),
        (if mirror then copy.roles.val = (ch.roles.val.map inv).reverse ∧ copy.sup = inv ch.sup else copy = ch) →
        ∃ o, (if alloc.vec.Vec.len out < core.num.Usize.MAX then do
            let out1 ← out.push copy
            let i2 ← index + 1#usize
            role_chains.copy_chains chains mirror i2 out1
          else Result.ok none) = .ok o ∧ ∀ v, o = some v →
          ∃ added, v.val = out.val ++ added ∧
            List.Forall₂ (fun ch ch' => (if mirror then ch'.roles.val = (ch.roles.val.map inv).reverse ∧
              ch'.sup = inv ch.sup else ch' = ch)) (chains.val.drop index.val) added := by
      intro copy copySpec
      by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out copy room)
        obtain ⟨o,run,spec⟩ := copy_chains_correct chains mirror index' pushed
        refine ⟨o,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,↓reduceIte,
            push,bind_ok,advance,run]
        · intro v same
          obtain ⟨added,vIs,pairs⟩ := spec v same
          refine ⟨copy :: added,by rw [vIs,contents]; simp,?_⟩
          rw [List.drop_eq_getElem_cons more,← chIs]
          rw [nextIndex] at pairs
          exact List.Forall₂.cons copySpec pairs
      · refine ⟨none,?_,by simp⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,alloc.vec.Vec.length,room,↓reduceIte]
    cases mirror with
    | true =>
      obtain ⟨v,run,spec⟩ := reversed_correct ch.roles (alloc.vec.Vec.len ch.roles)
        (alloc.vec.Vec.new ObjectPropertyExpression) (by simp [new_val])
      obtain ⟨o,next,spec'⟩ := after_ ⟨v,inv ch.sup⟩ (by
        simp only [↓reduceIte,and_true]
        rw [spec]; simp [new_val])
      refine ⟨o,?_,spec'⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,run,inverse_correct]
      exact next
    | false =>
      obtain ⟨v,run,spec⟩ := copied_correct ch.roles 0#usize (alloc.vec.Vec.new ObjectPropertyExpression)
        (by simp [new_val])
      have same : v = ch.roles := by
        apply alloc.vec.Vec.ext
        rw [spec]; simp [new_val]
      obtain ⟨o,next,spec'⟩ := after_ ⟨v,ch.sup⟩ (by simp only [Bool.false_eq_true,↓reduceIte]; rw [same])
      refine ⟨o,?_,spec'⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,run,copy_role_identity,Bool.false_eq_true]
      exact next
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro v same
    simp only [Option.some.injEq] at same
    subst same
    refine ⟨[],by simp,?_⟩
    rw [List.drop_eq_nil_iff.mpr (show chains.val.length ≤ index.val by omega)]
    exact List.Forall₂.nil
termination_by chains.val.length - index.val
decreasing_by all_goals omega


/-! ### Checks over lists -/

theorem long_from_correct (chains : alloc.vec.Vec role_chains.Chain) (index : Usize) :
    role_chains.long_from chains index = .ok (decide (∀ ch ∈ chains.val.drop index.val, 2 ≤ ch.roles.val.length)) := by
  rw [role_chains.long_from]
  by_cases more : index.val < chains.val.length
  · have lookup : chains.index_usize index = .ok chains.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := long_from_correct chains index'
    rw [nextIndex] at rest
    have split : chains.val.drop index.val = chains.val[index.val] :: chains.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases short : chains.val[index.val].roles.val.length < 2
    · have short' : alloc.vec.Vec.len chains.val[index.val].roles < 2#usize := by
        simp only [UScalar.lt_equiv,alloc.vec.Vec.len_val]; simpa using short
      have no : ¬ ∀ ch ∈ chains.val.drop index.val, 2 ≤ ch.roles.val.length := by
        rw [split]; intro all; have := all _ List.mem_cons_self; omega
      have two : (2#usize).val = 2 := by simp
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,alloc.vec.Vec.length,two,short]
      simp [no]
    · have two : (2#usize).val = 2 := by simp
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,alloc.vec.Vec.length,two,short,advance,rest]
      have iff : (∀ ch ∈ chains.val.drop (index.val+1), 2 ≤ ch.roles.val.length) ↔
          (∀ ch ∈ chains.val.drop index.val, 2 ≤ ch.roles.val.length) := by
        rw [split]
        constructor
        · intro all ch member
          rcases List.mem_cons.mp member with same | later
          · rw [same]; omega
          · exact all ch later
        · intro all ch member; exact all ch (List.mem_cons_of_mem _ member)
      simp only [iff]
  · have empty : chains.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by chains.val.length - index.val
decreasing_by omega

theorem pairs_fit_correct (h : hierarchy.RoleHierarchy) (chains : alloc.vec.Vec role_chains.Chain)
    (index : Usize) :
    role_chains.pairs_fit h chains index = .ok (decide (∀ d ∈ h.disjoint.val.drop index.val,
      ¬ Complex h chains.val d.left ∧ ¬ Complex h chains.val d.right)) := by
  rw [role_chains.pairs_fit]
  by_cases more : index.val < h.disjoint.val.length
  · have lookup : h.disjoint.index_usize index = .ok h.disjoint.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := pairs_fit_correct h chains index'
    rw [nextIndex] at rest
    have split : h.disjoint.val.drop index.val = h.disjoint.val[index.val] :: h.disjoint.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    set d := h.disjoint.val[index.val] with dIs
    by_cases left : Complex h chains.val d.left
    · have no : ¬ ∀ d ∈ h.disjoint.val.drop index.val, ¬ Complex h chains.val d.left ∧ ¬ Complex h chains.val d.right := by
        rw [split]; intro all; exact (all _ List.mem_cons_self).1 left
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,complex_correct,left,decide_true]
      simp [no]
    · by_cases right : Complex h chains.val d.right
      · have no : ¬ ∀ d ∈ h.disjoint.val.drop index.val, ¬ Complex h chains.val d.left ∧ ¬ Complex h chains.val d.right := by
          rw [split]; intro all; exact (all _ List.mem_cons_self).2 right
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,complex_correct,left,right,decide_true,decide_false,Bool.false_eq_true]
        simp [no]
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,complex_correct,left,right,decide_false,Bool.false_eq_true,advance,rest]
        have iff : (∀ d ∈ h.disjoint.val.drop (index.val+1), ¬ Complex h chains.val d.left ∧ ¬ Complex h chains.val d.right) ↔
            (∀ d ∈ h.disjoint.val.drop index.val, ¬ Complex h chains.val d.left ∧ ¬ Complex h chains.val d.right) := by
          rw [split]
          constructor
          · intro all d' member
            rcases List.mem_cons.mp member with same | later
            · rw [same]; exact ⟨left,right⟩
            · exact all d' later
          · intro all d' member; exact all d' (List.mem_cons_of_mem _ member)
        simp only [iff]
  · have empty : h.disjoint.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by h.disjoint.val.length - index.val
decreasing_by omega

theorem facts_fit_correct (h : hierarchy.RoleHierarchy) (chains : alloc.vec.Vec role_chains.Chain)
    (facts : alloc.vec.Vec completion.Fact) (index : Usize) :
    role_chains.facts_fit h chains facts index =
      .ok (decide (∀ f ∈ facts.val.drop index.val, Fits h chains.val f.concept)) := by
  rw [role_chains.facts_fit]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := facts_fit_correct h chains facts index'
    rw [nextIndex] at rest
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases fits : Fits h chains.val facts.val[index.val].concept
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,fits_correct,fits,decide_true,advance,rest]
      have iff : (∀ f ∈ facts.val.drop (index.val+1), Fits h chains.val f.concept) ↔
          (∀ f ∈ facts.val.drop index.val, Fits h chains.val f.concept) := by
        rw [split]
        constructor
        · intro all f member
          rcases List.mem_cons.mp member with same | later
          · rw [same]; exact fits
          · exact all f later
        · intro all f member; exact all f (List.mem_cons_of_mem _ member)
      simp only [iff]
    · have no : ¬ ∀ f ∈ facts.val.drop index.val, Fits h chains.val f.concept := by
        rw [split]; intro all; exact fits (all _ List.mem_cons_self)
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,fits_correct,fits,decide_false,Bool.false_eq_true]
      simp [no]
  · have empty : facts.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by facts.val.length - index.val
decreasing_by omega

theorem definitions_fit_correct (h : hierarchy.RoleHierarchy) (chains : alloc.vec.Vec role_chains.Chain)
    (definitions : alloc.vec.Vec completion.Definition) (index : Usize) :
    role_chains.definitions_fit h chains definitions index =
      .ok (decide (∀ d ∈ definitions.val.drop index.val, ¬ Spaced d.class ∧ Fits h chains.val d.concept)) := by
  rw [role_chains.definitions_fit]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := definitions_fit_correct h chains definitions index'
    rw [nextIndex] at rest
    have split : definitions.val.drop index.val = definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    set d := definitions.val[index.val] with dIs
    by_cases spaced : Spaced d.class
    · have no : ¬ ∀ d ∈ definitions.val.drop index.val, ¬ Spaced d.class ∧ Fits h chains.val d.concept := by
        rw [split]; intro all; exact (all _ List.mem_cons_self).1 spaced
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,spaced_correct,spaced,decide_true]
      simp [no]
    · by_cases fits : Fits h chains.val d.concept
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,spaced_correct,spaced,fits_correct,fits,decide_true,decide_false,Bool.false_eq_true,advance,rest]
        have iff : (∀ d ∈ definitions.val.drop (index.val+1), ¬ Spaced d.class ∧ Fits h chains.val d.concept) ↔
            (∀ d ∈ definitions.val.drop index.val, ¬ Spaced d.class ∧ Fits h chains.val d.concept) := by
          rw [split]
          constructor
          · intro all d' member
            rcases List.mem_cons.mp member with same | later
            · rw [same]; exact ⟨spaced,fits⟩
            · exact all d' later
          · intro all d' member; exact all d' (List.mem_cons_of_mem _ member)
        simp only [iff]
      · have no : ¬ ∀ d ∈ definitions.val.drop index.val, ¬ Spaced d.class ∧ Fits h chains.val d.concept := by
          rw [split]; intro all; exact fits (all _ List.mem_cons_self).2
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,spaced_correct,spaced,fits_correct,fits,decide_false,Bool.false_eq_true]
        simp [no]
  · have empty : definitions.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by definitions.val.length - index.val
decreasing_by omega


/-! ### Encoding the facts and definitions -/

theorem encode_facts_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (facts : alloc.vec.Vec completion.Fact) (index : Usize) (atoms : alloc.vec.Vec role_chains.Atom)
    (bases : alloc.vec.Vec concepts.Concept) (out : alloc.vec.Vec completion.Fact) (ok : TableOk atoms.val bases.val)
    (fits : ∀ f ∈ facts.val.drop index.val, Fits h chs.val f.concept) :
    ∃ o, role_chains.encode_facts h chs facts index atoms bases out = .ok o ∧
      ∀ atoms' bases' out', o = some (atoms',bases',out') →
        atoms.val <+: atoms'.val ∧ bases.val <+: bases'.val ∧ TableOk atoms'.val bases'.val ∧
        ∃ enc, out'.val = out.val ++ enc ∧
          List.Forall₂ (fun (f e : completion.Fact) => e.node = f.node ∧
            Enc h chs.val atoms'.val bases'.val true f.concept e.concept) (facts.val.drop index.val) enc := by
  rw [role_chains.encode_facts]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : facts.val.drop index.val = facts.val[index.val] :: facts.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    set f := facts.val[index.val] with fIs
    have fitsF : Fits h chs.val f.concept := fits f (by rw [split]; exact List.mem_cons_self)
    obtain ⟨oe,runE,specE⟩ := encode_correct h chs f.concept fitsF true atoms bases ok
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,runE]
    cases oe with
    | none => exact ⟨none,rfl,by simp⟩
    | some triple =>
      obtain ⟨atoms1,bases1,D⟩ := triple
      obtain ⟨pa1,pb1,ok1,encF,_⟩ := specE _ _ _ rfl
      by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out ({ f with concept := D } : completion.Fact) room)
        obtain ⟨o,run,spec⟩ := encode_facts_correct h chs facts index' atoms1 bases1 pushed ok1 (by
          intro g member
          rw [nextIndex] at member
          exact fits g (by rw [split]; exact List.mem_cons_of_mem _ member))
        refine ⟨o,?_,?_⟩
        · simp only [usize_max_val,alloc.vec.Vec.length,room,↓reduceIte]
          show (do
            let out1 ← out.push { f with concept := D }
            let i2 ← index + 1#usize
            role_chains.encode_facts h chs facts i2 atoms1 bases1 out1) = Result.ok o
          simp only [push,bind_ok,advance,run]
        · intro atoms' bases' out' same
          obtain ⟨pa2,pb2,ok2,enc,outIs,pairs⟩ := spec atoms' bases' out' same
          refine ⟨pa1.trans pa2,pb1.trans pb2,ok2,{ f with concept := D } :: enc,by rw [outIs,contents]; simp,?_⟩
          rw [split]
          rw [nextIndex] at pairs
          exact List.Forall₂.cons ⟨rfl,enc_mono pa2 pb2 encF⟩ pairs
      · refine ⟨none,?_,by simp⟩
        simp only [usize_max_val,alloc.vec.Vec.length,room,↓reduceIte]
        rfl
  · refine ⟨some (atoms,bases,out),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro atoms' bases' out' same
    simp only [Option.some.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl,rfl⟩ := same
    refine ⟨List.prefix_refl _,List.prefix_refl _,ok,[],by simp,?_⟩
    rw [List.drop_eq_nil_iff.mpr (show facts.val.length ≤ index.val by omega)]
    exact List.Forall₂.nil
termination_by facts.val.length - index.val
decreasing_by omega

theorem encode_definitions_correct (h : hierarchy.RoleHierarchy) (chs : alloc.vec.Vec role_chains.Chain)
    (definitions : alloc.vec.Vec completion.Definition) (index : Usize) (atoms : alloc.vec.Vec role_chains.Atom)
    (bases : alloc.vec.Vec concepts.Concept) (out : alloc.vec.Vec completion.Definition)
    (ok : TableOk atoms.val bases.val)
    (fits : ∀ d ∈ definitions.val.drop index.val, Fits h chs.val d.concept) :
    ∃ o, role_chains.encode_definitions h chs definitions index atoms bases out = .ok o ∧
      ∀ atoms' bases' out', o = some (atoms',bases',out') →
        atoms.val <+: atoms'.val ∧ bases.val <+: bases'.val ∧ TableOk atoms'.val bases'.val ∧
        ∃ enc, out'.val = out.val ++ enc ∧
          List.Forall₂ (fun (d e : completion.Definition) => e.class = d.class ∧
            Enc h chs.val atoms'.val bases'.val true d.concept e.concept) (definitions.val.drop index.val) enc := by
  rw [role_chains.encode_definitions]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : definitions.val.drop index.val = definitions.val[index.val] :: definitions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    set d := definitions.val[index.val] with dIs
    have fitsD : Fits h chs.val d.concept := fits d (by rw [split]; exact List.mem_cons_self)
    obtain ⟨oe,runE,specE⟩ := encode_correct h chs d.concept fitsD true atoms bases ok
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,runE]
    cases oe with
    | none => exact ⟨none,rfl,by simp⟩
    | some triple =>
      obtain ⟨atoms1,bases1,D⟩ := triple
      obtain ⟨pa1,pb1,ok1,encD,_⟩ := specE _ _ _ rfl
      by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out ({ «class» := d.class, concept := D } : completion.Definition) room)
        obtain ⟨o,run,spec⟩ := encode_definitions_correct h chs definitions index' atoms1 bases1 pushed ok1 (by
          intro g member
          rw [nextIndex] at member
          exact fits g (by rw [split]; exact List.mem_cons_of_mem _ member))
        refine ⟨o,?_,?_⟩
        · simp only [usize_max_val,alloc.vec.Vec.length,room,↓reduceIte]
          show (do
            let i2 ← nnf.copy_iri d.class.iri
            let out1 ← out.push { «class» := { iri := i2 }, concept := D }
            let i3 ← index + 1#usize
            role_chains.encode_definitions h chs definitions i3 atoms1 bases1 out1) = Result.ok o
          simp only [Rowl.Nnf.copy_iri_identity,bind_ok,push,advance,run]
        · intro atoms' bases' out' same
          obtain ⟨pa2,pb2,ok2,enc,outIs,pairs⟩ := spec atoms' bases' out' same
          refine ⟨pa1.trans pa2,pb1.trans pb2,ok2,{ «class» := d.class, concept := D } :: enc,
            by rw [outIs,contents]; simp,?_⟩
          rw [split]
          rw [nextIndex] at pairs
          exact List.Forall₂.cons ⟨rfl,enc_mono pa2 pb2 encD⟩ pairs
      · refine ⟨none,?_,by simp⟩
        simp only [usize_max_val,alloc.vec.Vec.length,room,↓reduceIte]
        rfl
  · refine ⟨some (atoms,bases,out),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro atoms' bases' out' same
    simp only [Option.some.injEq,Prod.mk.injEq] at same
    obtain ⟨rfl,rfl,rfl⟩ := same
    refine ⟨List.prefix_refl _,List.prefix_refl _,ok,[],by simp,?_⟩
    rw [List.drop_eq_nil_iff.mpr (show definitions.val.length ≤ index.val by omega)]
    exact List.Forall₂.nil
termination_by definitions.val.length - index.val
decreasing_by omega

end Rowl.ChainOps
