import Rowl.ShiParts

/-!
The role hierarchy of an axiom closure, proved against the independent Direct
Semantics. The kernel reads every inclusion without chains, equivalence,
inverse, symmetry and transitivity axiom on object property expressions, named
or inverse. Every inclusion is added with its inverse, each together with its
compositions with the inclusions already listed, skipping the inclusions the
hierarchy already has, and every transitive role with its inverse. The result
is closed under composition and inverses, as the completion graph tableau
requires, and an interpretation respects it exactly when it satisfies every role
axiom of the closure.
-/
namespace Rowl.ShiRoles
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv inverse_correct copy_role_identity same_role_correct)
open Rowl.Hierarchy (Below Closed Respects inclusionList transitives below_refl respects_below below_correct
  is_transitive_correct closed_of_empty)
open Rowl.ShiParts (RoleAxiom)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- What the role axioms of a closure require: every role axiom holds. -/
def RolesHold {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (items : List AnnotatedAxiom) :
    Prop :=
  ∀ a ∈ items, RoleAxiom a.axiom → Rowl.Owl.satisfies I a.axiom

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The roles listed below `sup` from `index` are found, after `found`. -/
theorem subs_from_correct (inclusions : alloc.vec.Vec hierarchy.Inclusion) (index : Usize)
    (sup : ObjectPropertyExpression) (found : alloc.vec.Vec ObjectPropertyExpression) :
    ∃ result, shi_ontology.subs_from inclusions index sup found = .ok result ∧
      ∀ out, result = some out → ∀ x, x ∈ out.val ↔
        x ∈ found.val ∨ ∃ i ∈ inclusions.val.drop index.val, i.sup = sup ∧ i.sub = x := by
  rw [shi_ontology.subs_from]
  by_cases more : index.val < inclusions.val.length
  · have lookup : inclusions.index_usize index = .ok inclusions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : inclusions.val.drop index.val = inclusions.val[index.val] :: inclusions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases hit : inclusions.val[index.val].sup = sup
    · by_cases room : found.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec found inclusions.val[index.val].sub room)
        obtain ⟨result,run,spec⟩ := subs_from_correct inclusions next sup appended
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,same_role_correct,hit,decide_true,usize_max_val,room,copy_role_identity,push,advance,run]
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
          lookup,bind_ok,same_role_correct,hit,decide_true,usize_max_val,room]
    · obtain ⟨result,run,spec⟩ := subs_from_correct inclusions next sup found
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,same_role_correct,hit,decide_false,Bool.false_eq_true,advance,run]
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

/-- The roles listed above `sub` from `index` are found, after `found`. -/
theorem sups_from_correct (inclusions : alloc.vec.Vec hierarchy.Inclusion) (index : Usize)
    (sub : ObjectPropertyExpression) (found : alloc.vec.Vec ObjectPropertyExpression) :
    ∃ result, shi_ontology.sups_from inclusions index sub found = .ok result ∧
      ∀ out, result = some out → ∀ x, x ∈ out.val ↔
        x ∈ found.val ∨ ∃ i ∈ inclusions.val.drop index.val, i.sub = sub ∧ i.sup = x := by
  rw [shi_ontology.sups_from]
  by_cases more : index.val < inclusions.val.length
  · have lookup : inclusions.index_usize index = .ok inclusions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : inclusions.val.drop index.val = inclusions.val[index.val] :: inclusions.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases hit : inclusions.val[index.val].sub = sub
    · by_cases room : found.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec found inclusions.val[index.val].sup room)
        obtain ⟨result,run,spec⟩ := sups_from_correct inclusions next sub appended
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,same_role_correct,hit,decide_true,usize_max_val,room,copy_role_identity,push,advance,run]
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
          lookup,bind_ok,same_role_correct,hit,decide_true,usize_max_val,room]
    · obtain ⟨result,run,spec⟩ := sups_from_correct inclusions next sub found
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,same_role_correct,hit,decide_false,Bool.false_eq_true,advance,run]
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

/-- One row: `sub` below every role listed above from `index`, skipping the
    inclusions the hierarchy already has; the old inclusions stay in front and
    the transitive roles are kept. -/
theorem row_from_correct (sub : ObjectPropertyExpression) (above : alloc.vec.Vec ObjectPropertyExpression)
    (index : Usize) (h : hierarchy.RoleHierarchy) :
    ∃ result, shi_ontology.row_from sub above index h = .ok result ∧
      ∀ h', result = some h' → h'.transitive = h.transitive ∧ (∃ more, h'.inclusions.val = h.inclusions.val ++ more) ∧
        ∀ a b, Below h' a b ↔ Below h a b ∨ (a = sub ∧ b ∈ above.val.drop index.val) := by
  rw [shi_ontology.row_from]
  by_cases more : index.val < above.val.length
  · have lookup : above.index_usize index = .ok above.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : above.val.drop index.val = above.val[index.val] :: above.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    by_cases already : Below h sub above.val[index.val]
    · obtain ⟨result,run,spec⟩ := row_from_correct sub above next h
      refine ⟨result,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,below_correct,already,decide_true,advance,run]
      · intro h' same
        obtain ⟨transitive,⟨extra,grows⟩,belowIff⟩ := spec h' same
        refine ⟨transitive,⟨extra,grows⟩,?_⟩
        intro a b
        rw [belowIff,nextIndex,split]
        simp only [List.mem_cons]
        constructor
        · rintro (old | ⟨first,later⟩)
          · exact .inl old
          · exact .inr ⟨first,.inr later⟩
        · rintro (old | ⟨rfl,(rfl | later)⟩)
          · exact .inl old
          · exact .inl already
          · exact .inr ⟨rfl,later⟩
    · by_cases room : h.inclusions.val.length < Usize.max
      · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec h.inclusions ⟨sub,above.val[index.val]⟩ room)
        obtain ⟨result,run,spec⟩ := row_from_correct sub above next { h with inclusions := appended }
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,below_correct,already,decide_false,Bool.false_eq_true,usize_max_val,room,
            copy_role_identity,push,advance,run]
        · intro h' same
          obtain ⟨transitive,⟨extra,grows⟩,belowIff⟩ := spec h' same
          refine ⟨transitive,⟨⟨sub,above.val[index.val]⟩ :: extra,by rw [grows,contents]; simp⟩,?_⟩
          intro a b
          rw [belowIff,nextIndex,split]
          simp only [Below,inclusionList,contents,List.map_append,List.mem_append,List.map_cons,List.map_nil,
            List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
          tauto
      · refine ⟨none,?_,by intro h' impossible; cases impossible⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,below_correct,already,decide_false,Bool.false_eq_true,usize_max_val,room]
  · have empty : above.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some h,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro h' same
    cases same
    exact ⟨rfl,⟨[],by simp⟩,by simp [empty]⟩
termination_by above.val.length - index.val
decreasing_by all_goals omega

/-- Every role listed below, from `index`, below every role listed above. -/
theorem pairs_from_correct (lower : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (above : alloc.vec.Vec ObjectPropertyExpression) (h : hierarchy.RoleHierarchy) :
    ∃ result, shi_ontology.pairs_from lower index above h = .ok result ∧
      ∀ h', result = some h' → h'.transitive = h.transitive ∧ (∃ more, h'.inclusions.val = h.inclusions.val ++ more) ∧
        ∀ a b, Below h' a b ↔ Below h a b ∨ (a ∈ lower.val.drop index.val ∧ b ∈ above.val) := by
  rw [shi_ontology.pairs_from]
  by_cases more : index.val < lower.val.length
  · have lookup : lower.index_usize index = .ok lower.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : lower.val.drop index.val = lower.val[index.val] :: lower.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨row,rowRun,rowSpec⟩ := row_from_correct lower.val[index.val] above 0#usize h
    cases row with
    | none =>
      exact ⟨none,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,rowRun],by intro h' impossible; cases impossible⟩
    | some h1 =>
      obtain ⟨rowTransitive,⟨rowExtra,rowGrows⟩,rowBelow⟩ := rowSpec h1 rfl
      obtain ⟨result,run,spec⟩ := pairs_from_correct lower next above h1
      refine ⟨result,by simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,bind_ok,rowRun,advance,run],?_⟩
      intro h' same
      obtain ⟨transitive,⟨extra,grows⟩,belowIff⟩ := spec h' same
      refine ⟨transitive.trans rowTransitive,⟨rowExtra ++ extra,by rw [grows,rowGrows]; simp⟩,?_⟩
      intro a b
      rw [belowIff,rowBelow,nextIndex,split]
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
  · have empty : lower.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some h,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro h' same
    cases same
    exact ⟨rfl,⟨[],by simp⟩,by simp [empty]⟩
termination_by lower.val.length - index.val
decreasing_by all_goals omega

/-- Adding one inclusion with its compositions: afterwards a role is below
    another when it was, or when it was below the new sub-role and the new
    super-role below the other. -/
theorem add_one_correct (h : hierarchy.RoleHierarchy) (sub sup : ObjectPropertyExpression) :
    ∃ result, shi_ontology.add_one h sub sup = .ok result ∧
      ∀ h', result = some h' → h'.transitive = h.transitive ∧ (∃ more, h'.inclusions.val = h.inclusions.val ++ more) ∧
        ∀ a b, Below h' a b ↔ Below h a b ∨ (Below h a sub ∧ Below h sup b) := by
  rw [shi_ontology.add_one]
  obtain ⟨start,startPush,startContents⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectPropertyExpression) sub (by simp; scalar_tac))
  obtain ⟨lowerResult,lowerRun,lowerSpec⟩ := subs_from_correct h.inclusions 0#usize sub start
  cases lowerResult with
  | none => exact ⟨none,by simp [copy_role_identity,startPush,lowerRun],by intro h' impossible; cases impossible⟩
  | some lower =>
    obtain ⟨finish,finishPush,finishContents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectPropertyExpression) sup (by simp; scalar_tac))
    obtain ⟨upperResult,upperRun,upperSpec⟩ := sups_from_correct h.inclusions 0#usize sup finish
    cases upperResult with
    | none =>
      exact ⟨none,by simp [copy_role_identity,startPush,lowerRun,finishPush,upperRun],
        by intro h' impossible; cases impossible⟩
    | some upper =>
      obtain ⟨pairsResult,pairsRun,pairsSpec⟩ := pairs_from_correct lower 0#usize upper h
      refine ⟨pairsResult,by simp [copy_role_identity,startPush,lowerRun,finishPush,upperRun,pairsRun],?_⟩
      intro h' same
      obtain ⟨transitive,grows,belowIff⟩ := pairsSpec h' same
      refine ⟨transitive,grows,?_⟩
      have lowerIff : ∀ x, x ∈ lower.val ↔ Below h x sub := by
        intro x
        rw [lowerSpec lower rfl x,startContents]
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero,Below,inclusionList,List.mem_map]
        constructor
        · rintro (same | ⟨i,member,first,second⟩)
          · simp at same; exact .inl same
          · exact .inr ⟨i,member,by rw [first,second]⟩
        · rintro (same | ⟨i,member,pair⟩)
          · exact .inl (by simp [same])
          · simp only [Prod.mk.injEq] at pair
            exact .inr ⟨i,member,pair.2,pair.1⟩
      have upperIff : ∀ y, y ∈ upper.val ↔ Below h sup y := by
        intro y
        rw [upperSpec upper rfl y,finishContents]
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero,Below,inclusionList,List.mem_map]
        constructor
        · rintro (same | ⟨i,member,first,second⟩)
          · simp at same; exact .inl same.symm
          · exact .inr ⟨i,member,by rw [first,second]⟩
        · rintro (same | ⟨i,member,pair⟩)
          · exact .inl (by simp [same])
          · simp only [Prod.mk.injEq] at pair
            exact .inr ⟨i,member,pair.1,pair.2⟩
      intro a b
      rw [belowIff,show (0#usize).val = 0 from rfl,List.drop_zero,lowerIff,upperIff]

/-- Composition stays closed when an inclusion is added with its compositions. -/
theorem composed_added {h h' : hierarchy.RoleHierarchy} {sub sup : ObjectPropertyExpression}
    (composed : ∀ a b c, Below h a b → Below h b c → Below h a c)
    (spec : ∀ a b, Below h' a b ↔ Below h a b ∨ (Below h a sub ∧ Below h sup b)) :
    ∀ a b c, Below h' a b → Below h' b c → Below h' a c := by
  intro a b c first second
  rw [spec] at first second ⊢
  rcases first with old | ⟨aBelow,bAbove⟩ <;> rcases second with old' | ⟨bBelow,cAbove⟩
  · exact .inl (composed a b c old old')
  · exact .inr ⟨composed a b sub old bBelow,cAbove⟩
  · exact .inr ⟨aBelow,composed sup b c bAbove old'⟩
  · exact .inr ⟨aBelow,cAbove⟩

/-- Adding an inclusion and then its inverse, each with its compositions, keeps
    a hierarchy closed. -/
theorem closed_both_added {h h1 h2 : hierarchy.RoleHierarchy} {sub sup : ObjectPropertyExpression}
    (closed : Closed h) (transitive1 : h1.transitive = h.transitive) (transitive2 : h2.transitive = h1.transitive)
    (spec1 : ∀ a b, Below h1 a b ↔ Below h a b ∨ (Below h a sub ∧ Below h sup b))
    (spec2 : ∀ a b, Below h2 a b ↔ Below h1 a b ∨ (Below h1 a (inv sub) ∧ Below h1 (inv sup) b)) :
    Closed h2 := by
  have composed1 := composed_added closed.1 spec1
  have composed2 := composed_added composed1 spec2
  have flip : ∀ a b, Below h a b → Below h (inv a) (inv b) := closed.2.1
  have flip' : ∀ a b, Below h (inv a) b → Below h a (inv b) := by
    intro a b below
    have := flip _ _ below
    rwa [Rowl.Concepts.inv_inv] at this
  have flipR : ∀ a b, Below h a (inv b) → Below h (inv a) b := by
    intro a b below
    have := flip _ _ below
    rwa [Rowl.Concepts.inv_inv] at this
  have lift1 : ∀ a b, Below h a b → Below h1 a b := fun a b below => (spec1 a b).mpr (.inl below)
  have lift2 : ∀ a b, Below h1 a b → Below h2 a b := fun a b below => (spec2 a b).mpr (.inl below)
  have lift : ∀ a b, Below h a b → Below h2 a b := fun a b below => lift2 a b (lift1 a b below)
  have new1 : Below h1 sub sup := (spec1 sub sup).mpr (.inr ⟨below_refl h sub,below_refl h sup⟩)
  have new2 : Below h2 (inv sub) (inv sup) :=
    (spec2 _ _).mpr (.inr ⟨below_refl h1 _,below_refl h1 _⟩)
  -- Everything below `inv sub` in `h1` has its inverse below `sub` in `h2`, and
  -- everything above `inv sup` in `h1` has its inverse above `sup` in `h2`.
  have down : ∀ a, Below h1 a (inv sub) → Below h2 (inv a) sub := by
    intro a below
    rcases (spec1 a (inv sub)).mp below with old | ⟨aBelow,supBelow⟩
    · exact lift _ _ (flipR _ _ old)
    · -- inv a ≤ inv sub ≤ inv sup ≤ sub
      refine composed2 _ _ _ (lift _ _ (flip _ _ aBelow)) (composed2 _ _ _ new2 ?_)
      exact lift _ _ (flipR _ _ supBelow)
  have up : ∀ b, Below h1 (inv sup) b → Below h2 sup (inv b) := by
    intro b below
    rcases (spec1 (inv sup) b).mp below with old | ⟨supBelow,bAbove⟩
    · exact lift _ _ (flip' _ _ old)
    · -- sup ≤ inv sub ≤ inv sup ≤ inv b
      refine composed2 _ _ _ (lift _ _ (flip' _ _ supBelow)) (composed2 _ _ _ new2 ?_)
      exact lift _ _ (flip _ _ bAbove)
  refine ⟨composed2,?_,?_⟩
  · intro a b below
    rcases (spec2 a b).mp below with first | ⟨aBelow,bAbove⟩
    · rcases (spec1 a b).mp first with old | ⟨aSub,supB⟩
      · exact lift _ _ (flip _ _ old)
      · exact composed2 _ _ _ (lift _ _ (flip _ _ aSub)) (composed2 _ _ _ new2 (lift _ _ (flip _ _ supB)))
    · exact composed2 _ _ _ (down a aBelow) (composed2 _ _ _ (lift2 _ _ new1) (up b bAbove))
  · intro t member
    have : transitives h2 = transitives h := by simp [transitives,transitive2,transitive1]
    rw [this] at member ⊢
    exact closed.2.2 t member

/-- An interpretation respects the hierarchy with an added inclusion and its
    compositions exactly when it respects the old one and the inclusion. -/
theorem respects_added {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    {h h' : hierarchy.RoleHierarchy} {sub sup : ObjectPropertyExpression} (transitive : h'.transitive = h.transitive)
    (grows : ∃ more, h'.inclusions.val = h.inclusions.val ++ more)
    (spec : ∀ a b, Below h' a b ↔ Below h a b ∨ (Below h a sub ∧ Below h sup b)) :
    Respects I h' ↔ Respects I h ∧ ∀ x y, objectRelation I sub x y → objectRelation I sup x y := by
  have transitivesSame : transitives h' = transitives h := by simp [transitives,transitive]
  obtain ⟨more,grows⟩ := grows
  constructor
  · rintro ⟨inclusions,transitives'⟩
    refine ⟨⟨fun s r listed => inclusions s r ?_,by rwa [transitivesSame] at transitives'⟩,?_⟩
    · simp only [inclusionList,grows,List.map_append,List.mem_append]
      exact .inl listed
    · intro x y edge
      exact respects_below ⟨inclusions,transitives'⟩
        ((spec sub sup).mpr (.inr ⟨below_refl h sub,below_refl h sup⟩)) edge
  · rintro ⟨respects,added⟩
    refine ⟨?_,by rw [transitivesSame]; exact respects.2⟩
    intro s r listed x y edge
    rcases (spec s r).mp (.inr listed) with old | ⟨below,above⟩
    · exact respects_below respects old edge
    · exact respects_below respects above (added x y (respects_below respects below edge))

/-- Adding an inclusion with its inverse. -/
theorem add_inclusion_correct (h : hierarchy.RoleHierarchy) (closed : Closed h) (sub sup : ObjectPropertyExpression) :
    ∃ result, shi_ontology.add_inclusion h sub sup = .ok result ∧
      ∀ h', result = some h' → Closed h' ∧ h'.transitive = h.transitive ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I h' ↔ Respects I h ∧ ∀ x y, objectRelation I sub x y → objectRelation I sup x y) := by
  rw [shi_ontology.add_inclusion]
  obtain ⟨first,firstRun,firstSpec⟩ := add_one_correct h sub sup
  cases first with
  | none => exact ⟨none,by simp [firstRun],by intro h' impossible; cases impossible⟩
  | some h1 =>
    obtain ⟨transitive1,grows1,spec1⟩ := firstSpec h1 rfl
    obtain ⟨second,secondRun,secondSpec⟩ := add_one_correct h1 (inv sub) (inv sup)
    refine ⟨second,by simp [firstRun,inverse_correct,secondRun],?_⟩
    intro h' same
    obtain ⟨transitive2,grows2,spec2⟩ := secondSpec h' same
    refine ⟨closed_both_added closed transitive1 transitive2 spec1 spec2,transitive2.trans transitive1,?_⟩
    intro Object Value I
    rw [respects_added I transitive2 grows2 spec2,respects_added I transitive1 grows1 spec1]
    simp only [relation_inv]
    constructor
    · rintro ⟨⟨respects,forward⟩,_⟩
      exact ⟨respects,forward⟩
    · rintro ⟨respects,forward⟩
      exact ⟨⟨respects,forward⟩,fun x y edge => forward y x edge⟩

/-- Adding both inclusions between two roles. -/
theorem add_equal_correct (h : hierarchy.RoleHierarchy) (closed : Closed h) (left right : ObjectPropertyExpression) :
    ∃ result, shi_ontology.add_equal h left right = .ok result ∧
      ∀ h', result = some h' → Closed h' ∧ h'.transitive = h.transitive ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I h' ↔ Respects I h ∧ ∀ x y, (objectRelation I left x y ↔ objectRelation I right x y)) := by
  rw [shi_ontology.add_equal]
  obtain ⟨first,firstRun,firstSpec⟩ := add_inclusion_correct.{u,v} h closed left right
  cases first with
  | none => exact ⟨none,by simp [firstRun],by intro h' impossible; cases impossible⟩
  | some h1 =>
    obtain ⟨closed1,transitive1,meaning1⟩ := firstSpec h1 rfl
    obtain ⟨second,secondRun,secondSpec⟩ := add_inclusion_correct.{u,v} h1 closed1 right left
    refine ⟨second,by simp [firstRun,secondRun],?_⟩
    intro h' same
    obtain ⟨closed2,transitive2,meaning2⟩ := secondSpec h' same
    refine ⟨closed2,transitive2.trans transitive1,?_⟩
    intro Object Value I
    rw [meaning2 Object Value I,meaning1 Object Value I]
    constructor
    · rintro ⟨⟨respects,forward⟩,backward⟩
      exact ⟨respects,fun x y => ⟨forward x y,backward x y⟩⟩
    · rintro ⟨respects,same⟩
      exact ⟨⟨respects,fun x y => (same x y).mp⟩,fun x y => (same x y).mpr⟩

/-- Equality with the first role, role by role. -/
theorem same_from_correct (first : ObjectPropertyExpression) (values : alloc.vec.Vec ObjectPropertyExpression)
    (index : Usize) (h : hierarchy.RoleHierarchy) (closed : Closed h) :
    ∃ result, shi_ontology.same_from first values index h = .ok result ∧
      ∀ h', result = some h' → Closed h' ∧ h'.transitive = h.transitive ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I h' ↔ Respects I h ∧
            ∀ e ∈ values.val.drop index.val, ∀ x y, (objectRelation I first x y ↔ objectRelation I e x y)) := by
  rw [shi_ontology.same_from]
  by_cases more : index.val < values.val.length
  · have lookup : values.index_usize index = .ok values.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : values.val.drop index.val = values.val[index.val] :: values.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨here,hereRun,hereSpec⟩ := add_equal_correct.{u,v} h closed first values.val[index.val]
    cases here with
    | none => exact ⟨none,by simp [more,lookup,hereRun],by intro h' impossible; cases impossible⟩
    | some h1 =>
      obtain ⟨closed1,transitive1,meaning1⟩ := hereSpec h1 rfl
      obtain ⟨rest,restRun,restSpec⟩ := same_from_correct first values next h1 closed1
      refine ⟨rest,by simp [more,lookup,hereRun,advance,restRun],?_⟩
      intro h' same
      obtain ⟨closed2,transitive2,meaning2⟩ := restSpec h' same
      refine ⟨closed2,transitive2.trans transitive1,?_⟩
      intro Object Value I
      rw [meaning2 Object Value I,meaning1 Object Value I,nextIndex,split]
      simp only [List.forall_mem_cons]
      tauto
  · have empty : values.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some h,by simp [more],?_⟩
    intro h' same
    cases same
    exact ⟨closed,rfl,fun Object Value I => by simp [empty]⟩
termination_by values.val.length - index.val
decreasing_by all_goals omega

/-- Roles are all equal exactly when each equals the first. -/
theorem all_equal_roles {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (first : ObjectPropertyExpression) (others : List ObjectPropertyExpression) :
    Rowl.Owl.allEqual (first :: others) (objectRelation I) ↔
      ∀ e ∈ others, ∀ x y, (objectRelation I first x y ↔ objectRelation I e x y) := by
  unfold Rowl.Owl.allEqual
  constructor
  · intro same e member x y
    rw [same first (List.mem_cons_self ..) e (List.mem_cons_of_mem _ member)]
  · intro same a aIn b bIn
    have toFirst : ∀ c ∈ first :: others, objectRelation I c = objectRelation I first := by
      intro c member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · funext x y
        exact propext (same c later x y).symm
    rw [toFirst a aIn,toFirst b bIn]

/-- Adding an equivalence of roles. -/
theorem add_equivalent_correct (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (members : AtLeastTwo ObjectPropertyExpression) :
    ∃ result, shi_ontology.add_equivalent h members = .ok result ∧
      ∀ h', result = some h' → Closed h' ∧ h'.transitive = h.transitive ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I h' ↔ Respects I h ∧ Rowl.Owl.allEqual members.elements (objectRelation I)) := by
  rw [shi_ontology.add_equivalent]
  obtain ⟨first,firstRun,firstSpec⟩ := add_equal_correct.{u,v} h closed members.first members.second
  cases first with
  | none => exact ⟨none,by simp [firstRun],by intro h' impossible; cases impossible⟩
  | some h1 =>
    obtain ⟨closed1,transitive1,meaning1⟩ := firstSpec h1 rfl
    obtain ⟨rest,restRun,restSpec⟩ := same_from_correct.{u,v} members.first members.rest 0#usize h1 closed1
    refine ⟨rest,by simp [firstRun,restRun],?_⟩
    intro h' same
    obtain ⟨closed2,transitive2,meaning2⟩ := restSpec h' same
    refine ⟨closed2,transitive2.trans transitive1,?_⟩
    intro Object Value I
    rw [meaning2 Object Value I,meaning1 Object Value I]
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero,AtLeastTwo.elements]
    rw [all_equal_roles,List.forall_mem_cons]
    tauto

/-- Adding a transitive role with its inverse, unless it is listed. -/
theorem add_transitive_correct (h : hierarchy.RoleHierarchy) (closed : Closed h) (role : ObjectPropertyExpression) :
    ∃ result, shi_ontology.add_transitive h role = .ok result ∧
      ∀ h', result = some h' → Closed h' ∧ h'.inclusions = h.inclusions ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I h' ↔ Respects I h ∧ ∀ x y z, objectRelation I role x y → objectRelation I role y z →
            objectRelation I role x z) := by
  rw [shi_ontology.add_transitive]
  by_cases listed : role ∈ transitives h
  · refine ⟨some h,by simp [is_transitive_correct,listed],?_⟩
    intro h' same
    cases same
    exact ⟨closed,rfl,fun Object Value I => ⟨fun respects => ⟨respects,respects.2 role listed⟩,fun both => both.1⟩⟩
  · by_cases room : h.transitive.val.length < Usize.max - 1
    · obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec h.transitive role (by omega))
      obtain ⟨twice,push2,contents2⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec appended (inv role) (by rw [contents]; simp; omega))
      obtain ⟨limit,limitRun,limitValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize) (by simp [usize_max_val]; scalar_tac))
      have limitIs : limit.val = Usize.max - 1 := by
        have := limitValue
        simp [usize_max_val] at this
        exact this.1
      refine ⟨some { h with transitive := twice },?_,?_⟩
      · simp only [is_transitive_correct,listed,decide_false,Bool.false_eq_true,↓reduceIte,bind_ok,limitRun,
          alloc.vec.Vec.len_val,UScalar.lt_equiv,limitIs,room,copy_role_identity,push,inverse_correct,push2]
      · intro h' same
        cases same
        have listing : transitives { h with transitive := twice } = transitives h ++ [role,inv role] := by
          simp [transitives,contents2,contents]
        refine ⟨⟨closed.1,closed.2.1,?_⟩,rfl,?_⟩
        · intro t member
          rw [listing] at member ⊢
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
          rcases member with old | rfl | rfl
          · exact .inl (closed.2.2 t old)
          · exact .inr (.inr rfl)
          · rw [Rowl.Concepts.inv_inv]
            exact .inr (.inl rfl)
        · intro Object Value I
          simp only [Respects,listing,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
          have inclusionsSame : inclusionList { h with transitive := twice } = inclusionList h := rfl
          rw [inclusionsSame]
          constructor
          · rintro ⟨inclusions,transitive⟩
            exact ⟨⟨inclusions,fun t member => transitive t (.inl member)⟩,transitive role (.inr (.inl rfl))⟩
          · rintro ⟨⟨inclusions,transitive⟩,added⟩
            refine ⟨inclusions,?_⟩
            rintro t (old | rfl | rfl)
            · exact transitive t old
            · exact added
            · intro x y z first second
              rw [relation_inv] at first second ⊢
              exact added z y x second first
    · obtain ⟨limit,limitRun,limitValue⟩ := WP.spec_imp_exists
        (Usize.sub_spec (x := core.num.Usize.MAX) (y := 1#usize) (by simp [usize_max_val]; scalar_tac))
      have limitIs : limit.val = Usize.max - 1 := by
        have := limitValue
        simp [usize_max_val] at this
        exact this.1
      refine ⟨none,?_,by intro h' impossible; cases impossible⟩
      simp only [is_transitive_correct,listed,decide_false,Bool.false_eq_true,↓reduceIte,bind_ok,limitRun,
        alloc.vec.Vec.len_val,UScalar.lt_equiv,limitIs,room]

/-- The role hierarchy with the role axioms of `items[index..]`: it stays
    closed, and an interpretation respects it exactly when it respects the
    hierarchy it started from and satisfies those role axioms. -/
theorem hierarchy_from_correct (items : alloc.vec.Vec AnnotatedAxiom) (index : Usize) (h : hierarchy.RoleHierarchy)
    (closed : Closed h) :
    ∃ result, shi_ontology.hierarchy_from items index h = .ok result ∧
      ∀ h', result = some h' → Closed h' ∧
        ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I h' ↔ Respects I h ∧ RolesHold I (items.val.drop index.val)) := by
  rw [shi_ontology.hierarchy_from]
  by_cases more : index.val < items.val.length
  · have lookup : items.index_usize index = .ok items.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : items.val.drop index.val = items.val[index.val] :: items.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    -- After this axiom's step, the rest of the role axioms follow by recursion.
    have continuation : ∀ middle : Option hierarchy.RoleHierarchy,
        (∀ mid, middle = some mid → Closed mid ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
          (Respects I mid ↔ Respects I h ∧ (RoleAxiom items.val[index.val].axiom →
            Rowl.Owl.satisfies I items.val[index.val].axiom))) →
        ∃ result, (match middle with
          | none => (ok none : Result (Option hierarchy.RoleHierarchy))
          | some roles2 => shi_ontology.hierarchy_from items next roles2) = .ok result ∧
          ∀ h', result = some h' → Closed h' ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
            (Respects I h' ↔ Respects I h ∧ RolesHold I (items.val.drop index.val)) := by
      intro middle middleSpec
      cases middle with
      | none => exact ⟨none,rfl,by intro h' impossible; cases impossible⟩
      | some mid =>
        obtain ⟨midClosed,midMeaning⟩ := middleSpec mid rfl
        obtain ⟨result,run,spec⟩ := hierarchy_from_correct items next mid midClosed
        refine ⟨result,run,?_⟩
        intro h' same
        obtain ⟨finalClosed,meaning⟩ := spec h' same
        refine ⟨finalClosed,?_⟩
        intro Object Value I
        rw [meaning,midMeaning,nextIndex,split]
        simp only [RolesHold,List.forall_mem_cons]
        tauto
    have unchanged : ∀ (_ : ¬ RoleAxiom items.val[index.val].axiom), ∃ result,
        (match (some h : Option hierarchy.RoleHierarchy) with
          | none => (ok none : Result (Option hierarchy.RoleHierarchy))
          | some roles2 => shi_ontology.hierarchy_from items next roles2) = .ok result ∧
          ∀ h', result = some h' → Closed h' ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
            (Respects I h' ↔ Respects I h ∧ RolesHold I (items.val.drop index.val)) := by
      intro notRole
      apply continuation (some h)
      intro mid same
      cases same
      exact ⟨closed,fun Object Value I => by simp [notRole]⟩
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,advance]
    cases here : items.val[index.val].axiom with
    | SubObjectPropertyOf sub sup =>
      cases sub with
      | Single p =>
        obtain ⟨added,addRun,addSpec⟩ := add_inclusion_correct.{u,v} h closed p sup
        simp only [addRun,bind_ok]
        apply continuation added
        intro h' same
        obtain ⟨closed',_,meaning⟩ := addSpec h' same
        refine ⟨closed',fun Object Value I => ?_⟩
        rw [meaning Object Value I,here]
        simp [RoleAxiom,Rowl.Owl.satisfies,Rowl.Owl.subRelation]
      | Chain c => simp only [bind_ok]; exact unchanged (by simp [here,RoleAxiom])
    | EquivalentObjectProperties members =>
      obtain ⟨added,addRun,addSpec⟩ := add_equivalent_correct.{u,v} h closed members
      simp only [addRun,bind_ok]
      apply continuation added
      intro h' same
      obtain ⟨closed',_,meaning⟩ := addSpec h' same
      refine ⟨closed',fun Object Value I => ?_⟩
      rw [meaning Object Value I,here]
      simp [RoleAxiom,Rowl.Owl.satisfies]
    | InverseObjectProperties first second =>
      obtain ⟨added,addRun,addSpec⟩ := add_equal_correct.{u,v} h closed first (inv second)
      simp only [inverse_correct,addRun,bind_ok]
      apply continuation added
      intro h' same
      obtain ⟨closed',_,meaning⟩ := addSpec h' same
      refine ⟨closed',fun Object Value I => ?_⟩
      rw [meaning Object Value I,here]
      simp [RoleAxiom,Rowl.Owl.satisfies,relation_inv]
    | SymmetricObjectProperty role =>
      obtain ⟨added,addRun,addSpec⟩ := add_inclusion_correct.{u,v} h closed role (inv role)
      simp only [inverse_correct,addRun,bind_ok]
      apply continuation added
      intro h' same
      obtain ⟨closed',_,meaning⟩ := addSpec h' same
      refine ⟨closed',fun Object Value I => ?_⟩
      rw [meaning Object Value I,here]
      simp [RoleAxiom,Rowl.Owl.satisfies,relation_inv]
    | TransitiveObjectProperty role =>
      obtain ⟨added,addRun,addSpec⟩ := add_transitive_correct.{u,v} h closed role
      simp only [addRun,bind_ok]
      apply continuation added
      intro h' same
      obtain ⟨closed',_,meaning⟩ := addSpec h' same
      refine ⟨closed',fun Object Value I => ?_⟩
      rw [meaning Object Value I,here]
      simp [RoleAxiom,Rowl.Owl.satisfies]
    | _ => simp only [bind_ok]; exact unchanged (by simp [here,RoleAxiom])
  · have empty : items.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some h,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro h' same
    cases same
    exact ⟨closed,fun Object Value I => by simp [RolesHold,empty]⟩
termination_by items.val.length - index.val
decreasing_by all_goals omega

/-- The actual role hierarchy of a closure is closed under composition and
    inverses, and an interpretation respects it exactly when it satisfies every
    role axiom of the closure. -/
theorem role_hierarchy_correct (items : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, shi_ontology.role_hierarchy items = .ok result ∧
      ∀ h, result = some h → Closed h ∧ ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value),
        (Respects I h ↔ RolesHold I items.val) := by
  rw [shi_ontology.role_hierarchy]
  obtain ⟨result,run,spec⟩ := hierarchy_from_correct.{u,v} items 0#usize
    ⟨alloc.vec.Vec.new hierarchy.Inclusion,alloc.vec.Vec.new ObjectPropertyExpression⟩ (closed_of_empty _ rfl rfl)
  refine ⟨result,run,?_⟩
  intro h same
  obtain ⟨closed,meaning⟩ := spec h same
  refine ⟨closed,fun Object Value I => ?_⟩
  rw [meaning Object Value I]
  simp only [show (0#usize).val = 0 from rfl,List.drop_zero]
  exact ⟨fun both => both.2,fun holds => ⟨Rowl.Hierarchy.respects_of_empty I _ rfl rfl,holds⟩⟩

end Rowl.ShiRoles
