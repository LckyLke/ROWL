import Rowl.Completion

/-!
The rule search of the completion forest, proved exact. A neighbour of a node
along a role is an active child whose edge has a role included in it, the
parent of a tree node whose edge has a role whose inverse is included in it, or
a named node that a link or an added edge relates to it, read through the
merges of named nodes. The search returns the first missing concept of a node or
an edge, else a neighbour that does not decide the filler of a maximum
restriction, else a maximum restriction with too many neighbours, else an
existential or minimum restriction of an unblocked node to expand, and it
reports a complete forest exactly when none of these exists. Blocking is
pairwise: a tree node is blocked when some tree node on its path has the label,
the parent's label and the roles from the parent of a tree node above it.
-/
namespace Rowl.ForestSearch
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Concepts (inv inverse_correct copy_role_identity same_role_correct)
open Rowl.Hierarchy (Below below_correct transitives)
open Rowl.CompletionSearch (Holds holds_correct contains_correct mem_index_iff EdgeNeeds EdgeOk HasAtom
  missing_along_correct missing_unfolding_correct SameLabel same_label_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The label of a node of the forest; empty out of range. -/
def labelOf (nodes : List forest.Node) (x : Nat) : List Usize :=
  match nodes[x]? with
  | some n => n.label.val
  | none => []

/-- The named node that the individual `a` was merged into. -/
def rep (F : forest.Forest) (a : Usize) : Usize :=
  match F.same.val[a.val]? with
  | some b => b
  | none => a

theorem representative_correct (F : forest.Forest) (a : Usize) : forest.representative F a = .ok (rep F a) := by
  rw [forest.representative]
  by_cases inside : a.val < F.same.val.length
  · have lookup : F.same.index_usize a = .ok F.same.val[a.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,rep,List.getElem?_eq_getElem inside]
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,rep,List.getElem?_eq_none_iff.mpr
      (show F.same.val.length ≤ a.val by omega)]

theorem along_from_correct (h : hierarchy.RoleHierarchy) (list : alloc.vec.Vec ObjectPropertyExpression)
    (role : ObjectPropertyExpression) (forward : Bool) (index : Usize) :
    forest.along_from h list role forward index =
      .ok (decide (∃ s ∈ list.val.drop index.val, Below h (if forward then s else inv s) role)) := by
  rw [forest.along_from]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := along_from_correct h list role forward index'
    rw [nextIndex] at rest
    have here : (if forward then hierarchy.below h list.val[index.val] role
        else hierarchy.below h (inv list.val[index.val]) role) =
        .ok (decide (Below h (if forward then list.val[index.val] else inv list.val[index.val]) role)) := by
      cases forward <;> simp [below_correct]
    by_cases found : Below h (if forward then list.val[index.val] else inv list.val[index.val]) role
    · have lhs : forest.along_from h list role forward index = .ok true := by
        rw [forest.along_from]
        cases forward <;> simp_all [alloc.vec.Vec.len_val,UScalar.lt_equiv,below_correct,inverse_correct]
      rw [forest.along_from] at lhs
      rw [lhs]
      congr 1
      symm
      rw [decide_eq_true_iff,split]
      exact ⟨_,List.mem_cons_self ..,found⟩
    · have lhs : forest.along_from h list role forward index = forest.along_from h list role forward index' := by
        conv_lhs => rw [forest.along_from]
        cases forward <;> simp_all [alloc.vec.Vec.len_val,UScalar.lt_equiv,below_correct,inverse_correct]
      rw [forest.along_from] at lhs
      rw [lhs,rest,split]
      congr 1
      rw [decide_eq_decide]
      constructor
      · intro ⟨s,member,below⟩
        exact ⟨s,List.mem_cons_of_mem _ member,below⟩
      · rintro ⟨s,member,below⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact absurd below found
        · exact ⟨s,later,below⟩
  · have empty : list.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by list.val.length - index.val
decreasing_by all_goals omega

/-- Adding a node to a list of nodes keeps the list without repetitions. -/
theorem with_node_correct (out : alloc.vec.Vec Usize) (y : Usize) :
    ∃ r, forest.with_node out y = .ok r ∧ ∀ out', r = some out' →
      (∀ z, z ∈ out'.val ↔ z ∈ out.val ∨ z = y) ∧ (out.val.Nodup → out'.val.Nodup) := by
  rw [forest.with_node,contains_correct]
  by_cases listed : y ∈ out.val
  · refine ⟨some out,by simp [listed],?_⟩
    intro out' same
    cases same
    refine ⟨?_,id⟩
    intro z
    constructor
    · exact .inl
    · rintro (member | rfl)
      · exact member
      · exact listed
  · by_cases room : out.val.length < Usize.max
    · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out y room)
      refine ⟨some pushed,by simp [listed,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room,push],?_⟩
      intro out' same
      cases same
      rw [contents]
      refine ⟨?_,fun nodup => List.nodup_append.mpr ⟨nodup,List.nodup_singleton y,?_⟩⟩
      · intro z
        simp
      · intro a member b other
        simp only [List.mem_singleton] at other
        subst other
        rintro rfl
        exact listed member
    · exact ⟨none,by simp [listed,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room],by simp⟩

/-- `y` is an active tree node below `x` whose edge from `x` has a role included
    in `r`. -/
def ChildAlong (h : hierarchy.RoleHierarchy) (nodes : List forest.Node) (x : Nat) (r : ObjectPropertyExpression)
    (y : Nat) : Prop :=
  ∃ n, nodes[y]? = some n ∧ n.tree = true ∧ n.active = true ∧ n.parent.val = x ∧ ∃ s ∈ n.roles.val, Below h s r

/-- `y` is the parent of the tree node `x`, whose edge has a role whose inverse is
    included in `r`. -/
def ParentAlong (h : hierarchy.RoleHierarchy) (nodes : List forest.Node) (x : Nat) (r : ObjectPropertyExpression)
    (y : Nat) : Prop :=
  ∃ n, nodes[x]? = some n ∧ n.tree = true ∧ n.parent.val = y ∧ ∃ s ∈ n.roles.val, Below h (inv s) r

theorem children_along_correct (F : forest.Forest) (h : hierarchy.RoleHierarchy) (x : Usize)
    (r : ObjectPropertyExpression) (index : Usize) (out : alloc.vec.Vec Usize) :
    ∃ res, forest.children_along F h x r index out = .ok res ∧ ∀ out', res = some out' →
      (∀ z : Usize, z ∈ out'.val ↔ z ∈ out.val ∨ (index.val ≤ z.val ∧ ChildAlong h F.nodes.val x.val r z.val)) ∧
      (out.val.Nodup → out'.val.Nodup) := by
  rw [forest.children_along]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have hereIff : ChildAlong h F.nodes.val x.val r index.val ↔
        F.nodes.val[index.val].tree = true ∧ F.nodes.val[index.val].active = true ∧
          F.nodes.val[index.val].parent = x ∧ ∃ s ∈ F.nodes.val[index.val].roles.val, Below h s r := by
      simp only [ChildAlong,List.getElem?_eq_getElem more,Option.some.injEq,exists_eq_left']
      constructor
      · rintro ⟨tree,active,parent,found⟩
        exact ⟨tree,active,UScalar.eq_of_val_eq parent,found⟩
      · rintro ⟨tree,active,parent,found⟩
        exact ⟨tree,active,by rw [parent],found⟩
    have hereRun : (if F.nodes.val[index.val].tree then
        if F.nodes.val[index.val].active then
          if F.nodes.val[index.val].parent = x then
            forest.along_from h F.nodes.val[index.val].roles r true 0#usize
          else .ok false
        else .ok false
      else .ok false) = .ok (decide (ChildAlong h F.nodes.val x.val r index.val)) := by
      rw [hereIff,along_from_correct]
      by_cases tree : F.nodes.val[index.val].tree = true <;>
      by_cases active : F.nodes.val[index.val].active = true <;>
      by_cases parent : F.nodes.val[index.val].parent = x <;> simp [tree,active,parent]
    by_cases here : ChildAlong h F.nodes.val x.val r index.val
    · obtain ⟨pushed,pushRun,pushSpec⟩ := with_node_correct out index
      cases pushed with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun,here,decide_true,pushRun]
      | some out1 =>
        obtain ⟨members1,nodup1⟩ := pushSpec out1 rfl
        obtain ⟨res,run,spec⟩ := children_along_correct F h x r index' out1
        refine ⟨res,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,hereRun,here,decide_true,pushRun,advance,run]
        · intro out' same
          obtain ⟨members,nodup⟩ := spec out' same
          refine ⟨?_,fun start => nodup (nodup1 start)⟩
          intro z
          rw [members,members1,nextIndex]
          constructor
          · rintro ((old | rfl) | ⟨low,child⟩)
            · exact .inl old
            · exact .inr ⟨le_refl _,here⟩
            · exact .inr ⟨by omega,child⟩
          · rintro (old | ⟨low,child⟩)
            · exact .inl (.inl old)
            · by_cases same : z.val = index.val
              · exact .inl (.inr (UScalar.eq_of_val_eq same))
              · exact .inr ⟨by omega,child⟩
    · obtain ⟨res,run,spec⟩ := children_along_correct F h x r index' out
      refine ⟨res,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,hereRun,here,decide_false,Bool.false_eq_true,advance,run]
      · intro out' same
        obtain ⟨members,nodup⟩ := spec out' same
        refine ⟨?_,nodup⟩
        intro z
        rw [members,nextIndex]
        constructor
        · rintro (old | ⟨low,child⟩)
          · exact .inl old
          · exact .inr ⟨by omega,child⟩
        · rintro (old | ⟨low,child⟩)
          · exact .inl old
          · by_cases same : z.val = index.val
            · rw [same] at child; exact absurd child here
            · exact .inr ⟨by omega,child⟩
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    refine ⟨?_,id⟩
    intro z
    constructor
    · exact .inl
    · rintro (old | ⟨low,⟨n,at_z,_⟩⟩)
      · exact old
      · have := (List.getElem?_eq_some_iff.mp at_z).1
        omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

theorem parent_along_correct (F : forest.Forest) (h : hierarchy.RoleHierarchy) (x : Usize)
    (r : ObjectPropertyExpression) (out : alloc.vec.Vec Usize) :
    ∃ res, forest.parent_along F h x r out = .ok res ∧ ∀ out', res = some out' →
      (∀ z : Usize, z ∈ out'.val ↔ z ∈ out.val ∨ ParentAlong h F.nodes.val x.val r z.val) ∧
      (out.val.Nodup → out'.val.Nodup) := by
  rw [forest.parent_along]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have parentIff : ∀ z : Usize, ParentAlong h F.nodes.val x.val r z.val ↔
        F.nodes.val[x.val].tree = true ∧ z = F.nodes.val[x.val].parent ∧
          ∃ s ∈ F.nodes.val[x.val].roles.val, Below h (inv s) r := by
      intro z
      simp only [ParentAlong,List.getElem?_eq_getElem inside,Option.some.injEq,exists_eq_left']
      constructor
      · rintro ⟨tree,parent,found⟩
        exact ⟨tree,UScalar.eq_of_val_eq parent.symm,found⟩
      · rintro ⟨tree,rfl,found⟩
        exact ⟨tree,rfl,found⟩
    by_cases tree : F.nodes.val[x.val].tree = true
    · by_cases found : ∃ s ∈ F.nodes.val[x.val].roles.val, Below h (inv s) r
      · obtain ⟨pushed,pushRun,pushSpec⟩ := with_node_correct out F.nodes.val[x.val].parent
        refine ⟨pushed,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,tree,along_from_correct,show (0#usize).val = 0 from rfl,List.drop_zero,
            Bool.false_eq_true,found,decide_true,pushRun]
        · intro out' same
          obtain ⟨members,nodup⟩ := pushSpec out' same
          refine ⟨?_,nodup⟩
          intro z
          rw [members,parentIff]
          constructor
          · rintro (old | rfl)
            · exact .inl old
            · exact .inr ⟨tree,rfl,found⟩
          · rintro (old | ⟨_,rfl,_⟩)
            · exact .inl old
            · exact .inr rfl
      · refine ⟨some out,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,tree,along_from_correct,show (0#usize).val = 0 from rfl,List.drop_zero,
            Bool.false_eq_true,found,decide_false]
        · intro out' same
          cases same
          refine ⟨?_,id⟩
          intro z
          rw [parentIff]
          constructor
          · exact .inl
          · rintro (old | ⟨_,_,found'⟩)
            · exact old
            · exact absurd found' found
    · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,tree],?_⟩
      intro out' same
      cases same
      refine ⟨?_,id⟩
      intro z
      rw [parentIff]
      constructor
      · exact .inl
      · rintro (old | ⟨isTree,_⟩)
        · exact old
        · exact absurd isTree tree
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],?_⟩
    intro out' same
    cases same
    refine ⟨?_,id⟩
    intro z
    constructor
    · exact .inl
    · rintro (old | ⟨n,at_x,_⟩)
      · exact old
      · have := (List.getElem?_eq_some_iff.mp at_x).1
        omega

theorem ends_correct (h : hierarchy.RoleHierarchy) (out : alloc.vec.Vec Usize) (source target : Usize)
    (edge : ObjectPropertyExpression) (x : Usize) (r : ObjectPropertyExpression) :
    ∃ res, forest.ends h out source target edge x r = .ok res ∧ ∀ out', res = some out' →
      (∀ z, z ∈ out'.val ↔ z ∈ out.val ∨ (source = x ∧ Below h edge r ∧ z = target) ∨
        (target = x ∧ Below h (inv edge) r ∧ z = source)) ∧ (out.val.Nodup → out'.val.Nodup) := by
  rw [forest.ends]
  by_cases at_source : source = x
  · subst at_source
    by_cases forward : Below h edge r
    · obtain ⟨p1,run1,spec1⟩ := with_node_correct out target
      cases p1 with
      | none => exact ⟨none,by simp [below_correct,forward,run1],by simp⟩
      | some mid =>
        obtain ⟨m1,n1⟩ := spec1 mid rfl
        by_cases at_target : target = source
        · subst at_target
          by_cases back : Below h (inv edge) r
          · obtain ⟨p2,run2,spec2⟩ := with_node_correct mid target
            refine ⟨p2,by simp [below_correct,forward,run1,inverse_correct,back,run2],?_⟩
            intro out' same
            obtain ⟨m2,n2⟩ := spec2 out' same
            refine ⟨fun z => ?_,fun start => n2 (n1 start)⟩
            rw [m2,m1]
            simp only [forward,back,true_and]
            tauto
          · refine ⟨some mid,by simp [below_correct,forward,run1,inverse_correct,back],?_⟩
            intro out' same
            cases same
            refine ⟨fun z => ?_,n1⟩
            rw [m1]
            simp only [forward,back,true_and,false_and,or_false]
        · refine ⟨some mid,by simp [below_correct,forward,run1,at_target],?_⟩
          intro out' same
          cases same
          refine ⟨fun z => ?_,n1⟩
          rw [m1]
          simp only [forward,at_target,true_and,false_and,or_false]
    · by_cases at_target : target = source
      · subst at_target
        by_cases back : Below h (inv edge) r
        · obtain ⟨p2,run2,spec2⟩ := with_node_correct out target
          refine ⟨p2,by simp [below_correct,forward,inverse_correct,back,run2],?_⟩
          intro out' same
          obtain ⟨m2,n2⟩ := spec2 out' same
          refine ⟨fun z => ?_,n2⟩
          rw [m2]
          simp only [forward,back,true_and,false_and,false_or]
        · refine ⟨some out,by simp [below_correct,forward,inverse_correct,back],?_⟩
          intro out' same
          cases same
          exact ⟨fun z => by simp [forward,back],id⟩
      · refine ⟨some out,by simp [below_correct,forward,at_target],?_⟩
        intro out' same
        cases same
        exact ⟨fun z => by simp [forward,at_target],id⟩
  · by_cases at_target : target = x
    · subst at_target
      by_cases back : Below h (inv edge) r
      · obtain ⟨p2,run2,spec2⟩ := with_node_correct out source
        refine ⟨p2,by simp [at_source,inverse_correct,below_correct,back,run2],?_⟩
        intro out' same
        obtain ⟨m2,n2⟩ := spec2 out' same
        refine ⟨fun z => ?_,n2⟩
        rw [m2]
        simp only [at_source,back,true_and,false_and,false_or]
      · refine ⟨some out,by simp [at_source,inverse_correct,below_correct,back],?_⟩
        intro out' same
        cases same
        exact ⟨fun z => by simp [at_source,back],id⟩
    · refine ⟨some out,by simp [at_source,at_target],?_⟩
      intro out' same
      cases same
      exact ⟨fun z => by simp [at_source,at_target],id⟩

/-- A link or edge relates `x` to `y` along `r`, read through the merges. -/
def LinkAlong (h : hierarchy.RoleHierarchy) (F : forest.Forest) (links : List (ObjectPropertyExpression × Usize × Usize))
    (x : Nat) (r : ObjectPropertyExpression) (y : Nat) : Prop :=
  ∃ l ∈ links, ((rep F l.2.1).val = x ∧ Below h l.1 r ∧ (rep F l.2.2).val = y) ∨
    ((rep F l.2.2).val = x ∧ Below h (inv l.1) r ∧ (rep F l.2.1).val = y)

/-- The role and ends of the problem's links. -/
def linkEnds (links : List completion.Link) : List (ObjectPropertyExpression × Usize × Usize) :=
  links.map (fun l => (l.role,l.from,l.to))

/-- The role and ends of the added edges. -/
def edgeEnds (edges : List forest.Edge) : List (ObjectPropertyExpression × Usize × Usize) :=
  edges.map (fun e => (e.role,e.from,e.to))

theorem links_along_correct (F : forest.Forest) (h : hierarchy.RoleHierarchy) (links : alloc.vec.Vec completion.Link)
    (x : Usize) (r : ObjectPropertyExpression) (index : Usize) (out : alloc.vec.Vec Usize) :
    ∃ res, forest.links_along F h links x r index out = .ok res ∧ ∀ out', res = some out' →
      (∀ z : Usize, z ∈ out'.val ↔ z ∈ out.val ∨ LinkAlong h F (linkEnds (links.val.drop index.val)) x.val r z.val) ∧
      (out.val.Nodup → out'.val.Nodup) := by
  rw [forest.links_along]
  by_cases more : index.val < links.val.length
  · have lookup : links.index_usize index = .ok links.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : links.val.drop index.val = links.val[index.val] :: links.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨found,foundRun,foundSpec⟩ := ends_correct h out (rep F links.val[index.val].from)
      (rep F links.val[index.val].to) links.val[index.val].role x r
    cases found with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,representative_correct,foundRun]
    | some mid =>
      obtain ⟨midMembers,midNodup⟩ := foundSpec mid rfl
      obtain ⟨res,run,spec⟩ := links_along_correct F h links x r index' mid
      refine ⟨res,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,representative_correct,foundRun,advance,run]
      · intro out' same
        obtain ⟨members,nodup⟩ := spec out' same
        refine ⟨fun z => ?_,fun start => nodup (midNodup start)⟩
        rw [members,midMembers,nextIndex,split]
        simp only [LinkAlong,linkEnds,List.map_cons,List.mem_cons,exists_eq_or_imp]
        constructor
        · rintro ((old | ⟨sx,below,rfl⟩ | ⟨tx,below,rfl⟩) | rest)
          · exact .inl old
          · exact .inr (.inl (.inl ⟨by rw [sx],below,rfl⟩))
          · exact .inr (.inl (.inr ⟨by rw [tx],below,rfl⟩))
          · exact .inr (.inr rest)
        · rintro (old | (⟨sx,below,zIs⟩ | ⟨tx,below,zIs⟩) | rest)
          · exact .inl (.inl old)
          · exact .inl (.inr (.inl ⟨UScalar.eq_of_val_eq sx,below,UScalar.eq_of_val_eq zIs.symm⟩))
          · exact .inl (.inr (.inr ⟨UScalar.eq_of_val_eq tx,below,UScalar.eq_of_val_eq zIs.symm⟩))
          · exact .inr rest
  · have empty : links.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    refine ⟨fun z => ?_,id⟩
    simp [empty,LinkAlong,linkEnds]
termination_by links.val.length - index.val
decreasing_by omega

theorem edges_along_correct (F : forest.Forest) (h : hierarchy.RoleHierarchy)
    (x : Usize) (r : ObjectPropertyExpression) (index : Usize) (out : alloc.vec.Vec Usize) :
    ∃ res, forest.edges_along F h x r index out = .ok res ∧ ∀ out', res = some out' →
      (∀ z : Usize, z ∈ out'.val ↔ z ∈ out.val ∨ LinkAlong h F (edgeEnds (F.edges.val.drop index.val)) x.val r z.val) ∧
      (out.val.Nodup → out'.val.Nodup) := by
  rw [forest.edges_along]
  by_cases more : index.val < F.edges.val.length
  · have lookup : F.edges.index_usize index = .ok F.edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : F.edges.val.drop index.val = F.edges.val[index.val] :: F.edges.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨found,foundRun,foundSpec⟩ := ends_correct h out (rep F F.edges.val[index.val].from)
      (rep F F.edges.val[index.val].to) F.edges.val[index.val].role x r
    cases found with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,representative_correct,foundRun]
    | some mid =>
      obtain ⟨midMembers,midNodup⟩ := foundSpec mid rfl
      obtain ⟨res,run,spec⟩ := edges_along_correct F h x r index' mid
      refine ⟨res,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,representative_correct,foundRun,advance,run]
      · intro out' same
        obtain ⟨members,nodup⟩ := spec out' same
        refine ⟨fun z => ?_,fun start => nodup (midNodup start)⟩
        rw [members,midMembers,nextIndex,split]
        simp only [LinkAlong,edgeEnds,List.map_cons,List.mem_cons,exists_eq_or_imp]
        constructor
        · rintro ((old | ⟨sx,below,rfl⟩ | ⟨tx,below,rfl⟩) | rest)
          · exact .inl old
          · exact .inr (.inl (.inl ⟨by rw [sx],below,rfl⟩))
          · exact .inr (.inl (.inr ⟨by rw [tx],below,rfl⟩))
          · exact .inr (.inr rest)
        · rintro (old | (⟨sx,below,zIs⟩ | ⟨tx,below,zIs⟩) | rest)
          · exact .inl (.inl old)
          · exact .inl (.inr (.inl ⟨UScalar.eq_of_val_eq sx,below,UScalar.eq_of_val_eq zIs.symm⟩))
          · exact .inl (.inr (.inr ⟨UScalar.eq_of_val_eq tx,below,UScalar.eq_of_val_eq zIs.symm⟩))
          · exact .inr rest
  · have empty : F.edges.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    refine ⟨fun z => ?_,id⟩
    simp [empty,LinkAlong,edgeEnds]
termination_by F.edges.val.length - index.val
decreasing_by omega

/-- `y` is a neighbour of `x` along `r`: an active child, the parent, or a named
    node related by a link or an added edge. -/
def Neighbour (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (y : Nat) : Prop :=
  ChildAlong h F.nodes.val x r y ∨ ParentAlong h F.nodes.val x r y ∨
    LinkAlong h F (linkEnds P.links.val) x r y ∨ LinkAlong h F (edgeEnds F.edges.val) x r y

/-- The neighbour list of a node along a role lists exactly its neighbours, once
    each. -/
theorem neighbours_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Usize)
    (r : ObjectPropertyExpression) :
    ∃ res, forest.neighbours P h F x r = .ok res ∧ ∀ list, res = some list →
      (∀ z : Usize, z ∈ list.val ↔ Neighbour P h F x.val r z.val) ∧ list.val.Nodup := by
  rw [forest.neighbours]
  obtain ⟨one,oneRun,oneSpec⟩ := children_along_correct F h x r 0#usize (alloc.vec.Vec.new Usize)
  cases one with
  | none => exact ⟨none,by simp [oneRun],by simp⟩
  | some out1 =>
    obtain ⟨members1,nodup1⟩ := oneSpec out1 rfl
    obtain ⟨two,twoRun,twoSpec⟩ := parent_along_correct F h x r out1
    cases two with
    | none => exact ⟨none,by simp [oneRun,twoRun],by simp⟩
    | some out2 =>
      obtain ⟨members2,nodup2⟩ := twoSpec out2 rfl
      obtain ⟨three,threeRun,threeSpec⟩ := links_along_correct F h P.links x r 0#usize out2
      cases three with
      | none => exact ⟨none,by simp [oneRun,twoRun,threeRun],by simp⟩
      | some out3 =>
        obtain ⟨members3,nodup3⟩ := threeSpec out3 rfl
        obtain ⟨four,fourRun,fourSpec⟩ := edges_along_correct F h x r 0#usize out3
        refine ⟨four,by simp [oneRun,twoRun,threeRun,fourRun],?_⟩
        intro list same
        obtain ⟨members4,nodup4⟩ := fourSpec list same
        refine ⟨fun z => ?_,nodup4 (nodup3 (nodup2 (nodup1 (by simp))))⟩
        rw [members4,members3,members2,members1]
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero,Nat.zero_le,true_and,Neighbour]
        simp [or_assoc]

/-- The label read for a node is its label. -/
theorem label_of_correct (F : forest.Forest) (x : Usize) :
    ∃ v, forest.label_of F x = .ok v ∧ v.val = labelOf F.nodes.val x.val := by
  rw [forest.label_of]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    refine ⟨F.nodes.val[x.val].label,?_,by simp [labelOf,List.getElem?_eq_getElem inside]⟩
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok]
    exact Rowl.Completion.copy_label_correct _ 0#usize _ (by simp) (by simp)
  · refine ⟨alloc.vec.Vec.new Usize,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],?_⟩
    simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)]

/-- The filter keeps exactly the listed nodes whose labels satisfy the entry. -/
theorem satisfying_correct (entries : alloc.vec.Vec concept_table.Entry) (F : forest.Forest)
    (list : alloc.vec.Vec Usize) (c index : Usize) (out : alloc.vec.Vec Usize) :
    ∃ res, forest.satisfying entries F list c index out = .ok res ∧ ∀ out', res = some out' →
      out'.val = out.val ++ (list.val.drop index.val).filter
        (fun y => decide (Holds entries.val (labelOf F.nodes.val y.val) c.val)) := by
  rw [forest.satisfying]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨label,labelRun,labelValue⟩ := label_of_correct F list.val[index.val]
    have holdsRun := holds_correct entries label c.val c rfl
    rw [labelValue] at holdsRun
    by_cases satisfied : Holds entries.val (labelOf F.nodes.val list.val[index.val].val) c.val
    · by_cases room : out.val.length < Usize.max
      · obtain ⟨pushed,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out list.val[index.val] room)
        obtain ⟨res,run,spec⟩ := satisfying_correct entries F list c index' pushed
        refine ⟨res,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,labelRun,holdsRun,satisfied,decide_true,usize_max_val,room,push,advance,run]
        · intro out' same
          rw [spec out' same,contents,nextIndex,split,List.filter_cons]
          simp [satisfied]
      · refine ⟨none,?_,by simp⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,labelRun,holdsRun,satisfied,decide_true,usize_max_val,room]
    · obtain ⟨res,run,spec⟩ := satisfying_correct entries F list c index' out
      refine ⟨res,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,labelRun,holdsRun,satisfied,decide_false,Bool.false_eq_true,advance,run]
      · intro out' same
        rw [spec out' same,nextIndex,split,List.filter_cons]
        simp [satisfied]
  · have empty : list.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    simp [empty]
termination_by list.val.length - index.val
decreasing_by all_goals omega

/-- What an active node must satisfy: the requirements of the individuals merged
    into it, the TBox concept, the unfoldings of the classes it lists, and a
    tree node's seed. -/
def NodeNeeds (P : completion.Problem) (F : forest.Forest) (x : Nat) (c : Usize) : Prop :=
  (∃ q ∈ P.requirements.val, (rep F q.node).val = x ∧ c = q.concept) ∨ c = P.axioms ∨
  (∃ u ∈ P.unfoldings.val, HasAtom P.entries.val (labelOf F.nodes.val x) u.class ∧ c = u.concept) ∨
  (∃ n, F.nodes.val[x]? = some n ∧ n.tree = true ∧ c = n.seed)

/-- The node is part of the forest. -/
def Active (nodes : List forest.Node) (x : Nat) : Prop :=
  ∃ n, nodes[x]? = some n ∧ n.active = true

theorem missing_requirement_correct (P : completion.Problem) (F : forest.Forest) (label : alloc.vec.Vec Usize)
    (x index : Usize) :
    ∃ r, forest.missing_requirement P F label x index = .ok r ∧
      (∀ c, r = some c → (∃ q ∈ P.requirements.val.drop index.val, rep F q.node = x ∧ q.concept = c) ∧
        ¬ Holds P.entries.val label.val c.val) ∧
      (r = none → ∀ q ∈ P.requirements.val.drop index.val, rep F q.node = x →
        Holds P.entries.val label.val q.concept.val) := by
  rw [forest.missing_requirement]
  by_cases more : index.val < P.requirements.val.length
  · have lookup : P.requirements.index_usize index = .ok P.requirements.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : P.requirements.val.drop index.val =
        P.requirements.val[index.val] :: P.requirements.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have holdsRun := holds_correct P.entries label P.requirements.val[index.val].concept.val
      P.requirements.val[index.val].concept rfl
    by_cases missing : rep F P.requirements.val[index.val].node = x ∧
        ¬ Holds P.entries.val label.val P.requirements.val[index.val].concept.val
    · refine ⟨some P.requirements.val[index.val].concept,?_,?_,by simp⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,missing.1,holdsRun,
          missing.2]
      · intro c same
        cases same
        rw [split]
        exact ⟨⟨_,List.mem_cons_self ..,missing.1,rfl⟩,missing.2⟩
    · obtain ⟨r,run,found,absent⟩ := missing_requirement_correct P F label x index'
      refine ⟨r,?_,?_,?_⟩
      · have quiet : (if rep F P.requirements.val[index.val].node = x then
            (do let b ← completion.holds P.entries label P.requirements.val[index.val].concept; ok (¬ b))
            else ok false) = .ok false := by
          by_cases at_x : rep F P.requirements.val[index.val].node = x
          · have : Holds P.entries.val label.val P.requirements.val[index.val].concept.val := by
              by_contra fails; exact missing ⟨at_x,fails⟩
            simp [at_x,holdsRun,this]
          · simp [at_x]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,representative_correct,quiet,Bool.false_eq_true,advance,run]
      · intro c same
        obtain ⟨⟨q,member,at_x,value⟩,fails⟩ := found c same
        rw [nextIndex] at member
        exact ⟨⟨q,by rw [split]; exact List.mem_cons_of_mem _ member,at_x,value⟩,fails⟩
      · intro none q member at_x
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · by_contra fails
          exact missing ⟨at_x,fails⟩
        · exact absent none q (by rw [nextIndex]; exact later) at_x
  · have empty : P.requirements.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ q member
    rw [empty] at member
    cases member
termination_by P.requirements.val.length - index.val
decreasing_by all_goals omega

theorem missing_at_correct (P : completion.Problem) (F : forest.Forest) (x : Usize) :
    ∃ r, forest.missing_at P F x = .ok r ∧
      (∀ c, r = some c → NodeNeeds P F x.val c ∧ ¬ Holds P.entries.val (labelOf F.nodes.val x.val) c.val) ∧
      (r = none → x.val < F.nodes.val.length → ∀ c, NodeNeeds P F x.val c →
        Holds P.entries.val (labelOf F.nodes.val x.val) c.val) := by
  rw [forest.missing_at]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem inside
    have labelIs : labelOf F.nodes.val x.val = F.nodes.val[x.val].label.val := by simp [labelOf,at_x]
    rw [labelIs]
    obtain ⟨r1,run1,found1,absent1⟩ := missing_requirement_correct P F F.nodes.val[x.val].label x 0#usize
    simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at found1 absent1
    cases r1 with
    | some c =>
      refine ⟨some c,?_,?_,by simp⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1]
      · intro c' same
        cases same
        obtain ⟨⟨q,member,at_q,value⟩,fails⟩ := found1 c rfl
        exact ⟨.inl ⟨q,member,by rw [at_q],value.symm⟩,fails⟩
    | none =>
      have axiomsRun := holds_correct P.entries F.nodes.val[x.val].label P.axioms.val P.axioms rfl
      by_cases axiomsHold : Holds P.entries.val F.nodes.val[x.val].label.val P.axioms.val
      · obtain ⟨r2,run2,found2,absent2⟩ := missing_unfolding_correct P F.nodes.val[x.val].label 0#usize
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at found2 absent2
        cases r2 with
        | some c =>
          refine ⟨some c,?_,?_,by simp⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold,run2]
          · intro c' same
            cases same
            obtain ⟨⟨u,member,atom,value⟩,fails⟩ := found2 c rfl
            exact ⟨.inr (.inr (.inl ⟨u,member,by rw [labelIs]; exact atom,value.symm⟩)),fails⟩
        | none =>
          have seedRun := holds_correct P.entries F.nodes.val[x.val].label F.nodes.val[x.val].seed.val
            F.nodes.val[x.val].seed rfl
          have rest : ∀ c, NodeNeeds P F x.val c → (∀ n, F.nodes.val[x.val]? = some n → n.tree = true →
              c = n.seed → Holds P.entries.val F.nodes.val[x.val].label.val c.val) →
              Holds P.entries.val F.nodes.val[x.val].label.val c.val := by
            intro c needs seedHolds
            rcases needs with ⟨q,member,at_q,rfl⟩ | rfl | ⟨u,member,atom,rfl⟩ | ⟨n,at_n,tree,rfl⟩
            · exact absent1 rfl q member (UScalar.eq_of_val_eq at_q)
            · exact axiomsHold
            · rw [labelIs] at atom; exact absent2 rfl u member atom
            · exact seedHolds n at_n tree rfl
          by_cases tree : F.nodes.val[x.val].tree = true
          · by_cases seedHolds : Holds P.entries.val F.nodes.val[x.val].label.val F.nodes.val[x.val].seed.val
            · refine ⟨none,?_,by simp,?_⟩
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold,run2,tree,
                  seedRun,seedHolds]
              · intro _ _ c needs
                refine rest c needs ?_
                intro n at_n _ rfl
                rw [at_x] at at_n
                cases at_n
                exact seedHolds
            · refine ⟨some F.nodes.val[x.val].seed,?_,?_,by simp⟩
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold,run2,tree,
                  seedRun,seedHolds]
              · intro c same
                cases same
                exact ⟨.inr (.inr (.inr ⟨_,at_x,tree,rfl⟩)),seedHolds⟩
          · refine ⟨none,?_,by simp,?_⟩
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold,run2,tree]
            · intro _ _ c needs
              refine rest c needs ?_
              intro n at_n isTree _
              rw [at_x] at at_n
              cases at_n
              exact absurd isTree tree
      · refine ⟨some P.axioms,?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold]
        · intro c same
          cases same
          exact ⟨.inr (.inl rfl),axiomsHold⟩
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,?_⟩
    intro _ within
    exact absurd within inside

theorem missing_node_correct (P : completion.Problem) (F : forest.Forest) (index : Usize) :
    ∃ r, forest.missing_node P F index = .ok r ∧
      (∀ x c, r = some (x,c) → Active F.nodes.val x.val ∧ NodeNeeds P F x.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val x.val) c.val) ∧
      (r = none → ∀ y, index.val ≤ y → Active F.nodes.val y → ∀ c, NodeNeeds P F y c →
        Holds P.entries.val (labelOf F.nodes.val y) c.val) := by
  rw [forest.missing_node]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_node_correct P F index'
    by_cases active : F.nodes.val[index.val].active = true
    · obtain ⟨here,hereRun,hereFound,hereAbsent⟩ := missing_at_correct P F index
      cases here with
      | some c =>
        refine ⟨some (index,c),?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,hereRun]
        · intro x c' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl⟩ := same
          exact ⟨⟨_,at_index,active⟩,hereFound c rfl⟩
      | none =>
        refine ⟨r,?_,found,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,hereRun,advance,run]
        · intro none y low isActive c needs
          by_cases same : y = index.val
          · subst same
            exact hereAbsent rfl more c needs
          · exact absent none y (by omega) isActive c needs
    · refine ⟨r,?_,found,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,advance,run]
      · intro none y low isActive c needs
        by_cases same : y = index.val
        · subst same
          obtain ⟨n,at_n,yes⟩ := isActive
          rw [at_index] at at_n
          cases at_n
          exact absurd yes active
        · exact absent none y (by omega) isActive c needs
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low ⟨n,at_n,_⟩
    have := (List.getElem?_eq_some_iff.mp at_n).1
    omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

/-- The search along one edge returns a node at either end with an entry the
    other end requires and it lacks, or nothing when both directions are
    satisfied. -/
theorem missing_edge_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (F : forest.Forest) (source target : Usize) (role : ObjectPropertyExpression) :
    ∃ r, forest.missing_edge entries h F source target role = .ok r ∧
      (∀ x c, r = some (x,c) → source.val < F.nodes.val.length ∧ target.val < F.nodes.val.length ∧
        ((x = target ∧ EdgeNeeds entries.val h (labelOf F.nodes.val source.val) role c ∧
            ¬ Holds entries.val (labelOf F.nodes.val target.val) c.val) ∨
          (x = source ∧ EdgeNeeds entries.val h (labelOf F.nodes.val target.val) (inv role) c ∧
            ¬ Holds entries.val (labelOf F.nodes.val source.val) c.val))) ∧
      (r = none → source.val < F.nodes.val.length → target.val < F.nodes.val.length →
        EdgeOk entries.val h (labelOf F.nodes.val source.val) role (labelOf F.nodes.val target.val) ∧
        EdgeOk entries.val h (labelOf F.nodes.val target.val) (inv role) (labelOf F.nodes.val source.val)) := by
  rw [forest.missing_edge]
  by_cases sourceIn : source.val < F.nodes.val.length
  · by_cases targetIn : target.val < F.nodes.val.length
    · have one : F.nodes.index_usize source = .ok F.nodes.val[source.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem sourceIn]
      have two : F.nodes.index_usize target = .ok F.nodes.val[target.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem targetIn]
      have sourceLabel : labelOf F.nodes.val source.val = F.nodes.val[source.val].label.val := by
        simp [labelOf,List.getElem?_eq_getElem sourceIn]
      have targetLabel : labelOf F.nodes.val target.val = F.nodes.val[target.val].label.val := by
        simp [labelOf,List.getElem?_eq_getElem targetIn]
      rw [sourceLabel,targetLabel]
      obtain ⟨forward,forwardRun,forwardFound,forwardAbsent⟩ :=
        missing_along_correct entries h F.nodes.val[source.val].label role F.nodes.val[target.val].label 0#usize
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at forwardFound forwardAbsent
      cases forward with
      | some c =>
        refine ⟨some (target,c),?_,?_,by simp⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn,↓reduceIte,
            alloc.vec.Vec.index_slice_index,one,two,bind_ok,forwardRun]
        · intro x c' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl⟩ := same
          exact ⟨sourceIn,targetIn,.inl ⟨rfl,forwardFound c rfl⟩⟩
      | none =>
        obtain ⟨backward,backwardRun,backwardFound,backwardAbsent⟩ :=
          missing_along_correct entries h F.nodes.val[target.val].label (inv role) F.nodes.val[source.val].label
            0#usize
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at backwardFound backwardAbsent
        cases backward with
        | some c =>
          refine ⟨some (source,c),?_,?_,by simp⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn,↓reduceIte,
              alloc.vec.Vec.index_slice_index,one,two,bind_ok,forwardRun,inverse_correct,backwardRun]
          · intro x c' same
            simp only [Option.some.injEq,Prod.mk.injEq] at same
            obtain ⟨rfl,rfl⟩ := same
            exact ⟨sourceIn,targetIn,.inr ⟨rfl,backwardFound c rfl⟩⟩
        | none =>
          refine ⟨none,?_,by simp,fun _ _ _ => ⟨forwardAbsent rfl,backwardAbsent rfl⟩⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn,↓reduceIte,
            alloc.vec.Vec.index_slice_index,one,two,bind_ok,forwardRun,inverse_correct,backwardRun]
    · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,targetIn],by simp,?_⟩
      intro _ _ within
      exact absurd within targetIn
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn],by simp,?_⟩
    intro _ within
    exact absurd within sourceIn

/-- Something an edge between two nodes requires of one end: the edge from the
    parent of an active tree node along one of its roles, in either
    direction. -/
def TreeNeeds (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (nodes : List forest.Node)
    (y : Nat) (c : Usize) : Prop :=
  ∃ child n, nodes[child]? = some n ∧ n.tree = true ∧ n.active = true ∧ n.parent.val < nodes.length ∧
    ∃ s ∈ n.roles.val, ((y = child ∧ EdgeNeeds entries h (labelOf nodes n.parent.val) s c) ∨
      (y = n.parent.val ∧ EdgeNeeds entries h (labelOf nodes child) (inv s) c))

theorem missing_roles_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (F : forest.Forest) (x index : Usize) :
    ∃ r, forest.missing_roles entries h F x index = .ok r ∧
      (∀ y c, r = some (y,c) → ∃ n, F.nodes.val[x.val]? = some n ∧ n.parent.val < F.nodes.val.length ∧
        ∃ s ∈ n.roles.val, ((y = x ∧ EdgeNeeds entries.val h (labelOf F.nodes.val n.parent.val) s c ∧
            ¬ Holds entries.val (labelOf F.nodes.val x.val) c.val) ∨
          (y = n.parent ∧ EdgeNeeds entries.val h (labelOf F.nodes.val x.val) (inv s) c ∧
            ¬ Holds entries.val (labelOf F.nodes.val n.parent.val) c.val))) ∧
      (r = none → ∀ n, F.nodes.val[x.val]? = some n → n.parent.val < F.nodes.val.length →
        ∀ s ∈ n.roles.val.drop index.val,
          EdgeOk entries.val h (labelOf F.nodes.val n.parent.val) s (labelOf F.nodes.val x.val) ∧
          EdgeOk entries.val h (labelOf F.nodes.val x.val) (inv s) (labelOf F.nodes.val n.parent.val)) := by
  rw [forest.missing_roles]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem inside
    by_cases more : index.val < F.nodes.val[x.val].roles.val.length
    · have roleLookup : F.nodes.val[x.val].roles.index_usize index = .ok F.nodes.val[x.val].roles.val[index.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      have split : F.nodes.val[x.val].roles.val.drop index.val =
          F.nodes.val[x.val].roles.val[index.val] :: F.nodes.val[x.val].roles.val.drop (index.val+1) :=
        List.drop_eq_getElem_cons more
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨e,eRun,eFound,eAbsent⟩ := missing_edge_correct entries h F F.nodes.val[x.val].parent x
        F.nodes.val[x.val].roles.val[index.val]
      cases e with
      | some found =>
        obtain ⟨y,c⟩ := found
        refine ⟨some (y,c),?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,roleLookup,eRun]
        · intro y' c' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl⟩ := same
          obtain ⟨parentIn,_,which⟩ := eFound y c rfl
          refine ⟨_,at_x,parentIn,_,List.getElem_mem more,?_⟩
          rcases which with ⟨rfl,needs,fails⟩ | ⟨rfl,needs,fails⟩
          · exact .inl ⟨rfl,needs,fails⟩
          · exact .inr ⟨rfl,needs,fails⟩
      | none =>
        obtain ⟨r,run,found,absent⟩ := missing_roles_correct entries h F x index'
        refine ⟨r,?_,found,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,roleLookup,eRun,advance,run]
        · intro none n at_n parentIn s member
          rw [at_x] at at_n
          cases at_n
          rw [split] at member
          rcases List.mem_cons.mp member with rfl | later
          · exact eAbsent rfl parentIn inside
          · exact absent none _ at_x parentIn s (by rw [nextIndex]; exact later)
    · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more],by simp,?_⟩
      intro _ n at_n _ s member
      rw [at_x] at at_n
      cases at_n
      rw [List.drop_eq_nil_iff.mpr (by omega)] at member
      cases member
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,?_⟩
    intro _ n at_n
    have := (List.getElem?_eq_some_iff.mp at_n).1
    omega
termination_by (match F.nodes.val[x.val]? with | some n => n.roles.val.length | none => 0) - index.val
decreasing_by
  all_goals
    simp only [List.getElem?_eq_getElem inside]
    omega

theorem missing_tree_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (index : Usize) :
    ∃ r, forest.missing_tree P h F index = .ok r ∧
      (∀ y c, r = some (y,c) → y.val < F.nodes.val.length ∧ TreeNeeds P.entries.val h F.nodes.val y.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) ∧
      (r = none → ∀ child n, index.val ≤ child → F.nodes.val[child]? = some n → n.tree = true → n.active = true →
        n.parent.val < F.nodes.val.length → ∀ s ∈ n.roles.val,
          EdgeOk P.entries.val h (labelOf F.nodes.val n.parent.val) s (labelOf F.nodes.val child) ∧
          EdgeOk P.entries.val h (labelOf F.nodes.val child) (inv s) (labelOf F.nodes.val n.parent.val)) := by
  rw [forest.missing_tree]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_tree_correct P h F index'
    have skip : (∀ n, F.nodes.val[index.val]? = some n → n.tree = true → n.active = true →
        n.parent.val < F.nodes.val.length → ∀ s ∈ n.roles.val,
          EdgeOk P.entries.val h (labelOf F.nodes.val n.parent.val) s (labelOf F.nodes.val index.val) ∧
          EdgeOk P.entries.val h (labelOf F.nodes.val index.val) (inv s) (labelOf F.nodes.val n.parent.val)) →
        r = none → ∀ child n, index.val ≤ child → F.nodes.val[child]? = some n → n.tree = true →
          n.active = true → n.parent.val < F.nodes.val.length → ∀ s ∈ n.roles.val,
            EdgeOk P.entries.val h (labelOf F.nodes.val n.parent.val) s (labelOf F.nodes.val child) ∧
            EdgeOk P.entries.val h (labelOf F.nodes.val child) (inv s) (labelOf F.nodes.val n.parent.val) := by
      intro here none child n low at_child tree active parentIn s member
      by_cases same : child = index.val
      · subst same
        exact here n at_child tree active parentIn s member
      · exact absent none child n (by omega) at_child tree active parentIn s member
    by_cases tree : F.nodes.val[index.val].tree = true
    · by_cases active : F.nodes.val[index.val].active = true
      · obtain ⟨e,eRun,eFound,eAbsent⟩ := missing_roles_correct P.entries h F index 0#usize
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at eAbsent
        cases e with
        | some pair =>
          obtain ⟨y,c⟩ := pair
          refine ⟨some (y,c),?_,?_,by simp⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,active,eRun]
          · intro y' c' same
            simp only [Option.some.injEq,Prod.mk.injEq] at same
            obtain ⟨rfl,rfl⟩ := same
            obtain ⟨n,at_n,parentIn,s,member,which⟩ := eFound y c rfl
            rw [at_index] at at_n
            cases at_n
            rcases which with ⟨rfl,needs,fails⟩ | ⟨rfl,needs,fails⟩
            · exact ⟨more,⟨_,_,at_index,tree,active,parentIn,s,member,.inl ⟨rfl,needs⟩⟩,fails⟩
            · exact ⟨parentIn,⟨_,_,at_index,tree,active,parentIn,s,member,.inr ⟨rfl,needs⟩⟩,fails⟩
        | none =>
          refine ⟨r,?_,found,skip ?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,active,eRun,advance,run]
          · intro n at_n _ _ parentIn s member
            exact eAbsent rfl n at_n parentIn s member
      · refine ⟨r,?_,found,skip ?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,active,advance,run]
        · intro n at_n _ isActive
          rw [at_index] at at_n
          cases at_n
          exact absurd isActive active
    · refine ⟨r,?_,found,skip ?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,advance,run]
      · intro n at_n isTree
        rw [at_index] at at_n
        cases at_n
        exact absurd isTree tree
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ child n low at_child
    have := (List.getElem?_eq_some_iff.mp at_child).1
    omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

/-- Something a link or added edge requires of one end, read through the
    merges, in either direction. -/
def LinkNeeds (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (links : List (ObjectPropertyExpression × Usize × Usize)) (y : Nat) (c : Usize) : Prop :=
  ∃ l ∈ links, (rep F l.2.1).val < F.nodes.val.length ∧ (rep F l.2.2).val < F.nodes.val.length ∧
    (((rep F l.2.2).val = y ∧ EdgeNeeds entries h (labelOf F.nodes.val (rep F l.2.1).val) l.1 c) ∨
      ((rep F l.2.1).val = y ∧ EdgeNeeds entries h (labelOf F.nodes.val (rep F l.2.2).val) (inv l.1) c))

/-- Every link or added edge, read through the merges, gives each end what the
    other requires. -/
def LinksOk (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (links : List (ObjectPropertyExpression × Usize × Usize)) : Prop :=
  ∀ l ∈ links, (rep F l.2.1).val < F.nodes.val.length → (rep F l.2.2).val < F.nodes.val.length →
    EdgeOk entries h (labelOf F.nodes.val (rep F l.2.1).val) l.1 (labelOf F.nodes.val (rep F l.2.2).val) ∧
    EdgeOk entries h (labelOf F.nodes.val (rep F l.2.2).val) (inv l.1) (labelOf F.nodes.val (rep F l.2.1).val)

theorem missing_link_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (index : Usize) :
    ∃ r, forest.missing_link P h F index = .ok r ∧
      (∀ y c, r = some (y,c) → y.val < F.nodes.val.length ∧
        LinkNeeds P.entries.val h F (linkEnds P.links.val) y.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) ∧
      (r = none → LinksOk P.entries.val h F (linkEnds (P.links.val.drop index.val))) := by
  rw [forest.missing_link]
  by_cases more : index.val < P.links.val.length
  · have lookup : P.links.index_usize index = .ok P.links.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : P.links.val.drop index.val = P.links.val[index.val] :: P.links.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have memberHere : (P.links.val[index.val].role,P.links.val[index.val].from,P.links.val[index.val].to) ∈
        linkEnds P.links.val := List.mem_map.mpr ⟨_,List.getElem_mem more,rfl⟩
    obtain ⟨e,eRun,eFound,eAbsent⟩ := missing_edge_correct P.entries h F (rep F P.links.val[index.val].from)
      (rep F P.links.val[index.val].to) P.links.val[index.val].role
    cases e with
    | some pair =>
      obtain ⟨y,c⟩ := pair
      refine ⟨some (y,c),?_,?_,by simp⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,eRun]
      · intro y' c' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        obtain ⟨sourceIn,targetIn,which⟩ := eFound y c rfl
        rcases which with ⟨rfl,needs,fails⟩ | ⟨rfl,needs,fails⟩
        · exact ⟨targetIn,⟨_,memberHere,sourceIn,targetIn,.inl ⟨rfl,needs⟩⟩,fails⟩
        · exact ⟨sourceIn,⟨_,memberHere,sourceIn,targetIn,.inr ⟨rfl,needs⟩⟩,fails⟩
    | none =>
      obtain ⟨r,run,found,absent⟩ := missing_link_correct P h F index'
      refine ⟨r,?_,found,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,eRun,advance,run]
      · intro none l member sourceIn targetIn
        rw [split,linkEnds,List.map_cons] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact eAbsent rfl sourceIn targetIn
        · exact absent none l (by rw [nextIndex,linkEnds]; exact later) sourceIn targetIn
  · have empty : P.links.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ l member
    simp [empty,linkEnds] at member
termination_by P.links.val.length - index.val
decreasing_by all_goals omega

theorem missing_added_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (index : Usize) :
    ∃ r, forest.missing_added P h F index = .ok r ∧
      (∀ y c, r = some (y,c) → y.val < F.nodes.val.length ∧
        LinkNeeds P.entries.val h F (edgeEnds F.edges.val) y.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) ∧
      (r = none → LinksOk P.entries.val h F (edgeEnds (F.edges.val.drop index.val))) := by
  rw [forest.missing_added]
  by_cases more : index.val < F.edges.val.length
  · have lookup : F.edges.index_usize index = .ok F.edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : F.edges.val.drop index.val = F.edges.val[index.val] :: F.edges.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have memberHere : (F.edges.val[index.val].role,F.edges.val[index.val].from,F.edges.val[index.val].to) ∈
        edgeEnds F.edges.val := List.mem_map.mpr ⟨_,List.getElem_mem more,rfl⟩
    obtain ⟨e,eRun,eFound,eAbsent⟩ := missing_edge_correct P.entries h F (rep F F.edges.val[index.val].from)
      (rep F F.edges.val[index.val].to) F.edges.val[index.val].role
    cases e with
    | some pair =>
      obtain ⟨y,c⟩ := pair
      refine ⟨some (y,c),?_,?_,by simp⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,eRun]
      · intro y' c' same
        simp only [Option.some.injEq,Prod.mk.injEq] at same
        obtain ⟨rfl,rfl⟩ := same
        obtain ⟨sourceIn,targetIn,which⟩ := eFound y c rfl
        rcases which with ⟨rfl,needs,fails⟩ | ⟨rfl,needs,fails⟩
        · exact ⟨targetIn,⟨_,memberHere,sourceIn,targetIn,.inl ⟨rfl,needs⟩⟩,fails⟩
        · exact ⟨sourceIn,⟨_,memberHere,sourceIn,targetIn,.inr ⟨rfl,needs⟩⟩,fails⟩
    | none =>
      obtain ⟨r,run,found,absent⟩ := missing_added_correct P h F index'
      refine ⟨r,?_,found,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,eRun,advance,run]
      · intro none l member sourceIn targetIn
        rw [split,edgeEnds,List.map_cons] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact eAbsent rfl sourceIn targetIn
        · exact absent none l (by rw [nextIndex,edgeEnds]; exact later) sourceIn targetIn
  · have empty : F.edges.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ l member
    simp [empty,edgeEnds] at member
termination_by F.edges.val.length - index.val
decreasing_by all_goals omega

theorem undecided_correct (entries : alloc.vec.Vec concept_table.Entry) (F : forest.Forest)
    (list : alloc.vec.Vec Usize) (left right index : Usize) :
    ∃ r, forest.undecided entries F list left right index = .ok r ∧
      (∀ y, r = some y → y ∈ list.val.drop index.val ∧
        ¬ Holds entries.val (labelOf F.nodes.val y.val) left.val ∧
        ¬ Holds entries.val (labelOf F.nodes.val y.val) right.val) ∧
      (r = none → ∀ y ∈ list.val.drop index.val, Holds entries.val (labelOf F.nodes.val y.val) left.val ∨
        Holds entries.val (labelOf F.nodes.val y.val) right.val) := by
  rw [forest.undecided]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨label,labelRun,labelValue⟩ := label_of_correct F list.val[index.val]
    have leftRun := holds_correct entries label left.val left rfl
    have rightRun := holds_correct entries label right.val right rfl
    rw [labelValue] at leftRun rightRun
    obtain ⟨r,run,found,absent⟩ := undecided_correct entries F list left right index'
    have later : r = none → ∀ y ∈ list.val.drop index.val, (y = list.val[index.val] →
        Holds entries.val (labelOf F.nodes.val y.val) left.val ∨
        Holds entries.val (labelOf F.nodes.val y.val) right.val) →
        Holds entries.val (labelOf F.nodes.val y.val) left.val ∨
        Holds entries.val (labelOf F.nodes.val y.val) right.val := by
      intro none y member here
      rw [split] at member
      rcases List.mem_cons.mp member with rfl | rest
      · exact here rfl
      · exact absent none y (by rw [nextIndex]; exact rest)
    have earlier : ∀ y, r = some y → y ∈ list.val.drop index.val ∧
        ¬ Holds entries.val (labelOf F.nodes.val y.val) left.val ∧
        ¬ Holds entries.val (labelOf F.nodes.val y.val) right.val := by
      intro y same
      obtain ⟨member,one,two⟩ := found y same
      exact ⟨by rw [split]; exact List.mem_cons_of_mem _ (by rw [nextIndex] at member; exact member),one,two⟩
    by_cases one : Holds entries.val (labelOf F.nodes.val list.val[index.val].val) left.val
    · refine ⟨r,?_,earlier,fun none y member => later none y member (fun same => by rw [same]; exact .inl one)⟩
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,labelRun,leftRun,one,decide_true,advance,run]
    · by_cases two : Holds entries.val (labelOf F.nodes.val list.val[index.val].val) right.val
      · refine ⟨r,?_,earlier,fun none y member => later none y member (fun same => by rw [same]; exact .inr two)⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,labelRun,leftRun,rightRun,one,two,decide_true,decide_false,Bool.false_eq_true,advance,
          run]
      · refine ⟨some list.val[index.val],?_,?_,by simp⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,labelRun,leftRun,rightRun,one,two,decide_false,Bool.false_eq_true]
        · intro y same
          cases same
          exact ⟨by rw [split]; exact List.mem_cons_self ..,one,two⟩
  · have empty : list.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y member
    rw [empty] at member
    cases member
termination_by list.val.length - index.val
decreasing_by all_goals omega

/-- More neighbours along `r` satisfy `c` than the bound `n` allows. -/
def Excess (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (c n : Usize) : Prop :=
  ∃ list : List Usize, list.Nodup ∧ n.val < list.length ∧
    ∀ z ∈ list, Neighbour P h F x r z.val ∧ Holds P.entries.val (labelOf F.nodes.val z.val) c.val

/-- The counted neighbours are those of the filter: too many exactly when the
    filter is longer than the bound. -/
theorem excess_iff (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (c n : Usize) (list : List Usize)
    (members : ∀ z : Usize, z ∈ list ↔ Neighbour P h F x r z.val) (nodup : list.Nodup) :
    Excess P h F x r c n ↔
      n.val < (list.filter (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val))).length := by
  constructor
  · rintro ⟨many,manyNodup,longer,inside⟩
    have sub : many ⊆ list.filter (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val)) := by
      intro z member
      obtain ⟨neighbour,holds⟩ := inside z member
      exact List.mem_filter.mpr ⟨(members z).mpr neighbour,by simpa using holds⟩
    have := (manyNodup.subperm sub).length_le
    omega
  · intro longer
    refine ⟨_,nodup.filter _,longer,?_⟩
    intro z member
    obtain ⟨listed,holds⟩ := List.mem_filter.mp member
    exact ⟨(members z).mp listed,by simpa using holds⟩

/-- What the choose rule (`choose`) or the merge rule requires at node `x` for
    the maximum restrictions among `items`. -/
def CountOkFrom (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (choose : Bool)
    (x : Nat) (items : List Usize) : Prop :=
  ∀ i ∈ items, ∀ n r c c', P.entries.val[i.val]? = some (.AtMost n r c c') →
    match choose with
    | true => ∀ y : Usize, Neighbour P h F x r y.val →
        Holds P.entries.val (labelOf F.nodes.val y.val) c.val ∨ Holds P.entries.val (labelOf F.nodes.val y.val) c'.val
    | false => ¬ Excess P h F x r c n

/-- A step of the choose rule (`choose`) or the merge rule at node `x`. -/
def CountStep (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (choose : Bool)
    (x : Usize) (step : forest.Step) : Prop :=
  ∃ i ∈ labelOf F.nodes.val x.val, ∃ n r c c', P.entries.val[i.val]? = some (.AtMost n r c c') ∧
    match choose with
    | true => ∃ y : Usize, step = .Choose y c c' ∧ Neighbour P h F x.val r y.val ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val ∧ ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c'.val
    | false => step = .Merge x i ∧ Excess P h F x.val r c n

theorem counting_from_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Usize)
    (choose : Bool) (index : Usize) :
    ∃ r, forest.counting_from P h F x choose index = .ok r ∧
      (∀ step, r = some (some step) → CountStep P h F choose x step) ∧
      (r = some none → CountOkFrom P h F choose x.val ((labelOf F.nodes.val x.val).drop index.val)) := by
  rw [forest.counting_from]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have labelIs : labelOf F.nodes.val x.val = F.nodes.val[x.val].label.val := by
      simp [labelOf,List.getElem?_eq_getElem inside]
    by_cases more : index.val < F.nodes.val[x.val].label.val.length
    · have itemLookup : F.nodes.val[x.val].label.index_usize index =
          .ok F.nodes.val[x.val].label.val[index.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      have split : F.nodes.val[x.val].label.val.drop index.val =
          F.nodes.val[x.val].label.val[index.val] :: F.nodes.val[x.val].label.val.drop (index.val+1) :=
        List.drop_eq_getElem_cons more
      have itemIn : F.nodes.val[x.val].label.val[index.val] ∈ labelOf F.nodes.val x.val := by
        rw [labelIs]; exact List.getElem_mem more
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,found,absent⟩ := counting_from_correct P h F x choose index'
      -- Skipping an item that is no maximum restriction keeps the answer of the rest.
      have skip : (∀ n r c c', P.entries.val[F.nodes.val[x.val].label.val[index.val].val]? =
            some (.AtMost n r c c') → False) →
          r = some none → CountOkFrom P h F choose x.val ((labelOf F.nodes.val x.val).drop index.val) := by
        intro notMost none i member n role c c' at_i
        rw [labelIs,split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact (notMost n role c c' at_i).elim
        · exact absent none i (by rw [labelIs,nextIndex]; exact later) n role c c' at_i
      by_cases itemInside : F.nodes.val[x.val].label.val[index.val].val < P.entries.val.length
      · have entryLookup : P.entries.index_usize F.nodes.val[x.val].label.val[index.val] =
            .ok P.entries.val[F.nodes.val[x.val].label.val[index.val].val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemInside]
        have at_item := List.getElem?_eq_getElem itemInside
        cases entry : P.entries.val[F.nodes.val[x.val].label.val[index.val].val] with
        | AtMost n role c c' =>
          obtain ⟨neighbours,neighboursRun,neighboursSpec⟩ := neighbours_correct P h F x role
          cases neighbours with
          | none =>
            refine ⟨none,?_,by simp,by simp⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
              entry,neighboursRun]
          | some list =>
            obtain ⟨members,nodup⟩ := neighboursSpec list rfl
            cases choose with
            | true =>
              obtain ⟨u,uRun,uFound,uAbsent⟩ := undecided_correct P.entries F list c c' 0#usize
              simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at uFound uAbsent
              cases u with
              | some y =>
                obtain ⟨member,one,two⟩ := uFound y rfl
                refine ⟨some (some (.Choose y c c')),?_,?_,by simp⟩
                · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                    entryLookup,entry,neighboursRun,uRun]
                · intro step same
                  simp only [Option.some.injEq] at same
                  subst same
                  refine ⟨_,itemIn,n,role,c,c',by rw [at_item,entry],y,rfl,(members y).mp member,one,two⟩
              | none =>
                refine ⟨r,?_,found,?_⟩
                · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                    entryLookup,entry,neighboursRun,uRun,advance,run]
                · intro none i member n' role' d d' at_i
                  rw [labelIs,split] at member
                  rcases List.mem_cons.mp member with rfl | later
                  · rw [at_item,entry] at at_i
                    simp only [Option.some.injEq,concept_table.Entry.AtMost.injEq] at at_i
                    obtain ⟨rfl,rfl,rfl,rfl⟩ := at_i
                    intro y neighbour
                    exact uAbsent rfl y ((members y).mpr neighbour)
                  · exact absent none i (by rw [labelIs,nextIndex]; exact later) n' role' d d' at_i
            | false =>
              obtain ⟨many,manyRun,manySpec⟩ := satisfying_correct P.entries F list c 0#usize
                (alloc.vec.Vec.new Usize)
              cases many with
              | none =>
                refine ⟨none,?_,by simp,by simp⟩
                simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                  entryLookup,entry,neighboursRun,manyRun]
              | some kept =>
                have keptIs : kept.val = list.val.filter
                    (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val)) := by
                  simpa using manySpec kept rfl
                have excess := excess_iff P h F x.val role c n list.val members nodup
                rw [← keptIs] at excess
                by_cases over : n.val < kept.val.length
                · refine ⟨some (some (.Merge x F.nodes.val[x.val].label.val[index.val])),?_,?_,by simp⟩
                  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                      entryLookup,entry,neighboursRun,manyRun,over]
                  · intro step same
                    simp only [Option.some.injEq] at same
                    subst same
                    exact ⟨_,itemIn,n,role,c,c',by rw [at_item,entry],rfl,excess.mpr over⟩
                · refine ⟨r,?_,found,?_⟩
                  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                      entryLookup,entry,neighboursRun,manyRun,over,advance,run]
                  · intro none i member n' role' d d' at_i
                    rw [labelIs,split] at member
                    rcases List.mem_cons.mp member with rfl | later
                    · rw [at_item,entry] at at_i
                      simp only [Option.some.injEq,concept_table.Entry.AtMost.injEq] at at_i
                      obtain ⟨rfl,rfl,rfl,rfl⟩ := at_i
                      exact fun excessive => over (excess.mp excessive)
                    · exact absent none i (by rw [labelIs,nextIndex]; exact later) n' role' d d' at_i
        | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ | And _ _ | Or _ _ | Exists _ _ | Forall _ _ | AtLeast _ _ _ =>
          refine ⟨r,?_,found,skip (by intro n role c c' at_i; rw [at_item,entry] at at_i; cases at_i)⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,entry,
            advance,run]
      · refine ⟨r,?_,found,skip (by
          intro n role c c' at_i
          have := (List.getElem?_eq_some_iff.mp at_i).1
          omega)⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,advance,run]
    · refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more],by simp,?_⟩
      intro _ i member
      rw [labelIs,List.drop_eq_nil_iff.mpr (by omega)] at member
      cases member
  · have empty : labelOf F.nodes.val x.val = [] := by
      simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)]
    refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,?_⟩
    intro _ i member
    rw [empty] at member
    simp at member
termination_by (labelOf F.nodes.val x.val).length - index.val
decreasing_by
  all_goals
    simp only [labelOf,List.getElem?_eq_getElem inside]
    omega

/-- No choose step (`choose`) or merge step applies at node `x`. -/
def CountOk (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (choose : Bool)
    (x : Nat) : Prop :=
  CountOkFrom P h F choose x (labelOf F.nodes.val x)

theorem counting_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (choose : Bool) (index : Usize) :
    ∃ r, forest.counting P h F choose index = .ok r ∧
      (∀ step, r = some (some step) → ∃ x : Usize, Active F.nodes.val x.val ∧ CountStep P h F choose x step) ∧
      (r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y → CountOk P h F choose y) := by
  rw [forest.counting]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := counting_correct P h F choose index'
    by_cases active : F.nodes.val[index.val].active = true
    · obtain ⟨here,hereRun,hereFound,hereAbsent⟩ := counting_from_correct P h F index choose 0#usize
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at hereAbsent
      cases here with
      | none => exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,hereRun],by simp,
          by simp⟩
      | some found' =>
        cases found' with
        | some step =>
          refine ⟨some (some step),?_,?_,by simp⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,hereRun]
          · intro step' same
            cases same
            exact ⟨index,⟨_,at_index,active⟩,hereFound step rfl⟩
        | none =>
          refine ⟨r,?_,found,?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,hereRun,advance,run]
          · intro none y low isActive
            by_cases same : y = index.val
            · subst same
              exact hereAbsent rfl
            · exact absent none y (by omega) isActive
    · refine ⟨r,?_,found,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,advance,run]
      · intro none y low isActive
        by_cases same : y = index.val
        · subst same
          obtain ⟨n,at_n,yes⟩ := isActive
          rw [at_index] at at_n
          cases at_n
          exact absurd yes active
        · exact absent none y (by omega) isActive
  · refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low ⟨n,at_n,_⟩
    have := (List.getElem?_eq_some_iff.mp at_n).1
    omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

theorem role_listed_correct (list : alloc.vec.Vec ObjectPropertyExpression) (role : ObjectPropertyExpression)
    (index : Usize) : forest.role_listed list role index = .ok (decide (role ∈ list.val.drop index.val)) := by
  rw [forest.role_listed]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := role_listed_correct list role index'
    rw [nextIndex] at rest
    rw [split]
    by_cases here : list.val[index.val] = role
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,same_role_correct,here]
    · have other : role ≠ list.val[index.val] := fun same => here same.symm
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,same_role_correct,here,decide_false,Bool.false_eq_true,advance,rest,List.mem_cons,other,false_or]
  · have empty : list.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by list.val.length - index.val
decreasing_by omega

theorem roles_within_correct (small large : alloc.vec.Vec ObjectPropertyExpression) (index : Usize) :
    forest.roles_within small large index = .ok (decide (∀ s ∈ small.val.drop index.val, s ∈ large.val)) := by
  rw [forest.roles_within]
  by_cases more : index.val < small.val.length
  · have lookup : small.index_usize index = .ok small.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : small.val.drop index.val = small.val[index.val] :: small.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := roles_within_correct small large index'
    rw [nextIndex] at rest
    rw [split]
    by_cases found : small.val[index.val] ∈ large.val
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,role_listed_correct,show (0#usize).val = 0 from rfl,List.drop_zero,found,decide_true,advance,
        rest,List.forall_mem_cons,true_and]
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
        lookup,bind_ok,role_listed_correct,show (0#usize).val = 0 from rfl,List.drop_zero,found,decide_false,
        Bool.false_eq_true,List.forall_mem_cons,false_and]
  · have empty : small.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by small.val.length - index.val
decreasing_by omega

/-- Two nodes have the same label, parents in range with the same label, and
    the same roles from their parents. -/
def SamePair (nodes : List forest.Node) (x y : Nat) : Prop :=
  ∃ nx ny, nodes[x]? = some nx ∧ nodes[y]? = some ny ∧ nx.parent.val < nodes.length ∧
    ny.parent.val < nodes.length ∧ SameLabel nx.label.val ny.label.val ∧
    SameLabel (labelOf nodes nx.parent.val) (labelOf nodes ny.parent.val) ∧ (∀ s, s ∈ nx.roles.val ↔ s ∈ ny.roles.val)

theorem same_pair_correct (F : forest.Forest) (x y : Usize) :
    forest.same_pair F x y = .ok (decide (SamePair F.nodes.val x.val y.val)) := by
  rw [forest.same_pair]
  by_cases xIn : x.val < F.nodes.val.length
  · by_cases yIn : y.val < F.nodes.val.length
    · have lookupX : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem xIn]
      have lookupY : F.nodes.index_usize y = .ok F.nodes.val[y.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem yIn]
      have unfold : SamePair F.nodes.val x.val y.val ↔ F.nodes.val[x.val].parent.val < F.nodes.val.length ∧
          F.nodes.val[y.val].parent.val < F.nodes.val.length ∧
          SameLabel F.nodes.val[x.val].label.val F.nodes.val[y.val].label.val ∧
          SameLabel (labelOf F.nodes.val F.nodes.val[x.val].parent.val)
            (labelOf F.nodes.val F.nodes.val[y.val].parent.val) ∧
          (∀ s, s ∈ F.nodes.val[x.val].roles.val ↔ s ∈ F.nodes.val[y.val].roles.val) := by
        simp [SamePair,List.getElem?_eq_getElem xIn,List.getElem?_eq_getElem yIn]
      rw [unfold]
      by_cases px : F.nodes.val[x.val].parent.val < F.nodes.val.length
      · by_cases py : F.nodes.val[y.val].parent.val < F.nodes.val.length
        · have lookupPX : F.nodes.index_usize F.nodes.val[x.val].parent =
              .ok F.nodes.val[F.nodes.val[x.val].parent.val] := by
            simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem px]
          have lookupPY : F.nodes.index_usize F.nodes.val[y.val].parent =
              .ok F.nodes.val[F.nodes.val[y.val].parent.val] := by
            simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem py]
          have labelPX : labelOf F.nodes.val F.nodes.val[x.val].parent.val =
              F.nodes.val[F.nodes.val[x.val].parent.val].label.val := by
            simp [labelOf,List.getElem?_eq_getElem px]
          have labelPY : labelOf F.nodes.val F.nodes.val[y.val].parent.val =
              F.nodes.val[F.nodes.val[y.val].parent.val].label.val := by
            simp [labelOf,List.getElem?_eq_getElem py]
          rw [labelPX,labelPY]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,yIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookupX,lookupY,bind_ok,px,py,same_label_correct,lookupPX,lookupPY,roles_within_correct,
            show (0#usize).val = 0 from rfl,List.drop_zero,true_and]
          by_cases one : SameLabel F.nodes.val[x.val].label.val F.nodes.val[y.val].label.val
          · rw [decide_eq_true (show ∀ i, i ∈ F.nodes.val[x.val].label.val ↔ i ∈ F.nodes.val[y.val].label.val
              from one)]
            by_cases two : SameLabel F.nodes.val[F.nodes.val[x.val].parent.val].label.val
                F.nodes.val[F.nodes.val[y.val].parent.val].label.val
            · rw [decide_eq_true (show ∀ i, i ∈ F.nodes.val[F.nodes.val[x.val].parent.val].label.val ↔
                i ∈ F.nodes.val[F.nodes.val[y.val].parent.val].label.val from two)]
              by_cases three : ∀ s ∈ F.nodes.val[x.val].roles.val, s ∈ F.nodes.val[y.val].roles.val
              · rw [decide_eq_true three]
                simp only [↓reduceIte]
                congr 1
                rw [decide_eq_decide]
                exact ⟨fun four => ⟨one,two,fun s => ⟨three s,four s⟩⟩,fun ⟨_,_,both⟩ s => (both s).mpr⟩
              · rw [decide_eq_false three]
                simp only [Bool.false_eq_true,↓reduceIte]
                congr 1
                symm
                rw [decide_eq_false_iff_not]
                rintro ⟨_,_,both⟩
                exact three (fun s => (both s).mp)
            · rw [decide_eq_false (show ¬ ∀ i, i ∈ F.nodes.val[F.nodes.val[x.val].parent.val].label.val ↔
                i ∈ F.nodes.val[F.nodes.val[y.val].parent.val].label.val from two)]
              simp only [Bool.false_eq_true,↓reduceIte]
              congr 1
              symm
              rw [decide_eq_false_iff_not]
              rintro ⟨_,sameParents,_⟩
              exact two sameParents
          · rw [decide_eq_false (show ¬ ∀ i, i ∈ F.nodes.val[x.val].label.val ↔ i ∈ F.nodes.val[y.val].label.val
              from one)]
            simp only [Bool.false_eq_true,↓reduceIte]
            congr 1
            symm
            rw [decide_eq_false_iff_not]
            rintro ⟨sameLabels,_⟩
            exact one sameLabels
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,yIn,lookupX,lookupY,px,py]
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,yIn,lookupX,lookupY,px]
    · have absent : ¬ SamePair F.nodes.val x.val y.val := by
        rintro ⟨_,_,_,at_y,_⟩
        have := (List.getElem?_eq_some_iff.mp at_y).1
        omega
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,yIn,absent]
  · have absent : ¬ SamePair F.nodes.val x.val y.val := by
      rintro ⟨_,_,at_x,_⟩
      have := (List.getElem?_eq_some_iff.mp at_x).1
      omega
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,absent]

/-- The tree nodes from `x` up to its root, nearest first, following parents
    with smaller indices. -/
def treePath (nodes : List forest.Node) (x : Nat) : List Nat :=
  match nodes[x]? with
  | some n =>
    if n.tree = true then
      if _below : n.parent.val < x then x :: treePath nodes n.parent.val else [x]
    else []
  | none => []
termination_by x

/-- Pairwise blocking: some tree node on the path from `x` to its root repeats
    the pair of a tree node above it. -/
def Blocked (nodes : List forest.Node) (x : Nat) : Prop :=
  match nodes[x]? with
  | some n =>
    if _below : n.parent.val < x then
      n.tree = true ∧ ((∃ v ∈ treePath nodes n.parent.val, SamePair nodes x v) ∨ Blocked nodes n.parent.val)
    else False
  | none => False
termination_by x

theorem repeats_above_correct (F : forest.Forest) (node : Usize) :
    ∀ (n : Nat) (ancestor : Usize), ancestor.val = n → forest.repeats_above F node ancestor =
      .ok (decide (∃ v ∈ treePath F.nodes.val ancestor.val, SamePair F.nodes.val node.val v)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ancestor same
    by_cases ancestorIn : ancestor.val < F.nodes.val.length
    · have at_ancestor := List.getElem?_eq_getElem ancestorIn
      have lookupAncestor : F.nodes.index_usize ancestor = .ok F.nodes.val[ancestor.val] := by
        simp [alloc.vec.Vec.index_usize,at_ancestor]
      by_cases tree : F.nodes.val[ancestor.val].tree = true
      · by_cases equal : SamePair F.nodes.val node.val ancestor.val
        · have lhs : forest.repeats_above F node ancestor = .ok true := by
            rw [forest.repeats_above]
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,ancestorIn,lookupAncestor,tree,same_pair_correct,equal]
          rw [lhs]
          congr 1
          symm
          rw [decide_eq_true_iff]
          refine ⟨ancestor.val,?_,equal⟩
          rw [treePath.eq_def,at_ancestor]
          simp only [tree,↓reduceIte]
          split <;> simp
        · by_cases parentVal : F.nodes.val[ancestor.val].parent.val < ancestor.val
          · have rest := ih F.nodes.val[ancestor.val].parent.val (by omega) F.nodes.val[ancestor.val].parent rfl
            have lhs : forest.repeats_above F node ancestor =
                forest.repeats_above F node F.nodes.val[ancestor.val].parent := by
              conv_lhs => rw [forest.repeats_above]
              simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,ancestorIn,lookupAncestor,tree,same_pair_correct,
                equal,parentVal]
            rw [lhs,rest]
            congr 1
            rw [decide_eq_decide]
            have path : treePath F.nodes.val ancestor.val =
                ancestor.val :: treePath F.nodes.val F.nodes.val[ancestor.val].parent.val := by
              rw [treePath.eq_def,at_ancestor]
              simp [tree,dif_pos parentVal]
            rw [path]
            constructor
            · rintro ⟨v,member,pair⟩
              exact ⟨v,List.mem_cons_of_mem _ member,pair⟩
            · rintro ⟨v,member,pair⟩
              rcases List.mem_cons.mp member with rfl | later
              · exact absurd pair equal
              · exact ⟨v,later,pair⟩
          · have lhs : forest.repeats_above F node ancestor = .ok false := by
              rw [forest.repeats_above]
              simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,ancestorIn,lookupAncestor,tree,same_pair_correct,
                equal,parentVal]
            rw [lhs]
            congr 1
            symm
            rw [decide_eq_false_iff_not]
            have path : treePath F.nodes.val ancestor.val = [ancestor.val] := by
              rw [treePath.eq_def,at_ancestor]
              simp [tree,dif_neg parentVal]
            rw [path]
            rintro ⟨v,member,pair⟩
            simp only [List.mem_singleton] at member
            subst member
            exact equal pair
      · have lhs : forest.repeats_above F node ancestor = .ok false := by
          rw [forest.repeats_above]
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,ancestorIn,lookupAncestor,tree]
        rw [lhs]
        congr 1
        symm
        rw [decide_eq_false_iff_not]
        have path : treePath F.nodes.val ancestor.val = [] := by
          rw [treePath.eq_def,at_ancestor]
          simp [tree]
        rw [path]
        simp
    · have lhs : forest.repeats_above F node ancestor = .ok false := by
        rw [forest.repeats_above]
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,ancestorIn]
      rw [lhs]
      congr 1
      symm
      rw [decide_eq_false_iff_not]
      have path : treePath F.nodes.val ancestor.val = [] := by
        rw [treePath.eq_def,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ ancestor.val by omega)]
      rw [path]
      simp

/-- The actual blocking test decides pairwise blocking. -/
theorem blocked_correct (F : forest.Forest) :
    ∀ (n : Nat) (x : Usize), x.val = n → forest.blocked F x = .ok (decide (Blocked F.nodes.val x.val)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x same
    by_cases inside : x.val < F.nodes.val.length
    · have at_x := List.getElem?_eq_getElem inside
      have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
        simp [alloc.vec.Vec.index_usize,at_x]
      have unfold : Blocked F.nodes.val x.val ↔ F.nodes.val[x.val].parent.val < x.val ∧ F.nodes.val[x.val].tree = true ∧
          ((∃ v ∈ treePath F.nodes.val F.nodes.val[x.val].parent.val, SamePair F.nodes.val x.val v) ∨
            Blocked F.nodes.val F.nodes.val[x.val].parent.val) := by
        rw [Blocked.eq_def,at_x]
        simp only
        split
        · rename_i below
          simp [below]
        · rename_i below
          simp [below]
      by_cases tree : F.nodes.val[x.val].tree = true
      · by_cases parentVal : F.nodes.val[x.val].parent.val < x.val
        · have rest := ih F.nodes.val[x.val].parent.val (by omega) F.nodes.val[x.val].parent rfl
          have repeatsRun := repeats_above_correct F x _ F.nodes.val[x.val].parent rfl
          by_cases repeats : ∃ v ∈ treePath F.nodes.val F.nodes.val[x.val].parent.val, SamePair F.nodes.val x.val v
          · have lhs : forest.blocked F x = .ok true := by
              rw [forest.blocked]
              simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,tree,parentVal,repeatsRun]
              simp [repeats]
            rw [lhs]
            congr 1
            symm
            rw [decide_eq_true_iff,unfold]
            exact ⟨parentVal,tree,.inl repeats⟩
          · have lhs : forest.blocked F x = forest.blocked F F.nodes.val[x.val].parent := by
              conv_lhs => rw [forest.blocked]
              simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,tree,parentVal,repeatsRun]
              simp [repeats]
            rw [lhs,rest]
            congr 1
            rw [decide_eq_decide,unfold]
            constructor
            · intro blocked
              exact ⟨parentVal,tree,.inr blocked⟩
            · rintro ⟨_,_,found | blocked⟩
              · exact absurd found repeats
              · exact blocked
        · have lhs : forest.blocked F x = .ok false := by
            rw [forest.blocked]
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,tree,parentVal]
          rw [lhs]
          congr 1
          symm
          rw [decide_eq_false_iff_not,unfold]
          rintro ⟨below,_⟩
          exact parentVal below
      · have lhs : forest.blocked F x = .ok false := by
          rw [forest.blocked]
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,tree]
        rw [lhs]
        congr 1
        symm
        rw [decide_eq_false_iff_not,unfold]
        rintro ⟨_,isTree,_⟩
        exact tree isTree
    · have lhs : forest.blocked F x = .ok false := by
        rw [forest.blocked]
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]
      rw [lhs]
      congr 1
      symm
      rw [decide_eq_false_iff_not,Blocked.eq_def,
        List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)]
      simp

/-- An entry that creates neighbours: an existential or minimum restriction. -/
def Generating : concept_table.Entry → Prop
  | .Exists _ _ | .AtLeast _ _ _ => True
  | _ => False

theorem generating_correct (e : concept_table.Entry) : forest.generating e = .ok (decide (Generating e)) := by
  cases e <;> simp [forest.generating,Generating]

/-- The restrictions a node already expanded. -/
def doneOf (nodes : List forest.Node) (x : Nat) : List Usize :=
  match nodes[x]? with
  | some n => n.done.val
  | none => []

/-- The role, the number of neighbours and the filler of an entry that creates
    neighbours: an existential restriction asks for one. -/
def generatorOf : concept_table.Entry → Option (ObjectPropertyExpression × Usize × Usize)
  | .Exists r c => some (r,1#usize,c)
  | .AtLeast n r c => some (r,n,c)
  | _ => none

theorem generator_of_correct (entries : alloc.vec.Vec concept_table.Entry) (g : Usize) :
    forest.generator_of entries g = .ok (match entries.val[g.val]? with
      | some e => generatorOf e
      | none => none) := by
  rw [forest.generator_of]
  by_cases inside : g.val < entries.val.length
  · have lookup : entries.index_usize g = .ok entries.val[g.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,List.getElem?_eq_getElem inside]
    cases entries.val[g.val] <;> simp [generatorOf,copy_role_identity]
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,List.getElem?_eq_none_iff.mpr
      (show entries.val.length ≤ g.val by omega)]

/-- At least `n` neighbours along `r` satisfy `c`. -/
def Enough (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (c n : Usize) : Prop :=
  ∃ list : List Usize, list.Nodup ∧ n.val ≤ list.length ∧
    ∀ z ∈ list, Neighbour P h F x r z.val ∧ Holds P.entries.val (labelOf F.nodes.val z.val) c.val

/-- Enough neighbours satisfy the filler exactly when the filter is long enough. -/
theorem enough_iff (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (c n : Usize) (list : List Usize)
    (members : ∀ z : Usize, z ∈ list ↔ Neighbour P h F x r z.val) (nodup : list.Nodup) :
    Enough P h F x r c n ↔
      n.val ≤ (list.filter (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val))).length := by
  constructor
  · rintro ⟨many,manyNodup,longer,inside⟩
    have sub : many ⊆ list.filter (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val)) := by
      intro z member
      obtain ⟨neighbour,holds⟩ := inside z member
      exact List.mem_filter.mpr ⟨(members z).mpr neighbour,by simpa using holds⟩
    have := (manyNodup.subperm sub).length_le
    omega
  · intro longer
    refine ⟨_,nodup.filter _,longer,?_⟩
    intro z member
    obtain ⟨listed,holds⟩ := List.mem_filter.mp member
    exact ⟨(members z).mp listed,by simpa using holds⟩

theorem enough_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x g : Usize) :
    ∃ r, forest.enough P h F x g = .ok r ∧ ∀ b, r = some b → ∃ e role c n, P.entries.val[g.val]? = some e ∧
      generatorOf e = some (role,n,c) ∧ (b = true ↔ Enough P h F x.val role c n) := by
  rw [forest.enough,generator_of_correct]
  cases at_g : P.entries.val[g.val]? with
  | none => exact ⟨none,by simp,by simp⟩
  | some e =>
    cases gen : generatorOf e with
    | none => exact ⟨none,by simp [gen],by simp⟩
    | some found =>
      obtain ⟨role,n,c⟩ := found
      obtain ⟨list,listRun,listSpec⟩ := neighbours_correct P h F x role
      cases list with
      | none => exact ⟨none,by simp [gen,listRun],by simp⟩
      | some list =>
        obtain ⟨members,nodup⟩ := listSpec list rfl
        obtain ⟨many,manyRun,manySpec⟩ := satisfying_correct P.entries F list c 0#usize (alloc.vec.Vec.new Usize)
        cases many with
        | none => exact ⟨none,by simp [gen,listRun,manyRun],by simp⟩
        | some kept =>
          have keptIs : kept.val = list.val.filter
              (fun y => decide (Holds P.entries.val (labelOf F.nodes.val y.val) c.val)) := by
            simpa using manySpec kept rfl
          refine ⟨some (decide (n.val ≤ kept.val.length)),?_,?_⟩
          · simp [gen,listRun,manyRun]
          · intro b same
            cases same
            refine ⟨e,role,c,n,rfl,gen,?_⟩
            rw [enough_iff P h F x.val role c n list.val members nodup,← keptIs]
            simp

/-- The entry creates neighbours and, when `expand`, was not expanded at the node. -/
def Candidate (P : completion.Problem) (F : forest.Forest) (x : Nat) (i : Usize) (expand : Bool) : Prop :=
  x < F.nodes.val.length ∧ (∃ e role c n, P.entries.val[i.val]? = some e ∧ generatorOf e = some (role,n,c)) ∧
    (expand = true → i ∉ doneOf F.nodes.val x)

theorem generating_iff (e : concept_table.Entry) : Generating e ↔ ∃ role c n, generatorOf e = some (role,n,c) := by
  cases e <;> simp [Generating,generatorOf]

theorem candidate_correct (P : completion.Problem) (F : forest.Forest) (x i : Usize) (expand : Bool) :
    forest.candidate P F x i expand = .ok (decide (Candidate P F x.val i expand)) := by
  rw [forest.candidate]
  by_cases itemInside : i.val < P.entries.val.length
  · by_cases inside : x.val < F.nodes.val.length
    · have entryLookup : P.entries.index_usize i = .ok P.entries.val[i.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemInside]
      have nodeLookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
      have doneIs : doneOf F.nodes.val x.val = F.nodes.val[x.val].done.val := by
        simp [doneOf,List.getElem?_eq_getElem inside]
      have genIff : (∃ e role c n, P.entries.val[i.val]? = some e ∧ generatorOf e = some (role,n,c)) ↔
          Generating P.entries.val[i.val] := by
        rw [generating_iff]
        simp [List.getElem?_eq_getElem itemInside]
      unfold Candidate
      rw [genIff,doneIs]
      by_cases gen : Generating P.entries.val[i.val]
      · cases expand with
        | true =>
          by_cases listed : i ∈ F.nodes.val[x.val].done.val
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,itemInside,inside,entryLookup,generating_correct,gen,
              nodeLookup,contains_correct,listed]
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,itemInside,inside,entryLookup,generating_correct,gen,
              nodeLookup,contains_correct,listed]
        | false =>
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,itemInside,inside,entryLookup,generating_correct,gen]
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,itemInside,inside,entryLookup,generating_correct,gen]
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,itemInside,inside,Candidate]
  · have absent : ¬ ∃ e role c n, P.entries.val[i.val]? = some e ∧ generatorOf e = some (role,n,c) := by
      rintro ⟨e,_,_,_,at_e,_⟩
      have := (List.getElem?_eq_some_iff.mp at_e).1
      omega
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,itemInside,Candidate,absent]

theorem lacking_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Usize)
    (expand : Bool) (index : Usize) :
    ∃ r, forest.lacking P h F x expand index = .ok r ∧
      (∀ i, r = some (some i) → i ∈ (labelOf F.nodes.val x.val).drop index.val ∧ ∃ e role c n,
        P.entries.val[i.val]? = some e ∧ generatorOf e = some (role,n,c) ∧ (expand = true → i ∉ doneOf F.nodes.val x.val) ∧
        ¬ Enough P h F x.val role c n) ∧
      (r = some none → ∀ i ∈ (labelOf F.nodes.val x.val).drop index.val, ∀ e role c n,
        P.entries.val[i.val]? = some e → generatorOf e = some (role,n,c) →
        (expand = true → i ∉ doneOf F.nodes.val x.val) → Enough P h F x.val role c n) := by
  rw [forest.lacking]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have labelIs : labelOf F.nodes.val x.val = F.nodes.val[x.val].label.val := by
      simp [labelOf,List.getElem?_eq_getElem inside]
    rw [labelIs]
    by_cases more : index.val < F.nodes.val[x.val].label.val.length
    · have itemLookup : F.nodes.val[x.val].label.index_usize index =
          .ok F.nodes.val[x.val].label.val[index.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      have split : F.nodes.val[x.val].label.val.drop index.val =
          F.nodes.val[x.val].label.val[index.val] :: F.nodes.val[x.val].label.val.drop (index.val+1) :=
        List.drop_eq_getElem_cons more
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,found,absent⟩ := lacking_correct P h F x expand index'
      rw [labelIs,nextIndex] at found absent
      obtain ⟨item,itemIs⟩ : ∃ item, F.nodes.val[x.val].label.val[index.val] = item := ⟨_,rfl⟩
      rw [itemIs] at itemLookup split
      have candRun := candidate_correct P F x item expand
      have foundRest : ∀ i, r = some (some i) → i ∈ F.nodes.val[x.val].label.val.drop index.val ∧ ∃ e role c n,
          P.entries.val[i.val]? = some e ∧ generatorOf e = some (role,n,c) ∧
          (expand = true → i ∉ doneOf F.nodes.val x.val) ∧ ¬ Enough P h F x.val role c n := by
        intro i same
        obtain ⟨member,rest⟩ := found i same
        exact ⟨by rw [split]; exact List.mem_cons_of_mem _ member,rest⟩
      have absentRest : (∀ e role c n, P.entries.val[item.val]? = some e → generatorOf e = some (role,n,c) →
          (expand = true → item ∉ doneOf F.nodes.val x.val) → Enough P h F x.val role c n) →
          r = some none → ∀ i ∈ F.nodes.val[x.val].label.val.drop index.val, ∀ e role c n,
            P.entries.val[i.val]? = some e → generatorOf e = some (role,n,c) →
            (expand = true → i ∉ doneOf F.nodes.val x.val) → Enough P h F x.val role c n := by
        intro here none i member e role c n at_i gen notDone
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | rest
        · exact here e role c n at_i gen notDone
        · exact absent none i rest e role c n at_i gen notDone
      by_cases cand : Candidate P F x.val item expand
      · obtain ⟨_,⟨e,role,c,n,at_e,gen⟩,notDone⟩ := cand
        obtain ⟨b,bRun,bSpec⟩ := enough_correct P h F x item
        cases b with
        | none =>
          refine ⟨none,?_,by simp,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,candRun,
            show Candidate P F x.val item expand from ⟨inside,⟨e,role,c,n,at_e,gen⟩,notDone⟩,bRun]
        | some b =>
          obtain ⟨e',role',c',n',at_e',gen',enoughIff⟩ := bSpec b rfl
          rw [at_e] at at_e'
          cases at_e'
          rw [gen] at gen'
          simp only [Option.some.injEq,Prod.mk.injEq] at gen'
          obtain ⟨rfl,rfl,rfl⟩ := gen'
          cases b with
          | true =>
            refine ⟨r,?_,foundRest,absentRest (fun e' role' c' n' at_e' gen'' _ => ?_)⟩
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,candRun,
                show Candidate P F x.val item expand from ⟨inside,⟨e,role,c,n,at_e,gen⟩,notDone⟩,bRun,advance,run]
            · rw [at_e] at at_e'
              cases at_e'
              rw [gen] at gen''
              simp only [Option.some.injEq,Prod.mk.injEq] at gen''
              obtain ⟨rfl,rfl,rfl⟩ := gen''
              exact enoughIff.mp rfl
          | false =>
            refine ⟨some (some item),?_,?_,by simp⟩
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,candRun,
                show Candidate P F x.val item expand from ⟨inside,⟨e,role,c,n,at_e,gen⟩,notDone⟩,bRun]
            · intro i same
              cases same
              refine ⟨by rw [split]; exact List.mem_cons_self ..,e,role,c,n,at_e,gen,notDone,?_⟩
              intro enough
              have := enoughIff.mpr enough
              cases this
      · refine ⟨r,?_,foundRest,absentRest ?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,candRun,cand,advance,run]
        · intro e role c n at_e gen notDone
          exact absurd ⟨inside,⟨e,role,c,n,at_e,gen⟩,notDone⟩ cand
    · refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more],by simp,?_⟩
      intro _ i member
      rw [List.drop_eq_nil_iff.mpr (by omega)] at member
      cases member
  · have empty : labelOf F.nodes.val x.val = [] := by
      simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)]
    refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,?_⟩
    intro _ i member
    rw [empty] at member
    simp at member
termination_by (labelOf F.nodes.val x.val).length - index.val
decreasing_by
  all_goals
    simp only [labelOf,List.getElem?_eq_getElem inside]
    omega

theorem missing_successor_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (expand : Bool) (index : Usize) :
    ∃ r, forest.missing_successor P h F expand index = .ok r ∧
      (∀ x i, r = some (some (x,i)) → Active F.nodes.val x.val ∧ ¬ Blocked F.nodes.val x.val ∧
        i ∈ labelOf F.nodes.val x.val ∧ ∃ e role c n, P.entries.val[i.val]? = some e ∧
        generatorOf e = some (role,n,c) ∧ (expand = true → i ∉ doneOf F.nodes.val x.val) ∧
        ¬ Enough P h F x.val role c n) ∧
      (r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y → ¬ Blocked F.nodes.val y →
        ∀ i ∈ labelOf F.nodes.val y, ∀ e role c n, P.entries.val[i.val]? = some e →
          generatorOf e = some (role,n,c) → (expand = true → i ∉ doneOf F.nodes.val y) →
          Enough P h F y role c n) := by
  rw [forest.missing_successor]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_successor_correct P h F expand index'
    have skip : (Active F.nodes.val index.val → ¬ Blocked F.nodes.val index.val →
        ∀ i ∈ labelOf F.nodes.val index.val, ∀ e role c n, P.entries.val[i.val]? = some e →
          generatorOf e = some (role,n,c) → (expand = true → i ∉ doneOf F.nodes.val index.val) →
          Enough P h F index.val role c n) → r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y →
        ¬ Blocked F.nodes.val y → ∀ i ∈ labelOf F.nodes.val y, ∀ e role c n, P.entries.val[i.val]? = some e →
          generatorOf e = some (role,n,c) → (expand = true → i ∉ doneOf F.nodes.val y) →
          Enough P h F y role c n := by
      intro here none y low isActive free
      by_cases same : y = index.val
      · subst same
        exact here isActive free
      · exact absent none y (by omega) isActive free
    have blockedRun := blocked_correct F index.val index rfl
    by_cases active : F.nodes.val[index.val].active = true
    · by_cases blocked : Blocked F.nodes.val index.val
      · refine ⟨r,?_,found,skip (fun _ free => absurd blocked free)⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,blockedRun,blocked,advance,run]
      · obtain ⟨l,lRun,lFound,lAbsent⟩ := lacking_correct P h F index expand 0#usize
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at lFound lAbsent
        cases l with
        | none =>
          refine ⟨none,?_,by simp,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,blockedRun,blocked,lRun]
        | some item =>
          cases item with
          | none =>
            refine ⟨r,?_,found,skip (fun _ _ => lAbsent rfl)⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,blockedRun,blocked,lRun,advance,run]
          | some i =>
            refine ⟨some (some (index,i)),?_,?_,by simp⟩
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,blockedRun,blocked,lRun]
            · intro x i' same
              simp only [Option.some.injEq,Prod.mk.injEq] at same
              obtain ⟨rfl,rfl⟩ := same
              obtain ⟨member,rest⟩ := lFound i rfl
              exact ⟨⟨_,at_index,active⟩,blocked,member,rest⟩
    · refine ⟨r,?_,found,skip ?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,advance,run]
      · intro isActive
        obtain ⟨n,at_n,yes⟩ := isActive
        rw [at_index] at at_n
        cases at_n
        exact absurd yes active
  · refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low ⟨n,at_n,_⟩
    have := (List.getElem?_eq_some_iff.mp at_n).1
    omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

/-- Something an active node or an edge requires of node `y`. -/
def AddNeeds (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (y : Nat) (c : Usize) :
    Prop :=
  (Active F.nodes.val y ∧ NodeNeeds P F y c) ∨ TreeNeeds P.entries.val h F.nodes.val y c ∨
    LinkNeeds P.entries.val h F (linkEnds P.links.val) y c ∨ LinkNeeds P.entries.val h F (edgeEnds F.edges.val) y c

/-- No rule applies: every active node has what it needs, every edge gives each
    end what the other requires, every neighbour that a maximum restriction
    counts decides its filler, no maximum restriction counts too many
    neighbours, and every existential and minimum restriction of an unblocked
    active node has enough neighbours satisfying its filler. -/
def Complete (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) : Prop :=
  (∀ y, Active F.nodes.val y → ∀ c, NodeNeeds P F y c → Holds P.entries.val (labelOf F.nodes.val y) c.val) ∧
  (∀ child n, F.nodes.val[child]? = some n → n.tree = true → n.active = true →
    n.parent.val < F.nodes.val.length → ∀ s ∈ n.roles.val,
      EdgeOk P.entries.val h (labelOf F.nodes.val n.parent.val) s (labelOf F.nodes.val child) ∧
      EdgeOk P.entries.val h (labelOf F.nodes.val child) (inv s) (labelOf F.nodes.val n.parent.val)) ∧
  LinksOk P.entries.val h F (linkEnds P.links.val) ∧ LinksOk P.entries.val h F (edgeEnds F.edges.val) ∧
  (∀ y, Active F.nodes.val y → CountOk P h F true y) ∧ (∀ y, Active F.nodes.val y → CountOk P h F false y) ∧
  (∀ y, Active F.nodes.val y → ¬ Blocked F.nodes.val y → ∀ i ∈ labelOf F.nodes.val y, ∀ e role c n,
    P.entries.val[i.val]? = some e → generatorOf e = some (role,n,c) → Enough P h F y role c n)

/-- The rule search returns a concept that a node lacks and that a node or edge
    requires, a neighbour to decide, a maximum restriction with too many
    neighbours, or a restriction to expand at an unblocked node; it reports
    `Done` exactly for a complete forest. -/
theorem next_step_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) :
    ∃ r, forest.next_step P h F = .ok r ∧
      (∀ y c, r = some (.Add y c) → y.val < F.nodes.val.length ∧ AddNeeds P h F y.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) ∧
      (∀ y c c', r = some (.Choose y c c') → ∃ x : Usize, Active F.nodes.val x.val ∧
        CountStep P h F true x (.Choose y c c')) ∧
      (∀ x i, r = some (.Merge x i) → Active F.nodes.val x.val ∧ CountStep P h F false x (.Merge x i)) ∧
      (∀ x i, r = some (.Create x i) → Active F.nodes.val x.val ∧ ¬ Blocked F.nodes.val x.val ∧
        i ∈ labelOf F.nodes.val x.val ∧ ∃ e role c n, P.entries.val[i.val]? = some e ∧
        generatorOf e = some (role,n,c) ∧ i ∉ doneOf F.nodes.val x.val ∧ ¬ Enough P h F x.val role c n) ∧
      (r = some .Done → Complete P h F) := by
  rw [forest.next_step]
  have zero : (0#usize).val = 0 := rfl
  obtain ⟨r0,run0,found0,absent0⟩ := missing_node_correct P F 0#usize
  cases r0 with
  | some pair =>
    obtain ⟨y,c⟩ := pair
    obtain ⟨⟨n,at_y,act⟩,needs,fails⟩ := found0 y c rfl
    refine ⟨some (.Add y c),by simp [run0],?_,by simp,by simp,by simp,by simp⟩
    intro y' c' same
    simp only [Option.some.injEq,forest.Step.Add.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨(List.getElem?_eq_some_iff.mp at_y).1,.inl ⟨⟨n,at_y,act⟩,needs⟩,fails⟩
  | none =>
  obtain ⟨r1,run1,found1,absent1⟩ := missing_tree_correct P h F 0#usize
  cases r1 with
  | some pair =>
    obtain ⟨y,c⟩ := pair
    obtain ⟨inside,needs,fails⟩ := found1 y c rfl
    refine ⟨some (.Add y c),by simp [run0,run1],?_,by simp,by simp,by simp,by simp⟩
    intro y' c' same
    simp only [Option.some.injEq,forest.Step.Add.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨inside,.inr (.inl needs),fails⟩
  | none =>
  obtain ⟨r2,run2,found2,absent2⟩ := missing_link_correct P h F 0#usize
  cases r2 with
  | some pair =>
    obtain ⟨y,c⟩ := pair
    obtain ⟨inside,needs,fails⟩ := found2 y c rfl
    refine ⟨some (.Add y c),by simp [run0,run1,run2],?_,by simp,by simp,by simp,by simp⟩
    intro y' c' same
    simp only [Option.some.injEq,forest.Step.Add.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨inside,.inr (.inr (.inl needs)),fails⟩
  | none =>
  obtain ⟨r3,run3,found3,absent3⟩ := missing_added_correct P h F 0#usize
  cases r3 with
  | some pair =>
    obtain ⟨y,c⟩ := pair
    obtain ⟨inside,needs,fails⟩ := found3 y c rfl
    refine ⟨some (.Add y c),by simp [run0,run1,run2,run3],?_,by simp,by simp,by simp,by simp⟩
    intro y' c' same
    simp only [Option.some.injEq,forest.Step.Add.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨inside,.inr (.inr (.inr needs)),fails⟩
  | none =>
  obtain ⟨r4,run4,found4,absent4⟩ := counting_correct P h F true 0#usize
  cases r4 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run4],by simp,by simp,by simp,by simp,by simp⟩
  | some r5 =>
  cases r5 with
  | some step =>
    obtain ⟨x,active,i,member,n,role,c,c',at_i,y,isChoose,neighbour,one,two⟩ := found4 step rfl
    subst isChoose
    refine ⟨some (.Choose y c c'),by simp [run0,run1,run2,run3,run4],by simp,?_,by simp,by simp,by simp⟩
    intro y' d d' same
    simp only [Option.some.injEq,forest.Step.Choose.injEq] at same
    obtain ⟨rfl,rfl,rfl⟩ := same
    exact ⟨x,active,i,member,n,role,c,c',at_i,y,rfl,neighbour,one,two⟩
  | none =>
  obtain ⟨r6,run6,found6,absent6⟩ := counting_correct P h F false 0#usize
  cases r6 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run4,run6],by simp,by simp,by simp,by simp,by simp⟩
  | some r7 =>
  cases r7 with
  | some step =>
    obtain ⟨x,active,i,member,n,role,c,c',at_i,isMerge,excess⟩ := found6 step rfl
    subst isMerge
    refine ⟨some (.Merge x i),by simp [run0,run1,run2,run3,run4,run6],by simp,by simp,?_,by simp,by simp⟩
    intro x' i' same
    simp only [Option.some.injEq,forest.Step.Merge.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨active,i,member,n,role,c,c',at_i,rfl,excess⟩
  | none =>
  obtain ⟨r8,run8,found8,absent8⟩ := missing_successor_correct P h F true 0#usize
  cases r8 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run4,run6,run8],by simp,by simp,by simp,by simp,by simp⟩
  | some r9 =>
  cases r9 with
  | some pair =>
    obtain ⟨x,i⟩ := pair
    refine ⟨some (.Create x i),by simp [run0,run1,run2,run3,run4,run6,run8],by simp,by simp,by simp,?_,by simp⟩
    intro x' i' same
    simp only [Option.some.injEq,forest.Step.Create.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    obtain ⟨active,free,member,e,role,c,n,at_i,gen,notDone,short⟩ := found8 x i rfl
    exact ⟨active,free,member,e,role,c,n,at_i,gen,notDone rfl,short⟩
  | none =>
  obtain ⟨r10,run10,found10,absent10⟩ := missing_successor_correct P h F false 0#usize
  cases r10 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run4,run6,run8,run10],by simp,by simp,by simp,by simp,by simp⟩
  | some r11 =>
  cases r11 with
  | some pair => exact ⟨some .Stuck,by simp [run0,run1,run2,run3,run4,run6,run8,run10],by simp,by simp,by simp,by simp,
      by simp⟩
  | none =>
  refine ⟨some .Done,by simp [run0,run1,run2,run3,run4,run6,run8,run10],by simp,by simp,by simp,by simp,?_⟩
  intro _
  rw [zero] at absent2 absent3
  refine ⟨fun y isActive c needs => absent0 rfl y (Nat.zero_le _) isActive c needs,
    fun child n at_child tree active parentIn s member =>
      absent1 rfl child n (Nat.zero_le _) at_child tree active parentIn s member,
    by simpa using absent2 rfl,by simpa using absent3 rfl,
    fun y isActive => absent4 rfl y (Nat.zero_le _) isActive,
    fun y isActive => absent6 rfl y (Nat.zero_le _) isActive,
    fun y isActive free i member e role c n at_i gen =>
      absent10 rfl y (Nat.zero_le _) isActive free i member e role c n at_i gen (by simp)⟩

end Rowl.ForestSearch
