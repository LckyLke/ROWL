import Rowl.Completion

/-!
The rule search of the completion forest, proved exact. A neighbour of a node
along a role is an active child whose edge has a role included in it, the
parent of a tree node whose edge has a role whose inverse is included in it, a
named node that a link relates to it, a node that an added edge from a live
node (active and not blocked) relates to it, read through the merges of named
nodes, or the node itself when a self restriction `∃s.Self` of its label is a
loop along the role. The named node of an individual is the representative of
the node of the first requirement with its nominal. The search returns the
first missing concept of a node, an edge or a loop (with the seeds of tree
nodes and of new named nodes), else an active node with `¬∃r.Self` that is its
own neighbour along `r`, or with a common neighbour along the two roles of a
disjoint pair of the hierarchy, which is a clash, else an active node with a
nominal whose named node is another node,
else a neighbour that does not decide the filler of a maximum restriction, else,
for a maximum restriction of a named node that counts a tree node that is no
child of it, new named nodes when the restriction has no bound from them yet
and the merge into them when it has, else a maximum restriction with too many
neighbours, else an existential or minimum restriction of an unblocked node to
expand, and it reports a complete forest exactly when none of these exists; it
has no answer when the individual of a nominal, or of the complement of one, in
the label of an active node has no named node, or when a restriction with a
bound has fewer counted named neighbours than the bound. Blocking is pairwise: a tree node is
blocked when some tree node on its path has the label, the parent's label and
the roles from the parent of a tree node above it whose parent is a tree node.
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

/-- The node is part of the forest. -/
def Active (nodes : List forest.Node) (x : Nat) : Prop :=
  ∃ n, nodes[x]? = some n ∧ n.active = true

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
    the same roles from their parents, where the parent of `y` is a tree node. -/
def SamePair (nodes : List forest.Node) (x y : Nat) : Prop :=
  ∃ nx ny, nodes[x]? = some nx ∧ nodes[y]? = some ny ∧ nx.parent.val < nodes.length ∧
    ny.parent.val < nodes.length ∧ (∃ q, nodes[ny.parent.val]? = some q ∧ q.tree = true) ∧
    SameLabel nx.label.val ny.label.val ∧
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
          (∃ q, F.nodes.val[F.nodes.val[y.val].parent.val]? = some q ∧ q.tree = true) ∧
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
          have parentTree : (∃ q, F.nodes.val[F.nodes.val[y.val].parent.val]? = some q ∧ q.tree = true) ↔
              F.nodes.val[F.nodes.val[y.val].parent.val].tree = true := by
            simp [List.getElem?_eq_getElem py]
          rw [parentTree]
          by_cases treeParent : F.nodes.val[F.nodes.val[y.val].parent.val].tree = true
          swap
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,yIn,lookupX,lookupY,px,py,lookupPY,treeParent]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,yIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookupX,lookupY,bind_ok,px,py,same_label_correct,lookupPX,lookupPY,roles_within_correct,
            show (0#usize).val = 0 from rfl,List.drop_zero,true_and,treeParent]
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

/-- The node is part of the model: active and not blocked, so its added edges
    count. -/
def Live (nodes : List forest.Node) (x : Nat) : Prop := Active nodes x ∧ ¬ Blocked nodes x

theorem live_correct (F : forest.Forest) (x : Usize) : forest.live F x = .ok (decide (Live F.nodes.val x.val)) := by
  rw [forest.live]
  by_cases inside : x.val < F.nodes.val.length
  · have at_x := List.getElem?_eq_getElem inside
    have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,at_x]
    by_cases act : F.nodes.val[x.val].active = true
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,act,blocked_correct F _ x rfl,Live,Active,at_x]
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,act,Live,Active,at_x]
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,Live,Active,
      List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)]

/-- The added edges whose source, read through the merges, is live. -/
noncomputable def liveEdges (F : forest.Forest) (edges : List forest.Edge) : List forest.Edge :=
  edges.filter (fun e => decide (Live F.nodes.val (rep F e.from).val))

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
      (∀ z : Usize, z ∈ out'.val ↔ z ∈ out.val ∨
        LinkAlong h F (edgeEnds (liveEdges F (F.edges.val.drop index.val))) x.val r z.val) ∧
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
    by_cases isLive : Live F.nodes.val (rep F F.edges.val[index.val].from).val
    · have liveSplit : liveEdges F (F.edges.val.drop index.val) =
          F.edges.val[index.val] :: liveEdges F (F.edges.val.drop (index.val+1)) := by
        rw [split,liveEdges,List.filter_cons_of_pos (by simpa using isLive)]
        rfl
      obtain ⟨found,foundRun,foundSpec⟩ := ends_correct h out (rep F F.edges.val[index.val].from)
        (rep F F.edges.val[index.val].to) F.edges.val[index.val].role x r
      cases found with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,representative_correct,live_correct,decide_eq_true isLive,foundRun]
      | some mid =>
        obtain ⟨midMembers,midNodup⟩ := foundSpec mid rfl
        obtain ⟨res,run,spec⟩ := edges_along_correct F h x r index' mid
        refine ⟨res,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,representative_correct,live_correct,decide_eq_true isLive,foundRun,advance,run]
        · intro out' same
          obtain ⟨members,nodup⟩ := spec out' same
          refine ⟨fun z => ?_,fun start => nodup (midNodup start)⟩
          rw [members,midMembers,nextIndex,liveSplit]
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
    · have liveSplit : liveEdges F (F.edges.val.drop index.val) = liveEdges F (F.edges.val.drop (index.val+1)) := by
        rw [split,liveEdges,List.filter_cons_of_neg (by simpa using isLive)]
        rfl
      obtain ⟨res,run,spec⟩ := edges_along_correct F h x r index' out
      refine ⟨res,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,representative_correct,live_correct,decide_eq_false isLive,Bool.false_eq_true,advance,run]
      · intro out' same
        obtain ⟨members,nodup⟩ := spec out' same
        refine ⟨fun z => ?_,nodup⟩
        rw [members,nextIndex,liveSplit]
  · have empty : F.edges.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    refine ⟨fun z => ?_,id⟩
    simp [empty,LinkAlong,edgeEnds,liveEdges]
termination_by F.edges.val.length - index.val
decreasing_by all_goals omega

/-- `y` is `x` itself, with a loop along `r`: the label of `x` has a self
    restriction `∃s.Self` with `s` or its inverse included in `r`. -/
def SelfAlong (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (y : Nat) : Prop :=
  y = x ∧ ∃ i ∈ labelOf F.nodes.val x, ∃ s, P.entries.val[i.val]? = some (.HasSelf s) ∧
    (Below h s r ∨ Below h (inv s) r)

/-- The loop test of an entry is exact. -/
theorem looping_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy) (item : Usize)
    (r : ObjectPropertyExpression) :
    forest.looping entries h item r = .ok (decide (∃ s, entries.val[item.val]? = some (.HasSelf s) ∧
      (Below h s r ∨ Below h (inv s) r))) := by
  rw [forest.looping]
  by_cases inside : item.val < entries.val.length
  · have lookup : entries.index_usize item = .ok entries.val[item.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have at_item := List.getElem?_eq_getElem inside
    obtain ⟨e,eIs⟩ : ∃ e, entries.val[item.val] = e := ⟨_,rfl⟩
    rw [eIs] at lookup at_item
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,at_item]
    cases e with
    | HasSelf s =>
      simp only [below_correct,inverse_correct,bind_ok,Option.some.injEq,concept_table.Entry.HasSelf.injEq,
        exists_eq_left']
      by_cases first : Below h s r <;> simp [first]
    | _ => simp
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,
      List.getElem?_eq_none_iff.mpr (show entries.val.length ≤ item.val by omega)]

/-- The loop test of a label is exact. -/
theorem self_along_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (label : alloc.vec.Vec Usize) (r : ObjectPropertyExpression) (index : Usize) :
    forest.self_along entries h label r index = .ok (decide (∃ i ∈ label.val.drop index.val, ∃ s,
      entries.val[i.val]? = some (.HasSelf s) ∧ (Below h s r ∨ Below h (inv s) r))) := by
  rw [forest.self_along]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : label.val.drop index.val = label.val[index.val] :: label.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := self_along_correct entries h label r index'
    rw [nextIndex] at rest
    rw [split]
    by_cases here : ∃ s, entries.val[label.val[index.val].val]? = some (.HasSelf s) ∧
        (Below h s r ∨ Below h (inv s) r)
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,looping_correct,here,decide_true]
      exact congrArg _ (decide_eq_true ⟨_,List.mem_cons_self ..,here⟩).symm
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,looping_correct,here,decide_false,Bool.false_eq_true,advance,rest]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨i,member,found⟩
        exact ⟨i,List.mem_cons_of_mem _ member,found⟩
      · rintro ⟨i,member,found⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact absurd found here
        · exact ⟨i,later,found⟩
  · have empty : label.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by label.val.length - index.val
decreasing_by omega

theorem loops_along_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Usize)
    (r : ObjectPropertyExpression) (out : alloc.vec.Vec Usize) :
    ∃ res, forest.loops_along P h F x r out = .ok res ∧ ∀ out', res = some out' →
      (∀ z : Usize, z ∈ out'.val ↔ z ∈ out.val ∨ SelfAlong P h F x.val r z.val) ∧
      (out.val.Nodup → out'.val.Nodup) := by
  rw [forest.loops_along]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have labelIs : labelOf F.nodes.val x.val = F.nodes.val[x.val].label.val := by
      simp [labelOf,List.getElem?_eq_getElem inside]
    have selfIff : ∀ z : Usize, SelfAlong P h F x.val r z.val ↔ z = x ∧
        ∃ i ∈ F.nodes.val[x.val].label.val, ∃ s, P.entries.val[i.val]? = some (.HasSelf s) ∧
          (Below h s r ∨ Below h (inv s) r) := by
      intro z
      rw [SelfAlong,labelIs]
      constructor
      · rintro ⟨same,found⟩
        exact ⟨UScalar.eq_of_val_eq same,found⟩
      · rintro ⟨rfl,found⟩
        exact ⟨rfl,found⟩
    by_cases found : ∃ i ∈ F.nodes.val[x.val].label.val, ∃ s, P.entries.val[i.val]? = some (.HasSelf s) ∧
        (Below h s r ∨ Below h (inv s) r)
    · obtain ⟨pushed,pushRun,pushSpec⟩ := with_node_correct out x
      refine ⟨pushed,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,self_along_correct,show (0#usize).val = 0 from rfl,List.drop_zero,found,decide_true,
          pushRun]
      · intro out' same
        obtain ⟨members,nodup⟩ := pushSpec out' same
        refine ⟨?_,nodup⟩
        intro z
        rw [members,selfIff]
        constructor
        · rintro (old | rfl)
          · exact .inl old
          · exact .inr ⟨rfl,found⟩
        · rintro (old | ⟨rfl,_⟩)
          · exact .inl old
          · exact .inr rfl
    · refine ⟨some out,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,self_along_correct,show (0#usize).val = 0 from rfl,List.drop_zero,found,decide_false,
          Bool.false_eq_true]
      · intro out' same
        cases same
        refine ⟨?_,id⟩
        intro z
        rw [selfIff]
        constructor
        · exact .inl
        · rintro (old | ⟨_,found'⟩)
          · exact old
          · exact absurd found' found
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],?_⟩
    intro out' same
    cases same
    refine ⟨?_,id⟩
    intro z
    constructor
    · exact .inl
    · rintro (old | ⟨_,i,member,_⟩)
      · exact old
      · simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)] at member

/-- `y` is a neighbour of `x` along `r`: an active child, the parent, a named
    node related by a link, a node related by an added edge from a live node, or
    `x` itself with a loop. -/
def Neighbour (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (y : Nat) : Prop :=
  ChildAlong h F.nodes.val x r y ∨ ParentAlong h F.nodes.val x r y ∨
    LinkAlong h F (linkEnds P.links.val) x r y ∨ LinkAlong h F (edgeEnds (liveEdges F F.edges.val)) x r y ∨
    SelfAlong P h F x r y

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
        cases four with
        | none => exact ⟨none,by simp [oneRun,twoRun,threeRun,fourRun],by simp⟩
        | some out4 =>
          obtain ⟨members4,nodup4⟩ := fourSpec out4 rfl
          obtain ⟨five,fiveRun,fiveSpec⟩ := loops_along_correct P h F x r out4
          refine ⟨five,by simp [oneRun,twoRun,threeRun,fourRun,fiveRun],?_⟩
          intro list same
          obtain ⟨members5,nodup5⟩ := fiveSpec list same
          refine ⟨fun z => ?_,nodup5 (nodup4 (nodup3 (nodup2 (nodup1 (by simp)))))⟩
          rw [members5,members4,members3,members2,members1]
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

/-- A node with a seed: a tree node, or a named node beyond the individuals'
    nodes. -/
def Seeded (F : forest.Forest) (x : Nat) : Prop :=
  ∃ n, F.nodes.val[x]? = some n ∧ (n.tree = true ∨ F.same.val.length ≤ x)

theorem seeded_correct (F : forest.Forest) (x : Usize) : forest.seeded F x = .ok (decide (Seeded F x.val)) := by
  rw [forest.seeded]
  by_cases inside : x.val < F.nodes.val.length
  · have at_x := List.getElem?_eq_getElem inside
    have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by simp [alloc.vec.Vec.index_usize,at_x]
    by_cases tree : F.nodes.val[x.val].tree = true
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,tree,Seeded,at_x]
    · by_cases low : x.val < F.same.val.length
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,tree,low,Seeded,at_x]
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,tree,low,Seeded,at_x]
        omega
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,Seeded,
      List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)]

/-- What an active node must satisfy: the requirements of the individuals merged
    into it, the TBox concept, the unfoldings of the classes it lists, and the
    seed of a tree node or of a named node beyond the individuals' nodes. -/
def NodeNeeds (P : completion.Problem) (F : forest.Forest) (x : Nat) (c : Usize) : Prop :=
  (∃ q ∈ P.requirements.val, (rep F q.node).val = x ∧ c = q.concept) ∨ c = P.axioms ∨
  (∃ u ∈ P.unfoldings.val, HasAtom P.entries.val (labelOf F.nodes.val x) u.class ∧ c = u.concept) ∨
  (∃ n, F.nodes.val[x]? = some n ∧ (n.tree = true ∨ F.same.val.length ≤ x) ∧ c = n.seed)

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
          have rest : ∀ c, NodeNeeds P F x.val c → (∀ n, F.nodes.val[x.val]? = some n →
              (n.tree = true ∨ F.same.val.length ≤ x.val) →
              c = n.seed → Holds P.entries.val F.nodes.val[x.val].label.val c.val) →
              Holds P.entries.val F.nodes.val[x.val].label.val c.val := by
            intro c needs seedHolds
            rcases needs with ⟨q,member,at_q,rfl⟩ | rfl | ⟨u,member,atom,rfl⟩ | ⟨n,at_n,seeded,rfl⟩
            · exact absent1 rfl q member (UScalar.eq_of_val_eq at_q)
            · exact axiomsHold
            · rw [labelIs] at atom; exact absent2 rfl u member atom
            · exact seedHolds n at_n seeded rfl
          by_cases seededX : Seeded F x.val
          · have seededHere : F.nodes.val[x.val].tree = true ∨ F.same.val.length ≤ x.val := by
              obtain ⟨n,at_n,cases⟩ := seededX
              rw [at_x] at at_n
              cases at_n
              exact cases
            by_cases seedHolds : Holds P.entries.val F.nodes.val[x.val].label.val F.nodes.val[x.val].seed.val
            · refine ⟨none,?_,by simp,?_⟩
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold,run2,
                  seeded_correct,seededX,seedRun,seedHolds]
              · intro _ _ c needs
                refine rest c needs ?_
                intro n at_n _ rfl
                rw [at_x] at at_n
                cases at_n
                exact seedHolds
            · refine ⟨some F.nodes.val[x.val].seed,?_,?_,by simp⟩
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold,run2,
                  seeded_correct,seededX,seedRun,seedHolds]
              · intro c same
                cases same
                exact ⟨.inr (.inr (.inr ⟨_,at_x,seededHere,rfl⟩)),seedHolds⟩
          · refine ⟨none,?_,by simp,?_⟩
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run1,axiomsRun,axiomsHold,run2,
                seeded_correct,seededX]
            · intro _ _ c needs
              refine rest c needs ?_
              intro n at_n isSeeded _
              exact absurd ⟨n,at_n,isSeeded⟩ seededX
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
        LinkNeeds P.entries.val h F (edgeEnds (liveEdges F F.edges.val)) y.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) ∧
      (r = none → LinksOk P.entries.val h F (edgeEnds (liveEdges F (F.edges.val.drop index.val)))) := by
  rw [forest.missing_added]
  by_cases more : index.val < F.edges.val.length
  · have lookup : F.edges.index_usize index = .ok F.edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : F.edges.val.drop index.val = F.edges.val[index.val] :: F.edges.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_added_correct P h F index'
    by_cases isLive : Live F.nodes.val (rep F F.edges.val[index.val].from).val
    · have liveSplit : liveEdges F (F.edges.val.drop index.val) =
          F.edges.val[index.val] :: liveEdges F (F.edges.val.drop (index.val+1)) := by
        rw [split,liveEdges,List.filter_cons_of_pos (by simpa using isLive)]
        rfl
      have memberHere : (F.edges.val[index.val].role,F.edges.val[index.val].from,F.edges.val[index.val].to) ∈
          edgeEnds (liveEdges F F.edges.val) :=
        List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨List.getElem_mem more,by simpa using isLive⟩,rfl⟩
      obtain ⟨e,eRun,eFound,eAbsent⟩ := missing_edge_correct P.entries h F (rep F F.edges.val[index.val].from)
        (rep F F.edges.val[index.val].to) F.edges.val[index.val].role
      cases e with
      | some pair =>
        obtain ⟨y,c⟩ := pair
        refine ⟨some (y,c),?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,live_correct,
            isLive,eRun]
        · intro y' c' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl⟩ := same
          obtain ⟨sourceIn,targetIn,which⟩ := eFound y c rfl
          rcases which with ⟨rfl,needs,fails⟩ | ⟨rfl,needs,fails⟩
          · exact ⟨targetIn,⟨_,memberHere,sourceIn,targetIn,.inl ⟨rfl,needs⟩⟩,fails⟩
          · exact ⟨sourceIn,⟨_,memberHere,sourceIn,targetIn,.inr ⟨rfl,needs⟩⟩,fails⟩
      | none =>
        refine ⟨r,?_,found,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,live_correct,
            isLive,eRun,advance,run]
        · intro none l member sourceIn targetIn
          rw [liveSplit,edgeEnds,List.map_cons] at member
          rcases List.mem_cons.mp member with rfl | later
          · exact eAbsent rfl sourceIn targetIn
          · exact absent none l (by rw [nextIndex,edgeEnds]; exact later) sourceIn targetIn
    · have liveSplit : liveEdges F (F.edges.val.drop index.val) = liveEdges F (F.edges.val.drop (index.val+1)) := by
        rw [split,liveEdges,List.filter_cons_of_neg (by simpa using isLive)]
        rfl
      refine ⟨r,?_,found,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,live_correct,
          isLive,advance,run]
      · intro none
        rw [liveSplit]
        rw [nextIndex] at absent
        exact absent none
  · have empty : F.edges.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ l member
    simp [empty,edgeEnds,liveEdges] at member
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

/-- A tree node `y` that is no child of `x`: a neighbour along an added edge,
    which the model may repeat. -/
def Repeated (nodes : List forest.Node) (x y : Nat) : Prop :=
  ∃ m, nodes[y]? = some m ∧ m.tree = true ∧ m.parent.val ≠ x

/-- For a named node `x`, no neighbour along `r` that the model may repeat
    satisfies `c`. -/
def Unrepeated (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (c : Usize) : Prop :=
  (∃ n, F.nodes.val[x]? = some n ∧ n.tree = false) → ∀ y : Usize, Neighbour P h F x r y.val →
    Repeated F.nodes.val x y.val → ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val

/-- What the choose rule (`choose`) or the merge rule requires at node `x` for
    the maximum restrictions among `items`. -/
def CountOkFrom (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (choose : Bool)
    (x : Nat) (items : List Usize) : Prop :=
  ∀ i ∈ items, ∀ n r c c', P.entries.val[i.val]? = some (.AtMost n r c c') →
    match choose with
    | true => ∀ y : Usize, Neighbour P h F x r y.val →
        Holds P.entries.val (labelOf F.nodes.val y.val) c.val ∨ Holds P.entries.val (labelOf F.nodes.val y.val) c'.val
    | false => ¬ Excess P h F x r c n ∧ Unrepeated P h F x r c

theorem repeated_satisfying_correct (entries : alloc.vec.Vec concept_table.Entry) (F : forest.Forest)
    (list : alloc.vec.Vec Usize) (x c index : Usize) :
    forest.repeated_satisfying entries F list x c index = .ok (decide (∃ y ∈ list.val.drop index.val,
      Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val)) := by
  rw [forest.repeated_satisfying]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := repeated_satisfying_correct entries F list x c next
    rw [nextIndex] at rest
    obtain ⟨y,yIs⟩ : ∃ y, list.val[index.val] = y := ⟨_,rfl⟩
    rw [yIs] at lookup split
    rw [split]
    simp only [List.mem_cons,exists_eq_or_imp]
    -- The answer of the rest, when `y` does not count.
    have skip : ¬ (Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val) →
        forest.repeated_satisfying entries F list x c next =
          .ok (decide ((Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val) ∨
            ∃ y' ∈ list.val.drop (index.val+1),
              Repeated F.nodes.val x.val y'.val ∧ Holds entries.val (labelOf F.nodes.val y'.val) c.val)) := by
      intro miss
      rw [rest]
      congr 1
      exact decide_eq_decide.mpr ⟨fun later => .inr later,fun both => both.resolve_left miss⟩
    by_cases yIn : y.val < F.nodes.val.length
    · have at_y := List.getElem?_eq_getElem yIn
      have nodeLookup : F.nodes.index_usize y = .ok F.nodes.val[y.val] := by
        simp [alloc.vec.Vec.index_usize,at_y]
      have labelIs : labelOf F.nodes.val y.val = F.nodes.val[y.val].label.val := by simp [labelOf,at_y]
      by_cases tree : F.nodes.val[y.val].tree = true
      · by_cases parent : F.nodes.val[y.val].parent = x
        · have miss : ¬ (Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val) := by
            rintro ⟨⟨m,at_m,_,other⟩,_⟩
            rw [at_y,Option.some.injEq] at at_m
            subst at_m
            exact other (by rw [parent])
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,yIn,nodeLookup,tree,parent,bne_self_eq_false,Bool.false_eq_true,advance,skip miss]
          exact congrArg _ (decide_eq_decide.mpr Iff.rfl)
        · have parentVal : F.nodes.val[y.val].parent.val ≠ x.val := fun same => parent (UScalar.eq_of_val_eq same)
          have repeated : Repeated F.nodes.val x.val y.val := ⟨_,at_y,tree,parentVal⟩
          by_cases holds : Holds entries.val F.nodes.val[y.val].label.val c.val
          · have hit : Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val :=
              ⟨repeated,by rw [labelIs]; exact holds⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,nodeLookup,tree,parent,parentVal,
              holds_correct entries F.nodes.val[y.val].label _ c rfl,holds,hit]
          · have miss : ¬ (Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val) :=
              fun ⟨_,holds'⟩ => holds (by rw [← labelIs]; exact holds')
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,yIn,nodeLookup,tree,bne_iff_ne,ne_eq,parent,not_false_eq_true,
              holds_correct entries F.nodes.val[y.val].label _ c rfl,decide_eq_false holds,Bool.false_eq_true,advance,
              skip miss]
            exact congrArg _ (decide_eq_decide.mpr Iff.rfl)
      · have miss : ¬ (Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val) := by
          rintro ⟨⟨m,at_m,isTree,_⟩,_⟩
          rw [at_y,Option.some.injEq] at at_m
          subst at_m
          exact tree isTree
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,yIn,nodeLookup,tree,Bool.false_eq_true,advance,skip miss]
        exact congrArg _ (decide_eq_decide.mpr Iff.rfl)
    · have miss : ¬ (Repeated F.nodes.val x.val y.val ∧ Holds entries.val (labelOf F.nodes.val y.val) c.val) := by
        rintro ⟨⟨m,at_m,_⟩,_⟩
        have := (List.getElem?_eq_some_iff.mp at_m).1
        omega
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,yIn,Bool.false_eq_true,advance,skip miss]
      exact congrArg _ (decide_eq_decide.mpr Iff.rfl)
  · have empty : list.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by list.val.length - index.val
decreasing_by omega

/-- The index of the first cap on the restriction `i` of node `x`. -/
theorem cap_at_correct (caps : alloc.vec.Vec forest.Cap) (x i index : Usize) :
    ∃ r, forest.cap_at caps x i index = .ok r ∧
      (∀ k, r = some k → ∃ inside : k.val < caps.val.length,
        caps.val[k.val].node = x ∧ caps.val[k.val].restriction = i) ∧
      (r = none → ∀ cap ∈ caps.val.drop index.val, ¬ (cap.node = x ∧ cap.restriction = i)) := by
  rw [forest.cap_at]
  by_cases more : index.val < caps.val.length
  · have lookup : caps.index_usize index = .ok caps.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : caps.val.drop index.val = caps.val[index.val] :: caps.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨r,run,found,absent⟩ := cap_at_correct caps x i next
    rw [nextIndex] at absent
    by_cases hit : caps.val[index.val].node = x ∧ caps.val[index.val].restriction = i
    · refine ⟨some index,?_,?_,by simp⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,hit.1,hit.2]
      · intro k same
        simp only [Option.some.injEq] at same
        subst same
        exact ⟨more,hit⟩
    · refine ⟨r,?_,found,?_⟩
      · by_cases first : caps.val[index.val].node = x
        · have second : ¬ caps.val[index.val].restriction = i := fun second => hit ⟨first,second⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,first,second,advance,run]
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,first,advance,run]
      · intro none cap member
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact hit
        · exact absent none cap later
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ cap member
    rw [List.drop_eq_nil_iff.mpr (by omega)] at member
    cases member
termination_by caps.val.length - index.val
decreasing_by omega

/-- The named nodes of a list, in order. -/
theorem named_of_correct (F : forest.Forest) (list : alloc.vec.Vec Usize) (index : Usize)
    (out : alloc.vec.Vec Usize) :
    ∃ r, forest.named_of F list index out = .ok r ∧ ∀ named, r = some named →
      named.val = out.val ++ (list.val.drop index.val).filter
        (fun y => decide (∃ n, F.nodes.val[y.val]? = some n ∧ n.tree = false)) := by
  rw [forest.named_of]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨y,yIs⟩ : ∃ y, list.val[index.val] = y := ⟨_,rfl⟩
    rw [yIs] at lookup split
    by_cases named : ∃ n, F.nodes.val[y.val]? = some n ∧ n.tree = false
    · obtain ⟨n,at_y,root⟩ := named
      have yIn : y.val < F.nodes.val.length := (List.getElem?_eq_some_iff.mp at_y).1
      have nodeLookup : F.nodes.index_usize y = .ok F.nodes.val[y.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem yIn]
      have nodeIs : F.nodes.val[y.val] = n := by
        rw [List.getElem?_eq_getElem yIn] at at_y
        exact Option.some.inj at_y
      by_cases room : out.val.length < Usize.max
      · obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out y room)
        obtain ⟨r,run,spec⟩ := named_of_correct F list next out1
        refine ⟨r,?_,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,nodeLookup,nodeIs,root,usize_max_val,room,
            push,advance,run]
        · intro named same
          rw [spec named same,contents,nextIndex,split,List.filter_cons]
          simp [at_y,root]
      · refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,nodeLookup,nodeIs,root,usize_max_val,room]
    · obtain ⟨r,run,spec⟩ := named_of_correct F list next out
      refine ⟨r,?_,?_⟩
      · by_cases yIn : y.val < F.nodes.val.length
        · have nodeLookup : F.nodes.index_usize y = .ok F.nodes.val[y.val] := by
            simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem yIn]
          have tree : F.nodes.val[y.val].tree = true := by
            cases treeIs : F.nodes.val[y.val].tree
            · exact absurd ⟨_,List.getElem?_eq_getElem yIn,treeIs⟩ named
            · rfl
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,nodeLookup,tree,advance,run]
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,advance,run]
      · intro named' same
        rw [spec named' same,nextIndex,split,List.filter_cons]
        simp only [decide_eq_true_eq]
        rw [if_neg named]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro named same
    cases same
    simp [List.drop_eq_nil_iff.mpr (show list.val.length ≤ index.val by omega)]
termination_by list.val.length - index.val
decreasing_by all_goals omega

/-- The first tree node of a list that is no child of `x`. -/
theorem first_repeated_correct (F : forest.Forest) (list : alloc.vec.Vec Usize) (x index : Usize) :
    ∃ r, forest.first_repeated F list x index = .ok r ∧
      (∀ y, r = some y → y ∈ list.val.drop index.val ∧ Repeated F.nodes.val x.val y.val) ∧
      (r = none → ∀ y ∈ list.val.drop index.val, ¬ Repeated F.nodes.val x.val y.val) := by
  rw [forest.first_repeated]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨r,run,found,absent⟩ := first_repeated_correct F list x next
    rw [nextIndex] at found absent
    obtain ⟨y,yIs⟩ : ∃ y, list.val[index.val] = y := ⟨_,rfl⟩
    rw [yIs] at lookup split
    by_cases hit : Repeated F.nodes.val x.val y.val
    · obtain ⟨m,at_y,tree,parent⟩ := hit
      have yIn : y.val < F.nodes.val.length := (List.getElem?_eq_some_iff.mp at_y).1
      have nodeLookup : F.nodes.index_usize y = .ok F.nodes.val[y.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem yIn]
      have nodeIs : F.nodes.val[y.val] = m := by
        rw [List.getElem?_eq_getElem yIn] at at_y
        exact Option.some.inj at_y
      have other : m.parent ≠ x := fun same => parent (by rw [same])
      refine ⟨some y,?_,?_,by simp⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,nodeLookup,nodeIs,tree,other]
      · intro y' same
        cases same
        exact ⟨by rw [split]; exact List.mem_cons_self ..,m,at_y,tree,parent⟩
    · refine ⟨r,?_,?_,?_⟩
      · by_cases yIn : y.val < F.nodes.val.length
        · have nodeLookup : F.nodes.index_usize y = .ok F.nodes.val[y.val] := by
            simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem yIn]
          by_cases tree : F.nodes.val[y.val].tree = true
          · have parent : F.nodes.val[y.val].parent = x := by
              by_contra other
              exact hit ⟨_,List.getElem?_eq_getElem yIn,tree,fun same => other (UScalar.eq_of_val_eq same)⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,nodeLookup,tree,parent,advance,run]
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,nodeLookup,tree,advance,run]
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,yIn,advance,run]
      · intro y' same
        obtain ⟨member,repeated⟩ := found y' same
        exact ⟨by rw [split]; exact List.mem_cons_of_mem _ member,repeated⟩
      · intro none y' member
        rw [split] at member
        rcases List.mem_cons.mp member with rfl | later
        · exact hit
        · exact absent none y' later
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y member
    rw [List.drop_eq_nil_iff.mpr (by omega)] at member
    cases member
termination_by list.val.length - index.val
decreasing_by all_goals omega

/-- A step of the choose rule (`choose`) or of the rules for too many
    neighbours at node `x`: the merge rule, or, for a maximum restriction of a
    named node that counts a neighbour the model may repeat, the rule for new
    named nodes when the restriction has no bound from them yet, and the merge
    into them when it has. -/
def CountStep (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (choose : Bool)
    (x : Usize) (step : forest.Step) : Prop :=
  ∃ i ∈ labelOf F.nodes.val x.val, ∃ n r c c', P.entries.val[i.val]? = some (.AtMost n r c c') ∧
    match choose with
    | true => ∃ y : Usize, step = .Choose y c c' ∧ Neighbour P h F x.val r y.val ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val ∧ ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c'.val
    | false => (step = .Merge x i ∧ Excess P h F x.val r c n ∧ Unrepeated P h F x.val r c) ∨
        (¬ Unrepeated P h F x.val r c ∧
          ((step = .Name x i ∧ ∀ cap ∈ F.caps.val, ¬ (cap.node = x ∧ cap.restriction = i)) ∨
           (step = .Capped x i ∧ ∃ cap ∈ F.caps.val, cap.node = x ∧ cap.restriction = i)))

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
              have repeatedRun := repeated_satisfying_correct P.entries F list x c 0#usize
              rw [show (0#usize).val = 0 from rfl,List.drop_zero] at repeatedRun
              -- Whether the restriction counts a neighbour that the model may repeat.
              have repeatedIs : (if F.nodes.val[x.val].tree = true then ok false else
                  forest.repeated_satisfying P.entries F list x c 0#usize) =
                  ok (decide (F.nodes.val[x.val].tree = false ∧ ∃ y ∈ list.val, Repeated F.nodes.val x.val y.val ∧
                    Holds P.entries.val (labelOf F.nodes.val y.val) c.val)) := by
                by_cases tree : F.nodes.val[x.val].tree = true
                · simp [tree]
                · have named : F.nodes.val[x.val].tree = false := by simpa using tree
                  simp [tree,named,repeatedRun]
              have unrepeated : ¬ (F.nodes.val[x.val].tree = false ∧ ∃ y ∈ list.val,
                  Repeated F.nodes.val x.val y.val ∧ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) →
                  Unrepeated P h F x.val role c := by
                intro none ⟨n',at_n,named⟩ y neighbour repeated holds
                rw [List.getElem?_eq_getElem inside,Option.some.injEq] at at_n
                subst at_n
                exact none ⟨named,y,(members y).mpr neighbour,repeated,holds⟩
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
                by_cases stop : F.nodes.val[x.val].tree = false ∧ ∃ y ∈ list.val,
                    Repeated F.nodes.val x.val y.val ∧ Holds P.entries.val (labelOf F.nodes.val y.val) c.val
                · -- A neighbour the model may repeat: new named nodes, or the merge into them.
                  have notUnrepeated : ¬ Unrepeated P h F x.val role c := by
                    intro unrep
                    obtain ⟨named,y,yIn,repeated,holds⟩ := stop
                    exact unrep ⟨_,List.getElem?_eq_getElem inside,named⟩ y ((members y).mp yIn) repeated holds
                  obtain ⟨capResult,capRun,capFound,capAbsent⟩ :=
                    cap_at_correct F.caps x F.nodes.val[x.val].label.val[index.val] 0#usize
                  cases capResult with
                  | none =>
                    refine ⟨some (some (.Name x F.nodes.val[x.val].label.val[index.val])),?_,?_,by simp⟩
                    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                        entryLookup,entry,neighboursRun,manyRun,repeatedIs,repeatedRun,stop.1,stop.2,capRun]
                    · intro step same
                      simp only [Option.some.injEq] at same
                      subst same
                      refine ⟨_,itemIn,n,role,c,c',by rw [at_item,entry],.inr ⟨notUnrepeated,.inl ⟨rfl,?_⟩⟩⟩
                      intro cap member
                      exact capAbsent rfl cap (by simpa using member)
                  | some k =>
                    obtain ⟨kIn,kNode,kRestriction⟩ := capFound k rfl
                    have capLookup : F.caps.index_usize k = .ok F.caps.val[k.val] := by
                      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem kIn]
                    obtain ⟨namedResult,namedRun,_⟩ := named_of_correct F kept 0#usize (alloc.vec.Vec.new Usize)
                    cases namedResult with
                    | none =>
                      refine ⟨none,?_,by simp,by simp⟩
                      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                        entryLookup,entry,neighboursRun,manyRun,repeatedIs,repeatedRun,stop.1,stop.2,capRun,namedRun]
                    | some named =>
                      by_cases enough : F.caps.val[k.val].bound.val ≤ named.val.length
                      · refine ⟨some (some (.Capped x F.nodes.val[x.val].label.val[index.val])),?_,?_,by simp⟩
                        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                            entryLookup,entry,neighboursRun,manyRun,repeatedIs,repeatedRun,stop.1,stop.2,capRun,namedRun,
                            alloc.vec.Vec.index_slice_index,capLookup,enough]
                        · intro step same
                          simp only [Option.some.injEq] at same
                          subst same
                          exact ⟨_,itemIn,n,role,c,c',by rw [at_item,entry],
                            .inr ⟨notUnrepeated,.inr ⟨rfl,F.caps.val[k.val],List.getElem_mem kIn,kNode,kRestriction⟩⟩⟩
                      · refine ⟨none,?_,by simp,by simp⟩
                        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                          entryLookup,entry,neighboursRun,manyRun,repeatedIs,repeatedRun,stop.1,stop.2,capRun,namedRun,
                          alloc.vec.Vec.index_slice_index,capLookup,enough]
                · have alright := unrepeated stop
                  by_cases over : n.val < kept.val.length
                  · refine ⟨some (some (.Merge x F.nodes.val[x.val].label.val[index.val])),?_,?_,by simp⟩
                    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                        entryLookup,entry,neighboursRun,manyRun,repeatedIs,stop,over]
                    · intro step same
                      simp only [Option.some.injEq] at same
                      subst same
                      exact ⟨_,itemIn,n,role,c,c',by rw [at_item,entry],.inl ⟨rfl,excess.mpr over,alright⟩⟩
                  · refine ⟨r,?_,found,?_⟩
                    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,
                        entryLookup,entry,neighboursRun,manyRun,repeatedIs,stop,over,advance,run]
                    · intro none i member n' role' d d' at_i
                      rw [labelIs,split] at member
                      rcases List.mem_cons.mp member with rfl | later
                      · rw [at_item,entry] at at_i
                        simp only [Option.some.injEq,concept_table.Entry.AtMost.injEq] at at_i
                        obtain ⟨rfl,rfl,rfl,rfl⟩ := at_i
                        exact ⟨fun excessive => over (excess.mp excessive),alright⟩
                      · exact absent none i (by rw [labelIs,nextIndex]; exact later) n' role' d d' at_i
        | Top | Bottom | Atom _ | NotAtom _ | One _ | NotOne _ | HasSelf _ | NotSelf _ | And _ _ | Or _ _ | Exists _ _
          | Forall _ _ | AtLeast _ _ _ =>
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

/-! ### Nominals -/

/-- The named node of an individual among `requirements`: the representative
    of the node of the first requirement with its nominal. -/
noncomputable def NominalRootIn (P : completion.Problem) (F : forest.Forest) (requirements : List completion.Requirement)
    (a : Individual) : Option Usize :=
  match requirements.find? (fun q => decide (P.entries.val[q.concept.val]? = some (.One a))) with
  | some q => some (rep F q.node)
  | none => none

/-- The named node of an individual. -/
noncomputable def NominalRoot (P : completion.Problem) (F : forest.Forest) (a : Individual) : Option Usize :=
  NominalRootIn P F P.requirements.val a

/-- What entry `i` in the label of node `y` needs of the nominals: the
    individual of a nominal has `y` as its named node, and the individual of
    the complement of a nominal has a named node. -/
def NominalOkFor (P : completion.Problem) (F : forest.Forest) (y : Nat) (i : Usize) : Prop :=
  (∀ a, P.entries.val[i.val]? = some (.One a) → ∃ root : Usize, NominalRoot P F a = some root ∧ root.val = y) ∧
  (∀ a, P.entries.val[i.val]? = some (.NotOne a) → ∃ root : Usize, NominalRoot P F a = some root)

/-- Every entry of the label of node `y` has what it needs of the nominals. -/
def NominalOkAt (P : completion.Problem) (F : forest.Forest) (y : Nat) : Prop :=
  ∀ i ∈ labelOf F.nodes.val y, NominalOkFor P F y i

/-- The named node of an individual is the representative of the node of a
    requirement with its nominal. -/
theorem nominalRoot_some {P : completion.Problem} {F : forest.Forest} {a : Individual} {root : Usize}
    (found : NominalRoot P F a = some root) :
    ∃ q ∈ P.requirements.val, P.entries.val[q.concept.val]? = some (.One a) ∧ rep F q.node = root := by
  unfold NominalRoot NominalRootIn at found
  split at found
  · rename_i q hq
    have holds := List.find?_some hq
    simp only [decide_eq_true_eq] at holds
    simp only [Option.some.injEq] at found
    exact ⟨q,List.mem_of_find?_eq_some hq,holds,found⟩
  · cases found

theorem nominalRootIn_cons (P : completion.Problem) (F : forest.Forest) (q : completion.Requirement)
    (rest : List completion.Requirement) (a : Individual) :
    NominalRootIn P F (q :: rest) a =
      if P.entries.val[q.concept.val]? = some (.One a) then some (rep F q.node) else NominalRootIn P F rest a := by
  by_cases h : P.entries.val[q.concept.val]? = some (.One a) <;> simp [NominalRootIn,List.find?_cons,h]

theorem names_correct (P : completion.Problem) (c : Usize) (a : Individual) :
    forest.names P c a = .ok (decide (P.entries.val[c.val]? = some (.One a))) := by
  rw [forest.names]
  by_cases inside : c.val < P.entries.val.length
  · have lookup : P.entries.index_usize c = .ok P.entries.val[c.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have at_c : P.entries.val[c.val]? = some P.entries.val[c.val] := List.getElem?_eq_getElem inside
    obtain ⟨e,eIs⟩ : ∃ e, P.entries.val[c.val] = e := ⟨_,rfl⟩
    rw [eIs] at lookup at_c
    rw [at_c]
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok]
    cases e <;> simp [Rowl.AssertionEquality.same_individual_value_total_correct]
  · have none : P.entries.val[c.val]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,none]

theorem nominal_root_correct (P : completion.Problem) (F : forest.Forest) (a : Individual) (index : Usize) :
    forest.nominal_root P F a index = .ok (NominalRootIn P F (P.requirements.val.drop index.val) a) := by
  rw [forest.nominal_root]
  by_cases more : index.val < P.requirements.val.length
  · have lookup : P.requirements.index_usize index = .ok P.requirements.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : P.requirements.val.drop index.val =
        P.requirements.val[index.val] :: P.requirements.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := nominal_root_correct P F a next
    rw [nextIndex] at rest
    rw [split,nominalRootIn_cons]
    by_cases hit : P.entries.val[P.requirements.val[index.val].concept.val]? = some (.One a)
    · rw [if_pos hit]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,names_correct,hit,representative_correct]
    · rw [if_neg hit]
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,names_correct,hit,decide_false,Bool.false_eq_true,advance,rest]
  · have empty : P.requirements.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty,NominalRootIn]
termination_by P.requirements.val.length - index.val
decreasing_by omega

/-- The search through a label for a nominal of another named node is exact; it
    has no answer when the individual of a nominal, or of the complement of
    one, has no named node. -/
theorem nominal_at_correct (P : completion.Problem) (F : forest.Forest) (node index : Usize) :
    ∃ r, forest.nominal_at P F node index = .ok r ∧
      (∀ root, r = some (some root) → ∃ i ∈ (labelOf F.nodes.val node.val).drop index.val, ∃ a,
        P.entries.val[i.val]? = some (.One a) ∧ NominalRoot P F a = some root ∧ root ≠ node) ∧
      (r = some none → ∀ i ∈ (labelOf F.nodes.val node.val).drop index.val, NominalOkFor P F node.val i) := by
  rw [forest.nominal_at]
  by_cases inside : node.val < F.nodes.val.length
  · have nodeLookup : F.nodes.index_usize node = .ok F.nodes.val[node.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have labelIs : labelOf F.nodes.val node.val = F.nodes.val[node.val].label.val := by
      simp [labelOf,List.getElem?_eq_getElem inside]
    by_cases more : index.val < F.nodes.val[node.val].label.val.length
    · have itemLookup : F.nodes.val[node.val].label.index_usize index =
          .ok F.nodes.val[node.val].label.val[index.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      have split : (labelOf F.nodes.val node.val).drop index.val =
          F.nodes.val[node.val].label.val[index.val] :: (labelOf F.nodes.val node.val).drop (index.val+1) := by
        rw [labelIs]; exact List.drop_eq_getElem_cons more
      obtain ⟨item,itemIs⟩ : ∃ item, F.nodes.val[node.val].label.val[index.val] = item := ⟨_,rfl⟩
      rw [itemIs] at itemLookup split
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val+1 := by simpa using nextValue
      obtain ⟨r,run,found,absent⟩ := nominal_at_correct P F node next
      rw [nextIndex] at found absent
      -- Moving on keeps the answer of the rest, when the item has what it needs.
      have skip : NominalOkFor P F node.val item →
          (∀ root, r = some (some root) → ∃ i ∈ (labelOf F.nodes.val node.val).drop index.val, ∃ a,
            P.entries.val[i.val]? = some (.One a) ∧ NominalRoot P F a = some root ∧ root ≠ node) ∧
          (r = some none → ∀ i ∈ (labelOf F.nodes.val node.val).drop index.val, NominalOkFor P F node.val i) := by
        intro here
        refine ⟨?_,?_⟩
        · intro root same
          obtain ⟨i,member,a,at_i,rootIs,different⟩ := found root same
          exact ⟨i,by rw [split]; exact List.mem_cons_of_mem _ member,a,at_i,rootIs,different⟩
        · intro none i member
          rw [split] at member
          rcases List.mem_cons.mp member with rfl | later
          · exact here
          · exact absent none i later
      have moveOn : forest.nominal_at P F node next = .ok r := run
      by_cases itemInside : item.val < P.entries.val.length
      · have entryLookup : P.entries.index_usize item = .ok P.entries.val[item.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemInside]
        have at_item : P.entries.val[item.val]? = some P.entries.val[item.val] :=
          List.getElem?_eq_getElem itemInside
        obtain ⟨e,eIs⟩ : ∃ e, P.entries.val[item.val] = e := ⟨_,rfl⟩
        rw [eIs] at entryLookup at_item
        -- An entry that is neither a nominal nor the complement of one needs nothing.
        have plain : (∀ a, e ≠ .One a) → (∀ a, e ≠ .NotOne a) → NominalOkFor P F node.val item := by
          intro notOne notNotOne
          refine ⟨fun a at_a => ?_,fun a at_a => ?_⟩
          · rw [at_item,Option.some.injEq] at at_a
            exact absurd at_a (notOne a)
          · rw [at_item,Option.some.injEq] at at_a
            exact absurd at_a (notNotOne a)
        cases e with
        | One a =>
          have rootRun := nominal_root_correct P F a 0#usize
          rw [show (0#usize).val = 0 from rfl,List.drop_zero] at rootRun
          cases rootIs : NominalRoot P F a with
          | none =>
            refine ⟨none,?_,by simp,by simp⟩
            simp only [NominalRoot] at rootIs
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more,itemLookup,itemInside,entryLookup,
              rootRun,rootIs]
          | some root =>
            by_cases same : root = node
            · subst same
              refine ⟨r,?_,skip ⟨fun a' at_a => ?_,fun a' at_a => ?_⟩⟩
              · simp only [NominalRoot] at rootIs
                simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more,itemLookup,itemInside,
                  entryLookup,rootRun,rootIs,advance,moveOn]
              · rw [at_item,Option.some.injEq,concept_table.Entry.One.injEq] at at_a
                subst at_a
                exact ⟨root,rootIs,rfl⟩
              · rw [at_item,Option.some.injEq] at at_a
                cases at_a
            · have sameVal : ¬ root.val = node.val := fun equal => same (UScalar.eq_of_val_eq equal)
              refine ⟨some (some root),?_,?_,by simp⟩
              · simp only [NominalRoot] at rootIs
                simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more,itemLookup,itemInside,
                  entryLookup,rootRun,rootIs,sameVal]
              · intro root' same'
                simp only [Option.some.injEq] at same'
                subst same'
                exact ⟨item,by rw [split]; exact List.mem_cons_self ..,a,at_item,rootIs,same⟩
        | NotOne a =>
          have rootRun := nominal_root_correct P F a 0#usize
          rw [show (0#usize).val = 0 from rfl,List.drop_zero] at rootRun
          cases rootIs : NominalRoot P F a with
          | none =>
            refine ⟨none,?_,by simp,by simp⟩
            simp only [NominalRoot] at rootIs
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more,itemLookup,itemInside,entryLookup,
              rootRun,rootIs]
          | some root =>
            refine ⟨r,?_,skip ⟨fun a' at_a => ?_,fun a' at_a => ?_⟩⟩
            · simp only [NominalRoot] at rootIs
              simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more,itemLookup,itemInside,
                entryLookup,rootRun,rootIs,advance,moveOn]
            · rw [at_item,Option.some.injEq] at at_a
              cases at_a
            · rw [at_item,Option.some.injEq,concept_table.Entry.NotOne.injEq] at at_a
              subst at_a
              exact ⟨root,rootIs⟩
        | Top | Bottom | Atom _ | NotAtom _ | HasSelf _ | NotSelf _ | And _ _ | Or _ _ | Exists _ _ | Forall _ _
          | AtLeast _ _ _ | AtMost _ _ _ _ =>
          exact ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more,itemLookup,itemInside,
            entryLookup,advance,moveOn],skip (plain (by simp) (by simp))⟩
      · refine ⟨r,?_,skip ⟨fun a at_a => ?_,fun a at_a => ?_⟩⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more,itemLookup,itemInside,advance,moveOn]
        · have := (List.getElem?_eq_some_iff.mp at_a).1
          omega
        · have := (List.getElem?_eq_some_iff.mp at_a).1
          omega
    · have empty : (labelOf F.nodes.val node.val).drop index.val = [] := by
        rw [labelIs]; exact List.drop_eq_nil_iff.mpr (by omega)
      refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,nodeLookup,more],by simp,?_⟩
      intro _ i member
      rw [empty] at member
      cases member
  · have empty : labelOf F.nodes.val node.val = [] := by
      simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ node.val by omega)]
    refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,?_⟩
    intro _ i member
    rw [empty] at member
    simp at member
termination_by (labelOf F.nodes.val node.val).length - index.val
decreasing_by
  all_goals
    rw [labelIs]
    omega

/-- The search for an active node with a nominal of another named node is
    exact; it has no answer when the individual of a nominal, or of the
    complement of one, has no named node. -/
theorem nominal_node_correct (P : completion.Problem) (F : forest.Forest) (index : Usize) :
    ∃ r, forest.nominal_node P F index = .ok r ∧
      (∀ x root, r = some (some (x,root)) → Active F.nodes.val x.val ∧ ∃ i ∈ labelOf F.nodes.val x.val, ∃ a,
        P.entries.val[i.val]? = some (.One a) ∧ NominalRoot P F a = some root ∧ root ≠ x) ∧
      (r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y → NominalOkAt P F y) := by
  rw [forest.nominal_node]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := nominal_node_correct P F index'
    by_cases active : F.nodes.val[index.val].active = true
    · obtain ⟨here,hereRun,hereFound,hereAbsent⟩ := nominal_at_correct P F index 0#usize
      rw [show (0#usize).val = 0 from rfl,List.drop_zero] at hereFound hereAbsent
      cases here with
      | none =>
        exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,hereRun],by simp,by simp⟩
      | some found' =>
        cases found' with
        | some root =>
          refine ⟨some (some (index,root)),?_,?_,by simp⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,hereRun]
          · intro x root' same
            simp only [Option.some.injEq,Prod.mk.injEq] at same
            obtain ⟨rfl,rfl⟩ := same
            exact ⟨⟨_,at_index,active⟩,hereFound root rfl⟩
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

/-- Something a loop requires of its node: what a self restriction `∃s.Self`
    of an active node requires along `s`, in either direction. -/
def LoopNeeds (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (y : Nat)
    (c : Usize) : Prop :=
  Active F.nodes.val y ∧ ∃ i ∈ labelOf F.nodes.val y, ∃ s, entries[i.val]? = some (.HasSelf s) ∧
    (EdgeNeeds entries h (labelOf F.nodes.val y) s c ∨ EdgeNeeds entries h (labelOf F.nodes.val y) (inv s) c)

/-- Every loop of node `y` gives it what it requires along the loop, in either
    direction. -/
def LoopsOk (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (y : Nat) :
    Prop :=
  ∀ i ∈ labelOf F.nodes.val y, ∀ s, entries[i.val]? = some (.HasSelf s) →
    EdgeOk entries h (labelOf F.nodes.val y) s (labelOf F.nodes.val y) ∧
    EdgeOk entries h (labelOf F.nodes.val y) (inv s) (labelOf F.nodes.val y)

theorem missing_loop_correct (entries : alloc.vec.Vec concept_table.Entry) (h : hierarchy.RoleHierarchy)
    (F : forest.Forest) (x index : Usize) :
    ∃ r, forest.missing_loop entries h F x index = .ok r ∧
      (∀ y c, r = some (y,c) → y = x ∧ x.val < F.nodes.val.length ∧
        ∃ i ∈ labelOf F.nodes.val x.val, ∃ s, entries.val[i.val]? = some (.HasSelf s) ∧
          (EdgeNeeds entries.val h (labelOf F.nodes.val x.val) s c ∨
            EdgeNeeds entries.val h (labelOf F.nodes.val x.val) (inv s) c) ∧
          ¬ Holds entries.val (labelOf F.nodes.val x.val) c.val) ∧
      (r = none → ∀ i ∈ (labelOf F.nodes.val x.val).drop index.val, ∀ s, entries.val[i.val]? = some (.HasSelf s) →
        EdgeOk entries.val h (labelOf F.nodes.val x.val) s (labelOf F.nodes.val x.val) ∧
        EdgeOk entries.val h (labelOf F.nodes.val x.val) (inv s) (labelOf F.nodes.val x.val)) := by
  rw [forest.missing_loop]
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
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,found,absent⟩ := missing_loop_correct entries h F x index'
      rw [nextIndex] at absent
      have member : F.nodes.val[x.val].label.val[index.val] ∈ labelOf F.nodes.val x.val := by
        rw [labelIs]; exact List.getElem_mem more
      -- Skipping an item that needs nothing keeps the answer of the rest.
      have skip : (∀ s, entries.val[F.nodes.val[x.val].label.val[index.val].val]? = some (.HasSelf s) →
            EdgeOk entries.val h (labelOf F.nodes.val x.val) s (labelOf F.nodes.val x.val) ∧
            EdgeOk entries.val h (labelOf F.nodes.val x.val) (inv s) (labelOf F.nodes.val x.val)) →
          r = none → ∀ i ∈ (labelOf F.nodes.val x.val).drop index.val, ∀ s,
            entries.val[i.val]? = some (.HasSelf s) →
            EdgeOk entries.val h (labelOf F.nodes.val x.val) s (labelOf F.nodes.val x.val) ∧
            EdgeOk entries.val h (labelOf F.nodes.val x.val) (inv s) (labelOf F.nodes.val x.val) := by
        intro here none i listed s at_i
        rw [labelIs,split] at listed
        rcases List.mem_cons.mp listed with rfl | later
        · exact here s at_i
        · exact absent none i (by rw [labelIs]; exact later) s at_i
      by_cases itemInside : F.nodes.val[x.val].label.val[index.val].val < entries.val.length
      · have entryLookup : entries.index_usize F.nodes.val[x.val].label.val[index.val] =
            .ok entries.val[F.nodes.val[x.val].label.val[index.val].val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemInside]
        have at_item := List.getElem?_eq_getElem itemInside
        obtain ⟨e,eIs⟩ : ∃ e, entries.val[F.nodes.val[x.val].label.val[index.val].val] = e := ⟨_,rfl⟩
        rw [eIs] at entryLookup at_item
        cases e with
        | HasSelf s =>
          obtain ⟨m,mRun,mFound,mAbsent⟩ := missing_edge_correct entries h F x x s
          cases m with
          | some pair =>
            obtain ⟨y,c⟩ := pair
            refine ⟨some (y,c),?_,?_,by simp⟩
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
                mRun]
            · intro y' c' same
              simp only [Option.some.injEq,Prod.mk.injEq] at same
              obtain ⟨rfl,rfl⟩ := same
              obtain ⟨_,_,which⟩ := mFound y c rfl
              rcases which with ⟨rfl,needs,fails⟩ | ⟨rfl,needs,fails⟩
              · exact ⟨rfl,inside,_,member,s,at_item,.inl needs,fails⟩
              · exact ⟨rfl,inside,_,member,s,at_item,.inr needs,fails⟩
          | none =>
            refine ⟨r,?_,found,skip ?_⟩
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
                mRun,advance,run]
            · intro s' at_s
              rw [at_item,Option.some.injEq,concept_table.Entry.HasSelf.injEq] at at_s
              subst at_s
              exact mAbsent rfl inside inside
        | _ =>
          refine ⟨r,?_,found,skip ?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
              advance,run]
          · intro s' at_s
            rw [at_item] at at_s
            cases at_s
      · refine ⟨r,?_,found,skip ?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,advance,run]
        · intro s' at_s
          have := (List.getElem?_eq_some_iff.mp at_s).1
          omega
    · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more],by simp,?_⟩
      intro _ i listed
      rw [labelIs,List.drop_eq_nil_iff.mpr (by omega)] at listed
      cases listed
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],by simp,?_⟩
    intro _ i listed
    simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)] at listed
termination_by (labelOf F.nodes.val x.val).length - index.val
decreasing_by
  all_goals
    rw [labelIs]
    omega

theorem missing_loops_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (index : Usize) :
    ∃ r, forest.missing_loops P h F index = .ok r ∧
      (∀ y c, r = some (y,c) → y.val < F.nodes.val.length ∧ LoopNeeds P.entries.val h F y.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) ∧
      (r = none → ∀ y, index.val ≤ y → Active F.nodes.val y → LoopsOk P.entries.val h F y) := by
  rw [forest.missing_loops]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := missing_loops_correct P h F index'
    have skip : (Active F.nodes.val index.val → LoopsOk P.entries.val h F index.val) →
        r = none → ∀ y, index.val ≤ y → Active F.nodes.val y → LoopsOk P.entries.val h F y := by
      intro here none y low active
      by_cases same : y = index.val
      · subst same
        exact here active
      · exact absent none y (by omega) active
    by_cases active : F.nodes.val[index.val].active = true
    · obtain ⟨m,mRun,mFound,mAbsent⟩ := missing_loop_correct P.entries h F index 0#usize
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at mAbsent
      cases m with
      | some pair =>
        obtain ⟨y,c⟩ := pair
        refine ⟨some (y,c),?_,?_,by simp⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,mRun]
        · intro y' c' same
          simp only [Option.some.injEq,Prod.mk.injEq] at same
          obtain ⟨rfl,rfl⟩ := same
          obtain ⟨rfl,yIn,i,member,s,at_i,needs,fails⟩ := mFound y c rfl
          exact ⟨yIn,⟨⟨_,at_index,active⟩,i,member,s,at_i,needs⟩,fails⟩
      | none =>
        refine ⟨r,?_,found,skip ?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,mRun,advance,run]
        · intro _ i member s at_i
          exact mAbsent rfl i member s at_i
    · refine ⟨r,?_,found,skip ?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,advance,run]
      · rintro ⟨n,at_n,isActive⟩
        rw [at_index] at at_n
        cases at_n
        exact absurd isActive active
  · refine ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low ⟨n,at_n,_⟩
    have := (List.getElem?_eq_some_iff.mp at_n).1
    omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

/-- A clash at a loop: the label of `x` has the complement `¬∃r.Self` of a
    self restriction while `x` is its own neighbour along `r`. -/
def Looped (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat) : Prop :=
  ∃ i ∈ labelOf F.nodes.val x, ∃ r, P.entries.val[i.val]? = some (.NotSelf r) ∧ Neighbour P h F x r x

theorem looped_from_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (x index : Usize) :
    ∃ r, forest.looped_from P h F x index = .ok r ∧ ∀ b, r = some b →
      (b = true ↔ ∃ i ∈ (labelOf F.nodes.val x.val).drop index.val, ∃ r,
        P.entries.val[i.val]? = some (.NotSelf r) ∧ Neighbour P h F x.val r x.val) := by
  rw [forest.looped_from]
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
      obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : index'.val = index.val+1 := by simpa using indexValue
      obtain ⟨r,run,spec⟩ := looped_from_correct P h F x index'
      rw [nextIndex] at spec
      -- Skipping an item without a clash keeps the answer of the rest.
      have skip : ¬ (∃ s, P.entries.val[F.nodes.val[x.val].label.val[index.val].val]? = some (.NotSelf s) ∧
            Neighbour P h F x.val s x.val) →
          ∀ b, r = some b → (b = true ↔ ∃ i ∈ (labelOf F.nodes.val x.val).drop index.val, ∃ r,
            P.entries.val[i.val]? = some (.NotSelf r) ∧ Neighbour P h F x.val r x.val) := by
        intro here b same
        rw [spec b same,labelIs,split]
        constructor
        · rintro ⟨i,member,found⟩
          exact ⟨i,List.mem_cons_of_mem _ member,found⟩
        · rintro ⟨i,member,found⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact absurd found here
          · exact ⟨i,later,found⟩
      by_cases itemInside : F.nodes.val[x.val].label.val[index.val].val < P.entries.val.length
      · have entryLookup : P.entries.index_usize F.nodes.val[x.val].label.val[index.val] =
            .ok P.entries.val[F.nodes.val[x.val].label.val[index.val].val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem itemInside]
        have at_item := List.getElem?_eq_getElem itemInside
        obtain ⟨e,eIs⟩ : ∃ e, P.entries.val[F.nodes.val[x.val].label.val[index.val].val] = e := ⟨_,rfl⟩
        rw [eIs] at entryLookup at_item
        cases e with
        | NotSelf s =>
          obtain ⟨list,listRun,listSpec⟩ := neighbours_correct P h F x s
          cases list with
          | none =>
            refine ⟨none,?_,by simp⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
              listRun]
          | some list =>
            obtain ⟨members,_⟩ := listSpec list rfl
            by_cases loop : Neighbour P h F x.val s x.val
            · refine ⟨some true,?_,?_⟩
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
                  listRun,contains_correct,(members x).mpr loop]
              · intro b same
                cases same
                simp only [true_iff]
                exact ⟨_,by rw [labelIs,split]; exact List.mem_cons_self ..,s,at_item,loop⟩
            · have absentX : x ∉ list.val := fun listed => loop ((members x).mp listed)
              refine ⟨r,?_,skip ?_⟩
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
                  listRun,contains_correct,absentX,advance,run]
              · rintro ⟨s',at_s,loop'⟩
                rw [at_item,Option.some.injEq,concept_table.Entry.NotSelf.injEq] at at_s
                subst at_s
                exact loop loop'
        | _ =>
          refine ⟨r,?_,skip ?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,entryLookup,
              advance,run]
          · rintro ⟨s',at_s,_⟩
            rw [at_item] at at_s
            cases at_s
      · refine ⟨r,?_,skip ?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more,itemLookup,itemInside,advance,run]
        · rintro ⟨s',at_s,_⟩
          have := (List.getElem?_eq_some_iff.mp at_s).1
          omega
    · refine ⟨some false,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,more],?_⟩
      intro b same
      cases same
      simp only [Bool.false_eq_true,false_iff]
      rintro ⟨i,member,_⟩
      rw [labelIs,List.drop_eq_nil_iff.mpr (by omega)] at member
      cases member
  · refine ⟨some false,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],?_⟩
    intro b same
    cases same
    simp only [Bool.false_eq_true,false_iff]
    rintro ⟨i,member,_⟩
    simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)] at member
termination_by (labelOf F.nodes.val x.val).length - index.val
decreasing_by
  all_goals
    rw [labelIs]
    omega

theorem looped_node_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (index : Usize) :
    ∃ r, forest.looped_node P h F index = .ok r ∧
      (∀ x, r = some (some x) → Active F.nodes.val x.val ∧ Looped P h F x.val) ∧
      (r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y → ¬ Looped P h F y) := by
  rw [forest.looped_node]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := looped_node_correct P h F index'
    have skip : (Active F.nodes.val index.val → ¬ Looped P h F index.val) →
        r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y → ¬ Looped P h F y := by
      intro here none y low active
      by_cases same : y = index.val
      · subst same
        exact here active
      · exact absent none y (by omega) active
    by_cases active : F.nodes.val[index.val].active = true
    · obtain ⟨l,lRun,lSpec⟩ := looped_from_correct P h F index 0#usize
      cases l with
      | none => exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,lRun],by simp,by simp⟩
      | some b =>
        have iff := lSpec b rfl
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at iff
        cases b with
        | true =>
          refine ⟨some (some index),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,lRun],?_,
            by simp⟩
          intro x same
          simp only [Option.some.injEq] at same
          subst same
          exact ⟨⟨_,at_index,active⟩,iff.mp rfl⟩
        | false =>
          refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,lRun,advance,run],found,
            skip ?_⟩
          intro _ looped
          exact absurd (iff.mpr looped) (by simp)
    · refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,advance,run],found,skip ?_⟩
      rintro ⟨n,at_n,isActive⟩
      rw [at_index] at at_n
      cases at_n
      exact absurd isActive active
  · refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low ⟨n,at_n,_⟩
    have := (List.getElem?_eq_some_iff.mp at_n).1
    omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

/-- A clash at a disjoint pair: a common neighbour of `x` along both roles of a
    disjoint pair of the hierarchy. -/
def Overlap (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat) : Prop :=
  ∃ d ∈ h.disjoint.val, ∃ y : Usize, Neighbour P h F x d.left y.val ∧ Neighbour P h F x d.right y.val

theorem common_correct (left right : alloc.vec.Vec Usize) (index : Usize) :
    forest.common left right index = .ok (decide (∃ y ∈ left.val.drop index.val, y ∈ right.val)) := by
  rw [forest.common]
  by_cases more : index.val < left.val.length
  · have lookup : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : left.val.drop index.val = left.val[index.val] :: left.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    have rest := common_correct left right index'
    rw [nextIndex] at rest
    rw [split]
    by_cases here : left.val[index.val] ∈ right.val
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,here,decide_true]
      exact congrArg _ (decide_eq_true ⟨_,List.mem_cons_self ..,here⟩).symm
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,here,decide_false,
        Bool.false_eq_true,advance,rest]
      congr 1
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨y,member,found⟩
        exact ⟨y,List.mem_cons_of_mem _ member,found⟩
      · rintro ⟨y,member,found⟩
        rcases List.mem_cons.mp member with rfl | later
        · exact absurd found here
        · exact ⟨y,later,found⟩
  · have empty : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by left.val.length - index.val
decreasing_by omega

theorem overlap_from_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (x index : Usize) :
    ∃ r, forest.overlap_from P h F x index = .ok r ∧ ∀ b, r = some b →
      (b = true ↔ ∃ d ∈ h.disjoint.val.drop index.val, ∃ y : Usize,
        Neighbour P h F x.val d.left y.val ∧ Neighbour P h F x.val d.right y.val) := by
  rw [forest.overlap_from]
  by_cases more : index.val < h.disjoint.val.length
  · have lookup : h.disjoint.index_usize index = .ok h.disjoint.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : h.disjoint.val.drop index.val = h.disjoint.val[index.val] :: h.disjoint.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨leftResult,leftRun,leftSpec⟩ := neighbours_correct P h F x h.disjoint.val[index.val].left
    cases leftResult with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,leftRun],by simp⟩
    | some left =>
    obtain ⟨leftMembers,_⟩ := leftSpec left rfl
    obtain ⟨rightResult,rightRun,rightSpec⟩ := neighbours_correct P h F x h.disjoint.val[index.val].right
    cases rightResult with
    | none =>
      exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,leftRun,rightRun],by simp⟩
    | some right =>
    obtain ⟨rightMembers,_⟩ := rightSpec right rfl
    have commonIff : (∃ y ∈ left.val, y ∈ right.val) ↔ ∃ y : Usize,
        Neighbour P h F x.val h.disjoint.val[index.val].left y.val ∧
          Neighbour P h F x.val h.disjoint.val[index.val].right y.val := by
      constructor
      · rintro ⟨y,inLeft,inRight⟩
        exact ⟨y,(leftMembers y).mp inLeft,(rightMembers y).mp inRight⟩
      · rintro ⟨y,inLeft,inRight⟩
        exact ⟨y,(leftMembers y).mpr inLeft,(rightMembers y).mpr inRight⟩
    rw [split]
    by_cases here : ∃ y ∈ left.val, y ∈ right.val
    · refine ⟨some true,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,leftRun,rightRun,common_correct,show (0#usize).val = 0 from rfl,List.drop_zero,here,decide_true]
      · intro b same
        cases same
        simp only [true_iff]
        exact ⟨_,List.mem_cons_self ..,commonIff.mp here⟩
    · obtain ⟨r,run,spec⟩ := overlap_from_correct P h F x index'
      refine ⟨r,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,leftRun,rightRun,common_correct,show (0#usize).val = 0 from rfl,List.drop_zero,here,decide_false,
          Bool.false_eq_true,advance,run]
      · intro b same
        rw [spec b same,nextIndex]
        constructor
        · rintro ⟨d,member,found⟩
          exact ⟨d,List.mem_cons_of_mem _ member,found⟩
        · rintro ⟨d,member,found⟩
          rcases List.mem_cons.mp member with rfl | later
          · exact absurd (commonIff.mpr found) here
          · exact ⟨d,later,found⟩
  · have empty : h.disjoint.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some false,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro b same
    cases same
    simp [empty]
termination_by h.disjoint.val.length - index.val
decreasing_by omega

theorem overlap_node_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (index : Usize) :
    ∃ r, forest.overlap_node P h F index = .ok r ∧
      (∀ x, r = some (some x) → Active F.nodes.val x.val ∧ Overlap P h F x.val) ∧
      (r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y → ¬ Overlap P h F y) := by
  rw [forest.overlap_node]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : index'.val = index.val+1 := by simpa using indexValue
    obtain ⟨r,run,found,absent⟩ := overlap_node_correct P h F index'
    have skip : (Active F.nodes.val index.val → ¬ Overlap P h F index.val) →
        r = some none → ∀ y, index.val ≤ y → Active F.nodes.val y → ¬ Overlap P h F y := by
      intro here none y low active
      by_cases same : y = index.val
      · subst same
        exact here active
      · exact absent none y (by omega) active
    by_cases active : F.nodes.val[index.val].active = true
    · obtain ⟨l,lRun,lSpec⟩ := overlap_from_correct P h F index 0#usize
      cases l with
      | none => exact ⟨none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,lRun],by simp,by simp⟩
      | some b =>
        have iff := lSpec b rfl
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at iff
        cases b with
        | true =>
          refine ⟨some (some index),by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,lRun],?_,
            by simp⟩
          intro x same
          simp only [Option.some.injEq] at same
          subst same
          exact ⟨⟨_,at_index,active⟩,iff.mp rfl⟩
        | false =>
          refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,lRun,advance,run],found,
            skip ?_⟩
          intro _ overlap
          exact absurd (iff.mpr overlap) (by simp)
    · refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,active,advance,run],found,skip ?_⟩
      rintro ⟨n,at_n,isActive⟩
      rw [at_index] at at_n
      cases at_n
      exact absurd isActive active
  · refine ⟨some none,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by simp,?_⟩
    intro _ y low ⟨n,at_n,_⟩
    have := (List.getElem?_eq_some_iff.mp at_n).1
    omega
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

/-- Something an active node, a tree edge, a link, an added edge from a live
    node or a loop requires of node `y`. -/
def AddNeeds (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (y : Nat) (c : Usize) :
    Prop :=
  (Active F.nodes.val y ∧ NodeNeeds P F y c) ∨ TreeNeeds P.entries.val h F.nodes.val y c ∨
    LinkNeeds P.entries.val h F (linkEnds P.links.val) y c ∨
    LinkNeeds P.entries.val h F (edgeEnds (liveEdges F F.edges.val)) y c ∨ LoopNeeds P.entries.val h F y c

/-- No rule applies: every active node has what it needs, every tree edge, link
    and added edge from a live node gives each end what the other requires,
    every neighbour that a maximum restriction counts decides its filler, no
    maximum restriction counts too many neighbours, nor, at a named node, a
    neighbour the model may repeat, every existential and minimum restriction
    of an unblocked active node has enough neighbours satisfying its filler,
    every nominal is on the named node of its individual, every loop of an
    active node gives it what it requires along the loop, no active node with
    `¬∃r.Self` is its own neighbour along `r`, and no active node has a common
    neighbour along the two roles of a disjoint pair. -/
def Complete (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) : Prop :=
  (∀ y, Active F.nodes.val y → ∀ c, NodeNeeds P F y c → Holds P.entries.val (labelOf F.nodes.val y) c.val) ∧
  (∀ child n, F.nodes.val[child]? = some n → n.tree = true → n.active = true →
    n.parent.val < F.nodes.val.length → ∀ s ∈ n.roles.val,
      EdgeOk P.entries.val h (labelOf F.nodes.val n.parent.val) s (labelOf F.nodes.val child) ∧
      EdgeOk P.entries.val h (labelOf F.nodes.val child) (inv s) (labelOf F.nodes.val n.parent.val)) ∧
  LinksOk P.entries.val h F (linkEnds P.links.val) ∧ LinksOk P.entries.val h F (edgeEnds (liveEdges F F.edges.val)) ∧
  (∀ y, Active F.nodes.val y → CountOk P h F true y) ∧ (∀ y, Active F.nodes.val y → CountOk P h F false y) ∧
  (∀ y, Active F.nodes.val y → ¬ Blocked F.nodes.val y → ∀ i ∈ labelOf F.nodes.val y, ∀ e role c n,
    P.entries.val[i.val]? = some e → generatorOf e = some (role,n,c) → Enough P h F y role c n) ∧
  (∀ y, Active F.nodes.val y → NominalOkAt P F y) ∧
  (∀ y, Active F.nodes.val y → LoopsOk P.entries.val h F y) ∧ (∀ y, Active F.nodes.val y → ¬ Looped P h F y) ∧
  (∀ y, Active F.nodes.val y → ¬ Overlap P h F y)

/-- The rule search returns a concept that a node lacks and that a node or edge
    requires, a nominal of an active node that names another node, a neighbour
    to decide, a maximum restriction with too many neighbours, or a restriction
    to expand at an unblocked node; it reports `Done` exactly for a complete
    forest. -/
theorem next_step_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) :
    ∃ r, forest.next_step P h F = .ok r ∧
      (∀ y c, r = some (.Add y c) → y.val < F.nodes.val.length ∧ AddNeeds P h F y.val c ∧
        ¬ Holds P.entries.val (labelOf F.nodes.val y.val) c.val) ∧
      (∀ y c c', r = some (.Choose y c c') → ∃ x : Usize, Active F.nodes.val x.val ∧
        CountStep P h F true x (.Choose y c c')) ∧
      (∀ x i, r = some (.Merge x i) → Active F.nodes.val x.val ∧ CountStep P h F false x (.Merge x i)) ∧
      (∀ x i, r = some (.Name x i) → Active F.nodes.val x.val ∧ CountStep P h F false x (.Name x i)) ∧
      (∀ x i, r = some (.Capped x i) → Active F.nodes.val x.val ∧ CountStep P h F false x (.Capped x i)) ∧
      (∀ x root, r = some (.Nominal x root) → Active F.nodes.val x.val ∧ ∃ i ∈ labelOf F.nodes.val x.val, ∃ a,
        P.entries.val[i.val]? = some (.One a) ∧ NominalRoot P F a = some root ∧ root ≠ x) ∧
      (∀ x, r = some (.Loop x) → Active F.nodes.val x.val ∧ Looped P h F x.val) ∧
      (∀ x, r = some (.Overlap x) → Active F.nodes.val x.val ∧ Overlap P h F x.val) ∧
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
    refine ⟨some (.Add y c),by simp [run0],?_,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
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
    refine ⟨some (.Add y c),by simp [run0,run1],?_,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
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
    refine ⟨some (.Add y c),by simp [run0,run1,run2],?_,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
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
    refine ⟨some (.Add y c),by simp [run0,run1,run2,run3],?_,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
    intro y' c' same
    simp only [Option.some.injEq,forest.Step.Add.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨inside,.inr (.inr (.inr (.inl needs))),fails⟩
  | none =>
  obtain ⟨r14,run14,found14,absent14⟩ := missing_loops_correct P h F 0#usize
  cases r14 with
  | some pair =>
    obtain ⟨y,c⟩ := pair
    obtain ⟨inside,needs,fails⟩ := found14 y c rfl
    refine ⟨some (.Add y c),by simp [run0,run1,run2,run3,run14],?_,by simp,by simp,by simp,by simp,by simp,by simp,by simp,
      by simp,by simp⟩
    intro y' c' same
    simp only [Option.some.injEq,forest.Step.Add.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨inside,.inr (.inr (.inr (.inr needs))),fails⟩
  | none =>
  obtain ⟨r15,run15,found15,absent15⟩ := looped_node_correct P h F 0#usize
  cases r15 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run14,run15],by simp,by simp,by simp,by simp,by simp,by simp,
      by simp,by simp,by simp,by simp⟩
  | some r16 =>
  cases r16 with
  | some x =>
    refine ⟨some (.Loop x),by simp [run0,run1,run2,run3,run14,run15],by simp,by simp,by simp,by simp,by simp,by simp,
      ?_,by simp,by simp,by simp⟩
    intro x' same
    simp only [Option.some.injEq,forest.Step.Loop.injEq] at same
    subst same
    exact found15 x rfl
  | none =>
  obtain ⟨r17,run17,found17,absent17⟩ := overlap_node_correct P h F 0#usize
  cases r17 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run14,run15,run17],by simp,by simp,by simp,by simp,by simp,
      by simp,by simp,by simp,by simp,by simp⟩
  | some r18 =>
  cases r18 with
  | some x =>
    refine ⟨some (.Overlap x),by simp [run0,run1,run2,run3,run14,run15,run17],by simp,by simp,by simp,by simp,
      by simp,by simp,by simp,?_,by simp,by simp⟩
    intro x' same
    simp only [Option.some.injEq,forest.Step.Overlap.injEq] at same
    subst same
    exact found17 x rfl
  | none =>
  obtain ⟨r12,run12,found12,absent12⟩ := nominal_node_correct P F 0#usize
  cases r12 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run14,run15,run17,run12],by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
  | some r13 =>
  cases r13 with
  | some pair =>
    obtain ⟨x,root⟩ := pair
    refine ⟨some (.Nominal x root),by simp [run0,run1,run2,run3,run14,run15,run17,run12],by simp,by simp,by simp,by simp,by simp,?_,by simp,by simp,by simp,by simp⟩
    intro x' root' same
    simp only [Option.some.injEq,forest.Step.Nominal.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    exact found12 x root rfl
  | none =>
  obtain ⟨r4,run4,found4,absent4⟩ := counting_correct P h F true 0#usize
  cases r4 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4],by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
  | some r5 =>
  cases r5 with
  | some step =>
    obtain ⟨x,active,i,member,n,role,c,c',at_i,y,isChoose,neighbour,one,two⟩ := found4 step rfl
    subst isChoose
    refine ⟨some (.Choose y c c'),by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4],by simp,?_,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
    intro y' d d' same
    simp only [Option.some.injEq,forest.Step.Choose.injEq] at same
    obtain ⟨rfl,rfl,rfl⟩ := same
    exact ⟨x,active,i,member,n,role,c,c',at_i,y,rfl,neighbour,one,two⟩
  | none =>
  obtain ⟨r6,run6,found6,absent6⟩ := counting_correct P h F false 0#usize
  cases r6 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6],by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
  | some r7 =>
  cases r7 with
  | some step =>
    obtain ⟨x,active,i,member,n,role,c,c',at_i,cases⟩ := found6 step rfl
    have counted : CountStep P h F false x step := ⟨i,member,n,role,c,c',at_i,cases⟩
    rcases cases with ⟨rfl,_⟩ | ⟨_,⟨rfl,_⟩ | ⟨rfl,_⟩⟩
    · refine ⟨some (.Merge x i),by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6],by simp,by simp,?_,by simp,by simp,
        by simp,by simp,by simp,by simp,by simp⟩
      intro x' i' same
      simp only [Option.some.injEq,forest.Step.Merge.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      exact ⟨active,counted⟩
    · refine ⟨some (.Name x i),by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6],by simp,by simp,by simp,?_,by simp,
        by simp,by simp,by simp,by simp,by simp⟩
      intro x' i' same
      simp only [Option.some.injEq,forest.Step.Name.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      exact ⟨active,counted⟩
    · refine ⟨some (.Capped x i),by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6],by simp,by simp,by simp,by simp,?_,
        by simp,by simp,by simp,by simp,by simp⟩
      intro x' i' same
      simp only [Option.some.injEq,forest.Step.Capped.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      exact ⟨active,counted⟩
  | none =>
  obtain ⟨r8,run8,found8,absent8⟩ := missing_successor_correct P h F true 0#usize
  cases r8 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6,run8],by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,
      by simp⟩
  | some r9 =>
  cases r9 with
  | some pair =>
    obtain ⟨x,i⟩ := pair
    refine ⟨some (.Create x i),by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6,run8],by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,?_,
      by simp⟩
    intro x' i' same
    simp only [Option.some.injEq,forest.Step.Create.injEq] at same
    obtain ⟨rfl,rfl⟩ := same
    obtain ⟨active,free,member,e,role,c,n,at_i,gen,notDone,short⟩ := found8 x i rfl
    exact ⟨active,free,member,e,role,c,n,at_i,gen,notDone rfl,short⟩
  | none =>
  obtain ⟨r10,run10,found10,absent10⟩ := missing_successor_correct P h F false 0#usize
  cases r10 with
  | none => exact ⟨none,by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6,run8,run10],by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,
      by simp,by simp⟩
  | some r11 =>
  cases r11 with
  | some pair => exact ⟨some .Stuck,by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6,run8,run10],by simp,by simp,by simp,by simp,by simp,
      by simp,by simp,by simp,by simp,by simp⟩
  | none =>
  refine ⟨some .Done,by simp [run0,run1,run2,run3,run14,run15,run17,run12,run4,run6,run8,run10],by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,by simp,
    ?_⟩
  intro _
  rw [zero] at absent2 absent3
  refine ⟨fun y isActive c needs => absent0 rfl y (Nat.zero_le _) isActive c needs,
    fun child n at_child tree active parentIn s member =>
      absent1 rfl child n (Nat.zero_le _) at_child tree active parentIn s member,
    by simpa using absent2 rfl,by simpa using absent3 rfl,
    fun y isActive => absent4 rfl y (Nat.zero_le _) isActive,
    fun y isActive => absent6 rfl y (Nat.zero_le _) isActive,
    fun y isActive free i member e role c n at_i gen =>
      absent10 rfl y (Nat.zero_le _) isActive free i member e role c n at_i gen (by simp),
    fun y isActive => absent12 rfl y (Nat.zero_le _) isActive,
    fun y isActive => absent14 rfl y (Nat.zero_le _) isActive,
    fun y isActive => absent15 rfl y (Nat.zero_le _) isActive,
    fun y isActive => absent17 rfl y (Nat.zero_le _) isActive⟩

end Rowl.ForestSearch
