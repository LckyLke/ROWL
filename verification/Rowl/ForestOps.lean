import Rowl.ForestSearch

/-!
The operations the completion forest's rules apply, proved exact: copying the
forest, adding a literal to a label, creating tree nodes with their
differences, the branch points a rule rests on, the pairs of nodes a maximum
restriction may merge, and the parts of a merge, which moves the edge, the
differences and the individuals of one node to another and prunes the
subtree of the merged node.
-/
namespace Rowl.ForestOps
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Concepts (inv inverse_correct copy_role_identity)
open Rowl.CompletionSearch (contains_correct)
open Rowl.Completion (copy_label_correct join_correct join_from_correct)
open Rowl.ForestSearch
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

theorem copy_roles_correct (roles : alloc.vec.Vec ObjectPropertyExpression) (index : Usize)
    (out : alloc.vec.Vec ObjectPropertyExpression) (copied : out.val = roles.val.take index.val)
    (inside : index.val ≤ roles.val.length) : forest.copy_roles roles index out = .ok roles := by
  rw [forest.copy_roles]
  by_cases more : index.val < roles.val.length
  · have lookup : roles.index_usize index = .ok roles.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have room : out.val.length < Usize.max := by
      rw [copied]; simp; have := roles.property; scalar_tac
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out roles.val[index.val] room)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := copy_roles_correct roles next appended
      (by rw [contents,copied,nextIndex,List.take_succ_eq_append_getElem more]) (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,copy_role_identity,push,advance,rest]
  · have full : index.val = roles.val.length := by omega
    have same : out = roles := by
      apply (alloc.vec.Vec.eq_iff out roles).mpr
      rw [copied,full,List.take_length]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,same]
termination_by roles.val.length - index.val
decreasing_by omega

theorem copy_nodes_correct (nodes : alloc.vec.Vec forest.Node) (index : Usize) (out : alloc.vec.Vec forest.Node)
    (copied : out.val = nodes.val.take index.val) (inside : index.val ≤ nodes.val.length) :
    forest.copy_nodes nodes index out = .ok nodes := by
  rw [forest.copy_nodes]
  by_cases more : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have room : out.val.length < Usize.max := by
      rw [copied]; simp; have := nodes.property; scalar_tac
    have labelCopy := copy_label_correct nodes.val[index.val].label 0#usize (alloc.vec.Vec.new Usize) (by simp)
      (by simp)
    have rolesCopy := copy_roles_correct nodes.val[index.val].roles 0#usize
      (alloc.vec.Vec.new ObjectPropertyExpression) (by simp) (by simp)
    have doneCopy := copy_label_correct nodes.val[index.val].done 0#usize (alloc.vec.Vec.new Usize) (by simp)
      (by simp)
    have depsCopy := copy_label_correct nodes.val[index.val].deps 0#usize (alloc.vec.Vec.new Usize) (by simp)
      (by simp)
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out nodes.val[index.val] room)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := copy_nodes_correct nodes next appended
      (by rw [contents,copied,nextIndex,List.take_succ_eq_append_getElem more]) (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,labelCopy,rolesCopy,doneCopy,depsCopy,push,advance,rest]
  · have full : index.val = nodes.val.length := by omega
    have same : out = nodes := by
      apply (alloc.vec.Vec.eq_iff out nodes).mpr
      rw [copied,full,List.take_length]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,same]
termination_by nodes.val.length - index.val
decreasing_by omega

theorem copy_edges_correct (edges : alloc.vec.Vec forest.Edge) (index : Usize) (out : alloc.vec.Vec forest.Edge)
    (copied : out.val = edges.val.take index.val) (inside : index.val ≤ edges.val.length) :
    forest.copy_edges edges index out = .ok edges := by
  rw [forest.copy_edges]
  by_cases more : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have room : out.val.length < Usize.max := by
      rw [copied]; simp; have := edges.property; scalar_tac
    have depsCopy := copy_label_correct edges.val[index.val].deps 0#usize (alloc.vec.Vec.new Usize) (by simp)
      (by simp)
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out edges.val[index.val] room)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := copy_edges_correct edges next appended
      (by rw [contents,copied,nextIndex,List.take_succ_eq_append_getElem more]) (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,copy_role_identity,depsCopy,push,advance,rest]
  · have full : index.val = edges.val.length := by omega
    have same : out = edges := by
      apply (alloc.vec.Vec.eq_iff out edges).mpr
      rw [copied,full,List.take_length]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,same]
termination_by edges.val.length - index.val
decreasing_by omega

theorem copy_distinct_correct (distinct : alloc.vec.Vec forest.Distinct) (index : Usize)
    (out : alloc.vec.Vec forest.Distinct) (copied : out.val = distinct.val.take index.val)
    (inside : index.val ≤ distinct.val.length) : forest.copy_distinct distinct index out = .ok distinct := by
  rw [forest.copy_distinct]
  by_cases more : index.val < distinct.val.length
  · have lookup : distinct.index_usize index = .ok distinct.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have room : out.val.length < Usize.max := by
      rw [copied]; simp; have := distinct.property; scalar_tac
    have depsCopy := copy_label_correct distinct.val[index.val].deps 0#usize (alloc.vec.Vec.new Usize) (by simp)
      (by simp)
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out distinct.val[index.val] room)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := copy_distinct_correct distinct next appended
      (by rw [contents,copied,nextIndex,List.take_succ_eq_append_getElem more]) (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,depsCopy,push,advance,rest]
  · have full : index.val = distinct.val.length := by omega
    have same : out = distinct := by
      apply (alloc.vec.Vec.eq_iff out distinct).mpr
      rw [copied,full,List.take_length]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,same]
termination_by distinct.val.length - index.val
decreasing_by omega

/-- Copying the forest reproduces it exactly. -/
theorem copy_forest_correct (F : forest.Forest) : forest.copy_forest F = .ok F := by
  rw [forest.copy_forest,copy_nodes_correct F.nodes 0#usize _ (by simp) (by simp),
    copy_edges_correct F.edges 0#usize _ (by simp) (by simp),
    copy_distinct_correct F.distinct 0#usize _ (by simp) (by simp),
    copy_label_correct F.same 0#usize _ (by simp) (by simp)]
  simp only [bind_ok]

/-- Adding an item to the label of a node in range: the label gets the item and
    the node's points join `deps`. -/
theorem insert_correct (F : forest.Forest) (x item : Usize) (deps : alloc.vec.Vec Usize) :
    ∃ r, forest.insert F x item deps = .ok r ∧ ∀ F', r = some F' →
      ∃ inside : x.val < F.nodes.val.length, ∃ (label joined : alloc.vec.Vec Usize),
        label.val = F.nodes.val[x.val].label.val ++ [item] ∧
        (∀ k, k ∈ joined.val ↔ k ∈ F.nodes.val[x.val].deps.val ∨ k ∈ deps.val) ∧
        F' = { F with nodes := (F.nodes.set x
          ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
            F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩) } := by
  rw [forest.insert]
  by_cases inside : x.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    by_cases room : F.nodes.val[x.val].label.val.length < Usize.max
    · obtain ⟨joinResult,joinRun,joinSpec⟩ := join_correct F.nodes.val[x.val].deps deps
      cases joinResult with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,usize_max_val,room,joinRun]
      | some joined =>
        obtain ⟨label,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec F.nodes.val[x.val].label item room)
        let n := F.nodes.val[x.val]
        refine ⟨some { F with nodes := (F.nodes.set x
          ⟨label,n.parent,n.roles,n.seed,n.tree,n.active,n.done,joined⟩) },?_,?_⟩
        · have setLookup : (F.nodes.set x ⟨label,n.parent,n.roles,n.seed,n.tree,n.active,n.done,n.deps⟩).index_usize x =
              .ok ⟨label,n.parent,n.roles,n.seed,n.tree,n.active,n.done,n.deps⟩ := by
            simp [alloc.vec.Vec.index_usize,alloc.vec.Vec.set_val_eq,inside]
          have twice : (F.nodes.set x ⟨label,n.parent,n.roles,n.seed,n.tree,n.active,n.done,n.deps⟩).set x
              ⟨label,n.parent,n.roles,n.seed,n.tree,n.active,n.done,joined⟩ =
              F.nodes.set x ⟨label,n.parent,n.roles,n.seed,n.tree,n.active,n.done,joined⟩ := by
            apply (alloc.vec.Vec.eq_iff _ _).mpr
            simp [alloc.vec.Vec.set_val_eq]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookup,bind_ok,usize_max_val,room,joinRun,alloc.vec.Vec.index_mut_slice_index,
            alloc.vec.Vec.index_mut_usize,push]
          simp [n,push,setLookup,twice]
        · intro F' same
          cases same
          exact ⟨inside,label,joined,contents,joinSpec joined rfl,rfl⟩
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,usize_max_val,room]
  · refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]

/-- The pending entries of a list. -/
def pendingOf : List Usize → completion.Pending
  | [] => .Empty
  | c :: rest => .Item c (pendingOf rest)

theorem pendingList_of (l : List Usize) : Rowl.Completion.pendingList (pendingOf l) = l := by
  induction l with
  | nil => rfl
  | cons c rest ih => simp [pendingOf,Rowl.Completion.pendingList,ih]

theorem pending_from_correct (label : alloc.vec.Vec Usize) (index : Usize) :
    forest.pending_from label index = .ok (pendingOf (label.val.drop index.val)) := by
  rw [forest.pending_from]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : label.val.drop index.val = label.val[index.val] :: label.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := pending_from_correct label next
    rw [nextIndex] at rest
    rw [split]
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
      bind_ok,advance,rest,pendingOf]
  · have empty : label.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty,pendingOf]
termination_by label.val.length - index.val
decreasing_by omega

/-- A new tree node below `x` along `role`, created for `filler`. -/
def child (x : Usize) (roles : alloc.vec.Vec ObjectPropertyExpression) (filler : Usize)
    (deps : alloc.vec.Vec Usize) : forest.Node :=
  ⟨alloc.vec.Vec.new Usize,x,roles,filler,true,true,alloc.vec.Vec.new Usize,deps⟩

/-- Creating tree nodes appends `count` new children with one role each. -/
theorem children_correct (F : forest.Forest) (x : Usize) (role : ObjectPropertyExpression) (filler : Usize)
    (deps : alloc.vec.Vec Usize) (count : Usize) :
    ∃ r, forest.children F x role filler deps count = .ok r ∧ ∀ F', r = some F' →
      ∃ (nodes : alloc.vec.Vec forest.Node) (roles : alloc.vec.Vec ObjectPropertyExpression),
        F' = { F with nodes := nodes } ∧ roles.val = [role] ∧
        nodes.val = F.nodes.val ++ List.replicate count.val (child x roles filler deps) := by
  rw [forest.children]
  by_cases positive : count > 0#usize
  · by_cases room : F.nodes.val.length < Usize.max
    · have one : (alloc.vec.Vec.new ObjectPropertyExpression).val.length < Usize.max := by simp; scalar_tac
      obtain ⟨roles,rolesPush,rolesContents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectPropertyExpression) role one)
      have depsCopy := copy_label_correct deps 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp)
      obtain ⟨nodes1,nodesPush,nodesContents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec F.nodes (child x roles filler deps) room)
      have countPositive : 0 < count.val := by
        have := positive; simp [GT.gt,UScalar.lt_equiv] at this; omega
      obtain ⟨less,lower,lowerValue⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize)
        (by scalar_tac))
      have lessIs : less.val = count.val - 1 := by simp at lowerValue; omega
      obtain ⟨r,run,spec⟩ := children_correct { F with nodes := nodes1 } x role filler deps less
      refine ⟨r,?_,?_⟩
      · simp only [positive,↓reduceIte,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room,
          copy_role_identity,bind_ok,rolesPush,depsCopy]
        simp only [child] at nodesPush
        simp [nodesPush,lower,run]
      · intro F' same
        obtain ⟨nodes,roles',shape,rolesIs,nodesIs⟩ := spec F' same
        have rolesSame : roles' = roles := by
          apply (alloc.vec.Vec.eq_iff _ _).mpr
          rw [rolesIs,rolesContents]
          simp
        subst rolesSame
        refine ⟨nodes,roles',by rw [shape],rolesIs,?_⟩
        rw [nodesIs,nodesContents,lessIs,List.append_assoc]
        congr 1
        cases hc : count.val with
        | zero => omega
        | succ k => simp [List.replicate_succ]
    · refine ⟨none,?_,by simp⟩
      simp [positive,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room]
  · have zero : count.val = 0 := by
      simp [GT.gt,UScalar.lt_equiv] at positive; omega
    have one : (alloc.vec.Vec.new ObjectPropertyExpression).val.length < Usize.max := by simp; scalar_tac
    obtain ⟨roles,_,rolesContents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec (alloc.vec.Vec.new ObjectPropertyExpression) role one)
    refine ⟨some F,by simp [positive],?_⟩
    intro F' same
    cases same
    refine ⟨F.nodes,roles,rfl,by rw [rolesContents]; simp,?_⟩
    simp [zero]
termination_by count.val
decreasing_by omega

/-- Differences from `x` to every node of `nodes[other..]`. -/
theorem differ_from_correct (F : forest.Forest) (x other : Usize) (deps : alloc.vec.Vec Usize) :
    ∃ r, forest.differ_from F x other deps = .ok r ∧ ∀ F', r = some F' →
      ∃ distinct : alloc.vec.Vec forest.Distinct, F' = { F with distinct := distinct } ∧
        ∀ d, d ∈ distinct.val ↔ d ∈ F.distinct.val ∨
          (d.left = x ∧ other.val ≤ d.right.val ∧ d.right.val < F.nodes.val.length ∧ d.deps = deps) := by
  rw [forest.differ_from]
  by_cases more : other.val < F.nodes.val.length
  · by_cases room : F.distinct.val.length < Usize.max
    · have depsCopy := copy_label_correct deps 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp)
      obtain ⟨distinct1,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec F.distinct (⟨x,other,deps⟩ : forest.Distinct) room)
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := other) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = other.val+1 := by simpa using nextValue
      obtain ⟨r,run,spec⟩ := differ_from_correct { F with distinct := distinct1 } x next deps
      refine ⟨r,?_,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,depsCopy,push,advance,run]
      · intro F' same
        obtain ⟨distinct,shape,members⟩ := spec F' same
        refine ⟨distinct,by rw [shape],?_⟩
        intro d
        rw [members,contents,nextIndex]
        simp only [List.mem_append,List.mem_singleton]
        constructor
        · rintro ((old | rfl) | ⟨left,low,high,depsIs⟩)
          · exact .inl old
          · exact .inr ⟨rfl,le_refl _,more,rfl⟩
          · exact .inr ⟨left,by omega,high,depsIs⟩
        · rintro (old | ⟨left,low,high,depsIs⟩)
          · exact .inl (.inl old)
          · by_cases here : d.right.val = other.val
            · refine .inl (.inr ?_)
              cases d
              simp only at left high depsIs here ⊢
              rw [left,depsIs,UScalar.eq_of_val_eq here]
            · exact .inr ⟨left,by omega,high,depsIs⟩
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room]
  · refine ⟨some F,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro F' same
    cases same
    refine ⟨F.distinct,rfl,?_⟩
    intro d
    constructor
    · exact .inl
    · rintro (old | ⟨_,low,high,_⟩)
      · exact old
      · omega
termination_by F.nodes.val.length - other.val
decreasing_by omega

/-- Differences between every two nodes of `nodes[x..]`. -/
theorem pairwise_correct (F : forest.Forest) (x : Usize) (deps : alloc.vec.Vec Usize) :
    ∃ r, forest.pairwise F x deps = .ok r ∧ ∀ F', r = some F' →
      ∃ distinct : alloc.vec.Vec forest.Distinct, F' = { F with distinct := distinct } ∧
        ∀ d, d ∈ distinct.val ↔ d ∈ F.distinct.val ∨ (x.val ≤ d.left.val ∧ d.left.val < d.right.val ∧
          d.right.val < F.nodes.val.length ∧ d.deps = deps) := by
  rw [forest.pairwise]
  by_cases more : x.val < F.nodes.val.length
  · obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := x) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = x.val+1 := by simpa using nextValue
    obtain ⟨one,oneRun,oneSpec⟩ := differ_from_correct F x next deps
    cases one with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,advance,oneRun]
    | some F1 =>
      obtain ⟨distinct1,shape1,members1⟩ := oneSpec F1 rfl
      subst shape1
      obtain ⟨r,run,spec⟩ := pairwise_correct { F with distinct := distinct1 } next deps
      refine ⟨r,?_,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,advance,oneRun,run]
      · intro F' same
        obtain ⟨distinct,shape,members⟩ := spec F' same
        refine ⟨distinct,by rw [shape],?_⟩
        intro d
        rw [members,members1,nextIndex]
        simp only
        constructor
        · rintro ((old | ⟨left,low,high,depsIs⟩) | ⟨low,between,high,depsIs⟩)
          · exact .inl old
          · exact .inr ⟨by rw [left],by rw [left]; omega,high,depsIs⟩
          · exact .inr ⟨by omega,between,high,depsIs⟩
        · rintro (old | ⟨low,between,high,depsIs⟩)
          · exact .inl (.inl old)
          · by_cases here : d.left.val = x.val
            · exact .inl (.inr ⟨UScalar.eq_of_val_eq here,by omega,high,depsIs⟩)
            · exact .inr ⟨by omega,between,high,depsIs⟩
  · refine ⟨some F,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro F' same
    cases same
    refine ⟨F.distinct,rfl,?_⟩
    intro d
    constructor
    · exact .inl
    · rintro (old | ⟨low,_,high,_⟩)
      · exact old
      · omega
termination_by F.nodes.val.length - x.val
decreasing_by all_goals omega

/-- The branch points the node `y` depends on. -/
def nodeDeps (F : forest.Forest) (y : Nat) : List Usize :=
  match F.nodes.val[y]? with
  | some n => n.deps.val
  | none => []

theorem end_deps_correct (F : forest.Forest) (e : Usize) (out : alloc.vec.Vec Usize) :
    ∃ r, forest.end_deps F e out = .ok r ∧ ∀ out', r = some out' →
      ∀ k, k ∈ out'.val ↔ k ∈ out.val ∨ k ∈ nodeDeps F e.val := by
  rw [forest.end_deps]
  by_cases inside : e.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize e = .ok F.nodes.val[e.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨r,run,spec⟩ := join_from_correct F.nodes.val[e.val].deps 0#usize out
    refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,run],?_⟩
    intro out' same k
    rw [spec out' same k]
    simp [nodeDeps,List.getElem?_eq_getElem inside]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside],?_⟩
    intro out' same k
    cases same
    simp [nodeDeps,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ e.val by omega)]

theorem children_deps_correct (F : forest.Forest) (x index : Usize) (out : alloc.vec.Vec Usize) :
    ∃ r, forest.children_deps F x index out = .ok r ∧ ∀ out', r = some out' →
      ∀ k, k ∈ out'.val ↔ k ∈ out.val ∨ ∃ y, index.val ≤ y ∧ ∃ n : forest.Node, F.nodes.val[y]? = some n ∧
        n.tree = true ∧ n.active = true ∧ n.parent = x ∧ k ∈ n.deps.val := by
  rw [forest.children_deps]
  by_cases more : index.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize index = .ok F.nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have at_index : F.nodes.val[index.val]? = some F.nodes.val[index.val] := List.getElem?_eq_getElem more
    have step : ∀ y, index.val ≤ y ↔ y = index.val ∨ next.val ≤ y := by intro y; omega
    by_cases child : F.nodes.val[index.val].tree = true ∧ F.nodes.val[index.val].active = true ∧
        F.nodes.val[index.val].parent = x
    · obtain ⟨tree,active,parent⟩ := child
      obtain ⟨joined,joinRun,joinSpec⟩ := join_from_correct F.nodes.val[index.val].deps 0#usize out
      cases joined with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,active,parent,joinRun]
      | some out1 =>
        obtain ⟨r,run,spec⟩ := children_deps_correct F x next out1
        refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,active,parent,joinRun,advance,
          run],?_⟩
        intro out' same k
        rw [spec out' same k,joinSpec out1 rfl k]
        simp only [show (0#usize).val = 0 from rfl,List.drop_zero]
        constructor
        · rintro ((old | here) | ⟨y,later,n,at_y,isTree,isActive,isParent,listed⟩)
          · exact .inl old
          · exact .inr ⟨index.val,le_refl _,F.nodes.val[index.val],at_index,tree,active,parent,here⟩
          · exact .inr ⟨y,by omega,n,at_y,isTree,isActive,isParent,listed⟩
        · rintro (old | ⟨y,from',n,at_y,isTree,isActive,isParent,listed⟩)
          · exact .inl (.inl old)
          · rcases (step y).mp from' with rfl | later
            · rw [at_index] at at_y
              cases at_y
              exact .inl (.inr listed)
            · exact .inr ⟨y,later,n,at_y,isTree,isActive,isParent,listed⟩
    · obtain ⟨r,run,spec⟩ := children_deps_correct F x next out
      refine ⟨r,?_,?_⟩
      · by_cases tree : F.nodes.val[index.val].tree = true
        · by_cases active : F.nodes.val[index.val].active = true
          · have parentNot : ¬ F.nodes.val[index.val].parent = x := fun same => child ⟨tree,active,same⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,active,parentNot,advance,run]
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,active,advance,run]
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,tree,advance,run]
      · intro out' same k
        rw [spec out' same k]
        constructor
        · rintro (old | ⟨y,later,n,at_y,isTree,isActive,isParent,listed⟩)
          · exact .inl old
          · exact .inr ⟨y,by omega,n,at_y,isTree,isActive,isParent,listed⟩
        · rintro (old | ⟨y,from',n,at_y,isTree,isActive,isParent,listed⟩)
          · exact .inl old
          · rcases (step y).mp from' with rfl | later
            · rw [at_index] at at_y
              cases at_y
              exact absurd ⟨isTree,isActive,isParent⟩ child
            · exact .inr ⟨y,later,n,at_y,isTree,isActive,isParent,listed⟩
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same k
    cases same
    constructor
    · exact .inl
    · rintro (old | ⟨y,from',n,at_y,_⟩)
      · exact old
      · rw [List.getElem?_eq_none_iff.mpr (by omega)] at at_y
        cases at_y
termination_by F.nodes.val.length - index.val
decreasing_by all_goals omega

theorem linked_deps_correct (F : forest.Forest) (links : alloc.vec.Vec completion.Link) (x index : Usize)
    (out : alloc.vec.Vec Usize) :
    ∃ r, forest.linked_deps F links x index out = .ok r ∧ ∀ out', r = some out' →
      ∀ k, k ∈ out'.val ↔ k ∈ out.val ∨ ∃ l ∈ links.val.drop index.val,
        (rep F l.from = x ∧ k ∈ nodeDeps F (rep F l.to).val) ∨ (rep F l.to = x ∧ k ∈ nodeDeps F (rep F l.from).val) := by
  rw [forest.linked_deps]
  by_cases more : index.val < links.val.length
  · have lookup : links.index_usize index = .ok links.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : links.val.drop index.val = links.val[index.val] :: links.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨l,lIs⟩ : ∃ l, links.val[index.val] = l := ⟨_,rfl⟩
    rw [lIs] at lookup split
    -- The other end of the link, in each orientation, then the rest.
    have finish : ∀ out2 : alloc.vec.Vec Usize, (∀ k, k ∈ out2.val ↔ k ∈ out.val ∨
        (rep F l.from = x ∧ k ∈ nodeDeps F (rep F l.to).val) ∨ (rep F l.to = x ∧ k ∈ nodeDeps F (rep F l.from).val)) →
        ∃ r, forest.linked_deps F links x next out2 = .ok r ∧ ∀ out', r = some out' →
          ∀ k, k ∈ out'.val ↔ k ∈ out.val ∨ ∃ l ∈ links.val.drop index.val,
            (rep F l.from = x ∧ k ∈ nodeDeps F (rep F l.to).val) ∨
            (rep F l.to = x ∧ k ∈ nodeDeps F (rep F l.from).val) := by
      intro out2 members2
      obtain ⟨r,run,spec⟩ := linked_deps_correct F links x next out2
      refine ⟨r,run,fun out' same k => ?_⟩
      rw [spec out' same k,members2,split,nextIndex]
      simp only [List.mem_cons,exists_eq_or_imp,or_assoc]
    by_cases fromHere : rep F l.from = x
    · obtain ⟨one,oneRun,oneSpec⟩ := end_deps_correct F (rep F l.to) out
      cases one with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,fromHere,oneRun]
      | some out1 =>
        by_cases toHere : rep F l.to = x
        · obtain ⟨two,twoRun,twoSpec⟩ := end_deps_correct F (rep F l.from) out1
          have oneRun' := oneRun
          rw [toHere] at oneRun'
          cases two with
          | none =>
            have twoRun' := twoRun
            rw [fromHere] at twoRun'
            refine ⟨none,?_,by simp⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,fromHere,oneRun',
              toHere,twoRun']
          | some out2 =>
            have twoRun' := twoRun
            rw [fromHere] at twoRun'
            obtain ⟨r,run,spec⟩ := finish out2 (fun k => by
              rw [twoSpec out2 rfl k,oneSpec out1 rfl k]
              simp only [fromHere,toHere,true_and]
              tauto)
            refine ⟨r,?_,spec⟩
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,fromHere,oneRun',
              toHere,twoRun',advance,run]
        · obtain ⟨r,run,spec⟩ := finish out1 (fun k => by
            rw [oneSpec out1 rfl k]
            simp [fromHere,toHere])
          refine ⟨r,?_,spec⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,fromHere,oneRun,toHere,
            advance,run]
    · by_cases toHere : rep F l.to = x
      · obtain ⟨two,twoRun,twoSpec⟩ := end_deps_correct F (rep F l.from) out
        cases two with
        | none =>
          refine ⟨none,?_,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,fromHere,toHere,twoRun]
        | some out2 =>
          obtain ⟨r,run,spec⟩ := finish out2 (fun k => by
            rw [twoSpec out2 rfl k]
            simp [fromHere,toHere])
          refine ⟨r,?_,spec⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,fromHere,toHere,twoRun,
            advance,run]
      · obtain ⟨r,run,spec⟩ := finish out (fun k => by simp [fromHere,toHere])
        refine ⟨r,?_,spec⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,representative_correct,fromHere,toHere,advance,run]
  · have empty : links.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same k
    cases same
    simp [empty]
termination_by links.val.length - index.val
decreasing_by all_goals omega

theorem edge_deps_correct (F : forest.Forest) (x index : Usize) (out : alloc.vec.Vec Usize) :
    ∃ r, forest.edge_deps F x index out = .ok r ∧ ∀ out', r = some out' →
      ∀ k, k ∈ out'.val ↔ k ∈ out.val ∨ ∃ e ∈ F.edges.val.drop index.val, (rep F e.from = x ∨ rep F e.to = x) ∧
        (k ∈ e.deps.val ∨ k ∈ nodeDeps F (rep F e.from).val ∨ k ∈ nodeDeps F (rep F e.to).val) := by
  rw [forest.edge_deps]
  by_cases more : index.val < F.edges.val.length
  · have lookup : F.edges.index_usize index = .ok F.edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : F.edges.val.drop index.val = F.edges.val[index.val] :: F.edges.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨e,eIs⟩ : ∃ e, F.edges.val[index.val] = e := ⟨_,rfl⟩
    rw [eIs] at lookup split
    have atIff : (if rep F e.from = x then (ok true : Result Bool) else if rep F e.to = x then ok true else ok false) =
        .ok (decide (rep F e.from = x ∨ rep F e.to = x)) := by
      by_cases one : rep F e.from = x
      · simp [one]
      · by_cases two : rep F e.to = x <;> simp [one,two]
    by_cases at_x : rep F e.from = x ∨ rep F e.to = x
    · obtain ⟨one,oneRun,oneSpec⟩ := join_from_correct e.deps 0#usize out
      cases one with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,representative_correct,atIff,at_x,decide_true,oneRun]
      | some out1 =>
        obtain ⟨two,twoRun,twoSpec⟩ := end_deps_correct F (rep F e.from) out1
        cases two with
        | none =>
          refine ⟨none,?_,by simp⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,representative_correct,atIff,at_x,decide_true,oneRun,twoRun]
        | some out2 =>
          obtain ⟨three,threeRun,threeSpec⟩ := end_deps_correct F (rep F e.to) out2
          cases three with
          | none =>
            refine ⟨none,?_,by simp⟩
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookup,bind_ok,representative_correct,atIff,at_x,decide_true,oneRun,twoRun,threeRun]
          | some out3 =>
            obtain ⟨r,run,spec⟩ := edge_deps_correct F x next out3
            refine ⟨r,?_,?_⟩
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
                lookup,bind_ok,representative_correct,atIff,at_x,decide_true,oneRun,twoRun,threeRun,advance,run]
            · intro out' same k
              rw [spec out' same k,threeSpec out3 rfl k,twoSpec out2 rfl k,oneSpec out1 rfl k,split,nextIndex]
              simp only [show (0#usize).val = 0 from rfl,List.drop_zero,List.mem_cons,exists_eq_or_imp,at_x,true_and,
                or_assoc]
    · obtain ⟨r,run,spec⟩ := edge_deps_correct F x next out
      refine ⟨r,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,representative_correct,atIff,at_x,decide_false,Bool.false_eq_true,advance,run]
      · intro out' same k
        rw [spec out' same k,split,nextIndex]
        simp only [List.mem_cons,exists_eq_or_imp,at_x,false_and,false_or]
  · have empty : F.edges.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same k
    cases same
    simp [empty]
termination_by F.edges.val.length - index.val
decreasing_by all_goals omega

/-- `y` is `x` or one of its neighbours along some role: its parent, an active
    child, or a named node that a link or an added edge relates to it, read
    through the merges. -/
def Near (P : completion.Problem) (F : forest.Forest) (x y : Nat) : Prop :=
  y = x ∨
  (∃ n : forest.Node, F.nodes.val[x]? = some n ∧ n.tree = true ∧ n.parent.val = y) ∨
  (∃ n : forest.Node, F.nodes.val[y]? = some n ∧ n.tree = true ∧ n.active = true ∧ n.parent.val = x) ∨
  (∃ l ∈ P.links.val, ((rep F l.from).val = x ∧ (rep F l.to).val = y) ∨ ((rep F l.to).val = x ∧ (rep F l.from).val = y)) ∨
  (∃ e ∈ F.edges.val, ((rep F e.from).val = x ∧ (rep F e.to).val = y) ∨ ((rep F e.to).val = x ∧ (rep F e.from).val = y))

/-- The points a rule at `x` rests on cover the points of every node near `x` and
    of every added edge at `x`, and come from nodes and added edges only. -/
theorem rule_deps_correct (P : completion.Problem) (F : forest.Forest) (x : Usize)
    (inside : x.val < F.nodes.val.length) :
    ∃ r, forest.rule_deps P F x = .ok r ∧ ∀ out, r = some out →
      (∀ y, Near P F x.val y → Rowl.Completion.Sub (nodeDeps F y) out.val) ∧
      (∀ e ∈ F.edges.val, (rep F e.from = x ∨ rep F e.to = x) → Rowl.Completion.Sub e.deps.val out.val) ∧
      (∀ k ∈ out.val, (∃ y, k ∈ nodeDeps F y) ∨ ∃ e ∈ F.edges.val, k ∈ e.deps.val) := by
  have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
  have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem inside
  have own : nodeDeps F x.val = F.nodes.val[x.val].deps.val := by simp [nodeDeps,at_x]
  rw [forest.rule_deps]
  simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,bind_ok,
    copy_label_correct F.nodes.val[x.val].deps 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp)]
  have parentStep : ∃ r1, (if F.nodes.val[x.val].tree = true then forest.end_deps F F.nodes.val[x.val].parent
        F.nodes.val[x.val].deps else ok (some F.nodes.val[x.val].deps)) = .ok r1 ∧ ∀ o, r1 = some o →
      ∀ k, k ∈ o.val ↔ k ∈ F.nodes.val[x.val].deps.val ∨
        (F.nodes.val[x.val].tree = true ∧ k ∈ nodeDeps F F.nodes.val[x.val].parent.val) := by
    by_cases tree : F.nodes.val[x.val].tree = true
    · obtain ⟨r1,run1,spec1⟩ := end_deps_correct F F.nodes.val[x.val].parent F.nodes.val[x.val].deps
      refine ⟨r1,by simp [tree,run1],fun o same k => ?_⟩
      rw [spec1 o same k]
      simp [tree]
    · refine ⟨some F.nodes.val[x.val].deps,by simp [tree],fun o same k => ?_⟩
      cases same
      simp [tree]
  obtain ⟨r1,run1,spec1⟩ := parentStep
  rw [run1]
  cases r1 with
  | none => exact ⟨none,by simp,by simp⟩
  | some out1 =>
    obtain ⟨r2,run2,spec2⟩ := children_deps_correct F x 0#usize out1
    simp only [bind_ok,run2]
    cases r2 with
    | none => exact ⟨none,by simp,by simp⟩
    | some out2 =>
      obtain ⟨r3,run3,spec3⟩ := linked_deps_correct F P.links x 0#usize out2
      simp only [bind_ok,run3]
      cases r3 with
      | none => exact ⟨none,by simp,by simp⟩
      | some out3 =>
        obtain ⟨r4,run4,spec4⟩ := edge_deps_correct F x 0#usize out3
        refine ⟨r4,by simp [run4],?_⟩
        intro out same
        have member : ∀ k, k ∈ out.val ↔ ((((k ∈ F.nodes.val[x.val].deps.val ∨
            (F.nodes.val[x.val].tree = true ∧ k ∈ nodeDeps F F.nodes.val[x.val].parent.val)) ∨
            (∃ y, 0 ≤ y ∧ ∃ n : forest.Node, F.nodes.val[y]? = some n ∧ n.tree = true ∧ n.active = true ∧
              n.parent = x ∧ k ∈ n.deps.val)) ∨
            ∃ l ∈ P.links.val, (rep F l.from = x ∧ k ∈ nodeDeps F (rep F l.to).val) ∨
              (rep F l.to = x ∧ k ∈ nodeDeps F (rep F l.from).val)) ∨
            ∃ e ∈ F.edges.val, (rep F e.from = x ∨ rep F e.to = x) ∧
              (k ∈ e.deps.val ∨ k ∈ nodeDeps F (rep F e.from).val ∨ k ∈ nodeDeps F (rep F e.to).val)) := by
          intro k
          rw [spec4 out same k,spec3 out3 rfl k,spec2 out2 rfl k,spec1 out1 rfl k]
          simp only [show (0#usize).val = 0 from rfl,List.drop_zero]
        refine ⟨?_,?_,?_⟩
        · intro y near k listed
          rw [member k]
          rcases near with rfl | ⟨n,at_n,tree,parent⟩ | ⟨n,at_n,tree,active,parent⟩ |
              ⟨l,linked,⟨source,target⟩ | ⟨target,source⟩⟩ | ⟨e,edge,⟨source,target⟩ | ⟨target,source⟩⟩
          · rw [own] at listed
            exact .inl (.inl (.inl (.inl listed)))
          · rw [at_x] at at_n
            cases at_n
            exact .inl (.inl (.inl (.inr ⟨tree,by rw [parent]; exact listed⟩)))
          · refine .inl (.inl (.inr ⟨y,Nat.zero_le _,n,at_n,tree,active,UScalar.eq_of_val_eq parent,?_⟩))
            simpa [nodeDeps,at_n] using listed
          · exact .inl (.inr ⟨l,linked,.inl ⟨UScalar.eq_of_val_eq source,by rw [target]; exact listed⟩⟩)
          · exact .inl (.inr ⟨l,linked,.inr ⟨UScalar.eq_of_val_eq target,by rw [source]; exact listed⟩⟩)
          · exact .inr ⟨e,edge,.inl (UScalar.eq_of_val_eq source),.inr (.inr (by rw [target]; exact listed))⟩
          · exact .inr ⟨e,edge,.inr (UScalar.eq_of_val_eq target),.inr (.inl (by rw [source]; exact listed))⟩
        · intro e edge at_x' k listed
          rw [member k]
          exact .inr ⟨e,edge,at_x',.inl listed⟩
        · intro k listed
          rcases (member k).mp listed with
              (((here | ⟨_,parent⟩) | ⟨y,_,n,at_n,_,_,_,there⟩) | ⟨l,_,⟨_,there⟩ | ⟨_,there⟩⟩) |
              ⟨e,edge,_,there | there | there⟩
          · exact .inl ⟨x.val,by rw [own]; exact here⟩
          · exact .inl ⟨_,parent⟩
          · exact .inl ⟨y,by simpa [nodeDeps,at_n] using there⟩
          · exact .inl ⟨_,there⟩
          · exact .inl ⟨_,there⟩
          · exact .inr ⟨e,edge,there⟩
          · exact .inl ⟨_,there⟩
          · exact .inl ⟨_,there⟩

/-- A difference says the two nodes differ, in either order. -/
def Differ (F : forest.Forest) (a b : Usize) : Prop :=
  ∃ d ∈ F.distinct.val, (d.left = a ∧ d.right = b) ∨ (d.left = b ∧ d.right = a)

theorem differ_correct (F : forest.Forest) (a b index : Usize) :
    forest.differ F a b index = .ok (decide (∃ d ∈ F.distinct.val.drop index.val,
      (d.left = a ∧ d.right = b) ∨ (d.left = b ∧ d.right = a))) := by
  rw [forest.differ]
  by_cases more : index.val < F.distinct.val.length
  · have lookup : F.distinct.index_usize index = .ok F.distinct.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : F.distinct.val.drop index.val = F.distinct.val[index.val] :: F.distinct.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := differ_correct F a b next
    rw [nextIndex] at rest
    obtain ⟨d,dIs⟩ : ∃ d, F.distinct.val[index.val] = d := ⟨_,rfl⟩
    rw [dIs] at lookup split
    rw [split]
    have hereRun : (if d.left = a then (ok (decide (d.right = b)) : Result Bool) else if d.left = b then
        ok (decide (d.right = a)) else ok false) =
        .ok (decide ((d.left = a ∧ d.right = b) ∨ (d.left = b ∧ d.right = a))) := by
      by_cases one : d.left = a
      · rw [if_pos one]
        congr 1
        apply decide_eq_decide.mpr
        constructor
        · intro two
          exact .inl ⟨one,two⟩
        · rintro (⟨_,two⟩ | ⟨three,four⟩)
          · exact two
          · rw [four,← one]
            exact three
      · by_cases three : d.left = b
        · rw [if_neg one,if_pos three]
          congr 1
          apply decide_eq_decide.mpr
          constructor
          · intro four
            exact .inr ⟨three,four⟩
          · rintro (⟨bad,_⟩ | ⟨_,four⟩)
            · exact absurd bad one
            · exact four
        · rw [if_neg one,if_neg three]
          congr 1
          symm
          apply decide_eq_false
          rintro (⟨bad,_⟩ | ⟨bad,_⟩)
          · exact one bad
          · exact three bad
    by_cases found : (d.left = a ∧ d.right = b) ∨ (d.left = b ∧ d.right = a)
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,hereRun,found,decide_true]
      congr 1
      symm
      rw [decide_eq_true_iff]
      exact ⟨d,List.mem_cons_self ..,found⟩
    · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
        bind_ok,hereRun,found,decide_false,Bool.false_eq_true,advance,rest]
      congr 1
      rw [decide_eq_decide]
      simp only [List.mem_cons,exists_eq_or_imp,found,false_or]
  · have empty : F.distinct.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,empty]
termination_by F.distinct.val.length - index.val
decreasing_by omega

theorem differences_deps_correct (F : forest.Forest) (chosen : alloc.vec.Vec Usize) (index : Usize)
    (out : alloc.vec.Vec Usize) :
    ∃ r, forest.differences_deps F chosen index out = .ok r ∧ ∀ out', r = some out' →
      ∀ k, k ∈ out'.val ↔ k ∈ out.val ∨ ∃ d ∈ F.distinct.val.drop index.val, d.left ∈ chosen.val ∧
        d.right ∈ chosen.val ∧ k ∈ d.deps.val := by
  rw [forest.differences_deps]
  by_cases more : index.val < F.distinct.val.length
  · have lookup : F.distinct.index_usize index = .ok F.distinct.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : F.distinct.val.drop index.val = F.distinct.val[index.val] :: F.distinct.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨d,dIs⟩ : ∃ d, F.distinct.val[index.val] = d := ⟨_,rfl⟩
    rw [dIs] at lookup split
    by_cases inside : d.left ∈ chosen.val ∧ d.right ∈ chosen.val
    · obtain ⟨joined,joinRun,joinSpec⟩ := join_from_correct d.deps 0#usize out
      cases joined with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,contains_correct,inside.1,inside.2,joinRun]
      | some out1 =>
        obtain ⟨r,run,spec⟩ := differences_deps_correct F chosen next out1
        refine ⟨r,?_,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,contains_correct,inside.1,inside.2,joinRun,
            advance,run]
        · intro out' same k
          rw [spec out' same k,joinSpec out1 rfl k,split,nextIndex]
          simp only [show (0#usize).val = 0 from rfl,List.drop_zero,List.mem_cons,exists_eq_or_imp,inside.1,
            inside.2,true_and]
          tauto
    · obtain ⟨r,run,spec⟩ := differences_deps_correct F chosen next out
      refine ⟨r,?_,?_⟩
      · by_cases one : d.left ∈ chosen.val
        · have two : d.right ∉ chosen.val := fun two => inside ⟨one,two⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,contains_correct,one,two,advance,run]
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,contains_correct,one,advance,run]
      · intro out' same k
        rw [spec out' same k,split,nextIndex]
        simp only [List.mem_cons,exists_eq_or_imp]
        constructor
        · rintro (old | later)
          · exact .inl old
          · exact .inr (.inr later)
        · rintro (old | ⟨one,two,_⟩ | later)
          · exact .inl old
          · exact absurd ⟨one,two⟩ inside
          · exact .inr later
  · have empty : F.distinct.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same k
    cases same
    simp [empty]
termination_by F.distinct.val.length - index.val
decreasing_by all_goals omega

/-- The pairs among the chosen nodes that are not known to differ: positions
    `i < j` with `first ≤ i`. -/
def PairAt (F : forest.Forest) (chosen : List Usize) (first : Nat) (p : forest.Pair) : Prop :=
  ∃ i j, ∃ (hi : i < chosen.length) (hj : j < chosen.length), first ≤ i ∧ i < j ∧
    p.first = chosen[i] ∧ p.second = chosen[j] ∧ ¬ Differ F chosen[i] chosen[j]

theorem pairs_with_correct (F : forest.Forest) (chosen : alloc.vec.Vec Usize) (first second : Usize)
    (out : alloc.vec.Vec forest.Pair) :
    ∃ r, forest.pairs_with F chosen first second out = .ok r ∧ ∀ out', r = some out' →
      ∀ p, p ∈ out'.val ↔ p ∈ out.val ∨ ∃ j, ∃ (hi : first.val < chosen.val.length)
        (hj : j < chosen.val.length), second.val ≤ j ∧ p.first = chosen.val[first.val] ∧ p.second = chosen.val[j] ∧
        ¬ Differ F chosen.val[first.val] chosen.val[j] := by
  rw [forest.pairs_with]
  by_cases one : first.val < chosen.val.length
  · by_cases more : second.val < chosen.val.length
    · have lookupOne : chosen.index_usize first = .ok chosen.val[first.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem one]
      have lookupTwo : chosen.index_usize second = .ok chosen.val[second.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := second) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = second.val+1 := by simpa using nextValue
      have differRun := differ_correct F chosen.val[first.val] chosen.val[second.val] 0#usize
      simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at differRun
      have step : ∀ j, second.val ≤ j ↔ j = second.val ∨ next.val ≤ j := by intro j; omega
      by_cases differs : Differ F chosen.val[first.val] chosen.val[second.val]
      · obtain ⟨r,run,spec⟩ := pairs_with_correct F chosen first next out
        refine ⟨r,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookupOne,lookupTwo,bind_ok,differRun]
          rw [decide_eq_true (show ∃ d ∈ F.distinct.val, (d.left = chosen.val[first.val] ∧
            d.right = chosen.val[second.val]) ∨ (d.left = chosen.val[second.val] ∧ d.right = chosen.val[first.val])
            from differs)]
          simp [advance,run]
        · intro out' same p
          rw [spec out' same p]
          constructor
          · rintro (old | ⟨j,hi,hj,later,firstIs,secondIs,notDiffer⟩)
            · exact .inl old
            · exact .inr ⟨j,hi,hj,by omega,firstIs,secondIs,notDiffer⟩
          · rintro (old | ⟨j,hi,hj,from',firstIs,secondIs,notDiffer⟩)
            · exact .inl old
            · rcases (step j).mp from' with rfl | later
              · exact absurd differs notDiffer
              · exact .inr ⟨j,hi,hj,later,firstIs,secondIs,notDiffer⟩
      · by_cases room : out.val.length < Usize.max
        · obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec out (⟨chosen.val[first.val],chosen.val[second.val]⟩ : forest.Pair) room)
          obtain ⟨r,run,spec⟩ := pairs_with_correct F chosen first next out1
          refine ⟨r,?_,?_⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookupOne,lookupTwo,bind_ok,differRun]
            rw [decide_eq_false (show ¬ ∃ d ∈ F.distinct.val, (d.left = chosen.val[first.val] ∧
              d.right = chosen.val[second.val]) ∨ (d.left = chosen.val[second.val] ∧ d.right = chosen.val[first.val])
              from differs)]
            simp [usize_max_val,room,push,advance,run]
          · intro out' same p
            rw [spec out' same p,contents]
            simp only [List.mem_append,List.mem_singleton]
            constructor
            · rintro ((old | rfl) | ⟨j,hi,hj,later,firstIs,secondIs,notDiffer⟩)
              · exact .inl old
              · exact .inr ⟨second.val,one,more,le_refl _,rfl,rfl,differs⟩
              · exact .inr ⟨j,hi,hj,by omega,firstIs,secondIs,notDiffer⟩
            · rintro (old | ⟨j,hi,hj,from',firstIs,secondIs,notDiffer⟩)
              · exact .inl (.inl old)
              · rcases (step j).mp from' with rfl | later
                · refine .inl (.inr ?_)
                  cases p
                  simp only at firstIs secondIs ⊢
                  rw [firstIs,secondIs]
                · exact .inr ⟨j,hi,hj,later,firstIs,secondIs,notDiffer⟩
        · refine ⟨none,?_,by simp⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,more,↓reduceIte,alloc.vec.Vec.index_slice_index,
            lookupOne,lookupTwo,bind_ok,differRun]
          rw [decide_eq_false (show ¬ ∃ d ∈ F.distinct.val, (d.left = chosen.val[first.val] ∧
            d.right = chosen.val[second.val]) ∨ (d.left = chosen.val[second.val] ∧ d.right = chosen.val[first.val])
            from differs)]
          simp [usize_max_val,room]
    · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,more],?_⟩
      intro out' same p
      cases same
      constructor
      · exact .inl
      · rintro (old | ⟨j,_,hj,from',_⟩)
        · exact old
        · omega
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one],?_⟩
    intro out' same p
    cases same
    constructor
    · exact .inl
    · rintro (old | ⟨j,hi,_⟩)
      · exact old
      · exact absurd hi one
termination_by chosen.val.length - second.val
decreasing_by all_goals omega

theorem pairs_from_correct (F : forest.Forest) (chosen : alloc.vec.Vec Usize) (first : Usize)
    (out : alloc.vec.Vec forest.Pair) :
    ∃ r, forest.pairs_from F chosen first out = .ok r ∧ ∀ out', r = some out' →
      ∀ p, p ∈ out'.val ↔ p ∈ out.val ∨ PairAt F chosen.val first.val p := by
  rw [forest.pairs_from]
  by_cases more : first.val < chosen.val.length
  · obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := first) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = first.val+1 := by simpa using nextValue
    obtain ⟨one,oneRun,oneSpec⟩ := pairs_with_correct F chosen first next out
    cases one with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,advance,oneRun]
    | some out1 =>
      obtain ⟨r,run,spec⟩ := pairs_from_correct F chosen next out1
      refine ⟨r,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,advance,oneRun,run],?_⟩
      intro out' same p
      rw [spec out' same p,oneSpec out1 rfl p,nextIndex]
      constructor
      · rintro ((old | ⟨j,hi,hj,low,firstIs,secondIs,notDiffer⟩) | ⟨i,j,hi,hj,low,less,firstIs,secondIs,notDiffer⟩)
        · exact .inl old
        · exact .inr ⟨first.val,j,hi,hj,le_refl _,by omega,firstIs,secondIs,notDiffer⟩
        · exact .inr ⟨i,j,hi,hj,by omega,less,firstIs,secondIs,notDiffer⟩
      · rintro (old | ⟨i,j,hi,hj,low,less,firstIs,secondIs,notDiffer⟩)
        · exact .inl (.inl old)
        · by_cases here : i = first.val
          · subst here
            exact .inl (.inr ⟨j,hi,hj,by omega,firstIs,secondIs,notDiffer⟩)
          · exact .inr ⟨i,j,hi,hj,by omega,less,firstIs,secondIs,notDiffer⟩
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same p
    cases same
    constructor
    · exact .inl
    · rintro (old | ⟨i,j,hi,_,low,_⟩)
      · exact old
      · omega
termination_by chosen.val.length - first.val
decreasing_by all_goals omega

theorem first_nodes_correct (list : alloc.vec.Vec Usize) (count index : Usize) (out : alloc.vec.Vec Usize)
    (fits : out.val.length ≤ count.val) :
    ∃ out', forest.first_nodes list count index out = .ok out' ∧
      out'.val = out.val ++ (list.val.drop index.val).take (count.val - out.val.length) := by
  rw [forest.first_nodes]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases room : out.val.length < count.val
    · have pushRoom : out.val.length < Usize.max := by have := count.hBounds; scalar_tac
      obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out list.val[index.val] pushRoom)
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val+1 := by simpa using nextValue
      obtain ⟨out',run,value⟩ := first_nodes_correct list count next out1 (by rw [contents]; simp; omega)
      refine ⟨out',by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,room,lookup,push,advance,run],?_⟩
      rw [value,contents,nextIndex,split]
      simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append]
      congr 1
      rw [show count.val - out.val.length = (count.val - (out.val.length + 1)) + 1 by omega,List.take_succ_cons]
    · refine ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,room],?_⟩
      simp [show count.val - out.val.length = 0 by omega]
  · refine ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    simp [List.drop_eq_nil_iff.mpr (show list.val.length ≤ index.val by omega)]
termination_by list.val.length - index.val
decreasing_by omega

/-- Which of a pair of neighbours of `x` is merged into which: a tree node into a
    named node, a child into the parent of `x`, the second sibling into the
    first, the second named node into the first. -/
def orientOf (F : forest.Forest) (x : Usize) (pair : forest.Pair) : Usize × Usize :=
  match F.nodes.val[pair.first.val]?, F.nodes.val[pair.second.val]?, F.nodes.val[x.val]? with
  | some a, some b, some n =>
    if a.tree = true then
      if b.tree = true then
        if n.tree = true ∧ n.parent = pair.first then (pair.second,pair.first) else (pair.first,pair.second)
      else (pair.first,pair.second)
    else (pair.second,pair.first)
  | _, _, _ => (pair.second,pair.first)

theorem orient_correct (F : forest.Forest) (x : Usize) (pair : forest.Pair) :
    forest.orient F x pair = .ok (orientOf F x pair) := by
  rw [forest.orient]
  by_cases one : pair.first.val < F.nodes.val.length
  · by_cases two : pair.second.val < F.nodes.val.length
    · by_cases three : x.val < F.nodes.val.length
      · have l1 : F.nodes.index_usize pair.first = .ok F.nodes.val[pair.first.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem one]
        have l2 : F.nodes.index_usize pair.second = .ok F.nodes.val[pair.second.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem two]
        have l3 : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem three]
        simp only [orientOf,List.getElem?_eq_getElem one,List.getElem?_eq_getElem two,List.getElem?_eq_getElem three]
        by_cases a : F.nodes.val[pair.first.val].tree = true
        · by_cases b : F.nodes.val[pair.second.val].tree = true
          · by_cases c : F.nodes.val[x.val].tree = true
            · by_cases d : F.nodes.val[x.val].parent = pair.first
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,two,three,l1,l2,l3,a,b,c,d]
              · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,two,three,l1,l2,l3,a,b,c,d]
            · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,two,three,l1,l2,l3,a,b,c]
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,two,three,l1,l2,a,b]
        · by_cases b : F.nodes.val[pair.second.val].tree = true <;>
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,two,three,l1,l2,a,b]
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,two,three,orientOf,List.getElem?_eq_getElem one,
          List.getElem?_eq_getElem two,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ x.val by omega)]
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,two,orientOf,List.getElem?_eq_getElem one,
        List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ pair.second.val by omega)]
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,one,orientOf,
      List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ pair.first.val by omega)]

theorem add_roles_correct (list : alloc.vec.Vec ObjectPropertyExpression) (invert : Bool) (index : Usize)
    (out : alloc.vec.Vec ObjectPropertyExpression) :
    ∃ r, forest.add_roles list invert index out = .ok r ∧ ∀ out', r = some out' →
      out'.val = out.val ++ (list.val.drop index.val).map (fun s => if invert then inv s else s) := by
  rw [forest.add_roles]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases room : out.val.length < Usize.max
    · obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out (if invert then inv list.val[index.val] else list.val[index.val]) room)
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val+1 := by simpa using nextValue
      obtain ⟨r,run,spec⟩ := add_roles_correct list invert next out1
      refine ⟨r,?_,?_⟩
      · cases invert with
        | true =>
          simp only [↓reduceIte] at push
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,inverse_correct,push,advance,run]
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte] at push
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,copy_role_identity,push,advance,
            run]
      · intro out' same
        rw [spec out' same,contents,nextIndex,split]
        simp only [List.map_cons,List.append_assoc,List.singleton_append]
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    simp [List.drop_eq_nil_iff.mpr (show list.val.length ≤ index.val by omega)]
termination_by list.val.length - index.val
decreasing_by omega

/-- A merge into the parent of `x`: `x` gets the inverses of the roles of
    `source` and depends on `deps`. -/
theorem upward_correct (F : forest.Forest) (x source : Usize) (deps : alloc.vec.Vec Usize) :
    ∃ r, forest.upward F x source deps = .ok r ∧ ∀ F', r = some F' →
      ∃ (xIn : x.val < F.nodes.val.length) (sourceIn : source.val < F.nodes.val.length)
        (roles : alloc.vec.Vec ObjectPropertyExpression) (joined : alloc.vec.Vec Usize),
        roles.val = F.nodes.val[x.val].roles.val ++ F.nodes.val[source.val].roles.val.map inv ∧
        (∀ k, k ∈ joined.val ↔ k ∈ F.nodes.val[x.val].deps.val ∨ k ∈ deps.val) ∧
        F' = { F with nodes := (F.nodes.set x
          ⟨F.nodes.val[x.val].label,F.nodes.val[x.val].parent,roles,F.nodes.val[x.val].seed,
            F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩) } := by
  rw [forest.upward]
  by_cases xIn : x.val < F.nodes.val.length
  · by_cases sourceIn : source.val < F.nodes.val.length
    · have lookupX : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem xIn]
      have lookupS : F.nodes.index_usize source = .ok F.nodes.val[source.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem sourceIn]
      have start := copy_roles_correct F.nodes.val[x.val].roles 0#usize (alloc.vec.Vec.new ObjectPropertyExpression)
        (by simp) (by simp)
      obtain ⟨added,addedRun,addedSpec⟩ := add_roles_correct F.nodes.val[source.val].roles true 0#usize
        F.nodes.val[x.val].roles
      cases added with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,sourceIn,lookupX,lookupS,start,addedRun]
      | some roles =>
        obtain ⟨joinResult,joinRun,joinSpec⟩ := join_correct F.nodes.val[x.val].deps deps
        cases joinResult with
        | none =>
          refine ⟨none,?_,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,sourceIn,lookupX,lookupS,start,addedRun,joinRun]
        | some joined =>
          let n := F.nodes.val[x.val]
          refine ⟨some { F with nodes := (F.nodes.set x ⟨n.label,n.parent,roles,n.seed,n.tree,n.active,n.done,
            joined⟩) },?_,?_⟩
          · have setLookup : (F.nodes.set x ⟨n.label,n.parent,roles,n.seed,n.tree,n.active,n.done,n.deps⟩).index_usize x =
                .ok ⟨n.label,n.parent,roles,n.seed,n.tree,n.active,n.done,n.deps⟩ := by
              simp [alloc.vec.Vec.index_usize,alloc.vec.Vec.set_val_eq,xIn]
            have twice : (F.nodes.set x ⟨n.label,n.parent,roles,n.seed,n.tree,n.active,n.done,n.deps⟩).set x
                ⟨n.label,n.parent,roles,n.seed,n.tree,n.active,n.done,joined⟩ =
                F.nodes.set x ⟨n.label,n.parent,roles,n.seed,n.tree,n.active,n.done,joined⟩ := by
              apply (alloc.vec.Vec.eq_iff _ _).mpr
              simp [alloc.vec.Vec.set_val_eq]
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,sourceIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
              lookupX,lookupS,bind_ok,start,addedRun,joinRun,alloc.vec.Vec.index_mut_slice_index,
              alloc.vec.Vec.index_mut_usize]
            simp [n,setLookup,twice]
          · intro F' same
            cases same
            refine ⟨xIn,sourceIn,roles,joined,?_,joinSpec joined rfl,rfl⟩
            rw [addedSpec roles rfl]
            simp
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn,sourceIn]
  · refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,xIn]

/-- A merge into a sibling: `into` gets the roles of `source`. -/
theorem sideways_correct (F : forest.Forest) (source into : Usize) :
    ∃ r, forest.sideways F source into = .ok r ∧ ∀ F', r = some F' →
      ∃ (sourceIn : source.val < F.nodes.val.length) (intoIn : into.val < F.nodes.val.length)
        (roles : alloc.vec.Vec ObjectPropertyExpression),
        roles.val = F.nodes.val[into.val].roles.val ++ F.nodes.val[source.val].roles.val ∧
        F' = { F with nodes := (F.nodes.set into
          ⟨F.nodes.val[into.val].label,F.nodes.val[into.val].parent,roles,F.nodes.val[into.val].seed,
            F.nodes.val[into.val].tree,F.nodes.val[into.val].active,F.nodes.val[into.val].done,
            F.nodes.val[into.val].deps⟩) } := by
  rw [forest.sideways]
  by_cases sourceIn : source.val < F.nodes.val.length
  · by_cases intoIn : into.val < F.nodes.val.length
    · have lookupS : F.nodes.index_usize source = .ok F.nodes.val[source.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem sourceIn]
      have lookupI : F.nodes.index_usize into = .ok F.nodes.val[into.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem intoIn]
      have start := copy_roles_correct F.nodes.val[into.val].roles 0#usize
        (alloc.vec.Vec.new ObjectPropertyExpression) (by simp) (by simp)
      obtain ⟨added,addedRun,addedSpec⟩ := add_roles_correct F.nodes.val[source.val].roles false 0#usize
        F.nodes.val[into.val].roles
      cases added with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,intoIn,lookupS,lookupI,start,addedRun]
      | some roles =>
        let n := F.nodes.val[into.val]
        refine ⟨some { F with nodes := (F.nodes.set into ⟨n.label,n.parent,roles,n.seed,n.tree,n.active,n.done,
          n.deps⟩) },?_,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,intoIn,lookupS,lookupI,start,addedRun,
            alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize,n]
        · intro F' same
          cases same
          refine ⟨sourceIn,intoIn,roles,?_,rfl⟩
          rw [addedSpec roles rfl]
          simp
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,intoIn]
  · refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn]

/-- An added edge from `x` to `into` along `role`, depending on `deps`. -/
def edgeOf (x into : Usize) (deps : alloc.vec.Vec Usize) (role : ObjectPropertyExpression) : forest.Edge :=
  ⟨role,x,into,deps⟩

theorem add_edges_correct (list : alloc.vec.Vec ObjectPropertyExpression) (x into : Usize)
    (deps : alloc.vec.Vec Usize) (index : Usize) (out : alloc.vec.Vec forest.Edge) :
    ∃ r, forest.add_edges list x into deps index out = .ok r ∧ ∀ out', r = some out' →
      out'.val = out.val ++ (list.val.drop index.val).map (edgeOf x into deps) := by
  rw [forest.add_edges]
  by_cases more : index.val < list.val.length
  · have lookup : list.index_usize index = .ok list.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : list.val.drop index.val = list.val[index.val] :: list.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    by_cases room : out.val.length < Usize.max
    · have depsCopy := copy_label_correct deps 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp)
      obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec out (edgeOf x into deps list.val[index.val]) room)
      obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
        (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextIndex : next.val = index.val+1 := by simpa using nextValue
      obtain ⟨r,run,spec⟩ := add_edges_correct list x into deps next out1
      refine ⟨r,?_,?_⟩
      · simp only [edgeOf] at push
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,copy_role_identity,depsCopy,
          push,advance,run]
      · intro out' same
        rw [spec out' same,contents,nextIndex,split]
        simp only [List.map_cons,List.append_assoc,List.singleton_append]
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    simp [List.drop_eq_nil_iff.mpr (show list.val.length ≤ index.val by omega)]
termination_by list.val.length - index.val
decreasing_by omega

/-- A merge of a tree node into a named node: edges from `x` to `into` along every
    role of `source`. -/
theorem linked_correct (F : forest.Forest) (x source into : Usize) (deps : alloc.vec.Vec Usize) :
    ∃ r, forest.linked F x source into deps = .ok r ∧ ∀ F', r = some F' →
      ∃ (sourceIn : source.val < F.nodes.val.length) (edges : alloc.vec.Vec forest.Edge),
        edges.val = F.edges.val ++ F.nodes.val[source.val].roles.val.map (edgeOf x into deps) ∧
        F' = { F with edges := edges } := by
  rw [forest.linked]
  by_cases sourceIn : source.val < F.nodes.val.length
  · have lookup : F.nodes.index_usize source = .ok F.nodes.val[source.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem sourceIn]
    have start := copy_edges_correct F.edges 0#usize (alloc.vec.Vec.new forest.Edge) (by simp) (by simp)
    obtain ⟨added,addedRun,addedSpec⟩ := add_edges_correct F.nodes.val[source.val].roles x into deps 0#usize F.edges
    cases added with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,lookup,start,addedRun]
    | some edges =>
      refine ⟨some { F with edges := edges },?_,?_⟩
      · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,lookup,start,addedRun]
      · intro F' same
        cases same
        exact ⟨sourceIn,edges,by rw [addedSpec edges rfl]; simp,rfl⟩
  · refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn]

/-- The edge from `into` that an added edge `e0` from the tree node `source`
    becomes, also depending on the points `joined`. -/
def CarriedEdge (source into : Usize) (joined : List Usize) (e0 e : forest.Edge) : Prop :=
  e0.from = source ∧ e.from = into ∧ e.to = e0.to ∧ e.role = e0.role ∧
    ∀ k, k ∈ e.deps.val ↔ k ∈ e0.deps.val ∨ k ∈ joined

theorem carried_from_correct (edges : alloc.vec.Vec forest.Edge) (source into : Usize) (deps : alloc.vec.Vec Usize)
    (index : Usize) (out : alloc.vec.Vec forest.Edge) :
    ∃ r, forest.carried_from edges source into deps index out = .ok r ∧ ∀ out', r = some out' →
      (∀ e ∈ out'.val, e ∈ out.val ∨ ∃ e0 ∈ edges.val, CarriedEdge source into deps.val e0 e) ∧
      (∀ e ∈ out.val, e ∈ out'.val) := by
  rw [forest.carried_from]
  by_cases more : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have listed : edges.val[index.val] ∈ edges.val := List.getElem_mem more
    by_cases from_source : edges.val[index.val].from = source
    · obtain ⟨joinResult,joinRun,joinSpec⟩ := join_correct edges.val[index.val].deps deps
      cases joinResult with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,from_source,joinRun]
      | some joined =>
        have joinedIs := joinSpec joined rfl
        by_cases room : out.val.length < Usize.max
        · let carriedEdge : forest.Edge := ⟨edges.val[index.val].role,into,edges.val[index.val].to,joined⟩
          obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out carriedEdge room)
          obtain ⟨r,run,spec⟩ := carried_from_correct edges source into deps next out1
          refine ⟨r,?_,?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,from_source,joinRun,usize_max_val,room,
              copy_role_identity,advance,run,carriedEdge] at push ⊢
            simp [push,run]
          · intro out' same
            obtain ⟨origin,kept⟩ := spec out' same
            refine ⟨?_,fun e member => kept e (by rw [contents]; exact List.mem_append_left _ member)⟩
            intro e member
            rcases origin e member with fromOut1 | carried
            · rw [contents] at fromOut1
              rcases List.mem_append.mp fromOut1 with old | new
              · exact .inl old
              · rw [List.mem_singleton] at new
                subst new
                exact .inr ⟨edges.val[index.val],listed,from_source,rfl,rfl,rfl,joinedIs⟩
            · exact .inr carried
        · refine ⟨none,?_,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,from_source,joinRun,usize_max_val,room]
    · obtain ⟨r,run,spec⟩ := carried_from_correct edges source into deps next out
      refine ⟨r,?_,spec⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,from_source,advance,run]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    exact ⟨fun e member => .inl member,fun e member => member⟩
termination_by edges.val.length - index.val
decreasing_by all_goals scalar_tac

/-- Carrying the added edges of the tree node `source` over to `into`: every old
    edge stays, and every new edge is the carried copy of an old one. -/
theorem carried_correct (F : forest.Forest) (source into : Usize) (deps : alloc.vec.Vec Usize) :
    ∃ r, forest.carried F source into deps = .ok r ∧ ∀ F', r = some F' →
      ∃ edges : alloc.vec.Vec forest.Edge, F' = { F with edges := edges } ∧ (∀ e ∈ F.edges.val, e ∈ edges.val) ∧
        ∀ e ∈ edges.val, e ∈ F.edges.val ∨ ∃ e0 ∈ F.edges.val, CarriedEdge source into deps.val e0 e := by
  have start := copy_edges_correct F.edges 0#usize (alloc.vec.Vec.new forest.Edge) (by simp) (by simp)
  obtain ⟨r,run,spec⟩ := carried_from_correct F.edges source into deps 0#usize F.edges
  rw [forest.carried]
  cases r with
  | none => exact ⟨none,by simp [start,run],by simp⟩
  | some edges =>
    refine ⟨some { F with edges := edges },by simp [start,run],?_⟩
    intro F' same
    cases same
    obtain ⟨origin,kept⟩ := spec edges rfl
    exact ⟨edges,rfl,kept,origin⟩

theorem at_node_correct (edge : forest.Edge) (node : Usize) :
    forest.at_node edge node = .ok (decide (edge.from = node ∨ edge.to = node)) := by
  rw [forest.at_node]
  by_cases first : edge.from = node <;> simp [first]

/-- The edge `e0` with its ends at the named node `source` moved to `into`; an
    edge with such an end then also depends on `joined`, any other stays. -/
def RelinkedEdge (source into : Usize) (joined : List Usize) (e0 e : forest.Edge) : Prop :=
  e.role = e0.role ∧ e.from = (if e0.from = source then into else e0.from) ∧
    e.to = (if e0.to = source then into else e0.to) ∧
    ((e0.from = source ∨ e0.to = source) → ∀ k, k ∈ e.deps.val ↔ k ∈ e0.deps.val ∨ k ∈ joined) ∧
    (¬ (e0.from = source ∨ e0.to = source) → e.deps = e0.deps)

theorem relink_correct (edge : forest.Edge) (source into : Usize) (deps : alloc.vec.Vec Usize) :
    ∃ r, forest.relink edge source into deps = .ok r ∧ ∀ e, r = some e → RelinkedEdge source into deps.val edge e := by
  rw [forest.relink]
  have copied := copy_label_correct edge.deps 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp)
  by_cases hit : edge.from = source ∨ edge.to = source
  · obtain ⟨joinResult,joinRun,joinSpec⟩ := join_correct edge.deps deps
    cases joinResult with
    | none =>
      refine ⟨none,?_,by simp⟩
      by_cases first : edge.from = source <;> by_cases second : edge.to = source <;>
        simp_all [at_node_correct]
    | some depends =>
      refine ⟨some ⟨edge.role,if edge.from = source then into else edge.from,
        if edge.to = source then into else edge.to,depends⟩,?_,?_⟩
      · by_cases first : edge.from = source <;> by_cases second : edge.to = source <;>
          simp_all [at_node_correct,copy_role_identity]
      · intro e same
        cases same
        exact ⟨rfl,rfl,rfl,fun _ => joinSpec depends rfl,fun miss => absurd hit miss⟩
  · have first : ¬ edge.from = source := fun same => hit (.inl same)
    have second : ¬ edge.to = source := fun same => hit (.inr same)
    refine ⟨some ⟨edge.role,edge.from,edge.to,edge.deps⟩,?_,?_⟩
    · simp [first,second,at_node_correct,copied,copy_role_identity]
    · intro e same
      cases same
      exact ⟨rfl,by simp [first],by simp [second],fun found => absurd found hit,fun _ => rfl⟩

/-- Relinking the edges from the named node `source` to `into`: every new edge
    is an old one relinked. -/
theorem relinked_correct (edges : alloc.vec.Vec forest.Edge) (source into : Usize) (deps : alloc.vec.Vec Usize)
    (index : Usize) (out : alloc.vec.Vec forest.Edge) :
    ∃ r, forest.relinked edges source into deps index out = .ok r ∧ ∀ out', r = some out' →
      ∀ e ∈ out'.val, e ∈ out.val ∨ ∃ e0 ∈ edges.val, RelinkedEdge source into deps.val e0 e := by
  rw [forest.relinked]
  by_cases more : index.val < edges.val.length
  · have lookup : edges.index_usize index = .ok edges.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have listed : edges.val[index.val] ∈ edges.val := List.getElem_mem more
    obtain ⟨relinkResult,relinkRun,relinkSpec⟩ := relink_correct edges.val[index.val] source into deps
    cases relinkResult with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,relinkRun]
    | some edge =>
      by_cases room : out.val.length < Usize.max
      · obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out edge room)
        obtain ⟨r,run,spec⟩ := relinked_correct edges source into deps next out1
        refine ⟨r,?_,?_⟩
        · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,relinkRun,usize_max_val,room,advance,run]
            at push ⊢
          simp [push,run]
        · intro out' same e member
          rcases spec out' same e member with fromOut1 | old
          · rw [contents] at fromOut1
            rcases List.mem_append.mp fromOut1 with kept | new
            · exact .inl kept
            · rw [List.mem_singleton] at new
              subst new
              exact .inr ⟨_,listed,relinkSpec _ rfl⟩
          · exact .inr old
      · refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,relinkRun,usize_max_val,room]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    exact fun e member => .inl member
termination_by edges.val.length - index.val
decreasing_by all_goals scalar_tac

theorem renamed_correct (same : alloc.vec.Vec Usize) (source into index : Usize) (out : alloc.vec.Vec Usize)
    (aligned : out.val.length = index.val) (inside : index.val ≤ same.val.length) :
    ∃ out', forest.renamed same source into index out = .ok out' ∧
      out'.val = out.val ++ (same.val.drop index.val).map (fun b => if b = source then into else b) := by
  rw [forest.renamed]
  by_cases more : index.val < same.val.length
  · have lookup : same.index_usize index = .ok same.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : same.val.drop index.val = same.val[index.val] :: same.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    have room : out.val.length < Usize.max := by have := same.property; scalar_tac
    obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out (if same.val[index.val] = source then into else same.val[index.val]) room)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨out',run,value⟩ := renamed_correct same source into next out1
      (by rw [contents]; simp; omega) (by omega)
    refine ⟨out',?_,?_⟩
    · by_cases here : same.val[index.val] = source
      · simp only [here,↓reduceIte] at push
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,here,push,advance,run]
      · simp only [here,↓reduceIte] at push
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,here,push,advance,run]
    · rw [value,contents,nextIndex,split]
      simp only [List.map_cons,List.append_assoc,List.singleton_append]
  · refine ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    simp [List.drop_eq_nil_iff.mpr (show same.val.length ≤ index.val by omega)]
termination_by same.val.length - index.val
decreasing_by omega

/-- The differences `into` inherits from `source`: from a difference between
    `source` and another node, the same difference for `into`. -/
def Inherited (source into : Usize) (deps : List Usize) (d d' : forest.Distinct) : Prop :=
  d'.left = into ∧ ((d.left = source ∧ d'.right = d.right) ∨ (d.right = source ∧ d'.right = d.left)) ∧
    ∀ k, k ∈ d'.deps.val ↔ k ∈ d.deps.val ∨ k ∈ deps

theorem inherit_correct (distinct : alloc.vec.Vec forest.Distinct) (source into : Usize) (deps : alloc.vec.Vec Usize)
    (index : Usize) (out : alloc.vec.Vec forest.Distinct) :
    ∃ r, forest.inherit distinct source into deps index out = .ok r ∧ ∀ out', r = some out' →
      (∀ d ∈ out.val, d ∈ out'.val) ∧
      ∀ d' ∈ out'.val, d' ∈ out.val ∨ ∃ d ∈ distinct.val.drop index.val, Inherited source into deps.val d d' := by
  rw [forest.inherit]
  by_cases more : index.val < distinct.val.length
  · have lookup : distinct.index_usize index = .ok distinct.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have split : distinct.val.drop index.val = distinct.val[index.val] :: distinct.val.drop (index.val+1) :=
      List.drop_eq_getElem_cons more
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨d,dIs⟩ : ∃ d, distinct.val[index.val] = d := ⟨_,rfl⟩
    rw [dIs] at lookup split
    have otherRun : (if d.left = source then (ok (some d.right) : Result (Option Usize)) else if d.right = source then
        ok (some d.left) else ok none) =
        .ok (if d.left = source then some d.right else if d.right = source then some d.left else none) := by
      by_cases one : d.left = source <;> by_cases two : d.right = source <;> simp [one,two]
    obtain ⟨other,otherIs⟩ : ∃ other, (if d.left = source then some d.right else
        if d.right = source then some d.left else none) = other := ⟨_,rfl⟩
    cases other with
    | none =>
      obtain ⟨r,run,spec⟩ := inherit_correct distinct source into deps next out
      refine ⟨r,?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,otherRun,otherIs,advance,run]
      · intro out' same
        obtain ⟨keeps,origin⟩ := spec out' same
        refine ⟨keeps,fun d' member => ?_⟩
        rcases origin d' member with old | ⟨d0,later,inherited⟩
        · exact .inl old
        · exact .inr ⟨d0,by rw [split]; exact List.mem_cons_of_mem _ (by rw [nextIndex] at later; exact later),
            inherited⟩
    | some other =>
      have otherSpec : (d.left = source ∧ other = d.right) ∨ (d.right = source ∧ other = d.left) := by
        by_cases one : d.left = source
        · simp only [one,↓reduceIte,Option.some.injEq] at otherIs
          exact .inl ⟨one,otherIs.symm⟩
        · by_cases two : d.right = source
          · simp only [one,two,↓reduceIte,Option.some.injEq] at otherIs
            exact .inr ⟨two,otherIs.symm⟩
          · simp [one,two] at otherIs
      obtain ⟨joinResult,joinRun,joinSpec⟩ := join_correct d.deps deps
      cases joinResult with
      | none =>
        refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,otherRun,otherIs,joinRun]
      | some joined =>
        by_cases room : out.val.length < Usize.max
        · obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
            (alloc.vec.Vec.push_spec out (⟨into,other,joined⟩ : forest.Distinct) room)
          obtain ⟨r,run,spec⟩ := inherit_correct distinct source into deps next out1
          refine ⟨r,?_,?_⟩
          · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,otherRun,otherIs,joinRun,usize_max_val,room,
              push,advance,run]
          · intro out' same
            obtain ⟨keeps,origin⟩ := spec out' same
            refine ⟨fun d0 member => keeps d0 (by rw [contents]; exact List.mem_append_left _ member),?_⟩
            intro d' member
            rcases origin d' member with old | ⟨d0,later,inherited⟩
            · rw [contents] at old
              rcases List.mem_append.mp old with old | here
              · exact .inl old
              · simp only [List.mem_singleton] at here
                subst here
                refine .inr ⟨d,by rw [split]; exact List.mem_cons_self ..,rfl,?_,joinSpec joined rfl⟩
                rcases otherSpec with ⟨one,two⟩ | ⟨one,two⟩
                · exact .inl ⟨one,two⟩
                · exact .inr ⟨one,two⟩
            · exact .inr ⟨d0,by rw [split]; exact List.mem_cons_of_mem _ (by rw [nextIndex] at later; exact later),
                inherited⟩
        · refine ⟨none,?_,by simp⟩
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,otherRun,otherIs,joinRun,usize_max_val,room]
  · refine ⟨some out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],?_⟩
    intro out' same
    cases same
    exact ⟨fun d member => member,fun d' member => .inl member⟩
termination_by distinct.val.length - index.val
decreasing_by all_goals omega

private theorem prefix_getElem? {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : Nat} {x : α}
    (at_i : l₁[i]? = some x) : l₂[i]? = some x := by
  obtain ⟨t,rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp at_i).1]
  exact at_i

/-- Whether the node `i` of a list is active; outside the list, yes. -/
def activeAt (nodes : List forest.Node) (i : Nat) : Bool :=
  match nodes[i]? with
  | some n => n.active
  | none => true

/-- A node of the pruned list: inactive when it is a tree node whose earlier
    parent is not active in the pruned list. -/
def prunedNode (pruned : List forest.Node) (i : Nat) (n : forest.Node) : forest.Node :=
  ⟨n.label,n.parent,n.roles,n.seed,n.tree,
    n.active && !(n.tree && decide (n.parent.val < i) && !activeAt pruned n.parent.val),n.done,n.deps⟩

theorem pruned_correct (nodes : alloc.vec.Vec forest.Node) (index : Usize) (out : alloc.vec.Vec forest.Node)
    (aligned : out.val.length = index.val) (inside : index.val ≤ nodes.val.length) :
    ∃ out', forest.pruned nodes index out = .ok out' ∧ out'.val.length = nodes.val.length ∧
      out.val <+: out'.val ∧
      ∀ i (h : i < nodes.val.length), index.val ≤ i → out'.val[i]? = some (prunedNode out'.val i nodes.val[i]) := by
  rw [forest.pruned]
  by_cases more : index.val < nodes.val.length
  · obtain ⟨n,nIs⟩ : ∃ n, nodes.val[index.val] = n := ⟨_,rfl⟩
    have lookup : nodes.index_usize index = .ok n := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more,nIs]
    have room : out.val.length < Usize.max := by have := nodes.property; scalar_tac
    obtain ⟨active,activeIs⟩ : ∃ active : Bool,
        (n.active && !(n.tree && decide (n.parent.val < index.val) && !activeAt out.val n.parent.val)) = active :=
      ⟨_,rfl⟩
    obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out ⟨n.label,n.parent,n.roles,n.seed,n.tree,active,n.done,n.deps⟩ room)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    obtain ⟨out',run,length',prefix',spec⟩ := pruned_correct nodes next out1
      (by rw [contents]; simp; omega) (by omega)
    refine ⟨out',?_,length',?_,?_⟩
    · have copies := And.intro (copy_label_correct n.label 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp))
        (And.intro (copy_roles_correct n.roles 0#usize (alloc.vec.Vec.new ObjectPropertyExpression) (by simp) (by simp))
          (And.intro (copy_label_correct n.done 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp))
            (copy_label_correct n.deps 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp))))
      by_cases tree : n.tree = true
      · by_cases parentIn : n.parent.val < out.val.length
        · have parentLookup : out.index_usize n.parent = .ok out.val[n.parent.val] := by
            simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem parentIn]
          by_cases parentActive : out.val[n.parent.val].active = true
          · have value : active = n.active := by
              rw [← activeIs]
              simp [tree,activeAt,List.getElem?_eq_getElem parentIn,parentActive]
            rw [value] at push
            simp only [tree] at push
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,tree,parentIn,parentLookup,
              parentActive,copies,push,advance,run]
          · have value : active = false := by
              rw [← activeIs]
              simp [tree,activeAt,List.getElem?_eq_getElem parentIn,parentActive,← aligned,parentIn]
            rw [value] at push
            simp only [tree] at push
            simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,tree,parentIn,parentLookup,
              parentActive,copies,push,advance,run]
        · have value : active = n.active := by
            rw [← activeIs]
            simp [tree,← aligned,parentIn]
          rw [value] at push
          simp only [tree] at push
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,tree,parentIn,copies,push,
            advance,run]
      · have value : active = n.active := by
          rw [← activeIs]
          simp [tree]
        rw [value] at push
        have treeFalse : n.tree = false := by simpa using tree
        simp only [treeFalse] at push
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,usize_max_val,room,lookup,treeFalse,copies,push,advance,run]
    · exact List.IsPrefix.trans (by rw [contents]; exact List.prefix_append _ _) prefix'
    · intro i h low
      by_cases here : i = index.val
      · subst here
        have at_out1 : out1.val[index.val]? = some ⟨n.label,n.parent,n.roles,n.seed,n.tree,active,n.done,n.deps⟩ := by
          rw [contents,List.getElem?_append_right (by omega)]
          simp [aligned]
        rw [prefix_getElem? prefix' at_out1,nIs]
        congr 1
        simp only [prunedNode]
        congr 1
        rw [← activeIs]
        -- The parent's activity among the earlier nodes is the same in the result.
        by_cases parentLow : n.parent.val < index.val
        · have inOut : n.parent.val < out.val.length := by omega
          have at_out : out.val[n.parent.val]? = some out.val[n.parent.val] := List.getElem?_eq_getElem inOut
          have at_out1' : out1.val[n.parent.val]? = some out.val[n.parent.val] := by
            rw [contents,List.getElem?_append_left inOut,at_out]
          have earlier : activeAt out'.val n.parent.val = activeAt out.val n.parent.val := by
            simp [activeAt,at_out,prefix_getElem? prefix' at_out1']
          rw [earlier]
        · simp [parentLow]
      · exact spec i h (by omega)
  · have full : index.val = nodes.val.length := by omega
    refine ⟨out,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by omega,List.prefix_refl _,?_⟩
    intro i h low
    omega
termination_by nodes.val.length - index.val
decreasing_by omega

end Rowl.ForestOps
