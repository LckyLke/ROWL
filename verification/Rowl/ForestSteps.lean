import Rowl.ForestInv

/-!
The steps of the completion forest that change its structure, proved to keep
the invariant, to decrease the measure and to carry models over. Expanding an
existential or minimum restriction of an unblocked node appends its children
with their seed, pairwise different, and marks the restriction as expanded; a
model of the restriction provides different witnesses for the children.
Merging a neighbour `source` of `x` into a neighbour `into` hands the edge of
`source` over to `into`, unless `into` is its tree parent, whose loops the merge
adds instead, gives `into` the differences of `source`, deactivates
`source` with its subtree and makes `into` depend on the points of the merge; a
model that places both on one element models the merged forest with the label
of `source` at `into`. New named nodes for a maximum restriction of a named
node come after the old nodes, pairwise different, with an added edge from the
node and a bound on its counted neighbours; the restriction loses more weight
than they bring, and a model where the node has exactly as many counted
neighbours as new nodes places them there.
-/
namespace Rowl.ForestSteps
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv denote)
open Rowl.Hierarchy (Below Closed Respects transitives below_refl respects_below)
open Rowl.ConceptTable (WellFormed meaning meaning_at rebuild)
open Rowl.CompletionSearch (Holds Complementary)
open Rowl.Completion (Sub copy_label_correct join_correct sum_drop label_le)
open Rowl.ForestSearch
open Rowl.ForestOps
open Rowl.ForestInv
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-! ### Expanding a restriction -/

/-- `F'` expands the restriction `i` of node `x`, which is `nx`: `count` children
    along `role` with seed `filler` and the points of `x`, pairwise different,
    and `i` marked as expanded. -/
structure Created (F F' : forest.Forest) (x i : Usize) (role : ObjectPropertyExpression) (filler : Usize)
    (count : Nat) (nx : forest.Node) : Prop where
  at_x : F.nodes.val[x.val]? = some nx
  length : F'.nodes.val.length = F.nodes.val.length + count
  edges : F'.edges = F.edges
  same : F'.same = F.same
  caps : F'.caps = F.caps
  old : ∀ y, y ≠ x.val → y < F.nodes.val.length → F'.nodes.val[y]? = F.nodes.val[y]?
  here : ∃ done : alloc.vec.Vec Usize, done.val = nx.done.val ++ [i] ∧ F'.nodes.val[x.val]? = some { nx with done := done }
  new : ∃ roles : alloc.vec.Vec ObjectPropertyExpression, roles.val = [role] ∧ ∀ k < count,
    F'.nodes.val[F.nodes.val.length + k]? = some (child x roles filler nx.deps)
  distinct : ∀ d, d ∈ F'.distinct.val ↔ d ∈ F.distinct.val ∨ (F.nodes.val.length ≤ d.left.val ∧
    d.left.val < d.right.val ∧ d.right.val < F.nodes.val.length + count ∧ d.deps = nx.deps)

theorem expanded_correct (entries : alloc.vec.Vec concept_table.Entry) (F : forest.Forest) (x i : Usize) :
    ∃ r, forest.expanded entries F x i = .ok r ∧ ∀ F', r = some F' →
      ∃ e role filler count nx, entries.val[i.val]? = some e ∧ generatorOf e = some (role,count,filler) ∧
        Created F F' x i role filler count.val nx := by
  rw [forest.expanded,generator_of_correct]
  cases at_i : entries.val[i.val]? with
  | none => exact ⟨none,by simp,by simp⟩
  | some e =>
  cases gen : generatorOf e with
  | none => exact ⟨none,by simp [gen],by simp⟩
  | some found =>
  obtain ⟨role,count,filler⟩ := found
  by_cases inside : x.val < F.nodes.val.length
  · have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem inside
    have lookup : F.nodes.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,at_x]
    have depsCopy := copy_label_correct F.nodes.val[x.val].deps 0#usize (alloc.vec.Vec.new Usize) (by simp) (by simp)
    obtain ⟨r1,run1,spec1⟩ := children_correct F x role filler F.nodes.val[x.val].deps count
    cases r1 with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [gen,alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,depsCopy,run1]
    | some F1 =>
    obtain ⟨nodes1,roles,F1Is,rolesIs,nodesIs⟩ := spec1 F1 rfl
    obtain ⟨r2,run2,spec2⟩ := pairwise_correct F1 (alloc.vec.Vec.len F.nodes) F.nodes.val[x.val].deps
    cases r2 with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [gen,alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,depsCopy,run1,run2]
    | some F2 =>
    obtain ⟨distinct2,F2Is,members⟩ := spec2 F2 rfl
    subst F2Is F1Is
    have xIn2 : x.val < nodes1.val.length := by rw [nodesIs]; simp; omega
    have at_x2 : nodes1.val[x.val] = F.nodes.val[x.val] := by
      simp only [nodesIs]
      rw [List.getElem_append_left inside]
    have lookup2 : nodes1.index_usize x = .ok F.nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem xIn2,at_x2]
    by_cases room : F.nodes.val[x.val].done.val.length < Usize.max
    · obtain ⟨done,push,doneIs⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec F.nodes.val[x.val].done i room)
      refine ⟨some { F with nodes := nodes1.set x { F.nodes.val[x.val] with done := done }, distinct := distinct2 },
        ?_,?_⟩
      · simp [gen,alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,depsCopy,run1,run2,lookup2,usize_max_val,
          room,alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize,push]
      · intro F' same
        cases same
        refine ⟨e,role,filler,count,F.nodes.val[x.val],rfl,gen,⟨at_x,?_,rfl,rfl,rfl,?_,?_,?_,?_⟩⟩
        · simp [alloc.vec.Vec.set_val_eq,nodesIs]
        · intro y different yIn
          simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_ne (Ne.symm different),nodesIs,List.getElem?_append_left yIn]
        · refine ⟨done,doneIs,?_⟩
          simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_self xIn2]
        · refine ⟨roles,rolesIs,?_⟩
          intro k kIn
          simp only [alloc.vec.Vec.set_val_eq]
          rw [List.getElem?_set_ne (by omega),nodesIs,List.getElem?_append_right (by omega)]
          simp [kIn]
        · intro d
          rw [members d]
          simp [nodesIs]
    · refine ⟨none,?_,by simp⟩
      simp [gen,alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,depsCopy,run1,run2,lookup2,usize_max_val,room]
  · refine ⟨none,?_,by simp⟩
    simp [gen,alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]

section Created
variable {F F' : forest.Forest} {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize} {count : Nat}
  {nx : forest.Node}

theorem created_x_inside (created : Created F F' x i role filler count nx) : x.val < F.nodes.val.length :=
  (List.getElem?_eq_some_iff.mp created.at_x).1

/-- Every node of the expanded forest is an old node, the expanded node, or a
    new child. -/
theorem created_lookup (created : Created F F' x i role filler count nx) (y : Nat) (n' : forest.Node)
    (at_y : F'.nodes.val[y]? = some n') :
    (y < F.nodes.val.length ∧ y ≠ x.val ∧ F.nodes.val[y]? = some n') ∨
    (y = x.val ∧ ∃ done : alloc.vec.Vec Usize, done.val = nx.done.val ++ [i] ∧ n' = { nx with done := done }) ∨
    (F.nodes.val.length ≤ y ∧ y < F.nodes.val.length + count ∧ ∃ roles : alloc.vec.Vec ObjectPropertyExpression,
      roles.val = [role] ∧ n' = child x roles filler nx.deps) := by
  have yIn : y < F'.nodes.val.length := (List.getElem?_eq_some_iff.mp at_y).1
  rw [created.length] at yIn
  by_cases old : y < F.nodes.val.length
  · by_cases same : y = x.val
    · subst same
      obtain ⟨done,doneIs,here⟩ := created.here
      rw [here] at at_y
      simp only [Option.some.injEq] at at_y
      exact .inr (.inl ⟨rfl,done,doneIs,at_y.symm⟩)
    · rw [created.old y same old] at at_y
      exact .inl ⟨old,same,at_y⟩
  · obtain ⟨roles,rolesIs,new⟩ := created.new
    have := new (y - F.nodes.val.length) (by omega)
    rw [show F.nodes.val.length + (y - F.nodes.val.length) = y by omega,at_y] at this
    simp only [Option.some.injEq] at this
    exact .inr (.inr ⟨by omega,yIn,roles,rolesIs,this⟩)

/-- An old node keeps everything but, at the expanded node, the expanded
    restrictions. -/
theorem created_old (created : Created F F' x i role filler count nx) (y : Nat) (yIn : y < F.nodes.val.length) :
    ∃ n n' : forest.Node, F.nodes.val[y]? = some n ∧ F'.nodes.val[y]? = some n' ∧ n'.label = n.label ∧
      n'.parent = n.parent ∧ n'.roles = n.roles ∧ n'.seed = n.seed ∧ n'.tree = n.tree ∧ n'.active = n.active ∧
      n'.deps = n.deps ∧ (y ≠ x.val → n'.done = n.done) := by
  by_cases same : y = x.val
  · subst same
    obtain ⟨done,_,here⟩ := created.here
    exact ⟨nx,_,created.at_x,here,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun different => absurd rfl different⟩
  · obtain ⟨n,at_y⟩ : ∃ n, F.nodes.val[y]? = some n := ⟨_,List.getElem?_eq_getElem yIn⟩
    exact ⟨n,n,at_y,by rw [created.old y same yIn]; exact at_y,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ => rfl⟩

theorem created_new (created : Created F F' x i role filler count nx) (y : Nat) (low : F.nodes.val.length ≤ y)
    (high : y < F.nodes.val.length + count) : ∃ roles : alloc.vec.Vec ObjectPropertyExpression, roles.val = [role] ∧
      F'.nodes.val[y]? = some (child x roles filler nx.deps) := by
  obtain ⟨roles,rolesIs,new⟩ := created.new
  refine ⟨roles,rolesIs,?_⟩
  have := new (y - F.nodes.val.length) (by omega)
  rwa [show F.nodes.val.length + (y - F.nodes.val.length) = y by omega] at this

theorem created_label (created : Created F F' x i role filler count nx) (y : Nat) :
    labelOf F'.nodes.val y = if y < F.nodes.val.length then labelOf F.nodes.val y else [] := by
  by_cases yIn : y < F.nodes.val.length
  · obtain ⟨n,n',at_y,at_y',label,_⟩ := created_old created y yIn
    rw [if_pos yIn]
    unfold labelOf
    rw [at_y,at_y']
    simp only [label]
  · rw [if_neg yIn]
    unfold labelOf
    by_cases new : y < F.nodes.val.length + count
    · obtain ⟨roles,_,at_y'⟩ := created_new created y (by omega) new
      simp [at_y',child]
    · rw [List.getElem?_eq_none_iff.mpr (by rw [created.length]; omega)]

theorem created_deps (created : Created F F' x i role filler count nx) (y : Nat) :
    nodeDeps F' y = if y < F.nodes.val.length then nodeDeps F y else
      if y < F.nodes.val.length + count then nx.deps.val else [] := by
  by_cases yIn : y < F.nodes.val.length
  · obtain ⟨n,n',at_y,at_y',_,_,_,_,_,_,deps,_⟩ := created_old created y yIn
    rw [if_pos yIn]
    unfold nodeDeps
    rw [at_y,at_y']
    simp only [deps]
  · rw [if_neg yIn]
    unfold nodeDeps
    by_cases new : y < F.nodes.val.length + count
    · obtain ⟨roles,_,at_y'⟩ := created_new created y (by omega) new
      simp [at_y',child,new]
    · rw [if_neg new,List.getElem?_eq_none_iff.mpr (by rw [created.length]; omega)]

theorem created_done (created : Created F F' x i role filler count nx) (y : Nat) (yIn : y < F.nodes.val.length) :
    doneOf F'.nodes.val y = if y = x.val then doneOf F.nodes.val y ++ [i] else doneOf F.nodes.val y := by
  by_cases same : y = x.val
  · subst same
    obtain ⟨done,doneIs,here⟩ := created.here
    simp [doneOf,here,created.at_x,doneIs]
  · obtain ⟨n,n',at_y,at_y',_,_,_,_,_,_,_,done⟩ := created_old created y yIn
    simp [doneOf,at_y,at_y',done same,same]

theorem created_active (created : Created F F' x i role filler count nx) (y : Nat) (yIn : y < F.nodes.val.length) :
    Active F'.nodes.val y ↔ Active F.nodes.val y := by
  obtain ⟨n,n',at_y,at_y',_,_,_,_,_,active,_⟩ := created_old created y yIn
  constructor
  · rintro ⟨m,at_m,act⟩
    rw [at_y'] at at_m
    cases at_m
    exact ⟨n,at_y,by rw [← active]; exact act⟩
  · rintro ⟨m,at_m,act⟩
    rw [at_y] at at_m
    cases at_m
    exact ⟨n',at_y',by rw [active]; exact act⟩

theorem created_named (created : Created F F' x i role filler count nx) (y : Nat) (yIn : y < F.nodes.val.length) :
    Named F'.nodes.val y ↔ Named F.nodes.val y := by
  obtain ⟨n,n',at_y,at_y',_,_,_,_,tree,_⟩ := created_old created y yIn
  constructor
  · rintro ⟨m,at_m,named⟩
    rw [at_y'] at at_m
    cases at_m
    exact ⟨n,at_y,by rw [← tree]; exact named⟩
  · rintro ⟨m,at_m,named⟩
    rw [at_y] at at_m
    cases at_m
    exact ⟨n',at_y',by rw [tree]; exact named⟩

theorem created_namedEnd (created : Created F F' x i role filler count nx) (c y : Nat) (named : NamedEnd F c y) :
    NamedEnd F' c y := by
  rcases named with below | ⟨named,active⟩
  · exact .inl below
  · have yIn := active_inside active
    exact .inr ⟨(created_named created y yIn).mpr named,(created_active created y yIn).mpr active⟩

theorem created_treePath (created : Created F F' x i role filler count nx) :
    ∀ y, y < F.nodes.val.length → treePath F'.nodes.val y = treePath F.nodes.val y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro yIn
    obtain ⟨n,n',at_y,at_y',_,parent,_,_,tree,_⟩ := created_old created y yIn
    rw [treePath.eq_def,treePath.eq_def F.nodes.val,at_y,at_y']
    simp only [tree,parent]
    split
    · split
      · rename_i below
        rw [ih n.parent.val below (by omega)]
      · rfl
    · rfl

theorem created_rep (created : Created F F' x i role filler count nx) (a : Usize) : rep F' a = rep F a := by
  unfold rep
  rw [created.same]

end Created

/-- A restriction that creates neighbours, at an element, has as many different
    witnesses as it asks for. -/
theorem generator_meaning {Object : Type u} {Value : Type v} (entries : List concept_table.Entry)
    (wf : WellFormed entries) (I : Interpretation Object Value) (i : Nat) (e : concept_table.Entry)
    (at_i : entries[i]? = some e) (role : ObjectPropertyExpression) (cnt filler : Usize)
    (gen : generatorOf e = some (role,cnt,filler)) (z : Object) (holds : denote I (meaning entries i) z) :
    Rowl.Owl.AtLeast cnt.val (fun y => objectRelation I role z y ∧ denote I (meaning entries filler.val) y) := by
  rw [meaning_at entries wf i e at_i] at holds
  cases e <;> simp only [generatorOf,reduceCtorEq,Option.some.injEq,Prod.mk.injEq] at gen
  · obtain ⟨rfl,rfl,rfl⟩ := gen
    obtain ⟨y,edge,fillerHolds⟩ := holds
    refine ⟨fun _ => y,?_,fun _ => ⟨edge,fillerHolds⟩⟩
    intro a b _
    apply Fin.ext
    have one : (1#usize).val = 1 := rfl
    have := a.isLt
    have := b.isLt
    omega
  · obtain ⟨rfl,rfl,rfl⟩ := gen
    exact holds

theorem created_done_new {F F' : forest.Forest} {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize}
    {cnt : Nat} {nx : forest.Node} (created : Created F F' x i role filler cnt nx) (y : Nat)
    (low : F.nodes.val.length ≤ y) : doneOf F'.nodes.val y = [] := by
  unfold doneOf
  by_cases new : y < F.nodes.val.length + cnt
  · obtain ⟨roles,_,at_y'⟩ := created_new created y low new
    simp [at_y',child]
  · rw [List.getElem?_eq_none_iff.mpr (by rw [created.length]; omega)]

/-- Expanding a restriction of an active node keeps the invariant. -/
theorem created_inv {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F F' : forest.Forest}
    {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize} {cnt : Nat} {nx : forest.Node}
    (inv : Inv P h count F) (created : Created F F' x i role filler cnt nx) (active : Active F.nodes.val x.val)
    (member : i ∈ labelOf F.nodes.val x.val) (notDone : i ∉ doneOf F.nodes.val x.val)
    (listed : role ∈ roleList P.entries.val) : Inv P h count F' := by
  have xIn := created_x_inside created
  have shape := inv.shape
  have countIn := shape.countIn
  refine ⟨⟨shape.wellFormed,shape.complements,shape.closedTable,shape.closed,shape.simple,?_,?_,?_,?_,?_,?_,
    shape.links,shape.requirements,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · intro y n' at_y'
    rcases created_lookup created y n' at_y' with ⟨_,_,at_y⟩ | ⟨rfl,done,_,rfl⟩ | ⟨low,_,roles,_,rfl⟩
    · exact shape.named y n' at_y
    · exact shape.named x.val nx created.at_x
    · intro below
      exfalso
      omega
  · rw [created.length]
    omega
  · rw [created.same]
    exact shape.sameLength
  · intro b member
    rw [created.same] at member
    obtain ⟨named,act⟩ := shape.reps b member
    have bIn := active_inside act
    exact ⟨(created_named created _ bIn).mpr named,(created_active created _ bIn).mpr act⟩
  · intro y n' at_y' tree
    rcases created_lookup created y n' at_y' with ⟨_,_,at_y⟩ | ⟨rfl,done,_,rfl⟩ | ⟨low,_,roles,_,rfl⟩
    · exact shape.parents y n' at_y tree
    · exact shape.parents x.val nx created.at_x tree
    · simp only [child]
      omega
  · intro y n' at_y' tree act
    rcases created_lookup created y n' at_y' with ⟨yIn,_,at_y⟩ | ⟨rfl,done,_,rfl⟩ | ⟨low,_,roles,_,rfl⟩
    · have parentIn := shape.parents y n' at_y tree
      exact (created_active created _ (by omega)).mpr (shape.activeParents y n' at_y tree act)
    · dsimp only at tree act ⊢
      have parentIn := shape.parents x.val nx created.at_x tree
      exact (created_active created _ (by omega)).mpr (shape.activeParents x.val nx created.at_x tree act)
    · exact (created_active created _ xIn).mpr active
  · intro e member
    rw [created.edges] at member
    obtain ⟨toIn,fromCases⟩ := shape.edges e member
    refine ⟨created_namedEnd created count _ toIn,fromCases.imp (created_namedEnd created count _) ?_⟩
    rintro ⟨n,at_n,tree⟩
    obtain ⟨n0,n',at_n0,at_n',_,_,_,_,tree',_⟩ := created_old created e.from.val
      (List.getElem?_eq_some_iff.mp at_n).1
    rw [at_n] at at_n0
    cases at_n0
    exact ⟨n',at_n',by rw [tree',tree]⟩
  · intro d member
    rw [created.length]
    rcases (created.distinct d).mp member with old | ⟨_,_,high,_⟩
    · have := shape.distinctIn d old
      omega
    · omega
  · intro y j member
    rw [created_label created y] at member
    split at member
    · exact shape.literals y j member
    · cases member
  · intro y j member k listed' e e' at_j at_k
    rw [created_label created y] at member listed'
    by_cases yIn : y < F.nodes.val.length
    · rw [if_pos yIn] at member listed'
      exact shape.clashFree y j member k listed' e e' at_j at_k
    · rw [if_neg yIn] at member
      cases member
  · intro cap member
    rw [created.caps] at member
    rw [created.length]
    have := shape.capsIn cap member
    omega
  · intro y
    rw [created_label created y]
    split
    · exact inv.nodup y
    · exact List.nodup_nil
  · intro y
    by_cases yIn : y < F.nodes.val.length
    · rw [created_done created y yIn]
      split
      · rename_i same
        subst same
        exact List.nodup_append.mpr ⟨inv.doneNodup _,List.nodup_singleton _,by
          intro a listed' b single
          simp only [List.mem_singleton] at single
          subst single
          intro equal; subst equal; exact notDone listed'⟩
      · exact inv.doneNodup y
    · rw [created_done_new created y (by omega)]
      exact List.nodup_nil
  · intro y j listed'
    by_cases yIn : y < F.nodes.val.length
    · rw [created_done created y yIn] at listed'
      rw [created_label created y,if_pos yIn]
      split at listed'
      · rename_i same
        subst same
        rcases List.mem_append.mp listed' with old | new
        · exact inv.doneIn _ j old
        · simp only [List.mem_singleton] at new
          subst new
          exact member
      · exact inv.doneIn y j listed'
    · rw [created_done_new created y (by omega)] at listed'
      cases listed'
  · intro y n' at_y' s sIn
    rcases created_lookup created y n' at_y' with ⟨_,_,at_y⟩ | ⟨rfl,done,_,rfl⟩ | ⟨_,_,roles,rolesIs,rfl⟩
    · exact inv.roles y n' at_y s sIn
    · exact inv.roles x.val nx created.at_x s sIn
    · simp only [child,rolesIs,List.mem_singleton] at sIn
      subst sIn
      exact listed

/-- The points of the expanded forest are those of the forest. -/
theorem created_fresh {F F' : forest.Forest} {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize}
    {cnt : Nat} {nx : forest.Node} (created : Created F F' x i role filler cnt nx) {fresh : Nat}
    (freshF : FreshForest F fresh) : FreshForest F' fresh := by
  have depsX : nodeDeps F x.val = nx.deps.val := by simp [nodeDeps,created.at_x]
  refine ⟨?_,?_,?_,?_⟩
  · intro y k member
    rw [created_deps created y] at member
    split at member
    · exact freshF.1 y k member
    · split at member
      · exact freshF.1 x.val k (by rw [depsX]; exact member)
      · cases member
  · rw [created.edges]
    exact freshF.2.1
  · intro d member k kIn
    rcases (created.distinct d).mp member with old | ⟨_,_,_,depsIs⟩
    · exact freshF.2.2.1 d old k kIn
    · rw [depsIs] at kIn
      exact freshF.1 x.val k (by rw [depsX]; exact kIn)
  · rw [created.caps]
    exact freshF.2.2.2

/-- Expanding a restriction of an active unblocked node decreases the measure:
    the node loses the room of one restriction, worth more than all the new
    children below it. -/
theorem created_measure {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F F' : forest.Forest}
    {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize} {cnt : Nat} {nx : forest.Node}
    (inv : Inv P h count F) (created : Created F F' x i role filler cnt nx) (active : Active F.nodes.val x.val)
    (free : ¬ Blocked F.nodes.val x.val) (member : i ∈ labelOf F.nodes.val x.val)
    (notDone : i ∉ doneOf F.nodes.val x.val) (few : cnt ≤ countSum P.entries.val) :
    ForestInv.measure P F' < ForestInv.measure P F := by
  have xIn := created_x_inside created
  have deep := depth_le_bound inv x.val free
  have depthX : depth F' x.val = depth F x.val := by
    unfold depth
    rw [created_treePath created x.val xIn]
  have oldWeight : ∀ y < F.nodes.val.length, y ≠ x.val → weight P F' y = weight P F y := by
    intro y yIn different
    have depthY : depth F' y = depth F y := by
      unfold depth
      rw [created_treePath created y yIn]
    unfold weight factor
    rw [depthY,created_label created y,if_pos yIn,created_done created y yIn,if_neg different]
    by_cases act : Active F.nodes.val y
    · rw [if_pos act,if_pos ((created_active created y yIn).mpr act)]
    · rw [if_neg act,if_neg (fun a => act ((created_active created y yIn).mp a))]
  have doneLen : (doneOf F.nodes.val x.val ++ [i]).length ≤ P.entries.val.length := by
    apply label_le
    · exact List.nodup_append.mpr ⟨inv.doneNodup _,List.nodup_singleton _,by
        intro a listed' b single
        simp only [List.mem_singleton] at single
        subst single
        intro equal; subst equal; exact notDone listed'⟩
    · intro j listed'
      rcases List.mem_append.mp listed' with old | new
      · exact done_in inv _ j old
      · simp only [List.mem_singleton] at new
        subst new
        exact labels_in inv.shape _ j member
  have labelLen := label_length inv x.val
  have xWeight : weight P F' x.val + base P ^ (bound P + 2 - depth F x.val) = weight P F x.val := by
    unfold weight factor
    rw [depthX,created_label created x.val,if_pos xIn,created_done created x.val xIn,if_pos rfl,
      if_pos ((created_active created x.val xIn).mpr active),if_pos active]
    simp only [List.length_append,List.length_singleton] at doneLen ⊢
    rw [← Nat.mul_succ]
    congr 1
    omega
  have newWeight : ∀ k < cnt, weight P F' (F.nodes.val.length + k) =
      base P ^ (bound P + 2 - (depth F x.val + 1)) * (2 * P.entries.val.length + 1) := by
    intro k kIn
    obtain ⟨roles,_,at_new⟩ := created_new created (F.nodes.val.length + k) (by omega) (by omega)
    have activeNew : Active F'.nodes.val (F.nodes.val.length + k) := ⟨_,at_new,rfl⟩
    have depthNew : depth F' (F.nodes.val.length + k) = depth F x.val + 1 := by
      unfold depth
      rw [treePath.eq_def,at_new]
      simp only [child,if_true]
      rw [dif_pos (show x.val < F.nodes.val.length + k by omega),List.length_cons,created_treePath created x.val xIn]
    have labelNew : labelOf F'.nodes.val (F.nodes.val.length + k) = [] := by
      rw [created_label created,if_neg (by omega)]
    have doneNew := created_done_new created (F.nodes.val.length + k) (by omega)
    unfold weight factor
    rw [if_pos activeNew,depthNew,labelNew,doneNew]
    simp
  have oldSum : (∑ y ∈ Finset.range F.nodes.val.length, weight P F' y) + base P ^ (bound P + 2 - depth F x.val) ≤
      ∑ y ∈ Finset.range F.nodes.val.length, weight P F y := by
    apply sum_drop F.nodes.val.length x.val _ xIn (weight P F) (weight P F')
    · intro y yIn
      by_cases same : y = x.val
      · subst same
        omega
      · rw [oldWeight y yIn same]
    · omega
  have newSum : ∑ k ∈ Finset.range cnt, weight P F' (F.nodes.val.length + k) =
      cnt * (base P ^ (bound P + 2 - (depth F x.val + 1)) * (2 * P.entries.val.length + 1)) := by
    rw [Finset.sum_congr rfl (fun k kIn => newWeight k (Finset.mem_range.mp kIn))]
    simp
  have power : base P ^ (bound P + 2 - depth F x.val) =
      base P * base P ^ (bound P + 2 - (depth F x.val + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  have small : cnt * (2 * P.entries.val.length + 1) < base P := by
    unfold base
    calc cnt * (2 * P.entries.val.length + 1) ≤ countSum P.entries.val * (2 * P.entries.val.length + 1) :=
          Nat.mul_le_mul_right _ few
      _ ≤ countSum P.entries.val * (2 * P.entries.val.length + 2) := Nat.mul_le_mul_left _ (by omega)
      _ < (countSum P.entries.val + 1) * (2 * P.entries.val.length + 2) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have positive : 0 < base P ^ (bound P + 2 - (depth F x.val + 1)) := pow_pos (base_pos P) _
  have children : cnt * (base P ^ (bound P + 2 - (depth F x.val + 1)) * (2 * P.entries.val.length + 1)) <
      base P ^ (bound P + 2 - depth F x.val) := by
    rw [power]
    calc cnt * (base P ^ (bound P + 2 - (depth F x.val + 1)) * (2 * P.entries.val.length + 1))
        = (cnt * (2 * P.entries.val.length + 1)) * base P ^ (bound P + 2 - (depth F x.val + 1)) := by ring
      _ < base P * base P ^ (bound P + 2 - (depth F x.val + 1)) := Nat.mul_lt_mul_of_pos_right small positive
  have names : nameWeight P F' = nameWeight P F := by
    apply nameWeight_append P (by rw [created.length]; omega) (fun y yIn => created_named created y yIn) _
      created.caps
    intro y low named
    obtain ⟨m,at_y,root⟩ := named
    rcases created_lookup created y m at_y with ⟨yIn,_,_⟩ | ⟨rfl,_⟩ | ⟨_,_,roles,_,rfl⟩
    · omega
    · omega
    · simp [child] at root
  unfold ForestInv.measure treeMeasure
  rw [names,created.length,Finset.sum_range_add,newSum]
  omega

/-- A model of the forest where the expanded restriction holds at the node has
    different witnesses for the new children. -/
theorem created_models {Object : Type u} {Value : Type v} {P : completion.Problem} {h : hierarchy.RoleHierarchy}
    {count : Nat} {F F' : forest.Forest} {x i : Usize} {role : ObjectPropertyExpression} {filler cnt : Usize}
    {nx : forest.Node} (shape : Shape P h count F) (created : Created F F' x i role filler cnt.val nx)
    (e : concept_table.Entry) (at_i : P.entries.val[i.val]? = some e) (gen : generatorOf e = some (role,cnt,filler))
    (member : i ∈ labelOf F.nodes.val x.val) {I : Interpretation Object Value} {π : Nat → Object} {D : List Usize}
    (models : Models P h F I π D) : ∃ π' : Nat → Object, Models P h F' I π' D := by
  have xIn := created_x_inside created
  have depsX : nodeDeps F x.val = nx.deps.val := by simp [nodeDeps,created.at_x]
  obtain ⟨f,witnesses⟩ : ∃ f : Nat → Object, Sub nx.deps.val D →
      (∀ k < cnt.val, objectRelation I role (π x.val) (f k) ∧ denote I (meaning P.entries.val filler.val) (f k)) ∧
      (∀ a < cnt.val, ∀ b < cnt.val, f a = f b → a = b) := by
    by_cases sub : Sub nx.deps.val D
    · have holds := models.labels x.val (by rw [depsX]; exact sub) i member
      obtain ⟨g,injective,each⟩ := generator_meaning P.entries.val shape.wellFormed I i.val e at_i role cnt filler gen
        _ holds
      refine ⟨fun k => if hk : k < cnt.val then g ⟨k,hk⟩ else π x.val,fun _ => ⟨?_,?_⟩⟩
      · intro k kIn
        simp only [dif_pos kIn]
        exact each ⟨k,kIn⟩
      · intro a aIn b bIn same
        simp only [dif_pos aIn,dif_pos bIn] at same
        exact congrArg Fin.val (injective same)
    · exact ⟨fun _ => π x.val,fun yes => absurd yes sub⟩
  let π' : Nat → Object := fun y => if y < F.nodes.val.length then π y else f (y - F.nodes.val.length)
  have old : ∀ y, y < F.nodes.val.length → π' y = π y := fun y yIn => by simp [π',yIn]
  have countIn := shape.countIn
  refine ⟨π',⟨models.respects,models.axioms,models.unfoldings,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro q listed
    rw [old _ (by have := shape.requirements q listed; omega)]
    exact models.requirements q listed
  · intro l listed
    have := shape.links l listed
    rw [old _ (by omega),old _ (by omega)]
    exact models.links l listed
  · intro a sub
    rw [created_rep created a] at sub ⊢
    by_cases aIn : a.val < F.same.val.length
    · have repIn := active_inside (rep_in shape a (by rw [← shape.sameLength]; exact aIn)).2
      rw [created_deps created,if_pos (by omega)] at sub
      rw [old _ (by rw [shape.sameLength] at aIn; omega),old _ (by omega)]
      exact models.same a sub
    · have same : rep F a = a := by
        simp [rep,List.getElem?_eq_none_iff.mpr (show F.same.val.length ≤ a.val by omega)]
      rw [same]
  · intro y sub j listed
    rw [created_label created y] at listed
    split at listed
    · rename_i yIn
      rw [created_deps created,if_pos yIn] at sub
      rw [old y yIn]
      exact models.labels y sub j listed
    · cases listed
  · intro y n' at_y' tree sub
    rcases created_lookup created y n' at_y' with ⟨yIn,_,at_y⟩ | ⟨rfl,done,_,rfl⟩ | ⟨low,high,roles,rolesIs,rfl⟩
    · have parentIn := shape.parents y n' at_y tree
      rw [old y yIn,old _ (by omega)]
      exact models.tree y n' at_y tree sub
    · dsimp only at tree sub ⊢
      have parentIn := shape.parents x.val nx created.at_x tree
      rw [old _ xIn,old _ (by omega)]
      exact models.tree x.val nx created.at_x tree sub
    · simp only [child] at sub ⊢
      obtain ⟨edges,_⟩ := witnesses sub
      obtain ⟨edge,fillerHolds⟩ := edges _ (show y - F.nodes.val.length < cnt.val by omega)
      have notOld : ¬ y < F.nodes.val.length := by omega
      refine ⟨?_,?_⟩
      · intro s sIn
        rw [rolesIs] at sIn
        simp only [List.mem_singleton] at sIn
        subst sIn
        rw [old x.val xIn]
        simp only [π',notOld,if_false]
        exact edge
      · simp only [π',notOld,if_false]
        exact fillerHolds
  · intro edge listed sub
    rw [created.edges] at listed
    obtain ⟨toIn,fromCases⟩ := shape.edges edge listed
    have fromIn : edge.from.val < F.nodes.val.length := by
      rcases fromCases with named | ⟨n,at_n,_⟩
      · exact namedEnd_inside shape named
      · exact (List.getElem?_eq_some_iff.mp at_n).1
    rw [old _ fromIn,old _ (namedEnd_inside shape toIn)]
    exact models.edges edge listed sub
  · intro d listed sub
    rcases (created.distinct d).mp listed with oldFact | ⟨low,less,high,depsIs⟩
    · have := shape.distinctIn d oldFact
      rw [old _ this.1,old _ this.2]
      exact models.distinct d oldFact sub
    · rw [depsIs] at sub
      obtain ⟨_,injective⟩ := witnesses sub
      simp only [π',show ¬ d.left.val < F.nodes.val.length by omega,
        show ¬ d.right.val < F.nodes.val.length by omega,if_false]
      intro same
      have := injective _ (by omega) _ (by omega) same
      omega
  · intro y n' at_y' named beyond sub
    rw [created.same] at beyond
    rcases created_lookup created y n' at_y' with ⟨yIn,_,at_y⟩ | ⟨rfl,done,_,rfl⟩ | ⟨low,high,roles,rolesIs,rfl⟩
    · rw [old y yIn]
      exact models.seeds y n' at_y named beyond sub
    · dsimp only at named sub ⊢
      rw [old _ xIn]
      exact models.seeds x.val nx created.at_x named beyond sub
    · simp [child] at named
  · intro cap member sub
    rw [created.caps] at member
    have capIn := shape.capsIn cap member
    intro n r c c' at_i
    rw [old _ capIn]
    exact models.caps cap member sub n r c c' at_i

/-! ### Merging two neighbours -/

/-- How a merge goes: `source`, a tree node, into the parent of its parent, into
    a sibling, into a named node or into its tree parent; or a named `source`
    into a named node. -/
def MergeShape (F : forest.Forest) (source into : Nat) : Prop :=
  source ≠ into ∧ Active F.nodes.val source ∧ Active F.nodes.val into ∧
  ((∃ ns : forest.Node, F.nodes.val[source]? = some ns ∧ ns.tree = true ∧
      ((∃ np : forest.Node, F.nodes.val[ns.parent.val]? = some np ∧ np.tree = true ∧ np.parent.val = into) ∨
       (∃ ni : forest.Node, F.nodes.val[into]? = some ni ∧ ni.tree = true ∧ ni.parent.val = ns.parent.val) ∨
       Named F.nodes.val into ∨ ns.parent.val = into)) ∨
   (Named F.nodes.val source ∧ Named F.nodes.val into))

/-- A role a merge adds to the edge into `y`: the inverse of a role of the tree
    node `source` when `y` is its parent below `into`, or a role of `source`
    when `y` is its sibling `into`. -/
def NewRole (F : forest.Forest) (source into y : Nat) (s : ObjectPropertyExpression) : Prop :=
  ∃ ns : forest.Node, F.nodes.val[source]? = some ns ∧ ns.tree = true ∧
    ((y = ns.parent.val ∧ (∃ np : forest.Node, F.nodes.val[ns.parent.val]? = some np ∧ np.parent.val = into) ∧
        ∃ s0 ∈ ns.roles.val, s = inv s0) ∨
     (y = into ∧ (∃ ni : forest.Node, F.nodes.val[into]? = some ni ∧ ni.parent.val = ns.parent.val) ∧
        s ∈ ns.roles.val))

/-- An edge a merge adds: from the parent of the tree node `source` to the named
    node `into` along a role of `source`, or from `into` for an added edge from
    `source`; or, for a named `source`, an added edge with its ends at `source`
    moved to `into`; each also depending on the points of the merge. -/
def NewEdge (F : forest.Forest) (source into : Nat) (joined : List Usize) (e : forest.Edge) : Prop :=
  (∃ ns : forest.Node, F.nodes.val[source]? = some ns ∧ ns.tree = true ∧
    ((e.from = ns.parent ∧ e.to.val = into ∧ Named F.nodes.val into ∧ e.deps.val = joined ∧
        e.role ∈ ns.roles.val) ∨
     (∃ e0 ∈ F.edges.val, e0.from.val = source ∧ e.from.val = into ∧ e.to = e0.to ∧ e.role = e0.role ∧
        ∀ k, k ∈ e.deps.val ↔ k ∈ e0.deps.val ∨ k ∈ joined))) ∨
  (Named F.nodes.val source ∧ Named F.nodes.val into ∧ ∃ e0 ∈ F.edges.val, (e0.from.val = source ∨ e0.to.val = source) ∧
    e.role = e0.role ∧ e.from.val = (if e0.from.val = source then into else e0.from.val) ∧
    e.to.val = (if e0.to.val = source then into else e0.to.val) ∧
    ∀ k, k ∈ e.deps.val ↔ k ∈ e0.deps.val ∨ k ∈ joined)

/-- `G` hands the edges of `source` over to `into`: new roles on one edge, new
    added edges, or the individuals and added edges of a named `source` passed
    to `into`. -/
structure Moved (F G : forest.Forest) (source into : Nat) (joined : List Usize) : Prop where
  length : G.nodes.val.length = F.nodes.val.length
  distinct : G.distinct = F.distinct
  node : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → ∃ n' : forest.Node, G.nodes.val[y]? = some n' ∧
    n'.label = n.label ∧ n'.parent = n.parent ∧ n'.seed = n.seed ∧ n'.tree = n.tree ∧ n'.done = n.done ∧
    n'.active = n.active ∧ Sub n.deps.val n'.deps.val ∧ (∀ k ∈ n'.deps.val, k ∈ n.deps.val ∨ k ∈ joined) ∧
    (∀ s ∈ n'.roles.val, s ∈ n.roles.val ∨ ((y = into ∨ Sub joined n'.deps.val) ∧ NewRole F source into y s))
  edges : ∀ e ∈ G.edges.val, (e ∈ F.edges.val ∧ (Named F.nodes.val source → e.from.val ≠ source ∧ e.to.val ≠ source)) ∨
    NewEdge F source into joined e
  sameLength : G.same.val.length = F.same.val.length
  same : ∀ (a : Nat) (b : Usize), G.same.val[a]? = some b → ∃ b0 : Usize, F.same.val[a]? = some b0 ∧
    ((b0.val ≠ source ∧ b = b0) ∨ (b0.val = source ∧ b.val = into ∧ Named F.nodes.val into))
  caps : G.caps = F.caps

/-- The individuals are never read as a tree node. -/
theorem same_not_tree {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (source : Nat) (ns : forest.Node) (at_s : F.nodes.val[source]? = some ns)
    (tree : ns.tree = true) : ∀ b ∈ F.same.val, b.val ≠ source := by
  intro b member same
  have named := (shape.reps b member).1
  rw [same] at named
  exact tree_not_named at_s tree named

/-- Changing the roles and the points of one node, as `upward` and `sideways` do. -/
theorem moved_of_set {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (source into : Nat) (joined : List Usize) (ns : forest.Node)
    (at_s : F.nodes.val[source]? = some ns) (sourceTree : ns.tree = true)
    (y : Usize) (yIn : y.val < F.nodes.val.length) (roles : alloc.vec.Vec ObjectPropertyExpression)
    (deps : alloc.vec.Vec Usize)
    (rolesOk : ∀ s ∈ roles.val, s ∈ F.nodes.val[y.val].roles.val ∨
      ((y.val = into ∨ Sub joined deps.val) ∧ NewRole F source into y.val s))
    (depsUp : Sub F.nodes.val[y.val].deps.val deps.val)
    (depsDown : ∀ k ∈ deps.val, k ∈ F.nodes.val[y.val].deps.val ∨ k ∈ joined) :
    Moved F { F with nodes := (F.nodes.set y
      ⟨F.nodes.val[y.val].label,F.nodes.val[y.val].parent,roles,F.nodes.val[y.val].seed,F.nodes.val[y.val].tree,
        F.nodes.val[y.val].active,F.nodes.val[y.val].done,deps⟩) } source into joined := by
  obtain ⟨length,other,here⟩ := set_node F.nodes y yIn
    ⟨F.nodes.val[y.val].label,F.nodes.val[y.val].parent,roles,F.nodes.val[y.val].seed,F.nodes.val[y.val].tree,
      F.nodes.val[y.val].active,F.nodes.val[y.val].done,deps⟩
  refine ⟨length,rfl,?_,fun e member => .inl ⟨member,fun named => absurd named (tree_not_named at_s sourceTree)⟩,
    rfl,?_,rfl⟩
  · intro z n at_z
    by_cases same : z = y.val
    · subst same
      rw [List.getElem?_eq_getElem yIn] at at_z
      cases at_z
      exact ⟨_,here,rfl,rfl,rfl,rfl,rfl,rfl,depsUp,depsDown,rolesOk⟩
    · refine ⟨n,by rw [other z same]; exact at_z,rfl,rfl,rfl,rfl,rfl,rfl,fun k member => member,
        fun k member => .inl member,fun s member => .inl member⟩
  · intro a b at_a
    refine ⟨b,at_a,.inl ⟨same_not_tree shape source ns at_s sourceTree b (List.mem_of_getElem? at_a),rfl⟩⟩

/-- Keeping the forest as it is hands nothing over yet. -/
theorem moved_refl {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (source into : Nat) (joined : List Usize) (ns : forest.Node)
    (at_s : F.nodes.val[source]? = some ns) (sourceTree : ns.tree = true) : Moved F F source into joined := by
  refine ⟨rfl,rfl,?_,fun e member => .inl ⟨member,fun named => absurd named (tree_not_named at_s sourceTree)⟩,
    rfl,?_,rfl⟩
  · intro z n at_z
    exact ⟨n,at_z,rfl,rfl,rfl,rfl,rfl,rfl,fun k member => member,fun k member => .inl member,
      fun s member => .inl member⟩
  · intro a b at_a
    exact ⟨b,at_a,.inl ⟨same_not_tree shape source ns at_s sourceTree b (List.mem_of_getElem? at_a),rfl⟩⟩

/-- Carrying the added edges of the tree node `source` over to `into` after the
    rest of a move keeps the move. -/
theorem moved_carried {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F G1 : forest.Forest}
    (shape : Shape P h count F) (source into : Usize) (joined : alloc.vec.Vec Usize) (ns : forest.Node)
    (at_s : F.nodes.val[source.val]? = some ns) (sourceTree : ns.tree = true) (different : source.val ≠ into.val)
    (moved : Moved F G1 source.val into.val joined.val) :
    ∃ r, forest.carried G1 source into joined = .ok r ∧ ∀ G, r = some G →
      Moved F G source.val into.val joined.val := by
  obtain ⟨r,run,spec⟩ := carried_correct G1 source into joined
  refine ⟨r,run,?_⟩
  intro G same
  obtain ⟨edges,rfl,_,origin⟩ := spec G same
  refine ⟨moved.length,moved.distinct,moved.node,?_,moved.sameLength,moved.same,moved.caps⟩
  intro e member
  rcases origin e member with old | ⟨e0,e0In,e0From,eFrom,eTo,eRole,eDeps⟩
  · exact moved.edges e old
  · -- The carried edge comes from an old edge: the new edges of the move do not start at `source`.
    have e0Old : e0 ∈ F.edges.val := by
      rcases moved.edges e0 e0In with ⟨old,_⟩ | ⟨ns',at_s',_,⟨linkFrom,_⟩ | ⟨_,_,_,carriedFrom,_⟩⟩ | ⟨named,_⟩
      · exact old
      · rw [at_s] at at_s'
        cases at_s'
        have below := shape.parents source.val ns at_s sourceTree
        rw [← linkFrom,e0From] at below
        omega
      · exact absurd (by rw [← carriedFrom,e0From]) different
      · exact absurd named (tree_not_named at_s sourceTree)
    exact .inr (.inl ⟨ns,at_s,sourceTree,.inr ⟨e0,e0Old,by rw [e0From],by rw [eFrom],eTo,eRole,eDeps⟩⟩)

/-- The structural part of a merge hands the edges of `source` over to `into`. -/
theorem moved_correct {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} (F : forest.Forest)
    (shape : Shape P h count F) (source into : Usize) (joined : alloc.vec.Vec Usize)
    (mergeShape : MergeShape F source.val into.val) :
    ∃ r, forest.moved F source into joined = .ok r ∧ ∀ G, r = some G →
      Moved F G source.val into.val joined.val := by
  obtain ⟨different,activeS,activeI,cases⟩ := mergeShape
  have sourceIn := active_inside activeS
  have intoIn := active_inside activeI
  have at_s : F.nodes.val[source.val]? = some F.nodes.val[source.val] := List.getElem?_eq_getElem sourceIn
  have at_i : F.nodes.val[into.val]? = some F.nodes.val[into.val] := List.getElem?_eq_getElem intoIn
  have lookupS : F.nodes.index_usize source = .ok F.nodes.val[source.val] := by
    simp [alloc.vec.Vec.index_usize,at_s]
  have lookupI : F.nodes.index_usize into = .ok F.nodes.val[into.val] := by
    simp [alloc.vec.Vec.index_usize,at_i]
  rw [forest.moved]
  simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn,intoIn,↓reduceIte,alloc.vec.Vec.index_slice_index,
    lookupS,bind_ok]
  by_cases sTree : F.nodes.val[source.val].tree = true
  · have sourceRoot : ¬ Named F.nodes.val source.val := tree_not_named at_s sTree
    obtain ⟨ns,at_s',_,shapeCases⟩ := cases.resolve_right (fun both => sourceRoot both.1)
    rw [at_s] at at_s'
    cases at_s'
    -- The parent of `source`, whose edge the merge hands over.
    have parentIn : F.nodes.val[source.val].parent.val < F.nodes.val.length := by
      have := shape.parents source.val _ at_s sTree
      omega
    have at_p : F.nodes.val[F.nodes.val[source.val].parent.val]? =
        some F.nodes.val[F.nodes.val[source.val].parent.val] := List.getElem?_eq_getElem parentIn
    have lookupP : F.nodes.index_usize F.nodes.val[source.val].parent =
        .ok F.nodes.val[F.nodes.val[source.val].parent.val] := by
      simp [alloc.vec.Vec.index_usize,at_p]
    simp only [sTree,↓reduceIte,parentIn,lookupP,bind_ok]
    -- After the edge of the parent, the added edges of `source` follow.
    have carry : ∀ G1, Moved F G1 source.val into.val joined.val →
        ∃ r, forest.carried G1 source into joined = .ok r ∧ ∀ G, r = some G →
          Moved F G source.val into.val joined.val :=
      fun G1 moved1 => moved_carried shape source into joined _ at_s sTree different moved1
    -- A sibling `into` takes the roles of `source`.
    have toSibling : F.nodes.val[into.val].tree = true →
        (∃ ni : forest.Node, F.nodes.val[into.val]? = some ni ∧ ni.tree = true ∧
          ni.parent.val = F.nodes.val[source.val].parent.val) →
        ∃ r, (do
            let graph1 ← forest.sideways F source into
            match graph1 with
            | none => ok none
            | some graph2 => forest.carried graph2 source into joined) = .ok r ∧ ∀ G, r = some G →
          Moved F G source.val into.val joined.val := by
      intro _ intoSibling
      obtain ⟨r,run,spec⟩ := sideways_correct F source into
      cases r with
      | none => exact ⟨none,by simp [run],by simp⟩
      | some G1 =>
        obtain ⟨_,_,roles,rolesIs,rfl⟩ := spec _ rfl
        have moved1 := moved_of_set shape source.val into.val joined.val _ at_s sTree into intoIn
          roles F.nodes.val[into.val].deps
          (by
            intro s member
            rw [rolesIs] at member
            rcases List.mem_append.mp member with old | new
            · exact .inl old
            · obtain ⟨ni,at_i',_,iParent⟩ := intoSibling
              exact .inr ⟨.inl rfl,F.nodes.val[source.val],at_s,sTree,.inr ⟨rfl,⟨ni,at_i',iParent⟩,new⟩⟩)
          (fun k listed => listed) (fun k listed => .inl listed)
        obtain ⟨r,run2,spec2⟩ := carry _ moved1
        exact ⟨r,by simp [run,run2],spec2⟩
    -- A named `into` gets edges from the parent of `source`.
    have toNamed : F.nodes.val[into.val].tree = false →
        ∃ r, (do
            let graph1 ← forest.linked F F.nodes.val[source.val].parent source into joined
            match graph1 with
            | none => ok none
            | some graph2 => forest.carried graph2 source into joined) = .ok r ∧ ∀ G, r = some G →
          Moved F G source.val into.val joined.val := by
      intro iRoot
      have intoNamed : Named F.nodes.val into.val := ⟨_,at_i,iRoot⟩
      obtain ⟨r,run,spec⟩ := linked_correct F F.nodes.val[source.val].parent source into joined
      cases r with
      | none => exact ⟨none,by simp [run],by simp⟩
      | some G1 =>
        obtain ⟨_,edges,edgesIs,rfl⟩ := spec _ rfl
        have moved1 : Moved F { F with edges := edges } source.val into.val joined.val := by
          refine ⟨rfl,rfl,?_,?_,rfl,?_,rfl⟩
          · intro z n at_z
            exact ⟨n,at_z,rfl,rfl,rfl,rfl,rfl,rfl,fun k member => member,fun k member => .inl member,
              fun s member => .inl member⟩
          · intro e member
            rw [edgesIs] at member
            rcases List.mem_append.mp member with old | new
            · exact .inl ⟨old,fun named => absurd named sourceRoot⟩
            · obtain ⟨s,sIn,rfl⟩ := List.mem_map.mp new
              exact .inr (.inl ⟨F.nodes.val[source.val],at_s,sTree,.inl ⟨rfl,rfl,intoNamed,rfl,sIn⟩⟩)
          · intro a b at_a
            refine ⟨b,at_a,.inl ⟨same_not_tree shape source.val _ at_s sTree b (List.mem_of_getElem? at_a),rfl⟩⟩
        obtain ⟨r,run2,spec2⟩ := carry _ moved1
        exact ⟨r,by simp [run,run2],spec2⟩
    by_cases pTree : F.nodes.val[F.nodes.val[source.val].parent.val].tree = true
    · simp only [pTree,↓reduceIte]
      by_cases up : F.nodes.val[F.nodes.val[source.val].parent.val].parent = into
      · simp only [up,↓reduceIte]
        obtain ⟨r,run,spec⟩ := upward_correct F F.nodes.val[source.val].parent source joined
        cases r with
        | none => exact ⟨none,by simp [run],by simp⟩
        | some G1 =>
          obtain ⟨_,_,roles,deps',rolesIs,depsIs,rfl⟩ := spec _ rfl
          have moved1 := moved_of_set shape source.val into.val joined.val _ at_s sTree
            F.nodes.val[source.val].parent parentIn roles deps'
            (by
              intro s member
              rw [rolesIs] at member
              rcases List.mem_append.mp member with old | new
              · exact .inl old
              · obtain ⟨s0,s0In,rfl⟩ := List.mem_map.mp new
                exact .inr ⟨.inr (fun k listed => (depsIs k).mpr (.inr listed)),F.nodes.val[source.val],at_s,sTree,
                  .inl ⟨rfl,⟨_,at_p,by rw [up]⟩,s0,s0In,rfl⟩⟩)
            (fun k listed => (depsIs k).mpr (.inl listed)) (fun k listed => (depsIs k).mp listed)
          obtain ⟨r,run2,spec2⟩ := carry _ moved1
          exact ⟨r,by simp [run,run2],spec2⟩
      · simp only [up,↓reduceIte,lookupI,bind_ok]
        by_cases iTree : F.nodes.val[into.val].tree = true
        · simp only [iTree,↓reduceIte]
          by_cases atParent : F.nodes.val[source.val].parent = into
          · rw [if_pos atParent]
            obtain ⟨r,run2,spec2⟩ := carry F (moved_refl shape source.val into.val joined.val _ at_s sTree)
            exact ⟨r,by simp [run2],spec2⟩
          rw [if_neg atParent]
          apply toSibling iTree
          rcases shapeCases with ⟨np,at_p',_,pParent⟩ | sibling | intoNamed | parentCase
          · rw [at_p] at at_p'
            cases at_p'
            exact absurd (UScalar.eq_of_val_eq pParent) up
          · exact sibling
          · exact absurd intoNamed (tree_not_named at_i iTree)
          · exact absurd (UScalar.eq_of_val_eq parentCase) atParent
        · simp only [iTree,Bool.false_eq_true,↓reduceIte]
          exact toNamed (by simpa using iTree)
    · simp only [pTree,Bool.false_eq_true,↓reduceIte,lookupI,bind_ok]
      by_cases iTree : F.nodes.val[into.val].tree = true
      · simp only [iTree,↓reduceIte]
        by_cases atParent : F.nodes.val[source.val].parent = into
        · rw [if_pos atParent]
          obtain ⟨r,run2,spec2⟩ := carry F (moved_refl shape source.val into.val joined.val _ at_s sTree)
          exact ⟨r,by simp [run2],spec2⟩
        rw [if_neg atParent]
        apply toSibling iTree
        rcases shapeCases with ⟨np,at_p',npTree,_⟩ | sibling | intoNamed | parentCase
        · rw [at_p] at at_p'
          cases at_p'
          exact absurd npTree pTree
        · exact sibling
        · exact absurd intoNamed (tree_not_named at_i iTree)
        · exact absurd (UScalar.eq_of_val_eq parentCase) atParent
      · simp only [iTree,Bool.false_eq_true,↓reduceIte]
        exact toNamed (by simpa using iTree)
  · have roots : Named F.nodes.val source.val ∧ Named F.nodes.val into.val := by
      rcases cases with ⟨ns,at_s',tree,_⟩ | both
      · rw [at_s] at at_s'
        cases at_s'
        exact absurd tree sTree
      · exact both
    simp only [sTree,Bool.false_eq_true,↓reduceIte]
    obtain ⟨same',run,sameIs⟩ := renamed_correct F.same source into 0#usize (alloc.vec.Vec.new Usize) (by simp)
      (by simp)
    obtain ⟨r,runEdges,edgesSpec⟩ := relinked_correct F.edges source into joined 0#usize
      (alloc.vec.Vec.new forest.Edge)
    cases r with
    | none => exact ⟨none,by simp [run,runEdges],by simp⟩
    | some edges =>
    refine ⟨some { F with same := same', edges := edges },by simp [run,runEdges],?_⟩
    intro G same
    cases same
    refine ⟨rfl,rfl,?_,?_,by simp [sameIs],?_,rfl⟩
    · intro z n at_z
      exact ⟨n,at_z,rfl,rfl,rfl,rfl,rfl,rfl,fun k member => member,fun k member => .inl member,
        fun s member => .inl member⟩
    · intro e member
      rcases edgesSpec edges rfl e member with empty | ⟨e0,e0In,roleIs,fromIs,toIs,moved,kept⟩
      · simp at empty
      · by_cases hit : e0.from = source ∨ e0.to = source
        · refine .inr (.inr ⟨roots.1,roots.2,e0,e0In,?_,roleIs,?_,?_,moved hit⟩)
          · rcases hit with first | second
            · exact .inl (by rw [first])
            · exact .inr (by rw [second])
          · rw [fromIs]
            by_cases first : e0.from = source
            · rw [if_pos first,if_pos (by rw [first])]
            · rw [if_neg first,if_neg (fun same => first (UScalar.eq_of_val_eq same))]
          · rw [toIs]
            by_cases second : e0.to = source
            · rw [if_pos second,if_pos (by rw [second])]
            · rw [if_neg second,if_neg (fun same => second (UScalar.eq_of_val_eq same))]
        · have first : ¬ e0.from = source := fun same => hit (.inl same)
          have second : ¬ e0.to = source := fun same => hit (.inr same)
          have eIs : e = e0 := by
            have deps := kept hit
            rw [if_neg first] at fromIs
            rw [if_neg second] at toIs
            cases e
            cases e0
            simp only at roleIs fromIs toIs deps
            subst roleIs fromIs toIs deps
            rfl
          subst eIs
          refine .inl ⟨e0In,fun _ => ⟨fun same => first (UScalar.eq_of_val_eq same),
            fun same => second (UScalar.eq_of_val_eq same)⟩⟩
    · intro a b at_a
      have sameVal : same'.val = F.same.val.map (fun b => if b = source then into else b) := by
        simpa using sameIs
      rw [sameVal,List.getElem?_map] at at_a
      cases at_b0 : F.same.val[a]? with
      | none => rw [at_b0] at at_a; cases at_a
      | some b0 =>
        rw [at_b0] at at_a
        simp only [Option.map_some,Option.some.injEq] at at_a
        refine ⟨b0,rfl,?_⟩
        by_cases hit : b0 = source
        · rw [if_pos hit] at at_a
          subst at_a
          exact .inr ⟨by rw [hit],rfl,roots.2⟩
        · rw [if_neg hit] at at_a
          subst at_a
          exact .inl ⟨fun same' => hit (UScalar.eq_of_val_eq same'),rfl⟩

/-- `G` merges `source` into `into` with the points `joined`: the edges of
    `source` handed over, `source` and its subtree inactive, and `into` active
    with the points of the merge and the differences of `source`. -/
structure Merged (F G : forest.Forest) (source into : Usize) (joined : List Usize) : Prop where
  length : G.nodes.val.length = F.nodes.val.length
  node : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → ∃ n' : forest.Node, G.nodes.val[y]? = some n' ∧
    n'.label = n.label ∧ n'.parent = n.parent ∧ n'.seed = n.seed ∧ n'.tree = n.tree ∧ n'.done = n.done ∧
    (n'.active = true → n.active = true) ∧ (n.tree = false → y ≠ source.val → n'.active = n.active) ∧
    Sub n.deps.val n'.deps.val ∧ (∀ k ∈ n'.deps.val, k ∈ n.deps.val ∨ k ∈ joined) ∧
    (∀ s ∈ n'.roles.val, s ∈ n.roles.val ∨ (Sub joined n'.deps.val ∧ NewRole F source.val into.val y s))
  sourceGone : ¬ Active G.nodes.val source.val
  intoActive : Active G.nodes.val into.val
  intoDeps : Sub joined (nodeDeps G into.val)
  activeParents : ∀ (y : Nat) (n' : forest.Node), G.nodes.val[y]? = some n' → n'.tree = true → n'.active = true →
    Active G.nodes.val n'.parent.val
  edges : ∀ e ∈ G.edges.val, (e ∈ F.edges.val ∧
    (Named F.nodes.val source.val → e.from.val ≠ source.val ∧ e.to.val ≠ source.val)) ∨
    NewEdge F source.val into.val joined e
  sameLength : G.same.val.length = F.same.val.length
  same : ∀ (a : Nat) (b : Usize), G.same.val[a]? = some b → ∃ b0 : Usize, F.same.val[a]? = some b0 ∧
    ((b0.val ≠ source.val ∧ b = b0) ∨ (b0.val = source.val ∧ b.val = into.val ∧ Named F.nodes.val into.val))
  distinct : ∀ d ∈ G.distinct.val, d ∈ F.distinct.val ∨ ∃ d0 ∈ F.distinct.val, Inherited source into joined d0 d
  caps : G.caps = F.caps

/-- A merge hands the edges over, deactivates the merged node with its subtree,
    keeps `into` active and makes it depend on the merge. -/
theorem merged_correct {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} (F : forest.Forest)
    (shape : Shape P h count F) (source into : Usize) (joined : alloc.vec.Vec Usize)
    (mergeShape : MergeShape F source.val into.val) :
    ∃ r, forest.merged F source into joined = .ok r ∧ ∀ G, r = some G →
      Merged F G source into joined.val := by
  obtain ⟨r1,run1,spec1⟩ := moved_correct F shape source into joined mergeShape
  obtain ⟨different,activeS,activeI,cases⟩ := mergeShape
  have sourceIn := active_inside activeS
  have intoIn := active_inside activeI
  rw [forest.merged,run1]
  cases r1 with
  | none => exact ⟨none,by simp,by simp⟩
  | some G1 =>
  have moved := spec1 G1 rfl
  have sourceIn1 : source.val < G1.nodes.val.length := by rw [moved.length]; exact sourceIn
  have intoIn1 : into.val < G1.nodes.val.length := by rw [moved.length]; exact intoIn
  have lookup1 : G1.nodes.index_usize source = .ok G1.nodes.val[source.val] := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem sourceIn1]
  obtain ⟨r2,run2,spec2⟩ := inherit_correct G1.distinct source into joined 0#usize G1.distinct
  cases r2 with
  | none =>
    refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn1,intoIn1,
      copy_distinct_correct G1.distinct 0#usize (alloc.vec.Vec.new forest.Distinct) (by simp) (by simp),run2]
  | some distinct =>
  obtain ⟨_,inherited⟩ := spec2 distinct rfl
  obtain ⟨nodes,prunedRun,prunedLength,_,prunedAt⟩ := pruned_correct
    (G1.nodes.set source { G1.nodes.val[source.val] with active := false }) 0#usize
    (alloc.vec.Vec.new forest.Node) (by simp) (by simp)
  have vLength : (G1.nodes.set source { G1.nodes.val[source.val] with active := false }).val.length =
      F.nodes.val.length := by
    simp [moved.length]
  have intoIn2 : into.val < nodes.val.length := by rw [prunedLength,vLength]; exact intoIn
  have lookup2 : nodes.index_usize into = .ok nodes.val[into.val] := by
    simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem intoIn2]
  obtain ⟨r3,run3,spec3⟩ := join_correct nodes.val[into.val].deps joined
  cases r3 with
  | none =>
    refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn1,intoIn1,
      copy_distinct_correct G1.distinct 0#usize (alloc.vec.Vec.new forest.Distinct) (by simp) (by simp),run2,
      alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize,lookup1,prunedRun,lookup2,run3]
  | some depends =>
  have dependsIs := spec3 depends rfl
  refine ⟨some { G1 with nodes := nodes.set into { nodes.val[into.val] with deps := depends }, distinct := distinct },
    ?_,?_⟩
  · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,sourceIn1,intoIn1,
      copy_distinct_correct G1.distinct 0#usize (alloc.vec.Vec.new forest.Distinct) (by simp) (by simp),run2,
      alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize,lookup1,prunedRun,lookup2,run3]
  · intro G same
    cases same
    have vAt : ∀ y, (G1.nodes.set source { G1.nodes.val[source.val] with active := false }).val[y]? =
        if y = source.val then some { G1.nodes.val[source.val] with active := false } else G1.nodes.val[y]? := by
      intro y
      simp only [alloc.vec.Vec.set_val_eq]
      by_cases same : y = source.val
      · subst same
        rw [if_pos rfl,List.getElem?_set_self sourceIn1]
      · rw [if_neg same,List.getElem?_set_ne (Ne.symm same)]
    have nodesAt : ∀ y, y < F.nodes.val.length → ∃ w,
        (G1.nodes.set source { G1.nodes.val[source.val] with active := false }).val[y]? = some w ∧
        nodes.val[y]? = some (prunedNode nodes.val y w) := by
      intro y yIn
      have yIn' : y < (G1.nodes.set source { G1.nodes.val[source.val] with active := false }).val.length := by
        rw [vLength]; exact yIn
      exact ⟨_,List.getElem?_eq_getElem yIn',prunedAt y yIn' (by simp)⟩
    have finalAt : ∀ y, (nodes.set into { nodes.val[into.val] with deps := depends }).val[y]? =
        if y = into.val then some { nodes.val[into.val] with deps := depends } else nodes.val[y]? := by
      intro y
      simp only [alloc.vec.Vec.set_val_eq]
      by_cases same : y = into.val
      · subst same
        rw [if_pos rfl,List.getElem?_set_self intoIn2]
      · rw [if_neg same,List.getElem?_set_ne (Ne.symm same)]
    -- Every node of the result: the moved node, inactive below an inactive
    -- parent or when it is `source`, and with the points of the merge at `into`.
    have nodeG : ∀ (y : Nat) (n1 : forest.Node), G1.nodes.val[y]? = some n1 → ∃ m : forest.Node,
        (nodes.set into { nodes.val[into.val] with deps := depends }).val[y]? = some m ∧
        m.label = n1.label ∧ m.parent = n1.parent ∧ m.roles = n1.roles ∧ m.seed = n1.seed ∧ m.tree = n1.tree ∧
        m.done = n1.done ∧
        m.active = ((if y = source.val then false else n1.active) &&
          !(n1.tree && decide (n1.parent.val < y) && !activeAt nodes.val n1.parent.val)) ∧
        (∀ k, k ∈ m.deps.val ↔ k ∈ n1.deps.val ∨ (y = into.val ∧ k ∈ joined.val)) := by
      intro y n1 at_y1
      have yIn : y < F.nodes.val.length := by
        rw [← moved.length]; exact (List.getElem?_eq_some_iff.mp at_y1).1
      obtain ⟨w,at_w,at_n⟩ := nodesAt y yIn
      have wIs : w = if y = source.val then { n1 with active := false } else n1 := by
        rw [vAt y] at at_w
        by_cases same : y = source.val
        · subst same
          rw [if_pos rfl] at at_w ⊢
          rw [List.getElem?_eq_getElem sourceIn1] at at_y1
          simp only [Option.some.injEq] at at_w at_y1
          rw [← at_w,at_y1]
        · rw [if_neg same,at_y1] at at_w
          rw [if_neg same]
          simp only [Option.some.injEq] at at_w
          exact at_w.symm
      by_cases atInto : y = into.val
      · subst atInto
        have notSource : into.val ≠ source.val := Ne.symm different
        have wIs' : w = n1 := by rw [wIs,if_neg notSource]
        subst wIs'
        have nodeIs : nodes.val[into.val] = prunedNode nodes.val into.val w := by
          rw [List.getElem?_eq_getElem intoIn2] at at_n
          simp only [Option.some.injEq] at at_n
          exact at_n
        refine ⟨{ nodes.val[into.val] with deps := depends },by rw [finalAt,if_pos rfl],?_⟩
        rw [nodeIs]
        refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,by simp only [prunedNode,if_neg notSource],?_⟩
        intro k
        rw [dependsIs k,nodeIs]
        simp [prunedNode]
      · refine ⟨prunedNode nodes.val y w,by rw [finalAt,if_neg atInto]; exact at_n,?_⟩
        by_cases same : y = source.val
        · have wIs' : w = { n1 with active := false } := by rw [wIs,if_pos same]
          subst wIs'
          refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,by simp only [prunedNode,if_pos same],?_⟩
          intro k
          simp [prunedNode,atInto]
        · have wIs' : w = n1 := by rw [wIs,if_neg same]
          subst wIs'
          refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,by simp only [prunedNode,if_neg same],?_⟩
          intro k
          simp [prunedNode,atInto]
    -- Nodes before `source` that are active stay active.
    have keep : ∀ y, y < source.val → Active F.nodes.val y → activeAt nodes.val y = true := by
      intro y
      induction y using Nat.strong_induction_on with
      | _ y ih =>
        intro low active
        obtain ⟨n,at_y,act⟩ := active
        have yIn : y < F.nodes.val.length := (List.getElem?_eq_some_iff.mp at_y).1
        obtain ⟨n1,at_y1,_,parent1,_,tree1,_,active1,_⟩ := moved.node y n at_y
        obtain ⟨w,at_w,at_n⟩ := nodesAt y yIn
        rw [vAt y,if_neg (by omega),at_y1] at at_w
        simp only [Option.some.injEq] at at_w
        subst at_w
        unfold activeAt
        rw [at_n]
        simp only [prunedNode]
        rw [active1,act]
        by_cases tree : n.tree = true
        · have parentLow := shape.parents y n at_y tree
          have parentAct := shape.activeParents y n at_y tree act
          rw [tree1,parent1,ih n.parent.val parentLow (by omega) parentAct]
          simp
        · simp [tree1,tree]
    have activeG : ∀ y, Active (nodes.set into { nodes.val[into.val] with deps := depends }).val y ↔
        activeAt nodes.val y = true ∧ y < F.nodes.val.length := by
      intro y
      constructor
      · rintro ⟨m,at_m,act⟩
        have yIn : y < F.nodes.val.length := by
          rw [← vLength,← prunedLength]
          have := (List.getElem?_eq_some_iff.mp at_m).1
          simpa using this
        refine ⟨?_,yIn⟩
        rw [finalAt] at at_m
        unfold activeAt
        by_cases same : y = into.val
        · subst same
          rw [if_pos rfl] at at_m
          simp only [Option.some.injEq] at at_m
          subst at_m
          rw [List.getElem?_eq_getElem intoIn2]
          exact act
        · rw [if_neg same] at at_m
          rw [at_m]
          exact act
      · rintro ⟨act,yIn⟩
        have yIn2 : y < nodes.val.length := by rw [prunedLength,vLength]; exact yIn
        unfold activeAt at act
        rw [List.getElem?_eq_getElem yIn2] at act
        by_cases same : y = into.val
        · subst same
          exact ⟨{ nodes.val[into.val] with deps := depends },by rw [finalAt,if_pos rfl],act⟩
        · exact ⟨_,by rw [finalAt,if_neg same,List.getElem?_eq_getElem yIn2],act⟩
    refine ⟨by simp [prunedLength,vLength,moved.length],?_,?_,?_,?_,?_,moved.edges,moved.sameLength,moved.same,?_,
      moved.caps⟩
    · intro y n at_y
      obtain ⟨n1,at_y1,label1,parent1,seed1,tree1,done1,active1,depsUp1,depsDown1,roles1⟩ := moved.node y n at_y
      obtain ⟨m,at_m,label,parent,roles,seed,tree,done,active,deps⟩ := nodeG y n1 at_y1
      refine ⟨m,at_m,label.trans label1,parent.trans parent1,seed.trans seed1,tree.trans tree1,done.trans done1,
        ?_,?_,?_,?_,?_⟩
      · intro act
        rw [active] at act
        rw [← active1]
        by_cases same : y = source.val
        · simp [same] at act
        · simp only [if_neg same,Bool.and_eq_true] at act
          exact act.1
      · intro root notSource
        rw [active,if_neg notSource,tree1,root,active1]
        simp
      · intro k listed
        exact (deps k).mpr (.inl (depsUp1 k listed))
      · intro k listed
        rcases (deps k).mp listed with old | ⟨_,new⟩
        · exact depsDown1 k old
        · exact .inr new
      · intro s listed
        rw [roles] at listed
        rcases roles1 s listed with old | ⟨place,newRole⟩
        · exact .inl old
        · refine .inr ⟨?_,newRole⟩
          rcases place with rfl | sub
          · intro k listed'
            exact (deps k).mpr (.inr ⟨rfl,listed'⟩)
          · intro k listed'
            exact (deps k).mpr (.inl (sub k listed'))
    · rintro ⟨m,at_m,act⟩
      obtain ⟨n,at_s⟩ : ∃ n, F.nodes.val[source.val]? = some n := ⟨_,List.getElem?_eq_getElem sourceIn⟩
      obtain ⟨n1,at_s1,_⟩ := moved.node source.val n at_s
      obtain ⟨m',at_m',_,_,_,_,_,_,active,_⟩ := nodeG source.val n1 at_s1
      rw [at_m'] at at_m
      simp only [Option.some.injEq] at at_m
      subst at_m
      rw [active] at act
      simp at act
    · -- `into` stays active: no node on its path up is `source`.
      refine (activeG into.val).mpr ⟨?_,intoIn⟩
      obtain ⟨ni,at_i,iAct⟩ := activeI
      obtain ⟨ni1,at_i1,_,parent1,_,tree1,_,active1,_⟩ := moved.node into.val ni at_i
      obtain ⟨w,at_w,at_n⟩ := nodesAt into.val intoIn
      rw [vAt,if_neg (Ne.symm different),at_i1] at at_w
      simp only [Option.some.injEq] at at_w
      subst at_w
      unfold activeAt
      rw [at_n]
      simp only [prunedNode]
      rw [active1,iAct]
      by_cases tree : ni.tree = true
      · rw [tree1,tree,parent1]
        have parentAct := shape.activeParents into.val ni at_i tree iAct
        have parentLow := shape.parents into.val ni at_i tree
        rcases cases with ⟨ns,at_s,sTree,shapeCases⟩ | ⟨_,intoRoot⟩
        · have sourceAbove := shape.parents source.val ns at_s sTree
          rcases shapeCases with ⟨np,at_p,npTree,npParent⟩ | ⟨ni',at_i',_,iParent⟩ | intoRoot | parentCase
          · have := shape.parents ns.parent.val np at_p npTree
            rw [keep ni.parent.val (by omega) parentAct]
            simp
          · rw [at_i] at at_i'
            simp only [Option.some.injEq] at at_i'
            subst at_i'
            rw [keep ni.parent.val (by omega) parentAct]
            simp
          · exact absurd intoRoot (tree_not_named at_i tree)
          · -- `into` is the parent of `source`, above it.
            rw [keep ni.parent.val (by omega) parentAct]
            simp
        · exact absurd intoRoot (tree_not_named at_i tree)
      · rw [tree1]
        simp [tree]
    · intro k listed
      simp only [nodeDeps]
      obtain ⟨n,at_i⟩ : ∃ n, F.nodes.val[into.val]? = some n := ⟨_,List.getElem?_eq_getElem intoIn⟩
      obtain ⟨n1,at_i1,_⟩ := moved.node into.val n at_i
      obtain ⟨m,at_m,_,_,_,_,_,_,_,deps⟩ := nodeG into.val n1 at_i1
      rw [at_m]
      exact (deps k).mpr (.inr ⟨rfl,listed⟩)
    · intro y m at_m tree act
      have yIn : y < F.nodes.val.length := by
        rw [← vLength,← prunedLength]
        have := (List.getElem?_eq_some_iff.mp at_m).1
        simpa using this
      obtain ⟨n,at_y⟩ : ∃ n, F.nodes.val[y]? = some n := ⟨_,List.getElem?_eq_getElem yIn⟩
      obtain ⟨n1,at_y1,_,parent1,_,tree1,_⟩ := moved.node y n at_y
      obtain ⟨m',at_m',_,parent,_,_,treeM,_,active,_⟩ := nodeG y n1 at_y1
      rw [at_m'] at at_m
      simp only [Option.some.injEq] at at_m
      subst at_m
      rw [active] at act
      rw [treeM] at tree
      simp only [Bool.and_eq_true,tree,Bool.true_and,Bool.not_eq_eq_eq_not,Bool.not_true,Bool.and_eq_false_imp,
        decide_eq_true_eq] at act
      have low : n1.parent.val < y := by
        rw [parent1]
        exact shape.parents y n at_y (by rw [← tree1]; exact tree)
      have parentAct : activeAt nodes.val n1.parent.val = true := by
        have := act.2 low
        simpa using this
      rw [parent]
      exact (activeG _).mpr ⟨parentAct,by omega⟩
    · intro d member
      rcases inherited d member with old | ⟨d0,d0In,inh⟩
      · exact .inl (by rw [← moved.distinct]; exact old)
      · simp only [show (0#usize).val = 0 from rfl,List.drop_zero] at d0In
        exact .inr ⟨d0,by rw [← moved.distinct]; exact d0In,inh⟩

section MergedFacts
variable {F G : forest.Forest} {source into : Usize} {joined : List Usize}

theorem merged_back (merged : Merged F G source into joined) (y : Nat) (n' : forest.Node)
    (at_y' : G.nodes.val[y]? = some n') : ∃ n : forest.Node, F.nodes.val[y]? = some n ∧
      n'.label = n.label ∧ n'.parent = n.parent ∧ n'.seed = n.seed ∧ n'.tree = n.tree ∧ n'.done = n.done ∧
      (n'.active = true → n.active = true) ∧ (n.tree = false → y ≠ source.val → n'.active = n.active) ∧
      Sub n.deps.val n'.deps.val ∧ (∀ k ∈ n'.deps.val, k ∈ n.deps.val ∨ k ∈ joined) ∧
      (∀ s ∈ n'.roles.val, s ∈ n.roles.val ∨ (Sub joined n'.deps.val ∧ NewRole F source.val into.val y s)) := by
  have yIn : y < F.nodes.val.length := by rw [← merged.length]; exact (List.getElem?_eq_some_iff.mp at_y').1
  obtain ⟨n'',at_y'',rest⟩ := merged.node y F.nodes.val[y] (List.getElem?_eq_getElem yIn)
  rw [at_y'] at at_y''
  simp only [Option.some.injEq] at at_y''
  subst at_y''
  exact ⟨_,List.getElem?_eq_getElem yIn,rest⟩

theorem merged_none (merged : Merged F G source into joined) (y : Nat) (absent : F.nodes.val[y]? = none) :
    G.nodes.val[y]? = none := by
  rw [List.getElem?_eq_none_iff] at absent ⊢
  rw [merged.length]
  exact absent

theorem merged_label (merged : Merged F G source into joined) (y : Nat) :
    labelOf G.nodes.val y = labelOf F.nodes.val y := by
  unfold labelOf
  cases at_y : F.nodes.val[y]? with
  | none => rw [merged_none merged y at_y]
  | some n =>
    obtain ⟨n',at_y',label,_⟩ := merged.node y n at_y
    simp only [at_y',label]

theorem merged_done (merged : Merged F G source into joined) (y : Nat) :
    doneOf G.nodes.val y = doneOf F.nodes.val y := by
  unfold doneOf
  cases at_y : F.nodes.val[y]? with
  | none => rw [merged_none merged y at_y]
  | some n =>
    obtain ⟨n',at_y',_,_,_,_,done,_⟩ := merged.node y n at_y
    simp only [at_y',done]

theorem merged_deps (merged : Merged F G source into joined) (y : Nat) :
    Sub (nodeDeps F y) (nodeDeps G y) ∧ ∀ k ∈ nodeDeps G y, k ∈ nodeDeps F y ∨ k ∈ joined := by
  unfold nodeDeps
  cases at_y : F.nodes.val[y]? with
  | none =>
    rw [merged_none merged y at_y]
    exact ⟨fun k member => member,fun k member => .inl member⟩
  | some n =>
    obtain ⟨n',at_y',_,_,_,_,_,_,_,up,down,_⟩ := merged.node y n at_y
    rw [at_y']
    exact ⟨up,down⟩

theorem merged_treePath (merged : Merged F G source into joined) :
    ∀ y, treePath G.nodes.val y = treePath F.nodes.val y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    rw [treePath.eq_def,treePath.eq_def F.nodes.val]
    cases at_y : F.nodes.val[y]? with
    | none => rw [merged_none merged y at_y]
    | some n =>
      obtain ⟨n',at_y',_,parent,_,tree,_⟩ := merged.node y n at_y
      rw [at_y']
      simp only [tree,parent]
      split
      · split
        · rename_i below
          rw [ih n.parent.val below]
        · rfl
      · rfl

theorem merged_active (merged : Merged F G source into joined) (y : Nat) :
    Active G.nodes.val y → Active F.nodes.val y := by
  rintro ⟨n',at_y',act⟩
  obtain ⟨n,at_y,_,_,_,_,_,back,_⟩ := merged_back merged y n' at_y'
  exact ⟨n,at_y,back act⟩

theorem merged_named (merged : Merged F G source into joined) (y : Nat) :
    Named G.nodes.val y ↔ Named F.nodes.val y := by
  constructor
  · rintro ⟨n',at_y',named⟩
    obtain ⟨n,at_y,_,_,_,tree,_⟩ := merged_back merged y n' at_y'
    exact ⟨n,at_y,by rw [← tree]; exact named⟩
  · rintro ⟨n,at_y,named⟩
    obtain ⟨n',at_y',_,_,_,tree,_⟩ := merged.node y n at_y
    exact ⟨n',at_y',by rw [tree]; exact named⟩

/-- An end of an added edge other than the merged node stays one. -/
theorem merged_namedEnd (merged : Merged F G source into joined) (c y : Nat) (named : NamedEnd F c y)
    (other : y ≠ source.val) : NamedEnd G c y := by
  rcases named with below | ⟨⟨n,at_y,root⟩,⟨n2,at_y2,act⟩⟩
  · exact .inl below
  · rw [at_y] at at_y2
    cases at_y2
    obtain ⟨n',at_y',_,_,_,tree,_,_,keep,_⟩ := merged.node y n at_y
    exact .inr ⟨⟨n',at_y',by rw [tree,root]⟩,n',at_y',by rw [keep root other]; exact act⟩

end MergedFacts

/-- A merge keeps the invariant. -/
theorem merged_inv {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F G : forest.Forest}
    {source into : Usize} {joined : List Usize} (inv : Inv P h count F)
    (merged : Merged F G source into joined) (activeS : Active F.nodes.val source.val) : Inv P h count G := by
  have shape := inv.shape
  refine ⟨⟨shape.wellFormed,shape.complements,shape.closedTable,shape.closed,shape.simple,?_,
    by rw [merged.length]; exact shape.countIn,by rw [merged.sameLength]; exact shape.sameLength,?_,?_,
    merged.activeParents,shape.links,shape.requirements,?_,?_,?_,?_,
    by rw [merged.caps,merged.length]; exact shape.capsIn⟩,?_,?_,?_,?_⟩
  · intro y n' at_y'
    obtain ⟨n,at_y,_,_,_,tree,_⟩ := merged_back merged y n' at_y'
    rw [tree]
    exact shape.named y n at_y
  · intro b member
    obtain ⟨a,at_a⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨b0,at_b0,cases⟩ := merged.same a b at_a
    rcases cases with ⟨notSource,rfl⟩ | ⟨_,isInto,intoRoot⟩
    · obtain ⟨⟨n,at_b,root⟩,⟨n2,at_b2,act⟩⟩ := shape.reps _ (List.mem_of_getElem? at_b0)
      rw [at_b] at at_b2
      cases at_b2
      obtain ⟨n',at_b',_,_,_,tree',_,_,keep,_⟩ := merged.node _ n at_b
      exact ⟨⟨n',at_b',by rw [tree',root]⟩,n',at_b',by rw [keep root notSource]; exact act⟩
    · rw [isInto]
      exact ⟨(merged_named merged _).mpr intoRoot,merged.intoActive⟩
  · intro y n' at_y' tree'
    obtain ⟨n,at_y,_,parent,_,tree,_⟩ := merged_back merged y n' at_y'
    rw [parent]
    exact shape.parents y n at_y (by rw [← tree]; exact tree')
  · intro e member
    -- A tree node of `F` is one of `G`.
    have treeKept : ∀ k : Nat, (∃ n, F.nodes.val[k]? = some n ∧ n.tree = true) →
        ∃ n, G.nodes.val[k]? = some n ∧ n.tree = true := by
      rintro k ⟨n,at_k,tree⟩
      obtain ⟨n',at_k',_,_,_,tree',_⟩ := merged.node k n at_k
      exact ⟨n',at_k',by rw [tree',tree]⟩
    -- A named end stays one unless it is the named `source`.
    have namedKept : ∀ k : Nat, NamedEnd F count k → (Named F.nodes.val source.val → k ≠ source.val) →
        NamedEnd G count k := by
      intro k named avoid
      rcases named with below | ⟨kNamed,kActive⟩
      · exact .inl below
      · have other : k ≠ source.val := fun same => avoid (same ▸ kNamed) same
        exact merged_namedEnd merged count k (.inr ⟨kNamed,kActive⟩) other
    -- A node that is no named node of `F` is a tree node of `G`.
    have otherwiseTree : ∀ k : Nat, k < F.nodes.val.length → ¬ Named F.nodes.val k →
        ∃ n, G.nodes.val[k]? = some n ∧ n.tree = true := by
      intro k kIn notNamed
      obtain ⟨n,at_k⟩ : ∃ n, F.nodes.val[k]? = some n := ⟨_,List.getElem?_eq_getElem kIn⟩
      apply treeKept k
      refine ⟨n,at_k,?_⟩
      cases tree : n.tree
      · exact absurd ⟨n,at_k,tree⟩ notNamed
      · rfl
    have intoIn := active_inside (merged_active merged _ merged.intoActive)
    have intoEnd : Named F.nodes.val into.val → NamedEnd G count into.val :=
      fun named => .inr ⟨(merged_named merged _).mpr named,merged.intoActive⟩
    -- The end `into`, of either kind.
    have intoKind : NamedEnd G count into.val ∨ ∃ n, G.nodes.val[into.val]? = some n ∧ n.tree = true := by
      by_cases named : Named F.nodes.val into.val
      · exact .inl (intoEnd named)
      · exact .inr (otherwiseTree _ intoIn named)
    rcases merged.edges e member with ⟨old,notAt⟩ |
        ⟨ns,at_s,sTree,⟨fromIs,toIs,intoNamed,_,_⟩ | ⟨e0,e0In,_,fromIs,toIs,_,_⟩⟩ |
        ⟨_,intoNamed,e0,e0In,_,_,fromIs,toIs,_⟩
    · obtain ⟨toIn,fromCases⟩ := shape.edges e old
      refine ⟨namedKept _ toIn (fun named => (notAt named).2),?_⟩
      rcases fromCases with named | tree
      · exact .inl (namedKept _ named (fun named => (notAt named).1))
      · exact .inr (treeKept _ tree)
    · have notSource : ¬ Named F.nodes.val source.val := tree_not_named at_s sTree
      refine ⟨by rw [toIs]; exact intoEnd intoNamed,?_⟩
      rw [fromIs]
      have parentAct := shape.activeParents source.val ns at_s sTree
        (by obtain ⟨m,at_m,act⟩ := activeS; rw [at_s] at at_m; cases at_m; exact act)
      by_cases named : Named F.nodes.val ns.parent.val
      · exact .inl (namedKept _ (.inr ⟨named,parentAct⟩) (fun named' => absurd named' notSource))
      · exact .inr (otherwiseTree _ (active_inside parentAct) named)
    · have notSource : ¬ Named F.nodes.val source.val := tree_not_named at_s sTree
      have fromInto : e.from = into := UScalar.eq_of_val_eq fromIs
      refine ⟨by rw [toIs]; exact namedKept _ (shape.edges e0 e0In).1 (fun named' => absurd named' notSource),?_⟩
      rw [fromInto]
      exact intoKind
    · constructor
      · rw [toIs]
        by_cases hit : e0.to.val = source.val
        · rw [if_pos hit]
          exact intoEnd intoNamed
        · rw [if_neg hit]
          exact namedKept _ (shape.edges e0 e0In).1 (fun _ => hit)
      · rw [fromIs]
        by_cases hit : e0.from.val = source.val
        · rw [if_pos hit]
          exact .inl (intoEnd intoNamed)
        · rw [if_neg hit]
          rcases (shape.edges e0 e0In).2 with named | tree
          · exact .inl (namedKept _ named (fun _ => hit))
          · exact .inr (treeKept _ tree)
  · intro d member
    rw [merged.length]
    rcases merged.distinct d member with old | ⟨d0,d0In,left,ends,_⟩
    · exact shape.distinctIn d old
    · have := shape.distinctIn d0 d0In
      have intoIn := active_inside (merged_active merged _ merged.intoActive)
      rw [left]
      rcases ends with ⟨_,right⟩ | ⟨_,right⟩
      · rw [right]; exact ⟨intoIn,this.2⟩
      · rw [right]; exact ⟨intoIn,this.1⟩
  · intro y i member
    rw [merged_label merged y] at member
    exact shape.literals y i member
  · intro y i member j listed e e' at_i at_j
    rw [merged_label merged y] at member listed
    exact shape.clashFree y i member j listed e e' at_i at_j
  · intro y
    rw [merged_label merged y]
    exact inv.nodup y
  · intro y
    rw [merged_done merged y]
    exact inv.doneNodup y
  · intro y i member
    rw [merged_done merged y] at member
    rw [merged_label merged y]
    exact inv.doneIn y i member
  · intro y n' at_y' s member
    obtain ⟨n,at_y,_,_,_,_,_,_,_,_,_,roles⟩ := merged_back merged y n' at_y'
    rcases roles s member with old | ⟨_,ns,at_s,_,cases⟩
    · exact inv.roles y n at_y s old
    · rcases cases with ⟨_,_,s0,s0In,rfl⟩ | ⟨_,_,sIn⟩
      · exact inv_listed _ _ (inv.roles _ ns at_s s0 s0In)
      · exact inv.roles _ ns at_s s sIn

/-- The points of a merged forest are those of the forest and of the merge. -/
theorem merged_fresh {F G : forest.Forest} {source into : Usize} {joined : List Usize}
    (merged : Merged F G source into joined) {fresh : Nat} (freshF : FreshForest F fresh)
    (joinedFresh : ∀ k ∈ joined, k.val < fresh) : FreshForest G fresh := by
  refine ⟨?_,?_,?_,by rw [merged.caps]; exact freshF.2.2.2⟩
  · intro y k member
    rcases (merged_deps merged y).2 k member with old | new
    · exact freshF.1 y k old
    · exact joinedFresh k new
  · intro e member k kIn
    rcases merged.edges e member with ⟨old,_⟩ | ⟨_,_,_,⟨_,_,_,depsIs,_⟩ | ⟨e0,e0In,_,_,_,_,deps⟩⟩ |
        ⟨_,_,e0,e0In,_,_,_,_,deps⟩
    · exact freshF.2.1 e old k kIn
    · rw [depsIs] at kIn
      exact joinedFresh k kIn
    · rcases (deps k).mp kIn with old | new
      · exact freshF.2.1 e0 e0In k old
      · exact joinedFresh k new
    · rcases (deps k).mp kIn with old | new
      · exact freshF.2.1 e0 e0In k old
      · exact joinedFresh k new
  · intro d member k kIn
    rcases merged.distinct d member with old | ⟨d0,d0In,_,_,deps⟩
    · exact freshF.2.2.1 d old k kIn
    · rcases (deps k).mp kIn with old | new
      · exact freshF.2.2.1 d0 d0In k old
      · exact joinedFresh k new

/-- A merge decreases the measure: the merged node no longer counts and no other
    weight grows. -/
theorem merged_measure {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F G : forest.Forest}
    {source into : Usize} {joined : List Usize} (inv : Inv P h count F)
    (merged : Merged F G source into joined) (activeS : Active F.nodes.val source.val) :
    ForestInv.measure P G < ForestInv.measure P F := by
  have weightLe : ∀ y, weight P G y ≤ weight P F y := by
    intro y
    unfold weight factor depth
    rw [merged_treePath merged y,merged_label merged y,merged_done merged y]
    by_cases act : Active G.nodes.val y
    · rw [if_pos act,if_pos (merged_active merged y act)]
    · rw [if_neg act]
      exact Nat.zero_le _
  have names : nameWeight P G = nameWeight P F := nameWeight_eq P merged.length (merged_named merged) merged.caps
  unfold ForestInv.measure
  rw [names]
  suffices treeMeasure P G < treeMeasure P F by omega
  unfold treeMeasure
  rw [merged.length]
  apply Finset.sum_lt_sum (fun y _ => weightLe y)
  refine ⟨source.val,Finset.mem_range.mpr (active_inside activeS),?_⟩
  unfold weight
  rw [if_neg merged.sourceGone,if_pos activeS]
  apply Nat.mul_pos (pow_pos (base_pos P) _)
  unfold factor
  have := label_length inv source.val
  have := done_length inv source.val
  omega

/-- A model that places `source` and `into` on one element, when the points of
    the merge are in `D`, models the merged forest, with the label of `source`
    at `into`. -/
theorem merged_models {Object : Type u} {Value : Type v} {P : completion.Problem} {h : hierarchy.RoleHierarchy}
    {F G : forest.Forest} {source into : Usize} {joined : List Usize}
    (merged : Merged F G source into joined) (sourceDeps : Sub (nodeDeps F source.val) joined)
    {I : Interpretation Object Value} {π : Nat → Object} {D : List Usize} (models : Models P h F I π D)
    (equal : Sub joined D → π source.val = π into.val) :
    Models P h G I π D ∧
      (Sub joined D → ∀ c ∈ labelOf F.nodes.val source.val, denote I (meaning P.entries.val c.val) (π into.val)) := by
  have intoDeps : ∀ sub : Sub (nodeDeps G into.val) D, Sub joined D :=
    fun sub k member => sub k (merged.intoDeps k member)
  have sourceSub : Sub joined D → Sub (nodeDeps F source.val) D :=
    fun sub k member => sub k (sourceDeps k member)
  -- The edge of `source` from its parent, when the merge holds.
  have sourceEdges : Sub joined D → ∀ ns : forest.Node, F.nodes.val[source.val]? = some ns → ns.tree = true →
      ∀ s ∈ ns.roles.val, objectRelation I s (π ns.parent.val) (π into.val) := by
    intro sub ns at_s tree s sIn
    rw [← equal sub]
    exact (models.tree source.val ns at_s tree (by simpa [nodeDeps,at_s] using sourceSub sub)).1 s sIn
  refine ⟨⟨models.respects,models.axioms,models.unfoldings,models.requirements,models.links,?_,?_,?_,?_,?_,?_,
    by rw [merged.caps]; exact models.caps⟩,?_⟩
  · intro a sub
    by_cases aIn : a.val < G.same.val.length
    · obtain ⟨b,at_a⟩ : ∃ b, G.same.val[a.val]? = some b := ⟨_,List.getElem?_eq_getElem aIn⟩
      have repG : rep G a = b := by simp [rep,at_a]
      obtain ⟨b0,at_b0,cases⟩ := merged.same a.val b at_a
      have repF : rep F a = b0 := by simp [rep,at_b0]
      rw [repG] at sub ⊢
      rcases cases with ⟨_,rfl⟩ | ⟨isSource,isInto,_⟩
      · have := models.same a (by rw [repF]; exact fun k member => sub k ((merged_deps merged _).1 k member))
        rwa [repF] at this
      · rw [isInto] at sub ⊢
        have joinedSub := intoDeps sub
        have := models.same a (by rw [repF,isSource]; exact sourceSub joinedSub)
        rw [repF,isSource] at this
        rw [this]
        exact equal joinedSub
    · have repG : rep G a = a := by
        simp [rep,List.getElem?_eq_none_iff.mpr (show G.same.val.length ≤ a.val by omega)]
      rw [repG]
  · intro y sub i member
    rw [merged_label merged y] at member
    exact models.labels y (fun k listed => sub k ((merged_deps merged y).1 k listed)) i member
  · intro y n' at_y' tree' sub
    obtain ⟨n,at_y,_,parent,seed,tree,_,_,_,up,_,roles⟩ := merged_back merged y n' at_y'
    have old := models.tree y n at_y (by rw [← tree]; exact tree') (fun k listed => sub k (up k listed))
    refine ⟨?_,by rw [seed]; exact old.2⟩
    intro s member
    rw [parent]
    rcases roles s member with oldRole | ⟨joinedIn,ns,at_s,sTree,cases⟩
    · exact old.1 s oldRole
    · have joinedSub : Sub joined D := fun k listed => sub k (joinedIn k listed)
      have edges := sourceEdges joinedSub ns at_s sTree
      rcases cases with ⟨rfl,⟨nx,at_x,xParent⟩,s0,s0In,rfl⟩ | ⟨rfl,⟨ni,at_i,iParent⟩,sIn⟩
      · rw [at_y] at at_x
        simp only [Option.some.injEq] at at_x
        subst at_x
        rw [xParent]
        exact (relation_inv I s0 _ _).mpr (edges s0 s0In)
      · rw [at_y] at at_i
        simp only [Option.some.injEq] at at_i
        subst at_i
        rw [iParent]
        exact edges s sIn
  · intro e member sub
    rcases merged.edges e member with ⟨old,_⟩ |
        ⟨ns,at_s,sTree,⟨fromIs,toInto,_,depsIs,roleIn⟩ | ⟨e0,e0In,e0From,fromInto,toIs,roleIs,deps⟩⟩ |
        ⟨_,_,e0,e0In,_,roleIs,fromIs,toIs,deps⟩
    · exact models.edges e old sub
    · rw [depsIs] at sub
      have edges := sourceEdges sub ns at_s sTree
      rw [fromIs,toInto]
      exact edges e.role roleIn
    · -- An added edge of `source`, now from `into`.
      have sub0 : Sub e0.deps.val D := fun k listed => sub k ((deps k).mpr (.inl listed))
      have joinedSub : Sub joined D := fun k listed => sub k ((deps k).mpr (.inr listed))
      have edge := models.edges e0 e0In sub0
      rw [e0From,equal joinedSub] at edge
      rw [fromInto,toIs,roleIs]
      exact edge
    · -- An added edge with an end at the named `source`, now at `into`.
      have sub0 : Sub e0.deps.val D := fun k listed => sub k ((deps k).mpr (.inl listed))
      have joinedSub : Sub joined D := fun k listed => sub k ((deps k).mpr (.inr listed))
      have edge := models.edges e0 e0In sub0
      have moveEq : ∀ v : Nat, π (if v = source.val then into.val else v) = π v := by
        intro v
        by_cases hit : v = source.val
        · rw [if_pos hit,hit,equal joinedSub]
        · rw [if_neg hit]
      rw [fromIs,toIs,roleIs,moveEq,moveEq]
      exact edge
  · intro d member sub
    rcases merged.distinct d member with old | ⟨d0,d0In,left,ends,deps⟩
    · exact models.distinct d old sub
    · have sub0 : Sub d0.deps.val D := fun k listed => sub k ((deps k).mpr (.inl listed))
      have joinedSub : Sub joined D := fun k listed => sub k ((deps k).mpr (.inr listed))
      have differ := models.distinct d0 d0In sub0
      rw [left,← equal joinedSub]
      rcases ends with ⟨d0Left,right⟩ | ⟨d0Right,right⟩
      · rw [right,← d0Left]
        exact differ
      · rw [right,← d0Right]
        exact Ne.symm differ
  · intro y n' at_y' named beyond sub
    obtain ⟨n,at_y,_,_,seed,tree,_,_,_,up,_⟩ := merged_back merged y n' at_y'
    rw [seed]
    exact models.seeds y n at_y (by rw [← tree]; exact named) (by rw [← merged.sameLength]; exact beyond)
      (fun k listed => sub k (up k listed))
  · intro sub c member
    rw [← equal sub]
    exact models.labels source.val (sourceSub sub) c member

/-- A pair of neighbours of an active node, oriented as `orient` does, has the
    shape of a merge, when, at a named node, neither is a tree node that is no
    child of it. -/
theorem orient_shape {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (x : Usize) (active : Active F.nodes.val x.val) (r : ObjectPropertyExpression)
    (p : forest.Pair) (first : Neighbour P h F x.val r p.first.val) (second : Neighbour P h F x.val r p.second.val)
    (different : p.first ≠ p.second)
    (children : Named F.nodes.val x.val → (∃ a, F.nodes.val[p.first.val]? = some a ∧ a.tree = true) →
      (∃ b, F.nodes.val[p.second.val]? = some b ∧ b.tree = true) →
      ¬ Repeated F.nodes.val x.val p.first.val ∧ ¬ Repeated F.nodes.val x.val p.second.val) :
    MergeShape F (orientOf F x p).1.val (orientOf F x p).2.val ∧
      (orientOf F x p = (p.first,p.second) ∨ orientOf F x p = (p.second,p.first)) := by
  have firstIn := neighbour_inside shape x.val r _ first
  have secondIn := neighbour_inside shape x.val r _ second
  have xIn := active_inside active
  have activeFirst := neighbour_active shape x.val active r _ first
  have activeSecond := neighbour_active shape x.val active r _ second
  have differentVal : p.first.val ≠ p.second.val := fun same => different (UScalar.eq_of_val_eq same)
  obtain ⟨a,at_a⟩ : ∃ a, F.nodes.val[p.first.val]? = some a := ⟨_,List.getElem?_eq_getElem firstIn⟩
  obtain ⟨b,at_b⟩ : ∃ b, F.nodes.val[p.second.val]? = some b := ⟨_,List.getElem?_eq_getElem secondIn⟩
  obtain ⟨n,at_x⟩ : ∃ n, F.nodes.val[x.val]? = some n := ⟨_,List.getElem?_eq_getElem xIn⟩
  -- A tree neighbour that the merge may take is a child of `x`, its parent or
  -- `x` itself.
  have treeNeighbour : ∀ (z : Usize) (m : forest.Node), Neighbour P h F x.val r z.val → F.nodes.val[z.val]? = some m →
      m.tree = true → (Named F.nodes.val x.val → ¬ Repeated F.nodes.val x.val z.val) →
      m.parent.val = x.val ∨ (n.tree = true ∧ n.parent.val = z.val) ∨ z = x := by
    intro z m neighbour at_z tree fine
    rcases neighbour_tree shape x.val r z.val neighbour m at_z tree with ⟨m',at_z',_,_,parent,_⟩ |
        ⟨n',at_x',xTree,parent,_⟩ | ⟨xNamed,_⟩ | loop
    · rw [at_z] at at_z'
      cases at_z'
      exact .inl parent
    · rw [at_x] at at_x'
      cases at_x'
      exact .inr (.inl ⟨xTree,parent⟩)
    · by_cases child : m.parent.val = x.val
      · exact .inl child
      · exact absurd ⟨m,at_z,tree,child⟩ (fine xNamed)
    · exact .inr (.inr (UScalar.eq_of_val_eq loop))
  unfold orientOf
  rw [at_a,at_b,at_x]
  simp only
  by_cases aTree : a.tree = true
  · rw [if_pos aTree]
    by_cases bTree : b.tree = true
    · rw [if_pos bTree]
      by_cases up : n.tree = true ∧ n.parent = p.first
      · rw [if_pos up]
        -- `second` is a child of `x` merged into the parent of `x`, or `x` itself.
        rcases treeNeighbour p.second b second at_b bTree (fun named => (children named ⟨a,at_a,aTree⟩ ⟨b,at_b,bTree⟩).2) with child |
            ⟨_,parent⟩ | loop
        · refine ⟨⟨Ne.symm differentVal,activeSecond,activeFirst,.inl ⟨b,at_b,bTree,.inl ⟨n,?_,up.1,?_⟩⟩⟩,.inr rfl⟩
          · rw [child]; exact at_x
          · rw [up.2]
        · exact absurd (by rw [← parent,up.2]) differentVal
        · -- `x` itself into its parent.
          have xb : F.nodes.val[x.val]? = some b := by rw [← loop]; exact at_b
          have bIs : b = n := by
            rw [at_x,Option.some.injEq] at xb
            exact xb.symm
          refine ⟨⟨Ne.symm differentVal,activeSecond,activeFirst,.inl ⟨b,at_b,bTree,.inr (.inr (.inr ?_))⟩⟩,.inr rfl⟩
          rw [bIs,up.2]
      · rw [if_neg up]
        by_cases selfFirst : n.tree = true ∧ p.first = x
        · rw [if_pos selfFirst]
          have xa : F.nodes.val[x.val]? = some a := by rw [← selfFirst.2]; exact at_a
          have aIs : a = n := by
            rw [at_x,Option.some.injEq] at xa
            exact xa.symm
          by_cases parentSecond : n.parent = p.second
          · -- `x` into its parent.
            rw [if_pos parentSecond]
            refine ⟨⟨differentVal,activeFirst,activeSecond,.inl ⟨a,at_a,aTree,.inr (.inr (.inr ?_))⟩⟩,.inl rfl⟩
            rw [aIs,parentSecond]
          · -- A child of `x` into `x`.
            rw [if_neg parentSecond]
            rcases treeNeighbour p.second b second at_b bTree (fun named => (children named ⟨a,at_a,aTree⟩ ⟨b,at_b,bTree⟩).2) with child |
                ⟨_,parent⟩ | loop
            · refine ⟨⟨Ne.symm differentVal,activeSecond,activeFirst,.inl ⟨b,at_b,bTree,.inr (.inr (.inr ?_))⟩⟩,
                .inr rfl⟩
              rw [child,selfFirst.2]
            · exact absurd (UScalar.eq_of_val_eq parent) parentSecond
            · exact absurd (loop.trans selfFirst.2.symm) (Ne.symm different)
        · rw [if_neg selfFirst]
          have aParent : a.parent.val = x.val := by
            rcases treeNeighbour p.first a first at_a aTree (fun named => (children named ⟨a,at_a,aTree⟩ ⟨b,at_b,bTree⟩).1) with child |
                ⟨xTree,parent⟩ | loop
            · exact child
            · exact absurd ⟨xTree,UScalar.eq_of_val_eq parent⟩ up
            · have xa : F.nodes.val[x.val]? = some a := by rw [← loop]; exact at_a
              have xTree : n.tree = true := by
                rw [at_x,Option.some.injEq] at xa
                rw [xa]
                exact aTree
              exact absurd ⟨xTree,loop⟩ selfFirst
          refine ⟨⟨differentVal,activeFirst,activeSecond,.inl ⟨a,at_a,aTree,?_⟩⟩,.inl rfl⟩
          rcases treeNeighbour p.second b second at_b bTree (fun named => (children named ⟨a,at_a,aTree⟩ ⟨b,at_b,bTree⟩).2) with child |
              ⟨xTree,parent⟩ | loop
          · exact .inr (.inl ⟨b,at_b,bTree,by rw [child,aParent]⟩)
          · exact .inl ⟨n,by rw [aParent]; exact at_x,xTree,parent⟩
          · -- A child of `x` into `x`.
            exact .inr (.inr (.inr (by rw [aParent,loop])))
    · rw [if_neg bTree]
      have bRoot : b.tree = false := by simpa using bTree
      exact ⟨⟨differentVal,activeFirst,activeSecond,.inl ⟨a,at_a,aTree,.inr (.inr (.inl ⟨b,at_b,bRoot⟩))⟩⟩,.inl rfl⟩
  · rw [if_neg aTree]
    have aRoot : a.tree = false := by simpa using aTree
    refine ⟨⟨Ne.symm differentVal,activeSecond,activeFirst,?_⟩,.inr rfl⟩
    by_cases bTree : b.tree = true
    · exact .inl ⟨b,at_b,bTree,.inr (.inr (.inl ⟨a,at_a,aRoot⟩))⟩
    · have bRoot : b.tree = false := by simpa using bTree
      exact .inr ⟨⟨b,at_b,bRoot⟩,⟨a,at_a,aRoot⟩⟩


/-! ### New named nodes -/

section NamedMade
variable {F F' : forest.Forest} {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize} {cnt : Nat}
  {deps : alloc.vec.Vec Usize}

theorem named_length (made : NamedMade F F' x i role filler cnt deps) :
    F'.nodes.val.length = F.nodes.val.length + cnt := by
  rw [made.nodes]
  simp

theorem named_old (made : NamedMade F F' x i role filler cnt deps) (y : Nat) (yIn : y < F.nodes.val.length) :
    F'.nodes.val[y]? = F.nodes.val[y]? := by
  rw [made.nodes,List.getElem?_append_left yIn]

theorem named_new (made : NamedMade F F' x i role filler cnt deps) (y : Nat) (low : F.nodes.val.length ≤ y)
    (high : y < F.nodes.val.length + cnt) : F'.nodes.val[y]? = some (freshNode x filler deps) := by
  rw [made.nodes,List.getElem?_append_right low,List.getElem?_replicate]
  simp only [ite_eq_left_iff,reduceCtorEq,imp_false,not_not]
  omega

/-- Every node of the forest with new named nodes is an old node or a new one. -/
theorem named_lookup (made : NamedMade F F' x i role filler cnt deps) (y : Nat) (n' : forest.Node)
    (at_y : F'.nodes.val[y]? = some n') :
    (y < F.nodes.val.length ∧ F.nodes.val[y]? = some n') ∨
    (F.nodes.val.length ≤ y ∧ y < F.nodes.val.length + cnt ∧ n' = freshNode x filler deps) := by
  have yIn : y < F'.nodes.val.length := (List.getElem?_eq_some_iff.mp at_y).1
  rw [named_length made] at yIn
  by_cases old : y < F.nodes.val.length
  · rw [named_old made y old] at at_y
    exact .inl ⟨old,at_y⟩
  · rw [named_new made y (by omega) yIn] at at_y
    exact .inr ⟨by omega,yIn,(Option.some.inj at_y).symm⟩

theorem named_label (made : NamedMade F F' x i role filler cnt deps) (y : Nat) :
    labelOf F'.nodes.val y = if y < F.nodes.val.length then labelOf F.nodes.val y else [] := by
  by_cases yIn : y < F.nodes.val.length
  · rw [if_pos yIn]
    unfold labelOf
    rw [named_old made y yIn]
  · rw [if_neg yIn]
    unfold labelOf
    by_cases new : y < F.nodes.val.length + cnt
    · rw [named_new made y (by omega) new]
      simp [freshNode]
    · rw [List.getElem?_eq_none_iff.mpr (by rw [named_length made]; omega)]

theorem named_done (made : NamedMade F F' x i role filler cnt deps) (y : Nat) :
    doneOf F'.nodes.val y = if y < F.nodes.val.length then doneOf F.nodes.val y else [] := by
  by_cases yIn : y < F.nodes.val.length
  · rw [if_pos yIn]
    unfold doneOf
    rw [named_old made y yIn]
  · rw [if_neg yIn]
    unfold doneOf
    by_cases new : y < F.nodes.val.length + cnt
    · rw [named_new made y (by omega) new]
      simp [freshNode]
    · rw [List.getElem?_eq_none_iff.mpr (by rw [named_length made]; omega)]

theorem named_deps (made : NamedMade F F' x i role filler cnt deps) (y : Nat) :
    nodeDeps F' y = if y < F.nodes.val.length then nodeDeps F y else
      if y < F.nodes.val.length + cnt then deps.val else [] := by
  by_cases yIn : y < F.nodes.val.length
  · rw [if_pos yIn]
    unfold nodeDeps
    rw [named_old made y yIn]
  · rw [if_neg yIn]
    unfold nodeDeps
    by_cases new : y < F.nodes.val.length + cnt
    · rw [named_new made y (by omega) new,if_pos new]
      simp [freshNode]
    · rw [if_neg new,List.getElem?_eq_none_iff.mpr (by rw [named_length made]; omega)]

theorem named_active (made : NamedMade F F' x i role filler cnt deps) (y : Nat) (yIn : y < F.nodes.val.length) :
    Active F'.nodes.val y ↔ Active F.nodes.val y := by
  unfold Active
  rw [named_old made y yIn]

theorem named_named (made : NamedMade F F' x i role filler cnt deps) (y : Nat) (yIn : y < F.nodes.val.length) :
    Named F'.nodes.val y ↔ Named F.nodes.val y := by
  unfold Named
  rw [named_old made y yIn]

theorem named_treePath (made : NamedMade F F' x i role filler cnt deps) :
    ∀ y, y < F.nodes.val.length → treePath F'.nodes.val y = treePath F.nodes.val y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro yIn
    rw [treePath.eq_def,treePath.eq_def F.nodes.val,named_old made y yIn]
    split
    · split
      · split
        · rename_i below
          rw [ih _ below (by omega)]
        · rfl
      · rfl
    · rfl

theorem named_rep (made : NamedMade F F' x i role filler cnt deps) (a : Usize) : rep F' a = rep F a := by
  unfold rep
  rw [made.same]

theorem named_namedEnd (made : NamedMade F F' x i role filler cnt deps) (c y : Nat) (named : NamedEnd F c y) :
    NamedEnd F' c y := by
  rcases named with below | ⟨named,active⟩
  · exact .inl below
  · have yIn := active_inside active
    exact .inr ⟨(named_named made y yIn).mpr named,(named_active made y yIn).mpr active⟩

/-- A new named node is an active named node. -/
theorem named_fresh_named (made : NamedMade F F' x i role filler cnt deps) (y : Nat) (low : F.nodes.val.length ≤ y)
    (high : y < F.nodes.val.length + cnt) : Named F'.nodes.val y ∧ Active F'.nodes.val y :=
  ⟨⟨_,named_new made y low high,rfl⟩,⟨_,named_new made y low high,rfl⟩⟩

end NamedMade

/-- New named nodes for a restriction of an active named node keep the invariant. -/
theorem named_inv {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F F' : forest.Forest}
    {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize} {cnt : Nat} {deps : alloc.vec.Vec Usize}
    (inv : Inv P h count F) (made : NamedMade F F' x i role filler cnt deps) (named : Named F.nodes.val x.val)
    (active : Active F.nodes.val x.val) : Inv P h count F' := by
  have shape := inv.shape
  have countIn := shape.countIn
  have xIn := active_inside active
  have length := named_length made
  refine ⟨⟨shape.wellFormed,shape.complements,shape.closedTable,shape.closed,shape.simple,?_,by omega,
    by rw [made.same]; exact shape.sameLength,?_,?_,?_,shape.links,shape.requirements,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · intro y n' at_y' below
    rcases named_lookup made y n' at_y' with ⟨_,at_y⟩ | ⟨low,_,rfl⟩
    · exact shape.named y n' at_y below
    · rfl
  · intro b member
    rw [made.same] at member
    obtain ⟨isNamed,act⟩ := shape.reps b member
    have bIn := active_inside act
    exact ⟨(named_named made _ bIn).mpr isNamed,(named_active made _ bIn).mpr act⟩
  · intro y n' at_y' tree
    rcases named_lookup made y n' at_y' with ⟨_,at_y⟩ | ⟨_,_,rfl⟩
    · exact shape.parents y n' at_y tree
    · cases tree
  · intro y n' at_y' tree act
    rcases named_lookup made y n' at_y' with ⟨yIn,at_y⟩ | ⟨_,_,rfl⟩
    · have parentIn := shape.parents y n' at_y tree
      exact (named_active made _ (by omega)).mpr (shape.activeParents y n' at_y tree act)
    · cases tree
  · intro e member
    rcases made.edges e member with old | ⟨_,fromX,low,high,_⟩
    · obtain ⟨toIn,fromCases⟩ := shape.edges e old
      refine ⟨named_namedEnd made count _ toIn,fromCases.imp (named_namedEnd made count _) ?_⟩
      rintro ⟨n,at_n,tree⟩
      have fromIn := (List.getElem?_eq_some_iff.mp at_n).1
      exact ⟨n,by rw [named_old made _ fromIn]; exact at_n,tree⟩
    · refine ⟨.inr (named_fresh_named made _ low high),?_⟩
      rw [fromX]
      exact .inl (.inr ⟨(named_named made _ xIn).mpr named,(named_active made _ xIn).mpr active⟩)
  · intro d member
    rw [length]
    rcases (made.distinct d).mp member with old | ⟨_,_,high,_⟩
    · have := shape.distinctIn d old
      omega
    · omega
  · intro y j member
    rw [named_label made y] at member
    split at member
    · exact shape.literals y j member
    · cases member
  · intro y j member k listed' e e' at_j at_k
    rw [named_label made y] at member listed'
    by_cases yIn : y < F.nodes.val.length
    · rw [if_pos yIn] at member listed'
      exact shape.clashFree y j member k listed' e e' at_j at_k
    · rw [if_neg yIn] at member
      cases member
  · intro cap member
    rw [length]
    rcases (made.caps cap).mp member with old | ⟨node,_⟩
    · have := shape.capsIn cap old
      omega
    · rw [node]
      omega
  · intro y
    rw [named_label made y]
    split
    · exact inv.nodup y
    · exact List.nodup_nil
  · intro y
    rw [named_done made y]
    split
    · exact inv.doneNodup y
    · exact List.nodup_nil
  · intro y j listed'
    rw [named_done made y] at listed'
    rw [named_label made y]
    split
    · rename_i yIn
      rw [if_pos yIn] at listed'
      exact inv.doneIn y j listed'
    · rename_i yIn
      rw [if_neg yIn] at listed'
      cases listed'
  · intro y n' at_y' s member
    rcases named_lookup made y n' at_y' with ⟨_,at_y⟩ | ⟨_,_,rfl⟩
    · exact inv.roles y n' at_y s member
    · simp [freshNode] at member

/-- The points of a forest with new named nodes are those of the forest and the
    given ones. -/
theorem named_fresh {F F' : forest.Forest} {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize}
    {cnt : Nat} {deps : alloc.vec.Vec Usize} (made : NamedMade F F' x i role filler cnt deps) {fresh : Nat}
    (freshF : FreshForest F fresh) (depsFresh : ∀ k ∈ deps.val, k.val < fresh) : FreshForest F' fresh := by
  refine ⟨?_,?_,?_,?_⟩
  · intro y k member
    rw [named_deps made y] at member
    split at member
    · exact freshF.1 y k member
    · split at member
      · exact depsFresh k member
      · cases member
  · intro e member k kIn
    rcases made.edges e member with old | ⟨_,_,_,_,depsIs⟩
    · exact freshF.2.1 e old k kIn
    · rw [depsIs] at kIn
      exact depsFresh k kIn
  · intro d member k kIn
    rcases (made.distinct d).mp member with old | ⟨_,_,_,depsIs⟩
    · exact freshF.2.2.1 d old k kIn
    · rw [depsIs] at kIn
      exact depsFresh k kIn
  · intro cap member k kIn
    rcases (made.caps cap).mp member with old | ⟨_,_,_,depsIs⟩
    · exact freshF.2.2.2 cap old k kIn
    · rw [depsIs] at kIn
      exact depsFresh k kIn


/-- New named nodes for a maximum restriction of a named node without a bound
    decrease the measure: the restriction loses its weight, which is more than
    the new nodes bring to the tree and the weight of their own restrictions. -/
theorem named_measure {P : completion.Problem} {F F' : forest.Forest}
    {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize} {cnt : Nat} {deps : alloc.vec.Vec Usize}
    (made : NamedMade F F' x i role filler cnt deps) (xIn : x.val < F.nodes.val.length)
    (named : Named F.nodes.val x.val) (most : AtMostAt P i.val) (iIn : i.val < P.entries.val.length)
    (uncapped : ¬ Capped F x.val i.val) (few : cnt ≤ (P.entries.val.map atMostCount).sum)
    (room : F'.nodes.val.length ≤ Usize.max) :
    ForestInv.measure P F' < ForestInv.measure P F := by
  have length := named_length made
  have positive : 0 < nameBase P := by unfold nameBase; omega
  have unitPositive : 0 < nameUnit P := by unfold nameUnit; omega
  -- The tree weight grows by less than `nameUnit` per new node.
  have oldWeight : ∀ y < F.nodes.val.length, weight P F' y = weight P F y := by
    intro y yIn
    unfold weight factor depth
    rw [named_treePath made y yIn,named_label made y,if_pos yIn,named_done made y,if_pos yIn]
    by_cases act : Active F.nodes.val y
    · rw [if_pos act,if_pos ((named_active made y yIn).mpr act)]
    · rw [if_neg act,if_neg (fun a => act ((named_active made y yIn).mp a))]
  have newWeight : ∀ y, weight P F' y ≤ nameUnit P - 1 := by
    intro y
    unfold weight
    split
    · have power : base P ^ (bound P + 2 - depth F' y) ≤ base P ^ (bound P + 2) :=
        Nat.pow_le_pow_right (base_pos P) (by omega)
      have room' : factor P F' y ≤ 2 * P.entries.val.length + 1 := by unfold factor; omega
      have := Nat.mul_le_mul power room'
      unfold nameUnit
      omega
    · omega
  have treeLe : treeMeasure P F' ≤ treeMeasure P F + cnt * (nameUnit P - 1) := by
    unfold treeMeasure
    rw [length,Finset.sum_range_add]
    have old : ∑ y ∈ Finset.range F.nodes.val.length, weight P F' y =
        ∑ y ∈ Finset.range F.nodes.val.length, weight P F y :=
      Finset.sum_congr rfl (fun y member => oldWeight y (Finset.mem_range.mp member))
    have new : ∑ k ∈ Finset.range cnt, weight P F' (F.nodes.val.length + k) ≤ cnt * (nameUnit P - 1) := by
      calc ∑ k ∈ Finset.range cnt, weight P F' (F.nodes.val.length + k)
          ≤ ∑ _k ∈ Finset.range cnt, (nameUnit P - 1) := Finset.sum_le_sum (fun k _ => newWeight _)
        _ = cnt * (nameUnit P - 1) := by simp
    omega
  -- The bounds: the new one at `x`, and the old ones.
  have cappedBack : ∀ y j, Capped F' y j → Capped F y j ∨ (y = x.val ∧ j = i.val) := by
    rintro y j ⟨cap,member,node,restriction⟩
    rcases (made.caps cap).mp member with old | ⟨capNode,capRestriction,_,_⟩
    · exact .inl ⟨cap,old,node,restriction⟩
    · exact .inr ⟨by rw [← node,capNode],by rw [← restriction,capRestriction]⟩
  have cappedKept : ∀ y j, Capped F y j → Capped F' y j := by
    rintro y j ⟨cap,member,node,restriction⟩
    exact ⟨cap,(made.caps cap).mpr (.inl member),node,restriction⟩
  have cappedX : Capped F' x.val i.val := by
    obtain ⟨cap,member,node,restriction⟩ := made.capped
    exact ⟨cap,member,by rw [node],by rw [restriction]⟩
  -- The summands of the weight of the restrictions.
  let term : forest.Forest → Nat → Nat → Nat := fun G y j =>
    if Named G.nodes.val y ∧ AtMostAt P j ∧ ¬ Capped G y j then nameUnit P * nameBase P ^ (Usize.max - y) else 0
  have weightIs : ∀ G, nameWeight P G = ∑ y ∈ Finset.range G.nodes.val.length,
      ∑ j ∈ Finset.range P.entries.val.length, term G y j := fun G => rfl
  have oldTerm : ∀ y < F.nodes.val.length, ∀ j, term F' y j ≤ term F y j := by
    intro y yIn j
    simp only [term]
    by_cases cond : Named F'.nodes.val y ∧ AtMostAt P j ∧ ¬ Capped F' y j
    · rw [if_pos cond,if_pos ⟨(named_named made y yIn).mp cond.1,cond.2.1,
        fun c => cond.2.2 (cappedKept y j c)⟩]
    · rw [if_neg cond]
      exact Nat.zero_le _
  have xTerm : term F' x.val i.val + nameUnit P * nameBase P ^ (Usize.max - x.val) ≤ term F x.val i.val := by
    simp only [term]
    rw [if_neg (fun cond => cond.2.2 cappedX),if_pos ⟨named,most,uncapped⟩]
    omega
  have oldPart : ∑ y ∈ Finset.range F.nodes.val.length, ∑ j ∈ Finset.range P.entries.val.length, term F' y j +
      nameUnit P * nameBase P ^ (Usize.max - x.val) ≤
      ∑ y ∈ Finset.range F.nodes.val.length, ∑ j ∈ Finset.range P.entries.val.length, term F y j := by
    apply sum_drop _ x.val _ xIn
    · intro y yIn
      exact Finset.sum_le_sum (fun j _ => oldTerm y yIn j)
    · exact sum_drop _ i.val _ iIn _ _ (fun j _ => oldTerm x.val xIn j) xTerm
  -- Every new node is later than `x`, so its restrictions weigh less.
  have smaller : ∀ y, x.val < y → nameUnit P * nameBase P ^ (Usize.max - y) ≤
      nameUnit P * nameBase P ^ (Usize.max - x.val - 1) := by
    intro y later
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right positive (by omega)
  have newPart : ∑ k ∈ Finset.range cnt, ∑ j ∈ Finset.range P.entries.val.length,
      term F' (F.nodes.val.length + k) j ≤
      cnt * (P.entries.val.length * (nameUnit P * nameBase P ^ (Usize.max - x.val - 1))) := by
    calc ∑ k ∈ Finset.range cnt, ∑ j ∈ Finset.range P.entries.val.length, term F' (F.nodes.val.length + k) j
        ≤ ∑ _k ∈ Finset.range cnt, ∑ _j ∈ Finset.range P.entries.val.length,
            nameUnit P * nameBase P ^ (Usize.max - x.val - 1) := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro j _
          simp only [term]
          split
          · exact smaller _ (by omega)
          · exact Nat.zero_le _
      _ = cnt * (P.entries.val.length * (nameUnit P * nameBase P ^ (Usize.max - x.val - 1))) := by simp
  have nameLe : nameWeight P F' + nameUnit P * nameBase P ^ (Usize.max - x.val) ≤
      nameWeight P F + cnt * (P.entries.val.length * (nameUnit P * nameBase P ^ (Usize.max - x.val - 1))) := by
    rw [weightIs F',weightIs F,length,Finset.sum_range_add]
    omega
  -- The restriction weighs more than all the new nodes bring.
  have xBelow : x.val + 1 ≤ Usize.max := by omega
  have power : nameBase P ^ (Usize.max - x.val) = nameBase P * nameBase P ^ (Usize.max - x.val - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have unitPower : 1 ≤ nameBase P ^ (Usize.max - x.val - 1) := Nat.one_le_pow _ _ positive
  have bound : cnt * (nameUnit P - 1) + cnt * (P.entries.val.length * (nameUnit P * nameBase P ^ (Usize.max -
      x.val - 1))) < nameUnit P * nameBase P ^ (Usize.max - x.val) := by
    set M := nameUnit P * nameBase P ^ (Usize.max - x.val - 1) with hM
    have unitLe : nameUnit P - 1 ≤ M := by
      have : nameUnit P ≤ M := by
        rw [hM]
        exact Nat.le_mul_of_pos_right _ unitPower
      omega
    have mPositive : 0 < M := Nat.mul_pos unitPositive (by omega)
    have sumBound := few
    calc cnt * (nameUnit P - 1) + cnt * (P.entries.val.length * M)
        ≤ cnt * M + cnt * (P.entries.val.length * M) := by
          have := Nat.mul_le_mul_left cnt unitLe
          omega
      _ = cnt * ((P.entries.val.length + 1) * M) := by ring
      _ ≤ (P.entries.val.map atMostCount).sum * ((P.entries.val.length + 1) * M) := Nat.mul_le_mul_right _ few
      _ < ((P.entries.val.map atMostCount).sum * (P.entries.val.length + 1) + 1) * M := by
          have : (P.entries.val.map atMostCount).sum * ((P.entries.val.length + 1) * M) =
              (P.entries.val.map atMostCount).sum * (P.entries.val.length + 1) * M := by ring
          rw [this,Nat.add_mul,Nat.one_mul]
          omega
      _ = nameUnit P * nameBase P ^ (Usize.max - x.val) := by
          rw [power,hM]
          unfold nameBase
          ring
  unfold ForestInv.measure
  omega

/-- A model of the forest whose node `x` has exactly `cnt` neighbours along the
    role of the restriction `i` that satisfy its filler, given by `g`, models
    the forest with new named nodes placed on them. -/
theorem named_models {Object : Type u} {Value : Type v} {P : completion.Problem} {h : hierarchy.RoleHierarchy}
    {count : Nat} {F F' : forest.Forest} {x i : Usize} {role : ObjectPropertyExpression} {filler : Usize} {cnt : Nat}
    {deps : alloc.vec.Vec Usize} (shape : Shape P h count F) (made : NamedMade F F' x i role filler cnt deps)
    (xIn : x.val < F.nodes.val.length) {I : Interpretation Object Value} {π : Nat → Object} {D : List Usize}
    (models : Models P h F I π D) (g : Nat → Object)
    (witnesses : Sub deps.val D → (∀ k < cnt, objectRelation I role (π x.val) (g k) ∧
      denote I (meaning P.entries.val filler.val) (g k)) ∧ (∀ a < cnt, ∀ b < cnt, g a = g b → a = b))
    (bounded : Sub deps.val D → ∀ n r c c', P.entries.val[i.val]? = some (.AtMost n r c c') →
      Rowl.Owl.AtMost cnt (fun y => objectRelation I r (π x.val) y ∧ denote I (meaning P.entries.val c.val) y)) :
    ∃ π' : Nat → Object, Models P h F' I π' D := by
  let π' : Nat → Object := fun y => if y < F.nodes.val.length then π y else g (y - F.nodes.val.length)
  have old : ∀ y, y < F.nodes.val.length → π' y = π y := fun y yIn => by simp [π',yIn]
  have countIn := shape.countIn
  have length := named_length made
  refine ⟨π',models.respects,models.axioms,models.unfoldings,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro q listed
    rw [old _ (by have := shape.requirements q listed; omega)]
    exact models.requirements q listed
  · intro l listed
    have := shape.links l listed
    rw [old _ (by omega),old _ (by omega)]
    exact models.links l listed
  · intro a sub
    rw [named_rep made a] at sub ⊢
    by_cases aIn : a.val < F.same.val.length
    · have repIn := active_inside (rep_in shape a (by rw [← shape.sameLength]; exact aIn)).2
      rw [named_deps made,if_pos repIn] at sub
      rw [old _ (by rw [shape.sameLength] at aIn; omega),old _ repIn]
      exact models.same a sub
    · have same : rep F a = a := by
        simp [rep,List.getElem?_eq_none_iff.mpr (show F.same.val.length ≤ a.val by omega)]
      rw [same]
  · intro y sub j listed
    rw [named_label made y] at listed
    split at listed
    · rename_i yIn
      rw [named_deps made,if_pos yIn] at sub
      rw [old y yIn]
      exact models.labels y sub j listed
    · cases listed
  · intro y n' at_y' tree sub
    rcases named_lookup made y n' at_y' with ⟨yIn,at_y⟩ | ⟨_,_,rfl⟩
    · have parentIn := shape.parents y n' at_y tree
      rw [old y yIn,old _ (by omega)]
      exact models.tree y n' at_y tree sub
    · cases tree
  · intro e member sub
    rcases made.edges e member with oldEdge | ⟨roleIs,fromX,low,high,depsIs⟩
    · obtain ⟨toIn,fromCases⟩ := shape.edges e oldEdge
      have fromIn : e.from.val < F.nodes.val.length := by
        rcases fromCases with namedFrom | ⟨n,at_n,_⟩
        · exact namedEnd_inside shape namedFrom
        · exact (List.getElem?_eq_some_iff.mp at_n).1
      rw [old _ fromIn,old _ (namedEnd_inside shape toIn)]
      exact models.edges e oldEdge sub
    · rw [depsIs] at sub
      obtain ⟨each,_⟩ := witnesses sub
      rw [fromX,roleIs,old _ xIn]
      simp only [π',show ¬ e.to.val < F.nodes.val.length by omega,if_false]
      exact (each _ (by omega)).1
  · intro d listed sub
    rcases (made.distinct d).mp listed with oldFact | ⟨low,less,high,depsIs⟩
    · have := shape.distinctIn d oldFact
      rw [old _ this.1,old _ this.2]
      exact models.distinct d oldFact sub
    · rw [depsIs] at sub
      obtain ⟨_,injective⟩ := witnesses sub
      simp only [π',show ¬ d.left.val < F.nodes.val.length by omega,
        show ¬ d.right.val < F.nodes.val.length by omega,if_false]
      intro same
      have := injective _ (by omega) _ (by omega) same
      omega
  · intro y n' at_y' isNamed beyond sub
    rw [made.same] at beyond
    rcases named_lookup made y n' at_y' with ⟨yIn,at_y⟩ | ⟨low,high,rfl⟩
    · rw [old y yIn]
      exact models.seeds y n' at_y isNamed beyond sub
    · obtain ⟨each,_⟩ := witnesses sub
      simp only [π',show ¬ y < F.nodes.val.length by omega,if_false]
      exact (each _ (by omega)).2
  · intro cap member sub
    rcases (made.caps cap).mp member with oldCap | ⟨node,restriction,boundIs,depsIs⟩
    · have capIn := shape.capsIn cap oldCap
      intro n r c c' at_i
      have := models.caps cap oldCap sub n r c c' at_i
      rw [old _ capIn]
      exact this
    · rw [depsIs] at sub
      intro n r c c' at_i
      rw [restriction] at at_i
      rw [boundIs,node,old _ xIn]
      exact bounded sub n r c c' at_i

end Rowl.ForestSteps
