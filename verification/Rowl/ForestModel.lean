import Rowl.Forest

/-!
The model of a complete completion forest, independent of how the forest was
built: its unravelling under pairwise blocking. The elements are the paths from
an active named node through active children, newest first, where a blocked
child stands for the node above it whose pair it repeats. A named class holds
where the label of a path's newest node lists it; an object property relates a
path to its extensions along the roles of the child's edge, back to its prefix
along the inverses, and named nodes along links and added edges, closed under
the transitive roles it includes. Every neighbour of a node in the forest
corresponds to exactly one neighbour path with the same label, so when the
forest is complete, every path satisfies every entry its label satisfies,
including the number restrictions on simple roles, and the model respects the
role hierarchy and satisfies the TBox concept, the unfoldings, the
requirements and the links.
-/
namespace Rowl.ForestModel
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv denote negate_correct)
open Rowl.Hierarchy (Below Closed Respects transitives below_refl respects_below)
open Rowl.ConceptTable (WellFormed meaning meaning_at rebuild parts TransitiveClosed Complements)
open Rowl.CompletionSearch (Holds Complementary HasAtom EdgeOk EdgeNeeds HasUniversal SameLabel)
open Rowl.CompletionModel (holds_same edgeOk_same edgeOk_mono below_inv_iff)
open Rowl.ForestSearch
open Rowl.ForestOps
open Rowl.ForestInv
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

/-! ### Blocking along tree paths -/

/-- Blocking passes down tree paths: a node is blocked when a tree node above it is. -/
theorem blocked_down (nodes : List forest.Node) :
    ∀ w v, v ∈ treePath nodes w → Blocked nodes v → Blocked nodes w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v member blocked
    rw [treePath.eq_def] at member
    cases at_w : nodes[w]? with
    | none => rw [at_w] at member; cases member
    | some n =>
      rw [at_w] at member
      simp only at member
      by_cases tree : n.tree = true
      · rw [if_pos tree] at member
        by_cases below : n.parent.val < w
        · rw [dif_pos below] at member
          rcases List.mem_cons.mp member with rfl | later
          · exact blocked
          · have parentBlocked := ih n.parent.val below v later blocked
            rw [Blocked.eq_def,at_w]
            simp only [dif_pos below]
            exact ⟨tree,.inr parentBlocked⟩
        · rw [dif_neg below] at member
          simp only [List.mem_singleton] at member
          subst member
          exact blocked
      · rw [if_neg tree] at member
        cases member

/-- A node that is not a tree node is never blocked. -/
theorem named_free (nodes : List forest.Node) (a : Nat) (n : forest.Node) (at_a : nodes[a]? = some n)
    (named : n.tree = false) : ¬ Blocked nodes a := by
  rw [Blocked.eq_def,at_a]
  simp only
  split
  · rintro ⟨isTree,_⟩; rw [named] at isTree; cases isTree
  · exact id

/-- A tree child of an unblocked node is blocked exactly when it repeats the pair
    of a node on its parent's path. -/
theorem child_blocked (nodes : List forest.Node) (z : Nat) (n : forest.Node) (at_z : nodes[z]? = some n)
    (tree : n.tree = true) (below : n.parent.val < z) (free : ¬ Blocked nodes n.parent.val) :
    Blocked nodes z ↔ ∃ v ∈ treePath nodes n.parent.val, SamePair nodes z v := by
  rw [Blocked.eq_def,at_z]
  simp only [dif_pos below]
  constructor
  · rintro ⟨_,found | blocked⟩
    · exact found
    · exact absurd blocked free
  · intro found
    exact ⟨tree,.inl found⟩

/-- Every node on the tree path of an active node is active. -/
theorem treePath_active {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) : ∀ w v, Active F.nodes.val w → v ∈ treePath F.nodes.val w → Active F.nodes.val v := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v active member
    rw [treePath.eq_def] at member
    cases at_w : F.nodes.val[w]? with
    | none => rw [at_w] at member; cases member
    | some n =>
      rw [at_w] at member
      simp only at member
      by_cases tree : n.tree = true
      · rw [if_pos tree] at member
        by_cases below : n.parent.val < w
        · rw [dif_pos below] at member
          rcases List.mem_cons.mp member with rfl | later
          · exact active
          · obtain ⟨m,at_w',act⟩ := active
            rw [at_w] at at_w'
            simp only [Option.some.injEq] at at_w'
            subst at_w'
            exact ih n.parent.val below v (shape.activeParents w n at_w tree act) later
        · rw [dif_neg below] at member
          simp only [List.mem_singleton] at member
          subst member
          exact active
      · rw [if_neg tree] at member
        cases member

/-! ### Paths -/

/-- The parent of a node; zero out of range. -/
def parentOf (nodes : List forest.Node) (z : Nat) : Nat :=
  match nodes[z]? with
  | some n => n.parent.val
  | none => 0

/-- The node a child stands for in the unravelling: a node on its parent's path
    whose pair it repeats, when there is one, else the child itself. -/
noncomputable def holder (nodes : List forest.Node) (z : Nat) : Nat :=
  if found : ∃ v ∈ treePath nodes (parentOf nodes z), SamePair nodes z v then Classical.choose found else z

theorem holder_found (nodes : List forest.Node) (z : Nat)
    (found : ∃ v ∈ treePath nodes (parentOf nodes z), SamePair nodes z v) :
    holder nodes z ∈ treePath nodes (parentOf nodes z) ∧ SamePair nodes z (holder nodes z) := by
  unfold holder
  rw [dif_pos found]
  exact Classical.choose_spec found

theorem holder_free (nodes : List forest.Node) (z : Nat)
    (absent : ¬ ∃ v ∈ treePath nodes (parentOf nodes z), SamePair nodes z v) : holder nodes z = z := by
  unfold holder
  rw [dif_neg absent]

/-- The paths of the unravelling, newest pair first: an active named node, then
    for every active child of the newest node, the node it stands for and the
    child. -/
inductive IsPath (count : Nat) (nodes : List forest.Node) : List (Nat × Nat) → Prop
  | root (a : Nat) (named : a < count) (active : Active nodes a) : IsPath count nodes [(a,a)]
  | child (x x0 : Nat) (rest : List (Nat × Nat)) (z : Nat) (n : forest.Node) :
      IsPath count nodes ((x,x0) :: rest) → nodes[z]? = some n → n.tree = true → n.active = true →
      n.parent.val = x → IsPath count nodes ((holder nodes z,z) :: (x,x0) :: rest)

/-- The elements of the model. -/
abbrev Element (count : Nat) (nodes : List forest.Node) := {p : List (Nat × Nat) // IsPath count nodes p}

/-- The node a path ends in. -/
def tailOf : List (Nat × Nat) → Nat
  | (x,_) :: _ => x
  | [] => 0

/-- The label of an element: the label of its newest node. -/
def lab {count : Nat} {nodes : List forest.Node} (p : Element count nodes) : List Usize :=
  labelOf nodes (tailOf p.val)

/-- The newest node of a path is active and unblocked. A path of one pair is a
    named node; a longer path's newest pair is an active child of the previous
    node and the node it stands for, a tree node with the same label, the same
    roles and a parent with the same label as the previous node. -/
theorem path_shape {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) : ∀ p, IsPath count F.nodes.val p → ∃ x x0 rest, p = (x,x0) :: rest ∧
      Active F.nodes.val x ∧ ¬ Blocked F.nodes.val x ∧
      ((rest = [] ∧ x0 = x ∧ x < count) ∨
       (∃ w w0 rest', rest = (w,w0) :: rest' ∧ ∃ n0 : forest.Node, F.nodes.val[x0]? = some n0 ∧
          n0.tree = true ∧ n0.active = true ∧ n0.parent.val = w ∧ x = holder F.nodes.val x0 ∧
          ∃ nx : forest.Node, F.nodes.val[x]? = some nx ∧ nx.tree = true ∧
            SameLabel n0.label.val nx.label.val ∧ (∀ s, s ∈ n0.roles.val ↔ s ∈ nx.roles.val) ∧
            SameLabel (labelOf F.nodes.val w) (labelOf F.nodes.val nx.parent.val))) := by
  have shape := inv.shape
  intro p path
  induction path with
  | root a named active =>
    obtain ⟨n,at_a,_⟩ := active
    have root : n.tree = false := (shape.named a n at_a).mpr named
    exact ⟨a,a,[],rfl,⟨n,at_a,by assumption⟩,named_free _ a n at_a root,.inl ⟨rfl,rfl,named⟩⟩
  | child x x0 rest z n _ at_z tree act parent ih =>
    obtain ⟨x1,x01,rest1,same,activeX,freeX,_⟩ := ih
    simp only [List.cons.injEq,Prod.mk.injEq] at same
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := same
    have below : n.parent.val < z := shape.parents z n at_z tree
    have parentIs : parentOf F.nodes.val z = x := by simp [parentOf,at_z,parent]
    have freeParent : ¬ Blocked F.nodes.val n.parent.val := by rw [parent]; exact freeX
    by_cases found : ∃ v ∈ treePath F.nodes.val (parentOf F.nodes.val z), SamePair F.nodes.val z v
    · obtain ⟨onPath,pair⟩ := holder_found F.nodes.val z found
      rw [parentIs] at onPath
      obtain ⟨nz,nv,at_z',at_v,_,_,sameLabel,sameParent,sameRoles⟩ := pair
      rw [at_z] at at_z'
      simp only [Option.some.injEq] at at_z'
      subst at_z'
      obtain ⟨nv',at_v',vTree⟩ := treePath_mem F.nodes.val x _ onPath
      rw [at_v] at at_v'
      simp only [Option.some.injEq] at at_v'
      subst at_v'
      refine ⟨holder F.nodes.val z,z,(x,x0) :: rest,rfl,treePath_active shape x _ activeX onPath,
        fun blocked => freeX (blocked_down F.nodes.val x _ onPath blocked),
        .inr ⟨x,x0,rest,rfl,n,at_z,tree,act,parent,rfl,nv,at_v,vTree,sameLabel,sameRoles,?_⟩⟩
      rw [← parent]
      exact sameParent
    · have holderIs := holder_free F.nodes.val z found
      have free : ¬ Blocked F.nodes.val z := by
        rw [child_blocked F.nodes.val z n at_z tree below freeParent]
        rw [parentIs] at found
        rw [parent]
        exact found
      rw [holderIs]
      refine ⟨z,z,(x,x0) :: rest,rfl,⟨n,at_z,act⟩,free,
        .inr ⟨x,x0,rest,rfl,n,at_z,tree,act,parent,holderIs.symm,n,at_z,tree,fun _ => Iff.rfl,
          fun _ => Iff.rfl,by rw [parent]; exact fun _ => Iff.rfl⟩⟩

/-- The prefix of a longer path is a path. -/
theorem path_tail {count : Nat} {nodes : List forest.Node} (a b : Nat × Nat) (rest : List (Nat × Nat))
    (path : IsPath count nodes (a :: b :: rest)) : IsPath count nodes (b :: rest) := by
  cases path with
  | child x x0 rest z n earlier _ _ _ _ => exact earlier

/-- A path's newest pair beyond the root is an active tree child of the
    previous node, and the node it stands for. -/
theorem path_step {count : Nat} {nodes : List forest.Node} (a b : Nat × Nat) (rest : List (Nat × Nat))
    (path : IsPath count nodes (a :: b :: rest)) : ∃ n : forest.Node, nodes[a.2]? = some n ∧ n.tree = true ∧
      n.active = true ∧ n.parent.val = b.1 ∧ a.1 = holder nodes a.2 := by
  cases path with
  | child x x0 rest z n _ at_z tree act parent => exact ⟨n,at_z,tree,act,parent,rfl⟩

/-- The facts of a path beyond its root: its newest pair is an active tree child
    of the previous node and the node it stands for, a tree node with the same
    label and roles, whose parent has the label of the previous node. -/
theorem extension_facts {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (a b : Nat × Nat) (rest : List (Nat × Nat))
    (path : IsPath count F.nodes.val (a :: b :: rest)) :
    ∃ n0 nx : forest.Node, F.nodes.val[a.2]? = some n0 ∧ n0.tree = true ∧ n0.active = true ∧ n0.parent.val = b.1 ∧
      a.1 = holder F.nodes.val a.2 ∧ F.nodes.val[a.1]? = some nx ∧ nx.tree = true ∧
      SameLabel (labelOf F.nodes.val a.2) (labelOf F.nodes.val a.1) ∧ (∀ s, s ∈ n0.roles.val ↔ s ∈ nx.roles.val) ∧
      SameLabel (labelOf F.nodes.val b.1) (labelOf F.nodes.val nx.parent.val) := by
  obtain ⟨x,x0,rest',same,_,_,cases⟩ := path_shape inv _ path
  simp only [List.cons.injEq] at same
  obtain ⟨rfl,rfl⟩ := same
  rcases cases with ⟨empty,_,_⟩ | ⟨w,w0,rest'',bIs,n0,at_x0,tree0,act0,parent0,holderIs,nx,at_x,treeX,sameLabel,
      sameRoles,sameParent⟩
  · cases empty
  · simp only [List.cons.injEq] at bIs
    obtain ⟨rfl,rfl⟩ := bIs
    refine ⟨n0,nx,at_x0,tree0,act0,parent0,holderIs,at_x,treeX,?_,sameRoles,sameParent⟩
    simp only [labelOf,at_x0,at_x]
    exact sameLabel

/-- The facts of a root path. -/
theorem root_facts {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (a : Nat × Nat) (path : IsPath count F.nodes.val [a]) :
    a.2 = a.1 ∧ a.1 < count ∧ Active F.nodes.val a.1 := by
  obtain ⟨x,x0,rest,same,active,_,cases⟩ := path_shape inv _ path
  simp only [List.cons.injEq] at same
  obtain ⟨rfl,rfl⟩ := same
  rcases cases with ⟨_,same,named⟩ | ⟨w,w0,rest',empty,_⟩
  · exact ⟨same,named,active⟩
  · cases empty

theorem tailOf_cons (a : Nat × Nat) (rest : List (Nat × Nat)) : tailOf (a :: rest) = a.1 := rfl

/-! ### The model -/

/-- One step along a role: from a path to its extension along a role of the
    child's edge included in the role, back from an extension to its prefix
    along a role of the child's edge whose inverse is included, and between
    named nodes along a link or an added edge. -/
def Step (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (count : Nat)
    (r : ObjectPropertyExpression) (p q : Element count F.nodes.val) : Prop :=
  (∃ z z', q.val = (z,z') :: p.val ∧ ∃ n : forest.Node, F.nodes.val[z']? = some n ∧
    ∃ s ∈ n.roles.val, Below h s r) ∨
  (∃ x x', p.val = (x,x') :: q.val ∧ ∃ n : forest.Node, F.nodes.val[x']? = some n ∧
    ∃ s ∈ n.roles.val, Below h (inv s) r) ∨
  (∃ a b, p.val = [(a,a)] ∧ q.val = [(b,b)] ∧
    (LinkAlong h F (linkEnds P.links.val) a r b ∨ LinkAlong h F (edgeEnds F.edges.val) a r b))

/-- The relation of a role: a step, or a path of steps along a transitive role
    included in it. -/
def Rel (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (count : Nat)
    (r : ObjectPropertyExpression) (p q : Element count F.nodes.val) : Prop :=
  Step P h F count r p q ∨ ∃ t ∈ transitives h, Below h t r ∧ Relation.TransGen (Step P h F count t) p q

/-- The model of a forest: a named class holds where the label lists it, and a
    named object property relates along `Rel`. -/
noncomputable def model (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (count : Nat)
    (root : Element count F.nodes.val) : Interpretation (Element count F.nodes.val) Unit where
  objectsNonempty := ⟨root⟩
  dataNonempty := ⟨()⟩
  classes k p := HasAtom P.entries.val (lab p) k
  objectProperties pr p q := Rel P h F count (.Property pr) p q
  dataProperties _ _ _ := False
  namedIndividuals _ := root
  anonymousIndividuals _ := root
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := False

theorem linkAlong_inv (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (links : List (ObjectPropertyExpression × Usize × Usize)) (r : ObjectPropertyExpression) (a b : Nat) :
    LinkAlong h F links a (inv r) b ↔ LinkAlong h F links b r a := by
  constructor
  · rintro ⟨l,member,⟨source,below,target⟩ | ⟨target,below,source⟩⟩
    · exact ⟨l,member,.inr ⟨target,(below_inv_iff h closed l.1 r).mp below,source⟩⟩
    · refine ⟨l,member,.inl ⟨source,?_,target⟩⟩
      have := (below_inv_iff h closed (inv l.1) r).mp below
      rwa [inv_inv] at this
  · rintro ⟨l,member,⟨source,below,target⟩ | ⟨target,below,source⟩⟩
    · refine ⟨l,member,.inr ⟨target,?_,source⟩⟩
      rw [below_inv_iff h closed,inv_inv]
      exact below
    · exact ⟨l,member,.inl ⟨source,(below_inv_iff h closed l.1 r).mpr below,target⟩⟩

theorem linkAlong_mono (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (links : List (ObjectPropertyExpression × Usize × Usize)) {s r : ObjectPropertyExpression} (included : Below h s r)
    (a b : Nat) : LinkAlong h F links a s b → LinkAlong h F links a r b := by
  rintro ⟨l,member,⟨source,below,target⟩ | ⟨target,below,source⟩⟩
  · exact ⟨l,member,.inl ⟨source,closed.1 _ _ _ below included,target⟩⟩
  · exact ⟨l,member,.inr ⟨target,closed.1 _ _ _ below included,source⟩⟩

theorem step_inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (count : Nat) (r : ObjectPropertyExpression) (p q : Element count F.nodes.val) :
    Step P h F count (inv r) p q ↔ Step P h F count r q p := by
  unfold Step
  constructor
  · rintro (⟨z,z',ext,n,at_z,s,sIn,below⟩ | ⟨x,x',ext,n,at_x,s,sIn,below⟩ | ⟨a,b,pa,qb,linked⟩)
    · exact .inr (.inl ⟨z,z',ext,n,at_z,s,sIn,(below_inv_iff h closed s r).mp below⟩)
    · refine .inl ⟨x,x',ext,n,at_x,s,sIn,?_⟩
      have := (below_inv_iff h closed (inv s) r).mp below
      rwa [inv_inv] at this
    · refine .inr (.inr ⟨b,a,qb,pa,?_⟩)
      rcases linked with one | two
      · exact .inl ((linkAlong_inv h closed F _ r a b).mp one)
      · exact .inr ((linkAlong_inv h closed F _ r a b).mp two)
  · rintro (⟨z,z',ext,n,at_z,s,sIn,below⟩ | ⟨x,x',ext,n,at_x,s,sIn,below⟩ | ⟨a,b,qa,pb,linked⟩)
    · refine .inr (.inl ⟨z,z',ext,n,at_z,s,sIn,?_⟩)
      rw [below_inv_iff h closed,inv_inv]
      exact below
    · exact .inl ⟨x,x',ext,n,at_x,s,sIn,(below_inv_iff h closed s r).mpr below⟩
    · refine .inr (.inr ⟨b,a,pb,qa,?_⟩)
      rcases linked with one | two
      · exact .inl ((linkAlong_inv h closed F _ r b a).mpr one)
      · exact .inr ((linkAlong_inv h closed F _ r b a).mpr two)

theorem rel_inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (count : Nat) (r : ObjectPropertyExpression) (p q : Element count F.nodes.val) :
    Rel P h F count (inv r) p q ↔ Rel P h F count r q p := by
  have path : ∀ t, Relation.TransGen (Step P h F count (inv t)) p q ↔
      Relation.TransGen (Step P h F count t) q p := by
    intro t
    have same : Function.swap (Step P h F count t) = Step P h F count (inv t) := by
      funext a b
      exact propext (step_inv P h closed F count t a b).symm
    rw [← same,Relation.transGen_swap]
  unfold Rel
  rw [step_inv P h closed F count r p q]
  apply or_congr_right
  constructor
  · rintro ⟨t,transitive,below,steps⟩
    refine ⟨inv t,closed.2.2 t transitive,(below_inv_iff h closed t r).mp below,?_⟩
    exact (path (inv t)).mp (by rwa [inv_inv])
  · rintro ⟨t,transitive,below,steps⟩
    refine ⟨inv t,closed.2.2 t transitive,?_,?_⟩
    · rw [below_inv_iff h closed,inv_inv]; exact below
    · exact (path t).mpr steps

/-- The model relates along every role expression exactly as `Rel`. -/
theorem relation_model (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (F : forest.Forest) (count : Nat) (root : Element count F.nodes.val) (r : ObjectPropertyExpression)
    (p q : Element count F.nodes.val) :
    objectRelation (model P h F count root) r p q ↔ Rel P h F count r p q := by
  cases r with
  | Property pr => rfl
  | Inverse pr =>
    show Rel P h F count (.Property pr) q p ↔ Rel P h F count (.Inverse pr) p q
    exact (rel_inv P h closed F count (.Property pr) p q).symm

theorem step_mono (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (count : Nat) {s r : ObjectPropertyExpression} (included : Below h s r) (p q : Element count F.nodes.val) :
    Step P h F count s p q → Step P h F count r p q := by
  rintro (⟨z,z',ext,n,at_z,s',sIn,below⟩ | ⟨x,x',ext,n,at_x,s',sIn,below⟩ | ⟨a,b,pa,qb,linked⟩)
  · exact .inl ⟨z,z',ext,n,at_z,s',sIn,closed.1 _ _ _ below included⟩
  · exact .inr (.inl ⟨x,x',ext,n,at_x,s',sIn,closed.1 _ _ _ below included⟩)
  · refine .inr (.inr ⟨a,b,pa,qb,?_⟩)
    rcases linked with one | two
    · exact .inl (linkAlong_mono h closed F _ included a b one)
    · exact .inr (linkAlong_mono h closed F _ included a b two)

theorem rel_mono (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (count : Nat) {s r : ObjectPropertyExpression} (included : Below h s r) (p q : Element count F.nodes.val) :
    Rel P h F count s p q → Rel P h F count r p q := by
  rintro (step | ⟨t,transitive,below,steps⟩)
  · exact .inl (step_mono P h closed F count included p q step)
  · exact .inr ⟨t,transitive,closed.1 _ _ _ below included,steps⟩

theorem rel_trans (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (count : Nat) {t : ObjectPropertyExpression} (transitive : t ∈ transitives h) {p q o : Element count F.nodes.val}
    (first : Rel P h F count t p q) (second : Rel P h F count t q o) : Rel P h F count t p o := by
  have along : ∀ a b, Rel P h F count t a b → Relation.TransGen (Step P h F count t) a b := by
    intro a b
    rintro (step | ⟨t',_,below,steps⟩)
    · exact .single step
    · exact Relation.TransGen.mono (fun c d => step_mono P h closed F count below c d) steps
  exact .inr ⟨t,transitive,below_refl h t,(along p q first).trans (along q o second)⟩

/-- The model respects a closed hierarchy. -/
theorem model_respects (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (F : forest.Forest)
    (count : Nat) (root : Element count F.nodes.val) : Respects (model P h F count root) h := by
  refine ⟨?_,?_⟩
  · intro s r listed p q related
    rw [relation_model P h closed] at related ⊢
    exact rel_mono P h closed F count (.inr listed) p q related
  · intro t transitive p q o first second
    rw [relation_model P h closed] at first second ⊢
    exact rel_trans P h closed F count transitive first second

/-! ### Neighbours and steps -/

/-- `q` is the neighbour path of `p` for the neighbour `y` of `p`'s newest node:
    its extension by the child `y`, its prefix when `y` is the parent, or the
    named node `y`. -/
def Corr (nodes : List forest.Node) (p q : List (Nat × Nat)) (y : Nat) : Prop :=
  q = (holder nodes y,y) :: p ∨ (∃ x x0, p = (x,x0) :: q ∧ q ≠ [] ∧ y = parentOf nodes x) ∨
    (∃ x, p = [(x,x)] ∧ q = [(y,y)])

theorem path_nonempty {count : Nat} {nodes : List forest.Node} (p : List (Nat × Nat)) (path : IsPath count nodes p) :
    p ≠ [] := by
  cases path <;> simp

/-- Every neighbour of a path's newest node has a neighbour path with the same
    label. -/
theorem step_of_neighbour {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (p : Element count F.nodes.val) (r : ObjectPropertyExpression) (y : Nat)
    (neighbour : Neighbour P h F (tailOf p.val) r y) :
    ∃ q : Element count F.nodes.val, Step P h F count r p q ∧ SameLabel (labelOf F.nodes.val y) (lab q) ∧
      Corr F.nodes.val p.val q.val y := by
  have shape := inv.shape
  obtain ⟨x,x0,rest,pIs,_,_,cases⟩ := path_shape inv p.val p.property
  have tailIs : tailOf p.val = x := by rw [pIs]; rfl
  rw [tailIs] at neighbour
  rcases neighbour with ⟨n,at_y,tree,act,parent,s,sIn,below⟩ | ⟨n,at_x,tree,parent,s,sIn,below⟩ | linked | linked
  · -- A child: the extension.
    have path : IsPath count F.nodes.val ((holder F.nodes.val y,y) :: (x,x0) :: rest) :=
      IsPath.child x x0 rest y n (by rw [← pIs]; exact p.property) at_y tree act parent
    obtain ⟨_,_,_,_,_,_,_,_,_,sameLabel,_⟩ := extension_facts inv _ _ _ path
    rw [← pIs] at path
    exact ⟨⟨_,path⟩,.inl ⟨_,y,rfl,n,at_y,s,sIn,below⟩,sameLabel,.inl rfl⟩
  · -- The parent: the prefix.
    rcases cases with ⟨_,_,named⟩ | ⟨w,w0,rest',restIs,n0,at_x0,_,_,_,_,nx,at_x',_,_,sameRoles,sameParent⟩
    · have := (shape.named x n at_x).mpr named
      rw [tree] at this
      cases this
    · rw [at_x] at at_x'
      simp only [Option.some.injEq] at at_x'
      subst at_x'
      have tailPath : IsPath count F.nodes.val ((w,w0) :: rest') := by
        have := p.property
        rw [pIs,restIs] at this
        exact path_tail _ _ _ this
      refine ⟨⟨_,tailPath⟩,.inr (.inl ⟨x,x0,by rw [pIs,restIs],n0,at_x0,s,(sameRoles s).mpr sIn,below⟩),?_,
        .inr (.inl ⟨x,x0,by rw [pIs,restIs],by simp,by simp [parentOf,at_x,parent]⟩)⟩
      rw [← parent]
      intro i
      exact (sameParent i).symm
  all_goals
    obtain ⟨a,b,aIn,bIn,repA,repB⟩ := linkAlong_rep shape x r y (by first | exact .inl linked | exact .inr linked)
    have xRoot : x < count := by rw [← repA]; exact (rep_in shape a aIn).1
    rcases cases with ⟨restEmpty,x0Is,_⟩ | ⟨w,w0,rest',restIs,n0,_,_,_,_,_,nx,at_x,treeX,_⟩
    · have path : IsPath count F.nodes.val [(y,y)] := by
        rw [← repB]
        exact IsPath.root _ (rep_in shape b bIn).1 (rep_in shape b bIn).2
      refine ⟨⟨_,path⟩,.inr (.inr ⟨x,y,by rw [pIs,restEmpty,x0Is],rfl,?_⟩),fun _ => Iff.rfl,
        .inr (.inr ⟨x,by rw [pIs,restEmpty,x0Is],rfl⟩)⟩
      first | exact .inl linked | exact .inr linked
    · have := (shape.named x nx at_x).mpr xRoot
      rw [treeX] at this
      cases this

/-- Every neighbour path is the neighbour path of a neighbour of the newest node
    with the same label. -/
theorem neighbour_of_step {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (r : ObjectPropertyExpression) (p q : Element count F.nodes.val)
    (step : Step P h F count r p q) :
    ∃ y, Neighbour P h F (tailOf p.val) r y ∧ SameLabel (labelOf F.nodes.val y) (lab q) ∧
      Corr F.nodes.val p.val q.val y := by
  rcases step with ⟨z,z',ext,n,at_z,s,sIn,below⟩ | ⟨x,x',ext,n,at_x,s,sIn,below⟩ | ⟨a,b,pa,qb,linked⟩
  · obtain ⟨x,x0,rest,pIs,_,_,_⟩ := path_shape inv p.val p.property
    have qPath := q.property
    rw [ext,pIs] at qPath
    obtain ⟨n0,nx,at_z0,tree0,act0,parent0,holderIs,_,_,sameLabel,_,_⟩ := extension_facts inv _ _ _ qPath
    simp only at at_z0 tree0 act0 parent0 holderIs sameLabel
    rw [at_z] at at_z0
    simp only [Option.some.injEq] at at_z0
    subst at_z0
    refine ⟨z',.inl ⟨n,at_z,tree0,act0,by rw [pIs]; exact parent0,s,sIn,below⟩,?_,.inl ?_⟩
    · show SameLabel (labelOf F.nodes.val z') (labelOf F.nodes.val (tailOf q.val))
      rw [ext]
      exact sameLabel
    · rw [ext,holderIs]
  · obtain ⟨w,w0,rest,qIs,_,_,_⟩ := path_shape inv q.val q.property
    have pPath := p.property
    rw [ext,qIs] at pPath
    obtain ⟨n0,nx,at_x0,_,_,_,_,at_x',treeX,_,sameRoles,sameParent⟩ := extension_facts inv _ _ _ pPath
    simp only at at_x0 at_x' sameParent
    rw [at_x] at at_x0
    simp only [Option.some.injEq] at at_x0
    subst at_x0
    have tailIs : tailOf p.val = x := by rw [ext]; rfl
    rw [tailIs]
    refine ⟨nx.parent.val,.inr (.inl ⟨nx,at_x',treeX,rfl,s,(sameRoles s).mp sIn,below⟩),?_,
      .inr (.inl ⟨x,x',ext,by rw [qIs]; simp,by simp [parentOf,at_x']⟩)⟩
    show SameLabel (labelOf F.nodes.val nx.parent.val) (labelOf F.nodes.val (tailOf q.val))
    rw [qIs]
    intro i
    exact (sameParent i).symm
  · have tailIs : tailOf p.val = a := by rw [pa]; rfl
    rw [tailIs]
    refine ⟨b,?_,?_,.inr (.inr ⟨a,pa,qb⟩)⟩
    · rcases linked with one | two
      · exact .inr (.inr (.inl one))
      · exact .inr (.inr (.inr two))
    · show SameLabel (labelOf F.nodes.val b) (labelOf F.nodes.val (tailOf q.val))
      rw [qb]
      exact fun _ => Iff.rfl

/-- A neighbour of the newest node has only one neighbour path. -/
theorem corr_unique {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (p q q' : Element count F.nodes.val) (y : Nat)
    (one : Corr F.nodes.val p.val q.val y) (two : Corr F.nodes.val p.val q'.val y) : q = q' := by
  have shape := inv.shape
  -- A child extension's node is a tree child of the newest node.
  have childOf : ∀ (o : Element count F.nodes.val), o.val = (holder F.nodes.val y,y) :: p.val →
      ∃ n : forest.Node, F.nodes.val[y]? = some n ∧ n.tree = true ∧ n.parent.val = tailOf p.val := by
    intro o oIs
    obtain ⟨x,x0,rest,pIs,_,_,_⟩ := path_shape inv p.val p.property
    have oPath := o.property
    rw [oIs,pIs] at oPath
    obtain ⟨n,at_y,tree,_,parent,_⟩ := path_step _ _ _ oPath
    exact ⟨n,at_y,tree,by rw [pIs]; exact parent⟩
  -- A parent is below the newest node.
  have parentBelow : ∀ x x0 (o : List (Nat × Nat)), p.val = (x,x0) :: o → o ≠ [] →
      parentOf F.nodes.val x < x ∧ ∃ nx : forest.Node, F.nodes.val[x]? = some nx ∧ nx.tree = true := by
    intro x x0 o pIs nonempty
    obtain ⟨b,rest,rfl⟩ : ∃ b rest, o = b :: rest := by
      cases o with
      | nil => exact absurd rfl nonempty
      | cons b rest => exact ⟨b,rest,rfl⟩
    have pPath := p.property
    rw [pIs] at pPath
    obtain ⟨_,nx,_,_,_,_,_,at_x,treeX,_⟩ := extension_facts inv _ _ _ pPath
    simp only at at_x
    refine ⟨?_,nx,at_x,treeX⟩
    simp only [parentOf,at_x]
    exact shape.parents x nx at_x treeX
  apply Subtype.ext
  rcases one with qa | ⟨x,x0,pq,qne,ya⟩ | ⟨x,px,qy⟩ <;>
    rcases two with qa' | ⟨x',x0',pq',qne',ya'⟩ | ⟨x',px',qy'⟩
  · rw [qa,qa']
  · exfalso
    obtain ⟨n,at_y,tree,parent⟩ := childOf q qa
    have tailIs : tailOf p.val = x' := by rw [pq']; rfl
    have above := shape.parents y n at_y tree
    obtain ⟨below,_⟩ := parentBelow x' x0' q'.val pq' qne'
    rw [parent,tailIs] at above
    rw [ya'] at above
    omega
  · exfalso
    obtain ⟨n,at_y,tree,_⟩ := childOf q qa
    have := (root_facts inv (y,y) (by rw [← qy']; exact q'.property)).2.1
    have root := (shape.named y n at_y).mpr this
    rw [tree] at root
    cases root
  · exfalso
    obtain ⟨n,at_y,tree,parent⟩ := childOf q' qa'
    have tailIs : tailOf p.val = x := by rw [pq]; rfl
    have above := shape.parents y n at_y tree
    obtain ⟨below,_⟩ := parentBelow x x0 q.val pq qne
    rw [parent,tailIs] at above
    rw [ya] at above
    omega
  · rw [pq] at pq'
    simp only [List.cons.injEq] at pq'
    exact pq'.2
  · exfalso
    rw [pq] at px'
    simp only [List.cons.injEq] at px'
    exact qne px'.2
  · exfalso
    obtain ⟨n,at_y,tree,_⟩ := childOf q' qa'
    have := (root_facts inv (y,y) (by rw [← qy]; exact q.property)).2.1
    have root := (shape.named y n at_y).mpr this
    rw [tree] at root
    cases root
  · exfalso
    rw [px] at pq'
    simp only [List.cons.injEq] at pq'
    exact qne' pq'.2.symm
  · rw [qy,qy']

/-- A neighbour path belongs to only one neighbour. -/
theorem corr_function {nodes : List forest.Node} (p q : List (Nat × Nat)) (y y' : Nat)
    (one : Corr nodes p q y) (two : Corr nodes p q y') : y = y' := by
  rcases one with qa | ⟨x,x0,pq,qne,ya⟩ | ⟨x,px,qy⟩ <;>
    rcases two with qa' | ⟨x',x0',pq',qne',ya'⟩ | ⟨x',px',qy'⟩
  · rw [qa] at qa'
    simp only [List.cons.injEq,Prod.mk.injEq] at qa'
    exact qa'.1.2
  · exfalso
    have := congrArg List.length qa
    rw [pq'] at this
    simp at this
    omega
  · exfalso
    rw [px',qy'] at qa
    simp at qa
  · exfalso
    have := congrArg List.length qa'
    rw [pq] at this
    simp at this
    omega
  · rw [pq] at pq'
    simp only [List.cons.injEq,Prod.mk.injEq] at pq'
    rw [ya,ya',pq'.1.1]
  · exfalso
    rw [pq] at px'
    simp only [List.cons.injEq] at px'
    exact qne px'.2
  · exfalso
    rw [px,qy] at qa'
    simp at qa'
  · exfalso
    rw [px] at pq'
    simp only [List.cons.injEq] at pq'
    exact qne' pq'.2.symm
  · rw [qy] at qy'
    simp only [List.cons.injEq,Prod.mk.injEq] at qy'
    exact qy'.1.1

/-- A step between paths gives each label what the other requires along the
    role. -/
theorem step_ok {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (complete : Complete P h F) (r : ObjectPropertyExpression)
    (p q : Element count F.nodes.val) (step : Step P h F count r p q) :
    EdgeOk P.entries.val h (lab p) r (lab q) := by
  have shape := inv.shape
  rcases step with ⟨z,z',ext,n,at_z,s,sIn,below⟩ | ⟨x,x',ext,n,at_x,s,sIn,below⟩ | ⟨a,b,pa,qb,linked⟩
  · obtain ⟨x,x0,rest,pIs,_,_,_⟩ := path_shape inv p.val p.property
    have qPath := q.property
    rw [ext,pIs] at qPath
    obtain ⟨n0,_,at_z0,tree0,act0,parent0,_,_,_,sameLabel,_,_⟩ := extension_facts inv _ _ _ qPath
    simp only at at_z0 parent0 sameLabel
    rw [at_z] at at_z0
    simp only [Option.some.injEq] at at_z0
    subst at_z0
    have parentIn : n.parent.val < F.nodes.val.length := by
      have := shape.parents z' n at_z tree0
      have := (List.getElem?_eq_some_iff.mp at_z).1
      omega
    have edge := (complete.2.1 z' n at_z tree0 act0 parentIn s sIn).1
    rw [parent0] at edge
    have labP : lab p = labelOf F.nodes.val x := by unfold lab; rw [pIs]; rfl
    have labQ : lab q = labelOf F.nodes.val z := by unfold lab; rw [ext]; rfl
    rw [labP,labQ]
    exact edgeOk_mono _ h shape.closed _ _ below (edgeOk_same _ h _ _ _ _ s (fun _ => Iff.rfl) sameLabel edge)
  · obtain ⟨w,w0,rest,qIs,_,_,_⟩ := path_shape inv q.val q.property
    have pPath := p.property
    rw [ext,qIs] at pPath
    obtain ⟨n0,_,at_x0,tree0,act0,parent0,_,_,_,sameLabel,_,_⟩ := extension_facts inv _ _ _ pPath
    simp only at at_x0 parent0 sameLabel
    rw [at_x] at at_x0
    simp only [Option.some.injEq] at at_x0
    subst at_x0
    have parentIn : n.parent.val < F.nodes.val.length := by
      have := shape.parents x' n at_x tree0
      have := (List.getElem?_eq_some_iff.mp at_x).1
      omega
    have edge := (complete.2.1 x' n at_x tree0 act0 parentIn s sIn).2
    rw [parent0] at edge
    have labP : lab p = labelOf F.nodes.val x := by unfold lab; rw [ext]; rfl
    have labQ : lab q = labelOf F.nodes.val w := by unfold lab; rw [qIs]; rfl
    rw [labP,labQ]
    exact edgeOk_mono _ h shape.closed _ _ below
      (edgeOk_same _ h _ _ _ _ (Rowl.Concepts.inv s) sameLabel (fun _ => Iff.rfl) edge)
  · have labP : lab p = labelOf F.nodes.val a := by unfold lab; rw [pa]; rfl
    have labQ : lab q = labelOf F.nodes.val b := by unfold lab; rw [qb]; rfl
    rw [labP,labQ]
    have linkOk : ∀ (links : List (ObjectPropertyExpression × Usize × Usize)),
        (∀ l ∈ links, l.2.1.val < count ∧ l.2.2.val < count) → LinksOk P.entries.val h F links →
        LinkAlong h F links a r b → EdgeOk P.entries.val h (labelOf F.nodes.val a) r (labelOf F.nodes.val b) := by
      intro links inside ok along
      have countIn := shape.countIn
      obtain ⟨l,member,⟨source,included,target⟩ | ⟨target,included,source⟩⟩ := along
      · obtain ⟨fromIn,toIn⟩ := inside l member
        have both := ok l member (by have := (rep_in shape _ fromIn).1; omega) (by have := (rep_in shape _ toIn).1; omega)
        rw [source,target] at both
        exact edgeOk_mono _ h shape.closed _ _ included both.1
      · obtain ⟨fromIn,toIn⟩ := inside l member
        have both := ok l member (by have := (rep_in shape _ fromIn).1; omega) (by have := (rep_in shape _ toIn).1; omega)
        rw [source,target] at both
        exact edgeOk_mono _ h shape.closed _ _ included both.2
    rcases linked with one | two
    · apply linkOk _ _ complete.2.2.1 one
      intro l member
      obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
      exact shape.links l0 listed
    · apply linkOk _ _ complete.2.2.2.1 two
      intro l member
      obtain ⟨e,listed,rfl⟩ := (edgeEnds_mem _ _).mp member
      exact shape.edges e listed

/-! ### The truth lemma -/

/-- The truth lemma: every path satisfies every entry its label satisfies,
    including the number restrictions, since every neighbour of a node has one
    neighbour path with the same label and number restrictions count along
    simple roles only. -/
theorem truth {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (complete : Complete P h F) (root : Element count F.nodes.val) :
    ∀ (c : Nat) (p : Element count F.nodes.val), Holds P.entries.val (lab p) c →
      denote (model P h F count root) (meaning P.entries.val c) p := by
  have shape := inv.shape
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro p holds
    obtain ⟨x,x0,rest,pIs,activeX,freeX,_⟩ := path_shape inv p.val p.property
    have tailIs : tailOf p.val = x := by rw [pIs]; rfl
    have labIs : lab p = labelOf F.nodes.val x := by unfold lab; rw [tailIs]
    rw [Holds.eq_def] at holds
    cases at_c : P.entries.val[c]? with
    | none => rw [at_c] at holds; exact holds.elim
    | some e =>
      rw [at_c] at holds
      have below := shape.wellFormed c e at_c
      rw [meaning_at P.entries.val shape.wellFormed c e at_c]
      cases e with
      | Top => trivial
      | Bottom => exact holds.elim
      | Atom k =>
        obtain ⟨i,member,value⟩ := holds
        exact ⟨i,member,by rw [value]; exact at_c⟩
      | NotAtom k =>
        obtain ⟨i,member,value⟩ := holds
        rintro ⟨j,listed,at_j⟩
        rw [labIs] at member listed
        exact shape.clashFree x i member j listed (.NotAtom k) (.Atom k) (by rw [value]; exact at_c) at_j
          (show Complementary (.NotAtom k) (.Atom k) from rfl)
      | And a b =>
        simp only at holds
        rw [dif_pos (below a.val (by simp [parts])),dif_pos (below b.val (by simp [parts]))] at holds
        exact ⟨ih a.val (below a.val (by simp [parts])) p holds.1,ih b.val (below b.val (by simp [parts])) p holds.2⟩
      | Or a b =>
        simp only at holds
        rw [dif_pos (below a.val (by simp [parts])),dif_pos (below b.val (by simp [parts]))] at holds
        rcases holds with one | two
        · exact .inl (ih a.val (below a.val (by simp [parts])) p one)
        · exact .inr (ih b.val (below b.val (by simp [parts])) p two)
      | Exists r f =>
        obtain ⟨i,member,value⟩ := holds
        have at_i : P.entries.val[i.val]? = some (.Exists r f) := by rw [value]; exact at_c
        rw [labIs] at member
        obtain ⟨list,_,longEnough,each⟩ := complete.2.2.2.2.2.2 x activeX freeX i member _ r f 1#usize at_i rfl
        obtain ⟨y,yIn⟩ : ∃ y, y ∈ list := by
          cases list with
          | nil => simp at longEnough
          | cons y _ => exact ⟨y,List.mem_cons_self ..⟩
        obtain ⟨neighbour,holdsY⟩ := each y yIn
        obtain ⟨q,step,same,_⟩ := step_of_neighbour inv p r y.val (by rw [tailIs]; exact neighbour)
        refine ⟨q,(relation_model P h shape.closed F count root r p q).mpr (.inl step),?_⟩
        exact ih f.val (below f.val (by simp [parts])) q ((holds_same _ _ _ same f.val).mp holdsY)
      | Forall r f =>
        obtain ⟨i,member,value⟩ := holds
        have at_i : P.entries.val[i.val]? = some (.Forall r f) := by rw [value]; exact at_c
        intro q related
        rw [relation_model P h shape.closed F count root r p q] at related
        apply ih f.val (below f.val (by simp [parts])) q
        rcases related with step | ⟨t,transitive,tr,steps⟩
        · exact (step_ok inv complete r p q step i member r f at_i (below_refl h r)).1
        · obtain ⟨j0,at_j0⟩ := shape.closedTable i.val r f at_i t transitive tr
          have along : ∀ o, Relation.TransGen (Step P h F count t) p o →
              Holds P.entries.val (lab o) f.val ∧ HasUniversal P.entries.val (lab o) t f := by
            intro o steps
            induction steps with
            | single step =>
              obtain ⟨holds,through⟩ := step_ok inv complete t p _ step i member r f at_i tr
              exact ⟨holds,through t transitive (below_refl h t) tr ⟨j0,at_j0⟩⟩
            | tail _ step ih' =>
              obtain ⟨_,⟨j,listed,at_j⟩⟩ := ih'
              obtain ⟨holds,through⟩ := step_ok inv complete t _ _ step j listed t f at_j (below_refl h t)
              exact ⟨holds,through t transitive (below_refl h t) (below_refl h t) ⟨j.val,at_j⟩⟩
          exact (along q steps).1
      | AtLeast m r f =>
        obtain ⟨i,member,value⟩ := holds
        have at_i : P.entries.val[i.val]? = some (.AtLeast m r f) := by rw [value]; exact at_c
        have memberX : i ∈ labelOf F.nodes.val x := by rw [← labIs]; exact member
        obtain ⟨list,nodup,longEnough,each⟩ := complete.2.2.2.2.2.2 x activeX freeX i memberX _ r f m at_i rfl
        have pick : ∀ k : Fin m.val, ∃ q : Element count F.nodes.val, Step P h F count r p q ∧
            SameLabel (labelOf F.nodes.val (list[k.val]'(Nat.lt_of_lt_of_le k.isLt longEnough)).val) (lab q) ∧
            Corr F.nodes.val p.val q.val (list[k.val]'(Nat.lt_of_lt_of_le k.isLt longEnough)).val := by
          intro k
          have inList := List.getElem_mem (l := list) (Nat.lt_of_lt_of_le k.isLt longEnough)
          exact step_of_neighbour inv p r _ (by rw [tailIs]; exact (each _ inList).1)
        choose g gStep gSame gCorr using pick
        refine ⟨g,?_,?_⟩
        · intro k1 k2 same
          have one := gCorr k1
          have two := gCorr k2
          rw [same] at one
          have values := corr_function _ _ _ _ one two
          apply Fin.ext
          exact (List.Nodup.getElem_inj_iff nodup).mp (UScalar.eq_of_val_eq values)
        · intro k
          have inList := List.getElem_mem (l := list) (Nat.lt_of_lt_of_le k.isLt longEnough)
          refine ⟨(relation_model P h shape.closed F count root r p (g k)).mpr (.inl (gStep k)),?_⟩
          exact ih f.val (below f.val (by simp [parts])) (g k)
            ((holds_same _ _ _ (gSame k) f.val).mp (each _ inList).2)
      | AtMost m r f f' =>
        obtain ⟨i,member,value⟩ := holds
        have at_i : P.entries.val[i.val]? = some (.AtMost m r f f') := by rw [value]; exact at_c
        have memberX : i ∈ labelOf F.nodes.val x := by rw [← labIs]; exact member
        simp only [rebuild,denote,Rowl.Owl.AtMost]
        rintro ⟨g,injective,each⟩
        have simple := shape.simple.2 i.val m r f f' at_i
        have steps : ∀ k, Step P h F count r p (g k) := by
          intro k
          rcases (relation_model P h shape.closed F count root r p (g k)).mp (each k).1 with step | ⟨t,transitive,tr,_⟩
          · exact step
          · exact absurd tr (simple t transitive)
        have pick : ∀ k, ∃ y : Usize, Neighbour P h F x r y.val ∧ SameLabel (labelOf F.nodes.val y.val) (lab (g k)) ∧
            Corr F.nodes.val p.val (g k).val y.val := by
          intro k
          obtain ⟨y,neighbour,same,corr⟩ := neighbour_of_step inv r p (g k) (steps k)
          rw [tailIs] at neighbour
          have yIn := neighbour_inside shape x r y neighbour
          have bounded := alloc.vec.Vec.len_ineq F.nodes
          let u : Usize := Usize.ofNatCore y (by scalar_tac)
          have value : u.val = y := UScalar.ofNatCore_val_eq _
          refine ⟨u,?_⟩
          rw [value]
          exact ⟨neighbour,same,corr⟩
        choose ys ysNeighbour ysSame ysCorr using pick
        have excess : Excess P h F x r f m := by
          refine ⟨List.ofFn ys,?_,by simp,?_⟩
          · rw [List.nodup_ofFn]
            intro k1 k2 same
            apply injective
            exact corr_unique inv p (g k1) (g k2) (ys k1).val (ysCorr k1) (by rw [same]; exact ysCorr k2)
          · intro z listed
            obtain ⟨k,rfl⟩ := List.mem_ofFn.mp listed
            refine ⟨ysNeighbour k,?_⟩
            rcases complete.2.2.2.2.1 x activeX i memberX m r f f' at_i (ys k) (ysNeighbour k) with yes | no
            · exact yes
            · exfalso
              have complementHolds := ih f'.val (below f'.val (by simp [parts])) (g k)
                ((holds_same _ _ _ (ysSame k) f'.val).mp no)
              obtain ⟨negated,negateRun,negateSpec⟩ := negate_correct.{0,0} (meaning P.entries.val f.val)
              rw [shape.complements i.val m r f f' at_i] at negateRun
              simp only [Result.ok.injEq] at negateRun
              subst negateRun
              exact (negateSpec _ rfl _ _ (model P h F count root) (g k)).mp complementHolds (each k).2
        exact complete.2.2.2.2.2.1 x activeX i memberX m r f f' at_i excess

/-! ### The model of a complete forest -/

/-- The element of an individual: the path of its representative. -/
noncomputable def place {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (root : Element count F.nodes.val) (a : Nat) : Element count F.nodes.val :=
  if found : ∃ u : Usize, u.val = a ∧ a < count then
    ⟨[((rep F (Classical.choose found)).val,(rep F (Classical.choose found)).val)],
      IsPath.root _
        (rep_in shape _ (by obtain ⟨same,inside⟩ := Classical.choose_spec found; rw [same]; exact inside)).1
        (rep_in shape _ (by obtain ⟨same,inside⟩ := Classical.choose_spec found; rw [same]; exact inside)).2⟩
  else root

theorem place_val {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (root : Element count F.nodes.val) (a : Usize) (inside : a.val < count) :
    (place shape root a.val).val = [((rep F a).val,(rep F a).val)] := by
  have found : ∃ u : Usize, u.val = a.val ∧ a.val < count := ⟨a,rfl,inside⟩
  have chosen : Classical.choose found = a := UScalar.eq_of_val_eq (Classical.choose_spec found).1
  unfold place
  rw [dif_pos found]
  show [((rep F (Classical.choose found)).val,(rep F (Classical.choose found)).val)] = _
  rw [chosen]

/-- A complete forest that keeps the invariant, with at least one individual, has
    a model in `Type` of the role hierarchy where the TBox concept and the
    unfoldings hold everywhere and every requirement and link holds at the
    elements of its individuals. -/
theorem model_of_complete {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (complete : Complete P h F) (positive : 0 < count) :
    ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
      Respects I h ∧ (∀ y, denote I (meaning P.entries.val P.axioms.val) y) ∧
      (∀ w ∈ P.unfoldings.val, ∀ y, I.classes w.class y → denote I (meaning P.entries.val w.concept.val) y) ∧
      (∀ q ∈ P.requirements.val, denote I (meaning P.entries.val q.concept.val) (π q.node.val)) ∧
      (∀ l ∈ P.links.val, objectRelation I l.role (π l.from.val) (π l.to.val)) := by
  have shape := inv.shape
  have zeroIn : (0#usize).val < count := positive
  let root : Element count F.nodes.val := ⟨[((rep F 0#usize).val,(rep F 0#usize).val)],
    IsPath.root _ (rep_in shape _ zeroIn).1 (rep_in shape _ zeroIn).2⟩
  have activeTail : ∀ p : Element count F.nodes.val, Active F.nodes.val (tailOf p.val) := by
    intro p
    obtain ⟨x,x0,rest,pIs,activeX,_,_⟩ := path_shape inv p.val p.property
    rw [pIs]
    exact activeX
  refine ⟨Element count F.nodes.val,model P h F count root,place shape root,
    model_respects P h shape.closed F count root,?_,?_,?_,?_⟩
  · intro p
    exact truth inv complete root _ p (complete.1 _ (activeTail p) P.axioms (.inr (.inl rfl)))
  · intro w member p classes
    exact truth inv complete root _ p (complete.1 _ (activeTail p) w.concept (.inr (.inr (.inl ⟨w,member,classes,rfl⟩))))
  · intro q member
    have inside := shape.requirements q member
    apply truth inv complete root
    have labIs : lab (place shape root q.node.val) = labelOf F.nodes.val (rep F q.node).val := by
      unfold lab
      rw [place_val shape root q.node inside]
      rfl
    rw [labIs]
    exact complete.1 _ (rep_in shape _ inside).2 q.concept (.inl ⟨q,member,rfl,rfl⟩)
  · intro l member
    have inside := shape.links l member
    rw [relation_model P h shape.closed F count root]
    exact .inl (.inr (.inr ⟨(rep F l.from).val,(rep F l.to).val,place_val shape root l.from inside.1,
      place_val shape root l.to inside.2,
      .inl ⟨(l.role,l.from,l.to),(linkEnds_mem _ _).mpr ⟨l,member,rfl⟩,.inl ⟨rfl,below_refl h l.role,rfl⟩⟩⟩))

/-- The completion forest decides SHIQ problems with named individuals: it
    answers unless a structure would exceed the `usize` range or a number
    restriction counts along a role that is not simple; an acceptance comes
    with a model in `Type` of the role hierarchy where the TBox concept and
    every definition hold everywhere and every fact and link holds at the
    elements of its individuals, and a rejection rules out every such model,
    in any universes. -/
theorem satisfiable_correct (count : Usize) (query facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (positive : 0 < count.val) (factsIn : ∀ f ∈ query.val ++ facts.val, f.node.val < count.val)
    (linksIn : ∀ l ∈ links.val, l.from.val < count.val ∧ l.to.val < count.val) :
    ∃ r, forest.satisfiable count query facts links axioms definitions h = .ok r ∧
      (r = some true → ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
        Respects I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) ∧
      (r = some false → ¬ ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Respects I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ query.val ++ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) := by
  obtain ⟨r,run,accepted,rejected⟩ := Rowl.Forest.satisfiable_answers.{u,v} count query facts links axioms
    definitions h closed factsIn linksIn
  refine ⟨r,run,?_,rejected⟩
  intro yes
  obtain ⟨P,F,⟨axMeaning,linksIs,corresponds,unfolds⟩,inv,complete⟩ := accepted yes
  obtain ⟨Object,I,π,respects,axiomsHold,unfoldingsHold,requirementsHold,linksHold⟩ :=
    model_of_complete inv complete positive
  refine ⟨Object,I,π,respects,?_,?_,?_,?_⟩
  · intro y
    have := axiomsHold y
    rwa [axMeaning] at this
  · intro d member y classes
    obtain ⟨w,wMember,same,means⟩ := unfolds.2 d member
    have := unfoldingsHold w wMember y (by rw [same]; exact classes)
    rwa [means] at this
  · intro f member
    obtain ⟨q,qMember,node,means⟩ := corresponds.2 f member
    have := requirementsHold q qMember
    rwa [means,node] at this
  · intro l member
    exact linksHold l (by rw [linksIs]; exact member)

end Rowl.ForestModel
