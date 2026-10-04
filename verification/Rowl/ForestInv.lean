import Rowl.ForestOps

/-!
What the completion forest's run maintains and why it ends. The invariant
keeps a well-formed table whose maximum restrictions record their complements
and count, with the complements of self restrictions, along simple roles, a
named node for every individual, each
individual read through the merges as an active named node, active tree nodes
below active parents, clash-free labels of literals without repetitions, the
expanded restrictions among the label, edge roles from a finite list, and
bounds from new named nodes on existing nodes. The measure weights each active
node by the room below it and the room left in its label and its expanded
restrictions, and every maximum restriction of a named node without a bound
from new named nodes by a weight that is the larger the earlier the node;
pairwise blocking bounds the depth of an unblocked node by the number of
different label pairs and role sets. A model of a forest under a set of branch
points places every node so that the problem holds, each individual sits where
its representative does, and the labels, tree edges, seeds, added edges,
differences and bounds hold whenever the points they depend on are in the set.
-/
namespace Rowl.ForestInv
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv inv_inv relation_inv denote)
open Rowl.Hierarchy (Below Closed Respects transitives below_refl respects_below)
open Rowl.ConceptTable (WellFormed meaning meaning_at rebuild TransitiveClosed Complements parts)
open Rowl.CompletionSearch (Holds Complementary Clashes HasAtom EdgeNeeds SameLabel)
open Rowl.Completion (Sub holds_mono holds_denote edge_need_holds label_le grow_strict sum_drop)
open Rowl.ForestSearch
open Rowl.ForestOps
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

/-- The entries a label of the forest lists: all but `⊤`, `⊥`, `⊓` and `⊔`. -/
def Literal : concept_table.Entry → Prop
  | .Atom _ | .NotAtom _ | .One _ | .NotOne _ | .HasSelf _ | .NotSelf _ | .Exists _ _ | .Forall _ _ | .AtLeast _ _ _
  | .AtMost _ _ _ _ => True
  | _ => False

/-- Every number restriction and every complement of a self restriction of the
    table is on a simple role: no transitive role is included in it. -/
def SimpleCounting (h : hierarchy.RoleHierarchy) (entries : List concept_table.Entry) : Prop :=
  (∀ (i : Nat) n r c, entries[i]? = some (.AtLeast n r c) → ∀ t ∈ transitives h, ¬ Below h t r) ∧
  (∀ (i : Nat) n r c d, entries[i]? = some (.AtMost n r c d) → ∀ t ∈ transitives h, ¬ Below h t r) ∧
  (∀ (i : Nat) r, entries[i]? = some (.NotSelf r) → ∀ t ∈ transitives h, ¬ Below h t r)

/-- The roles of an entry that creates neighbours, and their inverses. -/
def generatorRoles : concept_table.Entry → List ObjectPropertyExpression
  | .Exists r _ => [r,inv r]
  | .AtLeast _ r _ => [r,inv r]
  | _ => []

/-- The roles an edge of the forest can carry. -/
def roleList (entries : List concept_table.Entry) : List ObjectPropertyExpression :=
  entries.flatMap generatorRoles

/-- How many neighbours an entry creates. -/
def generatorCount : concept_table.Entry → Nat
  | .Exists _ _ => 1
  | .AtLeast n _ _ => n.val
  | _ => 0

/-- At least as many neighbours as any entry of the table creates at once. -/
def countSum (entries : List concept_table.Entry) : Nat := (entries.map generatorCount).sum

/-- A named node: a node of the forest that is no tree node. -/
def Named (nodes : List forest.Node) (x : Nat) : Prop := ∃ n, nodes[x]? = some n ∧ n.tree = false

/-- A tree node is no named node. -/
theorem tree_not_named {nodes : List forest.Node} {y : Nat} {n : forest.Node} (at_y : nodes[y]? = some n)
    (tree : n.tree = true) : ¬ Named nodes y := by
  rintro ⟨m,at_m,named⟩
  rw [at_y] at at_m
  cases at_m
  rw [tree] at named
  cases named

/-- An end of an added edge: an individual, read through the merges, or an
    active named node. -/
def NamedEnd (F : forest.Forest) (count x : Nat) : Prop := x < count ∨ (Named F.nodes.val x ∧ Active F.nodes.val x)

/-- The shape of a forest that the run keeps and the model needs. -/
structure Shape (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (F : forest.Forest) :
    Prop where
  wellFormed : WellFormed P.entries.val
  complements : Complements P.entries.val
  closedTable : TransitiveClosed h P.entries.val
  closed : Closed h
  simple : SimpleCounting h P.entries.val
  named : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → y < count → n.tree = false
  countIn : count ≤ F.nodes.val.length
  sameLength : F.same.val.length = count
  reps : ∀ b ∈ F.same.val, Named F.nodes.val b.val ∧ Active F.nodes.val b.val
  parents : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → n.tree = true → n.parent.val < y
  activeParents : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → n.tree = true → n.active = true →
    Active F.nodes.val n.parent.val
  links : ∀ l ∈ P.links.val, l.from.val < count ∧ l.to.val < count
  requirements : ∀ q ∈ P.requirements.val, q.node.val < count
  edges : ∀ e ∈ F.edges.val, NamedEnd F count e.to.val ∧
    (NamedEnd F count e.from.val ∨ ∃ n, F.nodes.val[e.from.val]? = some n ∧ n.tree = true)
  distinctIn : ∀ d ∈ F.distinct.val, d.left.val < F.nodes.val.length ∧ d.right.val < F.nodes.val.length
  literals : ∀ y, ∀ i ∈ labelOf F.nodes.val y, ∃ e, P.entries.val[i.val]? = some e ∧ Literal e
  clashFree : ∀ y, ∀ i ∈ labelOf F.nodes.val y, ∀ j ∈ labelOf F.nodes.val y, ∀ e e',
    P.entries.val[i.val]? = some e → P.entries.val[j.val]? = some e' → ¬ Complementary e e'
  capsIn : ∀ cap ∈ F.caps.val, cap.node.val < F.nodes.val.length

/-- What the run maintains: the shape, labels and expanded restrictions without
    repetitions, the expanded restrictions among the label, and edge roles from
    the role list. -/
structure Inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (F : forest.Forest) :
    Prop where
  shape : Shape P h count F
  nodup : ∀ y, (labelOf F.nodes.val y).Nodup
  doneNodup : ∀ y, (doneOf F.nodes.val y).Nodup
  doneIn : ∀ y, ∀ i ∈ doneOf F.nodes.val y, i ∈ labelOf F.nodes.val y
  roles : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → ∀ s ∈ n.roles.val, s ∈ roleList P.entries.val

/-- The number of tree nodes on the path from `y` up to its root. -/
def depth (F : forest.Forest) (y : Nat) : Nat := (treePath F.nodes.val y).length

/-- The number of different labels, parents' labels and role sets. -/
def bound (P : completion.Problem) : Nat :=
  2 ^ P.entries.val.length * 2 ^ P.entries.val.length * 2 ^ (roleList P.entries.val).length

/-- The base of the weights: more than the weight of the children one
    restriction creates. -/
def base (P : completion.Problem) : Nat := (countSum P.entries.val + 1) * (2 * P.entries.val.length + 2)

/-- The room left in a node: `2n + 1` minus its label and its expanded
    restrictions. -/
def factor (P : completion.Problem) (F : forest.Forest) (y : Nat) : Nat :=
  2 * P.entries.val.length + 1 - (labelOf F.nodes.val y).length - (doneOf F.nodes.val y).length

/-- The weight of an active node: the room below it times the room in it. -/
noncomputable def weight (P : completion.Problem) (F : forest.Forest) (y : Nat) : Nat :=
  if Active F.nodes.val y then base P ^ (bound P + 2 - depth F y) * factor P F y else 0

/-- The weight of the tree: the sum of the weights of the nodes. -/
noncomputable def treeMeasure (P : completion.Problem) (F : forest.Forest) : Nat :=
  ∑ y ∈ Finset.range F.nodes.val.length, weight P F y

/-- The table entry `i` is a maximum restriction. -/
def AtMostAt (P : completion.Problem) (i : Nat) : Prop := ∃ n r c c', P.entries.val[i]? = some (.AtMost n r c c')

/-- The restriction `i` of node `y` has a bound from new named nodes. -/
def Capped (F : forest.Forest) (y i : Nat) : Prop := ∃ cap ∈ F.caps.val, cap.node.val = y ∧ cap.restriction.val = i

/-- The bound of a maximum restriction. -/
def atMostCount : concept_table.Entry → Nat
  | .AtMost n _ _ _ => n.val
  | _ => 0

/-- More than the weight that a new named node brings to the tree. -/
def nameUnit (P : completion.Problem) : Nat := base P ^ (bound P + 2) * (2 * P.entries.val.length + 1) + 1

/-- More than the number of new named nodes for one restriction times the
    number of restrictions of the table, each of which may get its own. -/
def nameBase (P : completion.Problem) : Nat := (P.entries.val.map atMostCount).sum * (P.entries.val.length + 1) + 1

/-- The weight of the maximum restrictions of named nodes without a bound from
    new named nodes yet: the earlier the node, the heavier, so that new named
    nodes for one restriction weigh less than the restriction did. -/
noncomputable def nameWeight (P : completion.Problem) (F : forest.Forest) : Nat :=
  ∑ y ∈ Finset.range F.nodes.val.length, ∑ i ∈ Finset.range P.entries.val.length,
    if Named F.nodes.val y ∧ AtMostAt P i ∧ ¬ Capped F y i then nameUnit P * nameBase P ^ (Usize.max - y) else 0

/-- The termination measure: the weight of the tree and of the restrictions that
    may still get new named nodes. -/
noncomputable def measure (P : completion.Problem) (F : forest.Forest) : Nat := treeMeasure P F + nameWeight P F

/-- `F'` grows `F`: the same nodes, edges, differences and representatives,
    with every old label contained in the new one. -/
def Grows (F F' : forest.Forest) : Prop :=
  F'.nodes.val.length = F.nodes.val.length ∧ F'.edges = F.edges ∧ F'.distinct = F.distinct ∧ F'.same = F.same ∧
  F'.caps = F.caps ∧ ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → ∃ n' : forest.Node, F'.nodes.val[y]? = some n' ∧
    n'.parent = n.parent ∧ n'.roles = n.roles ∧ n'.seed = n.seed ∧ n'.tree = n.tree ∧ n'.active = n.active ∧
    n'.done = n.done ∧ ∀ i ∈ n.label.val, i ∈ n'.label.val

/-- A bound from new named nodes holds at the element of its node: at most
    `bound` neighbours along the role of its restriction satisfy the filler. -/
def CapHolds {Object : Type u} {Value : Type v} (entries : List concept_table.Entry)
    (I : Interpretation Object Value) (π : Nat → Object) (cap : forest.Cap) : Prop :=
  ∀ n r c c', entries[cap.restriction.val]? = some (.AtMost n r c c') →
    Rowl.Owl.AtMost cap.bound.val
      (fun y => objectRelation I r (π cap.node.val) y ∧ denote I (meaning entries c.val) y)

/-- An interpretation with a placement of every node that holds under the branch
    points `D`: it respects the role hierarchy, the TBox concept and the
    unfoldings hold everywhere, every requirement and link holds for the
    individuals, each individual sits where its representative does, and the
    labels, tree edges and seeds, the seeds of new named nodes, added edges,
    differences and bounds from new named nodes hold when the points they
    depend on are in `D`. -/
structure Models {Object : Type u} {Value : Type v} (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (F : forest.Forest) (I : Interpretation Object Value) (π : Nat → Object) (D : List Usize) : Prop where
  respects : Respects I h
  axioms : ∀ z, denote I (meaning P.entries.val P.axioms.val) z
  unfoldings : ∀ w ∈ P.unfoldings.val, ∀ z, I.classes w.class z → denote I (meaning P.entries.val w.concept.val) z
  requirements : ∀ q ∈ P.requirements.val, denote I (meaning P.entries.val q.concept.val) (π q.node.val)
  links : ∀ l ∈ P.links.val, objectRelation I l.role (π l.from.val) (π l.to.val)
  same : ∀ a : Usize, Sub (nodeDeps F (rep F a).val) D → π a.val = π (rep F a).val
  labels : ∀ y, Sub (nodeDeps F y) D → ∀ i ∈ labelOf F.nodes.val y, denote I (meaning P.entries.val i.val) (π y)
  tree : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → n.tree = true → Sub n.deps.val D →
    (∀ s ∈ n.roles.val, objectRelation I s (π n.parent.val) (π y)) ∧
      denote I (meaning P.entries.val n.seed.val) (π y)
  edges : ∀ e ∈ F.edges.val, Sub e.deps.val D → objectRelation I e.role (π e.from.val) (π e.to.val)
  distinct : ∀ d ∈ F.distinct.val, Sub d.deps.val D → π d.left.val ≠ π d.right.val
  seeds : ∀ (y : Nat) (n : forest.Node), F.nodes.val[y]? = some n → n.tree = false → F.same.val.length ≤ y →
    Sub n.deps.val D → denote I (meaning P.entries.val n.seed.val) (π y)
  caps : ∀ cap ∈ F.caps.val, Sub cap.deps.val D → CapHolds P.entries.val I π cap

/-- A model of the forest, in any universes, that also has the extra entries at
    node `x` when the points `deps` are in `D`. -/
def FullModel (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (extra deps D : List Usize) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
    Models P h F I π D ∧ (Sub deps D → ∀ c ∈ extra, denote I (meaning P.entries.val c.val) (π x))

/-- Every branch point the forest depends on is below `fresh`. -/
def FreshForest (F : forest.Forest) (fresh : Nat) : Prop :=
  (∀ y, ∀ k ∈ nodeDeps F y, k.val < fresh) ∧ (∀ e ∈ F.edges.val, ∀ k ∈ e.deps.val, k.val < fresh) ∧
  (∀ d ∈ F.distinct.val, ∀ k ∈ d.deps.val, k.val < fresh) ∧ (∀ cap ∈ F.caps.val, ∀ k ∈ cap.deps.val, k.val < fresh)

/-- What a run of the forest means: an acceptance comes with a complete forest
    that keeps the invariant, and a rejection with a set of branch points below
    `fresh` rules out every model, in any universes, that holds under those
    points, with the extra entries, depending on `deps`, at node `x`. -/
def Answers (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (F : forest.Forest) (x : Nat)
    (extra deps : List Usize) (fresh : Nat) (r : Option completion.Outcome) : Prop :=
  (r = some .Accepted → ∃ F' : forest.Forest, Inv P h count F' ∧ Complete P h F') ∧
  (∀ D : alloc.vec.Vec Usize, r = some (.Rejected D) → (∀ k ∈ D.val, k.val < fresh) ∧
    ¬ FullModel.{u,v} P h F x extra deps D.val)

/-! ### Basic facts -/

theorem labels_in {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) : ∀ y, ∀ i ∈ labelOf F.nodes.val y, i.val < P.entries.val.length := by
  intro y i member
  obtain ⟨e,at_i,_⟩ := shape.literals y i member
  exact (List.getElem?_eq_some_iff.mp at_i).1

theorem done_in {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) : ∀ y, ∀ i ∈ doneOf F.nodes.val y, i.val < P.entries.val.length :=
  fun y i member => labels_in inv.shape y i (inv.doneIn y i member)

theorem label_length {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (y : Nat) : (labelOf F.nodes.val y).length ≤ P.entries.val.length :=
  label_le _ _ (inv.nodup y) (labels_in inv.shape y)

theorem done_length {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (y : Nat) : (doneOf F.nodes.val y).length ≤ P.entries.val.length :=
  label_le _ _ (inv.doneNodup y) (done_in inv y)

theorem complementary_symm (a b : concept_table.Entry) : Complementary a b → Complementary b a := by
  cases a <;> cases b <;> simp [Complementary] <;> intro same <;> exact same.symm

theorem complementary_irrefl (e : concept_table.Entry) : ¬ Complementary e e := by
  cases e <;> simp [Complementary]

theorem inv_listed (entries : List concept_table.Entry) (s : ObjectPropertyExpression)
    (listed : s ∈ roleList entries) : inv s ∈ roleList entries := by
  unfold roleList at listed ⊢
  rw [List.mem_flatMap] at listed ⊢
  obtain ⟨e,member,there⟩ := listed
  refine ⟨e,member,?_⟩
  cases e <;> simp only [generatorRoles,List.mem_cons,List.not_mem_nil,or_false] at there ⊢
  all_goals
    rcases there with rfl | rfl
    · exact .inr rfl
    · exact .inl (inv_inv _)

theorem generator_listed (entries : List concept_table.Entry) (i : Nat) (e : concept_table.Entry)
    (at_i : entries[i]? = some e) (role : ObjectPropertyExpression) (c n : Usize)
    (gen : generatorOf e = some (role,n,c)) : role ∈ roleList entries := by
  unfold roleList
  rw [List.mem_flatMap]
  refine ⟨e,List.mem_of_getElem? at_i,?_⟩
  cases e <;> simp only [generatorOf,reduceCtorEq,Option.some.injEq,Prod.mk.injEq] at gen
  · obtain ⟨rfl,_,_⟩ := gen
    simp [generatorRoles]
  · obtain ⟨rfl,_,_⟩ := gen
    simp [generatorRoles]

theorem generator_count_le (entries : List concept_table.Entry) (i : Nat) (e : concept_table.Entry)
    (at_i : entries[i]? = some e) (role : ObjectPropertyExpression) (c n : Usize)
    (gen : generatorOf e = some (role,n,c)) : n.val ≤ countSum entries := by
  have counted : n.val = generatorCount e := by
    cases e <;> simp only [generatorOf,reduceCtorEq,Option.some.injEq,Prod.mk.injEq] at gen
    · obtain ⟨_,rfl,_⟩ := gen
      rfl
    · obtain ⟨_,rfl,_⟩ := gen
      rfl
  rw [counted]
  unfold countSum
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨e,List.mem_of_getElem? at_i,rfl⟩)

/-! ### Neighbours -/

/-- Every individual is read through the merges as an active named node. -/
theorem rep_in {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (a : Usize) (aIn : a.val < count) :
    Named F.nodes.val (rep F a).val ∧ Active F.nodes.val (rep F a).val := by
  have inside : a.val < F.same.val.length := by rw [shape.sameLength]; exact aIn
  have repIs : rep F a = F.same.val[a.val] := by simp [rep,List.getElem?_eq_getElem inside]
  rw [repIs]
  exact shape.reps _ (List.getElem_mem inside)


theorem linkEnds_mem (links : List completion.Link) (l : ObjectPropertyExpression × Usize × Usize) :
    l ∈ linkEnds links ↔ ∃ l0 ∈ links, l = (l0.role,l0.from,l0.to) := by
  unfold linkEnds
  rw [List.mem_map]
  constructor
  · rintro ⟨l0,member,rfl⟩
    exact ⟨l0,member,rfl⟩
  · rintro ⟨l0,member,rfl⟩
    exact ⟨l0,member,rfl⟩

theorem edgeEnds_mem (edges : List forest.Edge) (l : ObjectPropertyExpression × Usize × Usize) :
    l ∈ edgeEnds edges ↔ ∃ e ∈ edges, l = (e.role,e.from,e.to) := by
  unfold edgeEnds
  rw [List.mem_map]
  constructor
  · rintro ⟨e,member,rfl⟩
    exact ⟨e,member,rfl⟩
  · rintro ⟨e,member,rfl⟩
    exact ⟨e,member,rfl⟩

/-- A node beyond the individuals is read through the merges as itself. -/
theorem rep_beyond {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (a : Usize) (beyond : ¬ a.val < count) : rep F a = a := by
  unfold rep
  rw [List.getElem?_eq_none (by rw [shape.sameLength]; omega)]

/-- An end of an added edge is read through the merges as an active named node. -/
theorem end_in {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (a : Usize) (named : NamedEnd F count a.val) :
    Named F.nodes.val (rep F a).val ∧ Active F.nodes.val (rep F a).val := by
  by_cases below : a.val < count
  · exact rep_in shape a below
  · rcases named with below' | ⟨named,active⟩
    · exact absurd below' below
    · rw [rep_beyond shape a below]
      exact ⟨named,active⟩

/-- A tree node is read through the merges as itself. -/
theorem rep_tree {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (a : Usize) (n : forest.Node) (at_a : F.nodes.val[a.val]? = some n)
    (tree : n.tree = true) : rep F a = a := by
  apply rep_beyond shape a
  intro below
  have := shape.named a.val n at_a below
  rw [tree] at this
  cases this

/-- The source of an added edge, read through the merges, is an active named
    node or a tree node read as itself. -/
theorem edge_from {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (e : forest.Edge) (listed : e ∈ F.edges.val) :
    (Named F.nodes.val (rep F e.from).val ∧ Active F.nodes.val (rep F e.from).val) ∨
      (rep F e.from = e.from ∧ ∃ n, F.nodes.val[e.from.val]? = some n ∧ n.tree = true) := by
  rcases (shape.edges e listed).2 with named | ⟨n,at_n,tree⟩
  · exact .inl (end_in shape e.from named)
  · exact .inr ⟨rep_tree shape e.from n at_n tree,n,at_n,tree⟩

theorem liveEdgeEnds_mem (F : forest.Forest) (edges : List forest.Edge) (l : ObjectPropertyExpression × Usize × Usize) :
    l ∈ edgeEnds (liveEdges F edges) ↔ ∃ e ∈ edges, Live F.nodes.val (rep F e.from).val ∧ l = (e.role,e.from,e.to) := by
  unfold edgeEnds liveEdges
  rw [List.mem_map]
  constructor
  · rintro ⟨e,member,rfl⟩
    obtain ⟨listed,live⟩ := List.mem_filter.mp member
    exact ⟨e,listed,by simpa using live,rfl⟩
  · rintro ⟨e,listed,live,rfl⟩
    exact ⟨e,List.mem_filter.mpr ⟨listed,by simpa using live⟩,rfl⟩

/-- A node that a link relates, read through the merges, is the representative
    of an individual. -/
theorem linkAlong_rep {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (x : Nat) (r : ObjectPropertyExpression) (z : Nat) :
    LinkAlong h F (linkEnds P.links.val) x r z →
      ∃ a b : Usize, a.val < count ∧ b.val < count ∧ (rep F a).val = x ∧ (rep F b).val = z := by
  rintro ⟨l,member,⟨there,_,here⟩ | ⟨there,_,here⟩⟩
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    exact ⟨l0.from,l0.to,(shape.links l0 listed).1,(shape.links l0 listed).2,there,here⟩
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    exact ⟨l0.to,l0.from,(shape.links l0 listed).2,(shape.links l0 listed).1,there,here⟩

/-- Nodes that a live added edge relates, read through the merges: its source is
    live and its target is an active named node. -/
theorem edgeAlong_ends {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (x : Nat) (r : ObjectPropertyExpression) (z : Nat)
    (linked : LinkAlong h F (edgeEnds (liveEdges F F.edges.val)) x r z) :
    ∃ e ∈ F.edges.val, Live F.nodes.val (rep F e.from).val ∧ Named F.nodes.val (rep F e.to).val ∧
      Active F.nodes.val (rep F e.to).val ∧
      (((rep F e.from).val = x ∧ (rep F e.to).val = z) ∨ ((rep F e.to).val = x ∧ (rep F e.from).val = z)) := by
  obtain ⟨l,member,⟨there,_,here⟩ | ⟨there,_,here⟩⟩ := linked
  · obtain ⟨e,listed,live,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    exact ⟨e,listed,live,(end_in shape e.to (shape.edges e listed).1).1,(end_in shape e.to (shape.edges e listed).1).2,
      .inl ⟨there,here⟩⟩
  · obtain ⟨e,listed,live,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    exact ⟨e,listed,live,(end_in shape e.to (shape.edges e listed).1).1,(end_in shape e.to (shape.edges e listed).1).2,
      .inr ⟨there,here⟩⟩

/-- Every neighbour of an active node is an active node of the forest. -/
theorem neighbour_active {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (x : Nat) (active : Active F.nodes.val x) (r : ObjectPropertyExpression) (z : Nat)
    (neighbour : Neighbour P h F x r z) : Active F.nodes.val z := by
  rcases neighbour with ⟨n,at_z,_,act,_⟩ | ⟨n,at_x,tree,parent,_⟩ | linked | linked | ⟨rfl,_⟩
  · exact ⟨n,at_z,act⟩
  · obtain ⟨m,at_x',act⟩ := active
    rw [at_x] at at_x'
    cases at_x'
    rw [← parent]
    exact shape.activeParents x n at_x tree act
  · obtain ⟨_,b,_,bIn,_,rfl⟩ := linkAlong_rep shape x r z linked
    exact (rep_in shape b bIn).2
  · obtain ⟨e,_,live,_,toActive,⟨_,rfl⟩ | ⟨_,rfl⟩⟩ := edgeAlong_ends shape x r z linked
    · exact toActive
    · exact live.1
  · exact active

/-- A neighbour is near: the parent, an active child, or a node related by a
    link or an added edge. -/
theorem neighbour_near (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (r : ObjectPropertyExpression) (z : Nat) (neighbour : Neighbour P h F x r z) : Near P F x z := by
  rcases neighbour with ⟨n,at_z,tree,act,parent,_⟩ | ⟨n,at_x,tree,parent,_⟩ |
      ⟨l,member,⟨there,_,here⟩ | ⟨there,_,here⟩⟩ | ⟨l,member,⟨there,_,here⟩ | ⟨there,_,here⟩⟩ | ⟨loop,_⟩
  · exact .inr (.inr (.inl ⟨n,at_z,tree,act,parent⟩))
  · exact .inr (.inl ⟨n,at_x,tree,parent⟩)
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    exact .inr (.inr (.inr (.inl ⟨l0,listed,.inl ⟨there,here⟩⟩)))
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    exact .inr (.inr (.inr (.inl ⟨l0,listed,.inr ⟨there,here⟩⟩)))
  · obtain ⟨e,listed,_,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    exact .inr (.inr (.inr (.inr ⟨e,listed,.inl ⟨there,here⟩⟩)))
  · obtain ⟨e,listed,_,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    exact .inr (.inr (.inr (.inr ⟨e,listed,.inr ⟨there,here⟩⟩)))
  · exact .inl loop

/-- A named neighbour of a tree node is its parent or the target of a live
    added edge from it. -/
theorem neighbour_named {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (x : Nat) (n : forest.Node) (at_x : F.nodes.val[x]? = some n)
    (tree : n.tree = true) (r : ObjectPropertyExpression) (z : Nat) (neighbour : Neighbour P h F x r z)
    (m : forest.Node) (at_z : F.nodes.val[z]? = some m) (named : m.tree = false) :
    z = n.parent.val ∨ ∃ e ∈ F.edges.val, (rep F e.from).val = x ∧ (rep F e.to).val = z := by
  -- A named node is not the tree node `x`.
  have notX : ¬ Named F.nodes.val x := by
    rintro ⟨n',at_x',named'⟩
    rw [at_x] at at_x'
    cases at_x'
    rw [tree] at named'
    cases named'
  rcases neighbour with ⟨m',at_z',tree',_⟩ | ⟨n',at_x',_,parent,_⟩ | linked | linked | ⟨loop,_⟩
  · rw [at_z] at at_z'
    cases at_z'
    rw [named] at tree'
    cases tree'
  · rw [at_x] at at_x'
    cases at_x'
    exact .inl parent.symm
  · obtain ⟨a,_,aIn,_,there,_⟩ := linkAlong_rep shape x r z linked
    have named' := (rep_in shape a aIn).1
    rw [there] at named'
    exact absurd named' notX
  · obtain ⟨e,listed,_,toNamed,_,⟨fromX,toZ⟩ | ⟨toX,_⟩⟩ := edgeAlong_ends shape x r z linked
    · exact .inr ⟨e,listed,fromX,toZ⟩
    · rw [toX] at toNamed
      exact absurd toNamed notX
  · rw [loop,at_x] at at_z
    cases at_z
    rw [tree] at named
    cases named

/-- A tree node that neighbours `x` is a child of `x`, its parent, for a named
    node `x` the live source of an added edge into `x`, or `x` itself with a
    loop. -/
theorem neighbour_tree {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (x : Nat) (r : ObjectPropertyExpression) (z : Nat)
    (neighbour : Neighbour P h F x r z) (m : forest.Node) (at_z : F.nodes.val[z]? = some m) (tree : m.tree = true) :
    ChildAlong h F.nodes.val x r z ∨ ParentAlong h F.nodes.val x r z ∨ (Named F.nodes.val x ∧ Live F.nodes.val z) ∨
      z = x := by
  -- The tree node `z` is not named.
  have notZ : ¬ Named F.nodes.val z := by
    rintro ⟨m',at_z',named⟩
    rw [at_z] at at_z'
    cases at_z'
    rw [tree] at named
    cases named
  rcases neighbour with child | parent | linked | linked | ⟨loop,_⟩
  · exact .inl child
  · exact .inr (.inl parent)
  · obtain ⟨_,b,_,bIn,_,there⟩ := linkAlong_rep shape x r z linked
    have named := (rep_in shape b bIn).1
    rw [there] at named
    exact absurd named notZ
  · obtain ⟨e,_,live,toNamed,_,⟨_,toZ⟩ | ⟨toX,fromZ⟩⟩ := edgeAlong_ends shape x r z linked
    · rw [toZ] at toNamed
      exact absurd toNamed notZ
    · rw [toX] at toNamed
      rw [fromZ] at live
      exact .inr (.inr (.inl ⟨toNamed,live⟩))
  · exact .inr (.inr (.inr loop))

theorem neighbour_inside {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (x : Nat) (r : ObjectPropertyExpression) (z : Nat)
    (neighbour : Neighbour P h F x r z) : z < F.nodes.val.length := by
  have inside : ∀ y, Active F.nodes.val y → y < F.nodes.val.length := by
    rintro y ⟨n,at_y,_⟩
    exact (List.getElem?_eq_some_iff.mp at_y).1
  rcases neighbour with ⟨n,at_z,_⟩ | ⟨n,at_x,tree,parent,_⟩ | linked | linked | ⟨rfl,i,listed,_⟩
  · exact (List.getElem?_eq_some_iff.mp at_z).1
  · have := shape.parents x n at_x tree
    have := (List.getElem?_eq_some_iff.mp at_x).1
    omega
  · obtain ⟨_,b,_,bIn,_,there⟩ := linkAlong_rep shape x r z linked
    have active := (rep_in shape b bIn).2
    rw [there] at active
    exact inside z active
  · obtain ⟨e,_,live,_,toActive,⟨_,toZ⟩ | ⟨_,fromZ⟩⟩ := edgeAlong_ends shape x r z linked
    · rw [toZ] at toActive
      exact inside z toActive
    · rw [fromZ] at live
      exact inside z live.1
  · by_contra outside
    simp [labelOf,List.getElem?_eq_none_iff.mpr (show F.nodes.val.length ≤ z by omega)] at listed

/-! ### Growing labels -/

theorem grows_refl (F : forest.Forest) : Grows F F :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ n at_y => ⟨n,at_y,rfl,rfl,rfl,rfl,rfl,rfl,fun _ member => member⟩⟩

theorem grows_trans {F F' F'' : forest.Forest} (one : Grows F F') (two : Grows F' F'') : Grows F F'' := by
  obtain ⟨length1,edges1,distinct1,same1,caps1,nodes1⟩ := one
  obtain ⟨length2,edges2,distinct2,same2,caps2,nodes2⟩ := two
  refine ⟨length2.trans length1,edges2.trans edges1,distinct2.trans distinct1,same2.trans same1,caps2.trans caps1,?_⟩
  intro y n at_y
  obtain ⟨n',at_y',parent1,roles1,seed1,tree1,active1,done1,label1⟩ := nodes1 y n at_y
  obtain ⟨n'',at_y'',parent2,roles2,seed2,tree2,active2,done2,label2⟩ := nodes2 y n' at_y'
  exact ⟨n'',at_y'',parent2.trans parent1,roles2.trans roles1,seed2.trans seed1,tree2.trans tree1,
    active2.trans active1,done2.trans done1,fun i member => label2 i (label1 i member)⟩

theorem grows_back {F F' : forest.Forest} (grows : Grows F F') (y : Nat) (n' : forest.Node)
    (at_y' : F'.nodes.val[y]? = some n') : ∃ n : forest.Node, F.nodes.val[y]? = some n ∧
      n'.parent = n.parent ∧ n'.roles = n.roles ∧ n'.seed = n.seed ∧ n'.tree = n.tree ∧ n'.active = n.active ∧
      n'.done = n.done ∧ ∀ i ∈ n.label.val, i ∈ n'.label.val := by
  have yIn : y < F.nodes.val.length := by rw [← grows.1]; exact (List.getElem?_eq_some_iff.mp at_y').1
  obtain ⟨n'',at_y'',rest⟩ := grows.2.2.2.2.2 y F.nodes.val[y] (List.getElem?_eq_getElem yIn)
  rw [at_y'] at at_y''
  cases at_y''
  exact ⟨_,List.getElem?_eq_getElem yIn,rest⟩

theorem grows_none {F F' : forest.Forest} (grows : Grows F F') (y : Nat) (absent : F.nodes.val[y]? = none) :
    F'.nodes.val[y]? = none := by
  rw [List.getElem?_eq_none_iff] at absent ⊢
  rw [grows.1]
  exact absent

theorem grows_label {F F' : forest.Forest} (grows : Grows F F') (y : Nat) :
    ∀ i ∈ labelOf F.nodes.val y, i ∈ labelOf F'.nodes.val y := by
  intro i member
  unfold labelOf at member ⊢
  cases at_y : F.nodes.val[y]? with
  | none => rw [at_y] at member; cases member
  | some n =>
    rw [at_y] at member
    obtain ⟨n',at_y',_,_,_,_,_,_,labels⟩ := grows.2.2.2.2.2 y n at_y
    rw [at_y']
    exact labels i member

theorem grows_done {F F' : forest.Forest} (grows : Grows F F') (y : Nat) :
    doneOf F'.nodes.val y = doneOf F.nodes.val y := by
  unfold doneOf
  cases at_y : F.nodes.val[y]? with
  | none => rw [grows_none grows y at_y]
  | some n =>
    obtain ⟨n',at_y',_,_,_,_,_,done,_⟩ := grows.2.2.2.2.2 y n at_y
    simp only [at_y',done]

theorem grows_active {F F' : forest.Forest} (grows : Grows F F') (y : Nat) :
    Active F'.nodes.val y ↔ Active F.nodes.val y := by
  constructor
  · rintro ⟨n',at_y',active⟩
    obtain ⟨n,at_y,_,_,_,_,same,_⟩ := grows_back grows y n' at_y'
    exact ⟨n,at_y,by rw [← same]; exact active⟩
  · rintro ⟨n,at_y,active⟩
    obtain ⟨n',at_y',_,_,_,_,same,_⟩ := grows.2.2.2.2.2 y n at_y
    exact ⟨n',at_y',by rw [same]; exact active⟩

theorem grows_named {F F' : forest.Forest} (grows : Grows F F') (y : Nat) :
    Named F'.nodes.val y ↔ Named F.nodes.val y := by
  constructor
  · rintro ⟨n',at_y',named⟩
    obtain ⟨n,at_y,_,_,_,same,_⟩ := grows_back grows y n' at_y'
    exact ⟨n,at_y,by rw [← same]; exact named⟩
  · rintro ⟨n,at_y,named⟩
    obtain ⟨n',at_y',_,_,_,same,_⟩ := grows.2.2.2.2.2 y n at_y
    exact ⟨n',at_y',by rw [same]; exact named⟩

theorem grows_namedEnd {F F' : forest.Forest} (grows : Grows F F') (count y : Nat) :
    NamedEnd F' count y ↔ NamedEnd F count y := by
  unfold NamedEnd
  rw [grows_named grows,grows_active grows]

theorem grows_treePath {F F' : forest.Forest} (grows : Grows F F') :
    ∀ y, treePath F'.nodes.val y = treePath F.nodes.val y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    rw [treePath.eq_def,treePath.eq_def F.nodes.val]
    cases at_y : F.nodes.val[y]? with
    | none => rw [grows_none grows y at_y]
    | some n =>
      obtain ⟨n',at_y',parent,_,_,tree,_⟩ := grows.2.2.2.2.2 y n at_y
      rw [at_y']
      simp only [tree,parent]
      split
      · split
        · rename_i below
          rw [ih n.parent.val below]
        · rfl
      · rfl

theorem grows_depth {F F' : forest.Forest} (grows : Grows F F') (y : Nat) : depth F' y = depth F y := by
  unfold depth
  rw [grows_treePath grows y]

theorem grows_rep {F F' : forest.Forest} (grows : Grows F F') (a : Usize) : rep F' a = rep F a := by
  unfold rep
  rw [grows.2.2.2.1]

/-- The invariant carries over to a forest that only grows labels, when the new
    labels are clash-free literals without repetitions. -/
theorem inv_grows {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F F' : forest.Forest}
    (inv : Inv P h count F) (grows : Grows F F')
    (literals : ∀ y, ∀ i ∈ labelOf F'.nodes.val y, ∃ e, P.entries.val[i.val]? = some e ∧ Literal e)
    (clashFree : ∀ y, ∀ i ∈ labelOf F'.nodes.val y, ∀ j ∈ labelOf F'.nodes.val y, ∀ e e',
      P.entries.val[i.val]? = some e → P.entries.val[j.val]? = some e' → ¬ Complementary e e')
    (nodup : ∀ y, (labelOf F'.nodes.val y).Nodup) : Inv P h count F' := by
  have shape := inv.shape
  refine ⟨⟨shape.wellFormed,shape.complements,shape.closedTable,shape.closed,shape.simple,?_,
      by rw [grows.1]; exact shape.countIn,by rw [grows.2.2.2.1]; exact shape.sameLength,?_,?_,?_,shape.links,
      shape.requirements,?_,by rw [grows.2.2.1,grows.1]; exact shape.distinctIn,
      literals,clashFree,by rw [grows.2.2.2.2.1,grows.1]; exact shape.capsIn⟩,nodup,?_,?_,?_⟩
  · intro y n' at_y'
    obtain ⟨n,at_y,_,_,_,tree,_⟩ := grows_back grows y n' at_y'
    rw [tree]
    exact shape.named y n at_y
  · intro b member
    rw [grows.2.2.2.1] at member
    rw [grows_active grows,grows_named grows]
    exact shape.reps b member
  · intro y n' at_y' tree'
    obtain ⟨n,at_y,parent,_,_,tree,_⟩ := grows_back grows y n' at_y'
    rw [parent]
    exact shape.parents y n at_y (by rw [← tree]; exact tree')
  · intro y n' at_y' tree' active'
    obtain ⟨n,at_y,parent,_,_,tree,active,_⟩ := grows_back grows y n' at_y'
    rw [parent,grows_active grows]
    exact shape.activeParents y n at_y (by rw [← tree]; exact tree') (by rw [← active]; exact active')
  · intro e member
    rw [grows.2.1] at member
    obtain ⟨toIn,fromCases⟩ := shape.edges e member
    refine ⟨(grows_namedEnd grows count _).mpr toIn,fromCases.imp (grows_namedEnd grows count _).mpr ?_⟩
    rintro ⟨n,at_n,tree⟩
    obtain ⟨n',at_n',_,_,_,tree',_⟩ := grows.2.2.2.2.2 _ n at_n
    exact ⟨n',at_n',by rw [tree',tree]⟩
  · intro y
    rw [grows_done grows y]
    exact inv.doneNodup y
  · intro y i member
    rw [grows_done grows y] at member
    exact grows_label grows y i (inv.doneIn y i member)
  · intro y n' at_y' s member
    obtain ⟨n,at_y,_,roles,_⟩ := grows_back grows y n' at_y'
    rw [roles] at member
    exact inv.roles y n at_y s member

/-- The forest after adding an item to one label. -/
theorem set_node (nodes : alloc.vec.Vec forest.Node) (x : Usize) (inside : x.val < nodes.val.length)
    (n : forest.Node) :
    (nodes.set x n).val.length = nodes.val.length ∧ (∀ y, y ≠ x.val → (nodes.set x n).val[y]? = nodes.val[y]?) ∧
      (nodes.set x n).val[x.val]? = some n := by
  simp only [alloc.vec.Vec.set_val_eq]
  refine ⟨List.length_set ..,fun y different => List.getElem?_set_ne (Ne.symm different),
    List.getElem?_set_self inside⟩

/-- Inserting a new clash-free literal keeps the invariant, grows the forest and
    grows exactly that label. -/
theorem insert_inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (F : forest.Forest)
    (inv : Inv P h count F) (x : Usize) (inside : x.val < F.nodes.val.length) (item : Usize)
    (e : concept_table.Entry) (at_item : P.entries.val[item.val]? = some e) (literal : Literal e)
    (fresh : item ∉ labelOf F.nodes.val x.val) (noClash : ¬ Clashes P.entries.val (labelOf F.nodes.val x.val) item)
    (label joined : alloc.vec.Vec Usize) (labelIs : label.val = F.nodes.val[x.val].label.val ++ [item])
    (F' : forest.Forest)
    (isSet : F' = { F with nodes := (F.nodes.set x
      ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
        F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩) }) :
    Inv P h count F' ∧ Grows F F' ∧ (∀ y, y ≠ x.val → labelOf F'.nodes.val y = labelOf F.nodes.val y) ∧
      labelOf F'.nodes.val x.val = labelOf F.nodes.val x.val ++ [item] := by
  subst isSet
  obtain ⟨length,other,here⟩ := set_node F.nodes x inside
    ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
        F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩
  have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem inside
  have oldLabel : labelOf F.nodes.val x.val = F.nodes.val[x.val].label.val := by simp [labelOf,at_x]
  have newLabel : labelOf (F.nodes.set x
      ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
        F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩).val x.val =
      labelOf F.nodes.val x.val ++ [item] := by
    rw [oldLabel,← labelIs]
    unfold labelOf
    rw [here]
  have oldLabels : ∀ y, y ≠ x.val → labelOf (F.nodes.set x
      ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
        F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩).val y =
      labelOf F.nodes.val y := by
    intro y different
    unfold labelOf
    rw [other y different]
  have grows : Grows F { F with nodes := (F.nodes.set x
      ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
        F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩) } := by
    refine ⟨length,rfl,rfl,rfl,rfl,?_⟩
    intro y n at_y
    by_cases same : y = x.val
    · subst same
      rw [at_x] at at_y
      cases at_y
      refine ⟨_,here,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
      intro i member
      simp [labelIs,member]
    · refine ⟨n,by rw [other y same]; exact at_y,rfl,rfl,rfl,rfl,rfl,rfl,fun i member => member⟩
  refine ⟨inv_grows inv grows ?_ ?_ ?_,grows,oldLabels,newLabel⟩
  · intro y i member
    by_cases same : y = x.val
    · subst same
      rw [newLabel] at member
      rcases List.mem_append.mp member with old | new
      · exact inv.shape.literals _ i old
      · simp only [List.mem_singleton] at new
        subst new
        exact ⟨e,at_item,literal⟩
    · rw [oldLabels y same] at member
      exact inv.shape.literals y i member
  · intro y i member j listed e1 e2 at_i at_j
    by_cases same : y = x.val
    · subst same
      rw [newLabel] at member listed
      rcases List.mem_append.mp member with old | new
      · rcases List.mem_append.mp listed with old' | new'
        · exact inv.shape.clashFree _ i old j old' e1 e2 at_i at_j
        · simp only [List.mem_singleton] at new'
          subst new'
          intro complementary
          exact noClash ⟨i,old,e2,e1,at_j,at_i,complementary_symm _ _ complementary⟩
      · simp only [List.mem_singleton] at new
        subst new
        rcases List.mem_append.mp listed with old' | new'
        · intro complementary
          exact noClash ⟨j,old',e1,e2,at_i,at_j,complementary⟩
        · simp only [List.mem_singleton] at new'
          subst new'
          rw [at_i] at at_j
          cases at_j
          exact complementary_irrefl e1
    · rw [oldLabels y same] at member listed
      exact inv.shape.clashFree y i member j listed e1 e2 at_i at_j
  · intro y
    by_cases same : y = x.val
    · subst same
      rw [newLabel]
      exact List.nodup_append.mpr ⟨inv.nodup _,List.nodup_singleton _,by
        intro a member b single
        simp only [List.mem_singleton] at single
        subst single
        intro equal; subst equal; exact fresh member⟩
    · rw [oldLabels y same]; exact inv.nodup y

/-! ### The depth bound -/

theorem treePath_mem (nodes : List forest.Node) :
    ∀ x y, y ∈ treePath nodes x → ∃ n, nodes[y]? = some n ∧ n.tree = true := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y member
    rw [treePath.eq_def] at member
    cases at_x : nodes[x]? with
    | none => rw [at_x] at member; cases member
    | some n =>
      rw [at_x] at member
      simp only at member
      by_cases tree : n.tree = true
      · rw [if_pos tree] at member
        by_cases below : n.parent.val < x
        · rw [dif_pos below] at member
          rcases List.mem_cons.mp member with rfl | later
          · exact ⟨n,at_x,tree⟩
          · exact ih n.parent.val below y later
        · rw [dif_neg below] at member
          simp only [List.mem_singleton] at member
          subst member
          exact ⟨n,at_x,tree⟩
      · rw [if_neg tree] at member; cases member

/-- What pairwise blocking compares of a tree node: its label, its parent's
    label and its roles. -/
noncomputable def pairKey (nodes : List forest.Node) (y : Nat) :
    Finset Nat × Finset Nat × Finset ObjectPropertyExpression :=
  match nodes[y]? with
  | some n => (((labelOf nodes y).map (·.val)).toFinset,((labelOf nodes n.parent.val).map (·.val)).toFinset,
      n.roles.val.toFinset)
  | none => (∅,∅,∅)

theorem sameLabel_of_set (L L' : List Usize) (same : (L.map (·.val)).toFinset = (L'.map (·.val)).toFinset) :
    SameLabel L L' := by
  intro i
  have := congrArg (fun S => i.val ∈ S) same
  simp only [List.mem_toFinset,List.mem_map] at this
  constructor
  · intro member
    obtain ⟨j,listed,value⟩ := this.mp ⟨i,member,rfl⟩
    rwa [show j = i from UScalar.eq_of_val_eq value] at listed
  · intro member
    obtain ⟨j,listed,value⟩ := this.mpr ⟨i,member,rfl⟩
    rwa [show j = i from UScalar.eq_of_val_eq value] at listed

/-- Every node of a tree path but the topmost has a tree node as its parent. -/
theorem treePath_dropLast_parent (nodes : List forest.Node) :
    ∀ y v, v ∈ (treePath nodes y).dropLast →
      ∃ m q, nodes[v]? = some m ∧ nodes[m.parent.val]? = some q ∧ q.tree = true := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro v member
    rw [treePath.eq_def] at member
    cases at_y : nodes[y]? with
    | none => rw [at_y] at member; simp at member
    | some n =>
      rw [at_y] at member
      simp only at member
      by_cases tree : n.tree = true
      · rw [if_pos tree] at member
        by_cases below : n.parent.val < y
        · rw [dif_pos below] at member
          cases rest : treePath nodes n.parent.val with
          | nil => rw [rest] at member; simp at member
          | cons w ws =>
            rw [rest,List.dropLast_cons_cons] at member
            rcases List.mem_cons.mp member with rfl | later
            · -- The parent's path is not empty, so the parent is a tree node.
              have : ∃ q, nodes[n.parent.val]? = some q ∧ q.tree = true := by
                rw [treePath.eq_def] at rest
                cases at_p : nodes[n.parent.val]? with
                | none => rw [at_p] at rest; cases rest
                | some q =>
                  rw [at_p] at rest
                  simp only at rest
                  by_cases qTree : q.tree = true
                  · exact ⟨q,rfl,qTree⟩
                  · rw [if_neg qTree] at rest
                    cases rest
              obtain ⟨q,at_p,qTree⟩ := this
              exact ⟨n,q,at_y,at_p,qTree⟩
            · rw [← rest] at later
              exact ih n.parent.val below v later
        · rw [dif_neg below] at member
          simp at member
      · rw [if_neg tree] at member
        simp at member

/-- Along the path of an unblocked node, no two tree nodes other than the topmost
    have the same label, parent's label and roles. -/
theorem path_keys_nodup (nodes : List forest.Node)
    (parents : ∀ (y : Nat) (n : forest.Node), nodes[y]? = some n → n.tree = true → n.parent.val < y) :
    ∀ x, ¬ Blocked nodes x → (((treePath nodes x).dropLast).map (pairKey nodes)).Nodup := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro free
    rw [treePath.eq_def]
    cases at_x : nodes[x]? with
    | none => simp
    | some n =>
      simp only
      by_cases tree : n.tree = true
      · rw [if_pos tree]
        by_cases below : n.parent.val < x
        · rw [dif_pos below]
          have unfold : Blocked nodes x ↔ n.tree = true ∧ ((∃ v ∈ treePath nodes n.parent.val,
              SamePair nodes x v) ∨ Blocked nodes n.parent.val) := by
            rw [Blocked.eq_def,at_x]
            simp only [dif_pos below]
          have parentFree : ¬ Blocked nodes n.parent.val := fun blocked => free (unfold.mpr ⟨tree,.inr blocked⟩)
          have restNodup := ih n.parent.val below parentFree
          cases rest : treePath nodes n.parent.val with
          | nil => simp
          | cons w ws =>
            rw [rest] at restNodup
            rw [List.dropLast_cons_cons,List.map_cons,List.nodup_cons]
            refine ⟨?_,restNodup⟩
            intro member
            rw [List.mem_map] at member
            obtain ⟨v,onPath,same⟩ := member
            have onParentPath : v ∈ treePath nodes n.parent.val := by
              rw [rest]; exact List.dropLast_subset _ onPath
            obtain ⟨m',q,at_v',at_q,qTree⟩ := treePath_dropLast_parent nodes n.parent.val v (by rw [rest]; exact onPath)
            apply free
            refine unfold.mpr ⟨tree,.inl ⟨v,onParentPath,?_⟩⟩
            obtain ⟨m,at_v,vTree⟩ := treePath_mem nodes n.parent.val v onParentPath
            have sameNode : m' = m := Option.some.inj (at_v'.symm.trans at_v)
            rw [sameNode] at at_q
            have xIn : x < nodes.length := (List.getElem?_eq_some_iff.mp at_x).1
            have vIn : v < nodes.length := (List.getElem?_eq_some_iff.mp at_v).1
            have vBelow := parents v m at_v vTree
            have labelX : labelOf nodes x = n.label.val := by simp [labelOf,at_x]
            have labelV : labelOf nodes v = m.label.val := by simp [labelOf,at_v]
            simp only [pairKey,at_x,at_v,Prod.mk.injEq] at same
            obtain ⟨sameLabel,sameParent,sameRoles⟩ := same
            refine ⟨n,m,at_x,at_v,by omega,by omega,⟨q,at_q,qTree⟩,?_,sameLabel_of_set _ _ sameParent.symm,?_⟩
            · rw [← labelX,← labelV]
              exact sameLabel_of_set _ _ sameLabel.symm
            · intro s
              rw [← List.mem_toFinset,← List.mem_toFinset (l := m.roles.val),sameRoles]
        · rw [dif_neg below]
          simp
      · rw [if_neg tree]
        simp

/-- An unblocked node has at most `bound + 1` tree nodes on its path. -/
theorem depth_le_bound {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (inv : Inv P h count F) (x : Nat) (free : ¬ Blocked F.nodes.val x) : depth F x ≤ bound P + 1 := by
  have nodup := path_keys_nodup F.nodes.val inv.shape.parents x free
  have labelSub : ∀ y, ((labelOf F.nodes.val y).map (·.val)).toFinset ∈
      (Finset.range P.entries.val.length).powerset := by
    intro y
    rw [Finset.mem_powerset]
    intro k kIn
    simp only [List.mem_toFinset,List.mem_map] at kIn
    obtain ⟨i,listed,rfl⟩ := kIn
    exact Finset.mem_range.mpr (labels_in inv.shape y i listed)
  have sub : (((treePath F.nodes.val x).dropLast).map (pairKey F.nodes.val)).toFinset ⊆
      (Finset.range P.entries.val.length).powerset ×ˢ ((Finset.range P.entries.val.length).powerset ×ˢ
        (roleList P.entries.val).toFinset.powerset) := by
    intro k member
    rw [List.mem_toFinset,List.mem_map] at member
    obtain ⟨v,onPath,rfl⟩ := member
    obtain ⟨m,at_v,_⟩ := treePath_mem F.nodes.val x v (List.dropLast_subset _ onPath)
    simp only [pairKey,at_v,Finset.mem_product]
    refine ⟨labelSub v,labelSub m.parent.val,?_⟩
    rw [Finset.mem_powerset]
    intro s sIn
    rw [List.mem_toFinset] at sIn ⊢
    exact inv.roles v m at_v s sIn
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup nodup,List.length_map] at card
  simp only [Finset.card_product,Finset.card_powerset,Finset.card_range] at card
  have power : 2 ^ (roleList P.entries.val).toFinset.card ≤ 2 ^ (roleList P.entries.val).length :=
    Nat.pow_le_pow_right (by omega) (List.toFinset_card_le _)
  have dropped : (treePath F.nodes.val x).length ≤ ((treePath F.nodes.val x).dropLast).length + 1 := by
    rw [List.length_dropLast]
    omega
  unfold depth bound
  calc (treePath F.nodes.val x).length
      ≤ ((treePath F.nodes.val x).dropLast).length + 1 := dropped
    _ ≤ 2 ^ P.entries.val.length * (2 ^ P.entries.val.length * 2 ^ (roleList P.entries.val).toFinset.card) + 1 := by
        omega
    _ ≤ 2 ^ P.entries.val.length * (2 ^ P.entries.val.length * 2 ^ (roleList P.entries.val).length) + 1 := by
        apply Nat.add_le_add_right; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; exact power
    _ = 2 ^ P.entries.val.length * 2 ^ P.entries.val.length * 2 ^ (roleList P.entries.val).length + 1 := by ring

/-! ### The measure -/

theorem base_pos (P : completion.Problem) : 0 < base P := by
  unfold base
  positivity

theorem active_inside {nodes : List forest.Node} {y : Nat} (active : Active nodes y) : y < nodes.length := by
  obtain ⟨n,at_y,_⟩ := active
  exact (List.getElem?_eq_some_iff.mp at_y).1

theorem namedEnd_inside {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) {a : Nat} (named : NamedEnd F count a) : a < F.nodes.val.length := by
  rcases named with below | ⟨_,active⟩
  · have := shape.countIn
    omega
  · exact active_inside active

/-- Growing labels never increases a weight. -/
theorem weight_le_grows (P : completion.Problem) {F F' : forest.Forest} (grows : Grows F F') (y : Nat)
    (nodup : (labelOf F.nodes.val y).Nodup) : weight P F' y ≤ weight P F y := by
  unfold weight
  rw [grows_depth grows y]
  by_cases active : Active F.nodes.val y
  · rw [if_pos ((grows_active grows y).mpr active),if_pos active]
    apply Nat.mul_le_mul_left
    unfold factor
    rw [grows_done grows y]
    have := (List.Nodup.subperm nodup (grows_label grows y)).length_le
    omega
  · rw [if_neg (fun a => active ((grows_active grows y).mp a)),if_neg active]

/-- A label that grows strictly makes the weight of its active node drop. -/
theorem weight_lt_grows (P : completion.Problem) {F F' : forest.Forest} (grows : Grows F F') (y : Nat)
    (active : Active F.nodes.val y)
    (room : (labelOf F'.nodes.val y).length + (doneOf F.nodes.val y).length ≤ 2 * P.entries.val.length)
    (longer : (labelOf F.nodes.val y).length < (labelOf F'.nodes.val y).length) :
    weight P F' y < weight P F y := by
  unfold weight
  rw [grows_depth grows y,if_pos ((grows_active grows y).mpr active),if_pos active]
  apply Nat.mul_lt_mul_of_pos_left _ (pow_pos (base_pos P) _)
  unfold factor
  rw [grows_done grows y]
  omega

/-- The weight of the restrictions that may still get new named nodes depends
    only on the named nodes and the bounds from new named nodes. -/
theorem nameWeight_eq (P : completion.Problem) {F F' : forest.Forest}
    (length : F'.nodes.val.length = F.nodes.val.length) (named : ∀ y, Named F'.nodes.val y ↔ Named F.nodes.val y)
    (caps : F'.caps = F.caps) : nameWeight P F' = nameWeight P F := by
  have capped : ∀ y i, Capped F' y i ↔ Capped F y i := by
    intro y i
    unfold Capped
    rw [caps]
  unfold nameWeight
  rw [length]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  by_cases cond : Named F.nodes.val y ∧ AtMostAt P i ∧ ¬ Capped F y i
  · rw [if_pos ⟨(named y).mpr cond.1,cond.2.1,fun c => cond.2.2 ((capped y i).mp c)⟩,if_pos cond]
  · rw [if_neg (fun c' => cond ⟨(named y).mp c'.1,c'.2.1,fun c => c'.2.2 ((capped y i).mpr c)⟩),if_neg cond]

/-- New nodes that are no named nodes add no weight to the restrictions that may
    still get new named nodes. -/
theorem nameWeight_append (P : completion.Problem) {F F' : forest.Forest}
    (longer : F.nodes.val.length ≤ F'.nodes.val.length)
    (named : ∀ y, y < F.nodes.val.length → (Named F'.nodes.val y ↔ Named F.nodes.val y))
    (fresh : ∀ y, F.nodes.val.length ≤ y → ¬ Named F'.nodes.val y) (caps : F'.caps = F.caps) :
    nameWeight P F' = nameWeight P F := by
  have capped : ∀ y i, Capped F' y i ↔ Capped F y i := by
    intro y i
    unfold Capped
    rw [caps]
  unfold nameWeight
  rw [← Finset.sum_range_add_sum_Ico _ longer]
  have zero : ∑ y ∈ Finset.Ico F.nodes.val.length F'.nodes.val.length, ∑ i ∈ Finset.range P.entries.val.length,
      (if Named F'.nodes.val y ∧ AtMostAt P i ∧ ¬ Capped F' y i then nameUnit P * nameBase P ^ (Usize.max - y)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y member
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (fun ⟨isNamed,_⟩ => fresh y (Finset.mem_Ico.mp member).1 isNamed)
  rw [zero,Nat.add_zero]
  apply Finset.sum_congr rfl
  intro y member
  apply Finset.sum_congr rfl
  intro i _
  have same := named y (Finset.mem_range.mp member)
  by_cases cond : Named F.nodes.val y ∧ AtMostAt P i ∧ ¬ Capped F y i
  · rw [if_pos ⟨same.mpr cond.1,cond.2.1,fun c => cond.2.2 ((capped y i).mp c)⟩,if_pos cond]
  · rw [if_neg (fun c' => cond ⟨same.mp c'.1,c'.2.1,fun c => c'.2.2 ((capped y i).mpr c)⟩),if_neg cond]

theorem treeMeasure_le_grows (P : completion.Problem) {F F' : forest.Forest} (grows : Grows F F')
    (nodup : ∀ y, (labelOf F.nodes.val y).Nodup) : treeMeasure P F' ≤ treeMeasure P F := by
  unfold treeMeasure
  rw [grows.1]
  exact Finset.sum_le_sum (fun y _ => weight_le_grows P grows y (nodup y))

theorem nameWeight_grows (P : completion.Problem) {F F' : forest.Forest} (grows : Grows F F') :
    nameWeight P F' = nameWeight P F :=
  nameWeight_eq P grows.1 (grows_named grows) grows.2.2.2.2.1

theorem measure_le_grows (P : completion.Problem) {F F' : forest.Forest} (grows : Grows F F')
    (nodup : ∀ y, (labelOf F.nodes.val y).Nodup) : measure P F' ≤ measure P F := by
  unfold measure
  rw [nameWeight_grows P grows]
  have := treeMeasure_le_grows P grows nodup
  omega

/-- Growing the label of an active node strictly decreases the measure. -/
theorem measure_lt_label {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat}
    {F F' : forest.Forest} (inv : Inv P h count F) (inv' : Inv P h count F') (grows : Grows F F') (x : Nat)
    (active : Active F.nodes.val x) (longer : (labelOf F.nodes.val x).length < (labelOf F'.nodes.val x).length) :
    measure P F' < measure P F := by
  unfold measure
  rw [nameWeight_grows P grows]
  suffices treeMeasure P F' < treeMeasure P F by omega
  unfold treeMeasure
  rw [grows.1]
  apply Finset.sum_lt_sum
  · intro y _
    exact weight_le_grows P grows y (inv.nodup y)
  · refine ⟨x,Finset.mem_range.mpr (active_inside active),weight_lt_grows P grows x active ?_ longer⟩
    have := label_length inv' x
    have := done_length inv x
    omega

/-! ### Models -/

/-- A model under `D` is a model under every `D'` that adds no branch point
    below `fresh`. -/
theorem models_transfer {Object : Type u} {Value : Type v} {P : completion.Problem} {h : hierarchy.RoleHierarchy}
    {F : forest.Forest} {I : Interpretation Object Value} {π : Nat → Object} {D D' : List Usize} {fresh : Nat}
    (freshF : FreshForest F fresh) (within : ∀ k : Usize, k.val < fresh → k ∈ D' → k ∈ D)
    (models : Models P h F I π D) : Models P h F I π D' := by
  have lift : ∀ X : List Usize, (∀ k ∈ X, k.val < fresh) → Sub X D' → Sub X D :=
    fun X below sub k member => within k (below k member) (sub k member)
  refine ⟨models.respects,models.axioms,models.unfoldings,models.requirements,models.links,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a sub
    exact models.same a (lift _ (freshF.1 _) sub)
  · intro y sub
    exact models.labels y (lift _ (freshF.1 y) sub)
  · intro y n at_y tree sub
    apply models.tree y n at_y tree
    apply lift _ _ sub
    intro k member
    exact freshF.1 y k (by simp [nodeDeps,at_y,member])
  · intro e member sub
    exact models.edges e member (lift _ (freshF.2.1 e member) sub)
  · intro d member sub
    exact models.distinct d member (lift _ (freshF.2.2.1 d member) sub)
  · intro y n at_y named beyond sub
    apply models.seeds y n at_y named beyond
    apply lift _ _ sub
    intro k member
    exact freshF.1 y k (by simp [nodeDeps,at_y,member])
  · intro cap member sub
    exact models.caps cap member (lift _ (freshF.2.2.2 cap member) sub)

theorem fullModel_drop (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (c : Usize) (rest deps D : List Usize) :
    FullModel.{u,v} P h F x (c :: rest) deps D → FullModel.{u,v} P h F x rest deps D := by
  rintro ⟨Object,Value,I,π,models,extra⟩
  exact ⟨Object,Value,I,π,models,fun sub c' member => extra sub c' (List.mem_cons_of_mem _ member)⟩

theorem fullModel_any (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest)
    (x y : Nat) (deps deps' D : List Usize) :
    FullModel.{u,v} P h F x [] deps D → FullModel.{u,v} P h F y [] deps' D := by
  rintro ⟨Object,Value,I,π,models,_⟩
  exact ⟨Object,Value,I,π,models,by simp⟩

/-- A model of the forest with the extra entries also has entries implied by them. -/
theorem fullModel_imply (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Nat)
    (extra extra' deps D : List Usize)
    (implies : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (z : Object),
      (∀ c ∈ extra, denote I (meaning P.entries.val c.val) z) → ∀ c ∈ extra', denote I (meaning P.entries.val c.val) z) :
    FullModel.{u,v} P h F x extra deps D → FullModel.{u,v} P h F x extra' deps D := by
  rintro ⟨Object,Value,I,π,models,extras⟩
  exact ⟨Object,Value,I,π,models,fun sub => implies Object Value I (π x) (extras sub)⟩

/-- A model with the inserted item at its node models the forest with the
    inserted item and the joined points. -/
theorem fullModel_insert (P : completion.Problem) (h : hierarchy.RoleHierarchy) (F : forest.Forest) (x : Usize)
    (inside : x.val < F.nodes.val.length) (item : Usize) (rest deps D : List Usize) (label joined : alloc.vec.Vec Usize)
    (labelIs : label.val = F.nodes.val[x.val].label.val ++ [item])
    (joinedIs : ∀ k, k ∈ joined.val ↔ k ∈ F.nodes.val[x.val].deps.val ∨ k ∈ deps) :
    FullModel.{u,v} P h F x.val (item :: rest) deps D →
      FullModel.{u,v} P h { F with nodes := (F.nodes.set x
        ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
          F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩) } x.val rest deps D := by
  rintro ⟨Object,Value,I,π,models,extra⟩
  obtain ⟨_,other,here⟩ := set_node F.nodes x inside
    ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
        F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩
  have at_x : F.nodes.val[x.val]? = some F.nodes.val[x.val] := List.getElem?_eq_getElem inside
  have oldDeps : nodeDeps F x.val = F.nodes.val[x.val].deps.val := by simp [nodeDeps,at_x]
  have depsAt : ∀ y, Sub (nodeDeps { F with nodes := (F.nodes.set x
      ⟨label,F.nodes.val[x.val].parent,F.nodes.val[x.val].roles,F.nodes.val[x.val].seed,
        F.nodes.val[x.val].tree,F.nodes.val[x.val].active,F.nodes.val[x.val].done,joined⟩) } y) D →
      Sub (nodeDeps F y) D ∧ (y = x.val → Sub deps D) := by
    intro y sub
    by_cases same : y = x.val
    · subst same
      have joinedSub : Sub joined.val D := by
        intro k listed
        apply sub k
        simp only [nodeDeps]
        rw [here]
        exact listed
      refine ⟨fun k listed => joinedSub k ((joinedIs k).mpr (.inl (by rw [← oldDeps]; exact listed))),
        fun _ k listed => joinedSub k ((joinedIs k).mpr (.inr listed))⟩
    · refine ⟨?_,fun same' => absurd same' same⟩
      intro k listed
      apply sub k
      simp only [nodeDeps] at listed ⊢
      rw [other y same]
      exact listed
  refine ⟨Object,Value,I,π,⟨models.respects,models.axioms,models.unfoldings,models.requirements,models.links,
    ?_,?_,?_,models.edges,models.distinct,?_,models.caps⟩,fun sub c member => extra sub c (List.mem_cons_of_mem _ member)⟩
  · intro a sub
    exact models.same a (depsAt _ sub).1
  · intro y sub i member
    obtain ⟨oldSub,newSub⟩ := depsAt y sub
    by_cases same : y = x.val
    · subst same
      unfold labelOf at member
      rw [here] at member
      simp only [labelIs,List.mem_append,List.mem_singleton] at member
      rcases member with old | rfl
      · exact models.labels _ oldSub i (by simp [labelOf,at_x,old])
      · exact extra (newSub rfl) _ (List.mem_cons_self ..)
    · unfold labelOf at member
      rw [other y same] at member
      exact models.labels y oldSub i member
  · intro y n at_y isTree sub
    by_cases same : y = x.val
    · subst same
      rw [here] at at_y
      cases at_y
      have oldSub := (depsAt _ (by simp only [nodeDeps]; rw [here]; exact sub)).1
      exact models.tree _ F.nodes.val[x.val] at_x isTree (by rw [← oldDeps]; exact oldSub)
    · rw [other y same] at at_y
      exact models.tree y n at_y isTree sub
  · intro y n at_y named beyond sub
    by_cases same : y = x.val
    · subst same
      rw [here] at at_y
      cases at_y
      have oldSub := (depsAt _ (by simp only [nodeDeps]; rw [here]; exact sub)).1
      exact models.seeds _ F.nodes.val[x.val] at_x named beyond (by rw [← oldDeps]; exact oldSub)
    · rw [other y same] at at_y
      exact models.seeds y n at_y named beyond sub

/-- In a model, a neighbour along `r` is reached along `r` when the points of
    the two nodes and of the added edges at `x` are in `D`. -/
theorem neighbour_holds {Object : Type u} {Value : Type v} {P : completion.Problem} {h : hierarchy.RoleHierarchy}
    {F : forest.Forest} {I : Interpretation Object Value} {π : Nat → Object} {D : List Usize}
    (models : Models P h F I π D) (x : Usize) (r : ObjectPropertyExpression) (z : Nat)
    (neighbour : Neighbour P h F x.val r z) (cover : ∀ y, Near P F x.val y → Sub (nodeDeps F y) D)
    (edgeCover : ∀ e ∈ F.edges.val, (rep F e.from = x ∨ rep F e.to = x) → Sub e.deps.val D) :
    objectRelation I r (π x.val) (π z) := by
  have near := neighbour_near P h F x.val r z neighbour
  rcases neighbour with ⟨n,at_z,tree,_,parent,s,role,below⟩ | ⟨n,at_x,tree,parent,s,role,below⟩ |
      ⟨l,member,⟨there,below,here⟩ | ⟨there,below,here⟩⟩ | ⟨l,member,⟨there,below,here⟩ | ⟨there,below,here⟩⟩ |
      ⟨rfl,i,listed,s,at_i,below | below⟩
  · have edge := (models.tree z n at_z tree (by simpa [nodeDeps,at_z] using cover z near)).1 s role
    rw [parent] at edge
    exact respects_below models.respects below edge
  · have edge := (models.tree x.val n at_x tree (by simpa [nodeDeps,at_x] using cover x.val (.inl rfl))).1 s role
    rw [parent] at edge
    exact respects_below models.respects below ((relation_inv I s _ _).mpr edge)
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    have link := models.links l0 listed
    rw [models.same l0.from (by rw [there]; exact cover x.val (.inl rfl)),
      models.same l0.to (by rw [here]; exact cover z near),there,here] at link
    exact respects_below models.respects below link
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    have link := models.links l0 listed
    rw [models.same l0.from (by rw [here]; exact cover z near),
      models.same l0.to (by rw [there]; exact cover x.val (.inl rfl)),there,here] at link
    exact respects_below models.respects below ((relation_inv I l0.role _ _).mpr link)
  · obtain ⟨e,listed,_,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    have edge := models.edges e listed (edgeCover e listed (.inl (UScalar.eq_of_val_eq there)))
    rw [models.same e.from (by rw [there]; exact cover x.val (.inl rfl)),
      models.same e.to (by rw [here]; exact cover z near),there,here] at edge
    exact respects_below models.respects below edge
  · obtain ⟨e,listed,_,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    have edge := models.edges e listed (edgeCover e listed (.inr (UScalar.eq_of_val_eq there)))
    rw [models.same e.from (by rw [here]; exact cover z near),
      models.same e.to (by rw [there]; exact cover x.val (.inl rfl)),there,here] at edge
    exact respects_below models.respects below ((relation_inv I e.role _ _).mpr edge)
  · -- A loop: the self restriction holds at the node.
    have self := models.labels x.val (cover x.val (.inl rfl)) i listed
    rw [meaning.eq_def,at_i] at self
    exact respects_below models.respects below self
  · have self := models.labels x.val (cover x.val (.inl rfl)) i listed
    rw [meaning.eq_def,at_i] at self
    exact respects_below models.respects below ((relation_inv I s _ _).mpr self)

/-- Everything a node or an edge requires of node `y` holds at its element in a
    model where the points of the nodes near `y` and of the added edges at `y`
    are in `D`. -/
theorem needs_hold {Object : Type u} {Value : Type v} {P : completion.Problem} {h : hierarchy.RoleHierarchy}
    {F : forest.Forest} {I : Interpretation Object Value} {π : Nat → Object} {D : List Usize}
    (wf : WellFormed P.entries.val) (models : Models P h F I π D) (y : Usize) (c : Usize)
    (needs : AddNeeds P h F y.val c) (cover : ∀ z, Near P F y.val z → Sub (nodeDeps F z) D)
    (edgeCover : ∀ e ∈ F.edges.val, (rep F e.from = y ∨ rep F e.to = y) → Sub e.deps.val D) :
    denote I (meaning P.entries.val c.val) (π y.val) := by
  rcases needs with ⟨_,⟨q,member,node,rfl⟩ | rfl | ⟨w,member,⟨i,listed,at_i⟩,rfl⟩ | ⟨n,at_y,seeded,rfl⟩⟩ |
      ⟨child,n,at_child,tree,active,_,s,role,⟨rfl,edgeNeeds⟩ | ⟨here,edgeNeeds⟩⟩ |
      ⟨l,member,_,_,⟨here,edgeNeeds⟩ | ⟨here,edgeNeeds⟩⟩ | ⟨l,member,_,_,⟨here,edgeNeeds⟩ | ⟨here,edgeNeeds⟩⟩ |
      ⟨_,i,listed,s,at_i,edgeNeeds | edgeNeeds⟩
  · have := models.requirements q member
    rwa [models.same q.node (by rw [node]; exact cover y.val (.inl rfl)),node] at this
  · exact models.axioms _
  · apply models.unfoldings w member
    have := models.labels y.val (cover y.val (.inl rfl)) i listed
    rwa [meaning_at P.entries.val wf i.val _ at_i] at this
  · -- The seed, of a tree node or of a new named node.
    cases treeIs : n.tree
    · exact models.seeds y.val n at_y treeIs (seeded.resolve_left (by simp [treeIs]))
        (by simpa [nodeDeps,at_y] using cover y.val (.inl rfl))
    · exact (models.tree y.val n at_y treeIs (by simpa [nodeDeps,at_y] using cover y.val (.inl rfl))).2
  · -- The tree edge into `y` from its parent.
    have parentNear : Near P F y.val n.parent.val := .inr (.inl ⟨n,at_child,tree,rfl⟩)
    exact edge_need_holds I h models.respects P.entries.val wf _ s c (π n.parent.val) (π y.val)
      (models.labels n.parent.val (cover _ parentNear))
      ((models.tree y.val n at_child tree (by simpa [nodeDeps,at_child] using cover y.val (.inl rfl))).1 s role)
      edgeNeeds
  · -- The tree edge from `y` to an active child.
    rw [here] at cover ⊢
    have childNear : Near P F n.parent.val child := .inr (.inr (.inl ⟨n,at_child,tree,active,rfl⟩))
    exact edge_need_holds I h models.respects P.entries.val wf _ (inv s) c (π child) (π n.parent.val)
      (models.labels child (cover child childNear))
      ((relation_inv I s _ _).mpr
        ((models.tree child n at_child tree (by simpa [nodeDeps,at_child] using cover child childNear)).1 s role))
      edgeNeeds
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    have otherNear : Near P F y.val (rep F l0.from).val := .inr (.inr (.inr (.inl ⟨l0,listed,.inr ⟨here,rfl⟩⟩)))
    have link := models.links l0 listed
    rw [models.same l0.from (cover _ otherNear),models.same l0.to (by rw [here]; exact cover y.val (.inl rfl)),
      here] at link
    exact edge_need_holds I h models.respects P.entries.val wf _ l0.role c _ _
      (models.labels _ (cover _ otherNear)) link edgeNeeds
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    have otherNear : Near P F y.val (rep F l0.to).val := .inr (.inr (.inr (.inl ⟨l0,listed,.inl ⟨here,rfl⟩⟩)))
    have link := models.links l0 listed
    rw [models.same l0.to (cover _ otherNear),models.same l0.from (by rw [here]; exact cover y.val (.inl rfl)),
      here] at link
    exact edge_need_holds I h models.respects P.entries.val wf _ (inv l0.role) c _ _
      (models.labels _ (cover _ otherNear)) ((relation_inv I l0.role _ _).mpr link) edgeNeeds
  · obtain ⟨e,listed,_,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    have otherNear : Near P F y.val (rep F e.from).val := .inr (.inr (.inr (.inr ⟨e,listed,.inr ⟨here,rfl⟩⟩)))
    have edge := models.edges e listed (edgeCover e listed (.inr (UScalar.eq_of_val_eq here)))
    rw [models.same e.from (cover _ otherNear),models.same e.to (by rw [here]; exact cover y.val (.inl rfl)),
      here] at edge
    exact edge_need_holds I h models.respects P.entries.val wf _ e.role c _ _
      (models.labels _ (cover _ otherNear)) edge edgeNeeds
  · obtain ⟨e,listed,_,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    have otherNear : Near P F y.val (rep F e.to).val := .inr (.inr (.inr (.inr ⟨e,listed,.inl ⟨here,rfl⟩⟩)))
    have edge := models.edges e listed (edgeCover e listed (.inl (UScalar.eq_of_val_eq here)))
    rw [models.same e.to (cover _ otherNear),models.same e.from (by rw [here]; exact cover y.val (.inl rfl)),
      here] at edge
    exact edge_need_holds I h models.respects P.entries.val wf _ (inv e.role) c _ _
      (models.labels _ (cover _ otherNear)) ((relation_inv I e.role _ _).mpr edge) edgeNeeds
  · -- A loop along `s` at `y`.
    have self := models.labels y.val (cover y.val (.inl rfl)) i listed
    rw [meaning_at P.entries.val wf i.val _ at_i] at self
    exact edge_need_holds I h models.respects P.entries.val wf _ s c (π y.val) (π y.val)
      (models.labels y.val (cover y.val (.inl rfl))) self edgeNeeds
  · have self := models.labels y.val (cover y.val (.inl rfl)) i listed
    rw [meaning_at P.entries.val wf i.val _ at_i] at self
    exact edge_need_holds I h models.respects P.entries.val wf _ (inv s) c (π y.val) (π y.val)
      (models.labels y.val (cover y.val (.inl rfl))) ((relation_inv I s _ _).mpr self) edgeNeeds

/-- A node that something requires a concept of is active. -/
theorem addNeeds_active {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {F : forest.Forest}
    (shape : Shape P h count F) (y : Nat) (c : Usize) (needs : AddNeeds P h F y c) : Active F.nodes.val y := by
  rcases needs with ⟨active,_⟩ | ⟨child,n,at_child,tree,act,_,s,_,⟨rfl,_⟩ | ⟨rfl,_⟩⟩ |
      ⟨l,member,_,_,⟨here,_⟩ | ⟨here,_⟩⟩ | ⟨l,member,_,_,⟨here,_⟩ | ⟨here,_⟩⟩ | ⟨active,_⟩
  · exact active
  · exact ⟨n,at_child,act⟩
  · exact shape.activeParents child n at_child tree act
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    rw [← here]
    exact (rep_in shape _ (shape.links l0 listed).2).2
  · obtain ⟨l0,listed,rfl⟩ := (linkEnds_mem _ _).mp member
    rw [← here]
    exact (rep_in shape _ (shape.links l0 listed).1).2
  · obtain ⟨e,listed,_,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    rw [← here]
    exact (end_in shape _ (shape.edges e listed).1).2
  · obtain ⟨e,listed,live,rfl⟩ := (liveEdgeEnds_mem F _ _).mp member
    rw [← here]
    exact live.1
  · exact active

end Rowl.ForestInv
