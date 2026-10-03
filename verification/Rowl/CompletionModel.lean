import Rowl.CompletionSearch

/-!
The model of a complete completion graph, independent of how the graph was
built. Its elements are the named nodes and the labels of the unblocked tree
nodes. A named node belongs to a named class when its label lists the class; two
named nodes are related only along their links (and paths along transitive
roles); every other pair is related along `r` when each satisfies what the
other's label requires along `r` and along its inverse. When the graph is
complete and clash-free, every element satisfies every entry its label
satisfies (the truth lemma), the model respects the role hierarchy, and every
fact, link, TBox concept and unfolding holds.
-/
namespace Rowl.CompletionModel
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv relation_inv denote)
open Rowl.Hierarchy (Below Closed Respects transitives below_refl)
open Rowl.ConceptTable (WellFormed meaning meaning_at rebuild TransitiveClosed parts)
open Rowl.CompletionSearch
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false

/-- A literal entry: a named class, its complement, or a restriction. -/
def Literal : concept_table.Entry → Prop
  | .Atom _ | .NotAtom _ | .Exists _ _ | .Forall _ _ => True
  | _ => False

/-- The shape of a graph that the model needs: a well-formed table closed under
    the restrictions of transitive roles, a closed hierarchy, named nodes first
    and links and requirements on them, parents before their tree children, and
    clash-free labels of literals. -/
structure Shape (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat)
    (nodes : List completion.Node) : Prop where
  wellFormed : WellFormed P.entries.val
  closedTable : TransitiveClosed h P.entries.val
  closed : Closed h
  named : ∀ y (n : completion.Node), nodes[y]? = some n → (n.tree = false ↔ y < count)
  countIn : count ≤ nodes.length
  parents : ∀ y (n : completion.Node), nodes[y]? = some n → n.tree = true → n.parent.val < y
  links : ∀ l ∈ P.links.val, l.from.val < count ∧ l.to.val < count
  requirements : ∀ q ∈ P.requirements.val, q.node.val < count
  literals : ∀ y, ∀ i ∈ labelOf nodes y, ∃ e, P.entries.val[i.val]? = some e ∧ Literal e
  clashFree : ∀ y, ∀ i ∈ labelOf nodes y, ∀ j ∈ labelOf nodes y, ∀ e e',
    P.entries.val[i.val]? = some e → P.entries.val[j.val]? = some e' → ¬ Complementary e e'

theorem holds_same (entries : List concept_table.Entry) (L L' : List Usize) (same : SameLabel L L') :
    ∀ c, Holds entries L c ↔ Holds entries L' c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rw [Holds.eq_def,Holds.eq_def (label := L')]
    cases entries[c]? with
    | none => rfl
    | some e =>
      cases e with
      | And a b =>
        simp only
        by_cases first : a.val < c
        · by_cases second : b.val < c
          · rw [dif_pos first,dif_pos second,dif_pos first,dif_pos second,ih a.val first,ih b.val second]
          · rw [dif_pos first,dif_neg second,dif_pos first,dif_neg second]
        · rw [dif_neg first,dif_neg first]
      | Or a b =>
        simp only
        by_cases first : a.val < c
        · by_cases second : b.val < c
          · rw [dif_pos first,dif_pos second,dif_pos first,dif_pos second,ih a.val first,ih b.val second]
          · rw [dif_pos first,dif_neg second,dif_pos first,dif_neg second]
        · rw [dif_neg first,dif_neg first]
      | Top | Bottom => rfl
      | Atom _ | NotAtom _ | Exists _ _ | Forall _ _ | AtLeast _ _ _ | AtMost _ _ _ _ =>
        simp only
        constructor
        · rintro ⟨i,member,value⟩; exact ⟨i,(same i).mp member,value⟩
        · rintro ⟨i,member,value⟩; exact ⟨i,(same i).mpr member,value⟩

theorem edgeOk_same (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (L L' M M' : List Usize)
    (r : ObjectPropertyExpression) (left : SameLabel L L') (right : SameLabel M M') :
    EdgeOk entries h L r M → EdgeOk entries h L' r M' := by
  intro ok i member q f at_i below
  obtain ⟨holds,through⟩ := ok i ((left i).mpr member) q f at_i below
  refine ⟨(holds_same entries M M' right f.val).mp holds,?_⟩
  intro t transitive first second found
  obtain ⟨j,listed,at_j⟩ := through t transitive first second found
  exact ⟨j,(right j).mp listed,at_j⟩

/-- What a label requires along `r` it also requires along every role included
    in `r`, so satisfying it along the smaller role is enough. -/
theorem edgeOk_mono (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (L L' : List Usize) {s r : ObjectPropertyExpression} (included : Below h s r) :
    EdgeOk entries h L s L' → EdgeOk entries h L r L' := by
  intro ok i member q f at_i below
  obtain ⟨holds,through⟩ := ok i member q f at_i (closed.1 s r q included below)
  exact ⟨holds,fun t transitive first second found =>
    through t transitive (closed.1 s r t included first) second found⟩

/-- Blocking passes down tree paths: a node is blocked when a tree node above it is. -/
theorem blocked_down (nodes : List completion.Node) :
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

/-- Every node on a tree path is a tree node of the graph. -/
theorem treePath_tree (nodes : List completion.Node) :
    ∀ w v, v ∈ treePath nodes w → ∃ n, nodes[v]? = some n ∧ n.tree = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v member
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
          · exact ⟨n,at_w,tree⟩
          · exact ih n.parent.val below v later
        · rw [dif_neg below] at member
          simp only [List.mem_singleton] at member
          subst member
          exact ⟨n,at_w,tree⟩
      · rw [if_neg tree] at member
        cases member

/-- A child of a node that is not blocked is blocked only by a node on its
    parent's tree path with the same label. -/
theorem child_blocked (nodes : List completion.Node) (w y : Nat) (n : completion.Node) (at_y : nodes[y]? = some n)
    (parent : n.parent.val = w) (blocked : Blocked nodes y) (free : ¬ Blocked nodes w) :
    ∃ v ∈ treePath nodes w, SameLabel (labelOf nodes y) (labelOf nodes v) := by
  rw [Blocked.eq_def,at_y] at blocked
  simp only at blocked
  split at blocked
  · obtain ⟨_,found | parentBlocked⟩ := blocked
    · rw [← parent]; exact found
    · rw [parent] at parentBlocked; exact absurd parentBlocked free
  · exact blocked.elim

/-- A node that is not a tree node is never blocked. -/
theorem named_free (nodes : List completion.Node) (a : Nat) (n : completion.Node) (at_a : nodes[a]? = some n)
    (named : n.tree = false) : ¬ Blocked nodes a := by
  rw [Blocked.eq_def,at_a]
  simp only
  split
  · rintro ⟨isTree,_⟩; rw [named] at isTree; cases isTree
  · exact id

/-- The labels of the unblocked tree nodes. -/
noncomputable def family (nodes : List completion.Node) : List (List Usize) :=
  ((List.range nodes.length).filter
    (fun y => decide ((∃ n, nodes[y]? = some n ∧ n.tree = true) ∧ ¬ Blocked nodes y))).map (labelOf nodes)

theorem family_mem (nodes : List completion.Node) (L : List Usize) :
    L ∈ family nodes ↔ ∃ y n, nodes[y]? = some n ∧ n.tree = true ∧ ¬ Blocked nodes y ∧ L = labelOf nodes y := by
  simp only [family,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨y,⟨_,⟨n,at_y,tree⟩,free⟩,rfl⟩
    exact ⟨y,n,at_y,tree,free,rfl⟩
  · rintro ⟨y,n,at_y,tree,free,rfl⟩
    exact ⟨y,⟨(List.getElem?_eq_some_iff.mp at_y).1,⟨n,at_y,tree⟩,free⟩,rfl⟩

/-- The elements of the model: the named nodes, and the labels of the unblocked
    tree nodes. -/
abbrev Element (count : Nat) (nodes : List completion.Node) :=
  {a : Nat // a < count} ⊕ {L : List Usize // L ∈ family nodes}

/-- The label of an element. -/
def lab {count : Nat} {nodes : List completion.Node} : Element count nodes → List Usize
  | .inl a => labelOf nodes a.val
  | .inr L => L.val

/-- Each label satisfies what the other requires along the role and its
    inverse respectively. -/
def Compatible (entries : List concept_table.Entry) (h : hierarchy.RoleHierarchy) (L : List Usize)
    (r : ObjectPropertyExpression) (L' : List Usize) : Prop :=
  EdgeOk entries h L r L' ∧ EdgeOk entries h L' (inv r) L

/-- One step along a role: two named nodes along a link whose role (or its
    inverse, for the reverse direction) is included in the role; any other pair
    when the labels are compatible. -/
def Step (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (r : ObjectPropertyExpression) : Element count nodes → Element count nodes → Prop
  | .inl a, .inl b => ∃ l ∈ P.links.val, (l.from.val = a.val ∧ l.to.val = b.val ∧ Below h l.role r) ∨
      (l.to.val = a.val ∧ l.from.val = b.val ∧ Below h (inv l.role) r)
  | .inl a, .inr L => Compatible P.entries.val h (labelOf nodes a.val) r L.val
  | .inr L, .inl b => Compatible P.entries.val h L.val r (labelOf nodes b.val)
  | .inr L, .inr L' => Compatible P.entries.val h L.val r L'.val

/-- The relation of a role: a step, or a path of steps along a transitive role
    included in it. -/
def Rel (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (r : ObjectPropertyExpression) (x y : Element count nodes) : Prop :=
  Step P h count nodes r x y ∨ ∃ t ∈ transitives h, Below h t r ∧ Relation.TransGen (Step P h count nodes t) x y

/-- The model of a graph: a named class holds where the label lists it, and a
    named object property relates along `Rel`. -/
noncomputable def model (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat)
    (nodes : List completion.Node) (root : Element count nodes) : Interpretation (Element count nodes) Unit where
  objectsNonempty := ⟨root⟩
  dataNonempty := ⟨()⟩
  classes k x := HasAtom P.entries.val (lab x) k
  objectProperties p x y := Rel P h count nodes (.Property p) x y
  dataProperties _ _ _ := False
  namedIndividuals _ := root
  anonymousIndividuals _ := root
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := False

theorem below_inv_iff (h : hierarchy.RoleHierarchy) (closed : Closed h) (a b : ObjectPropertyExpression) :
    Below h a (inv b) ↔ Below h (inv a) b := by
  constructor
  · intro below
    have := closed.2.1 a (inv b) below
    rwa [Rowl.Concepts.inv_inv] at this
  · intro below
    have := closed.2.1 (inv a) b below
    rwa [Rowl.Concepts.inv_inv] at this

theorem step_inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (count : Nat)
    (nodes : List completion.Node) (r : ObjectPropertyExpression) (x y : Element count nodes) :
    Step P h count nodes (inv r) x y ↔ Step P h count nodes r y x := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      simp only [Step]
      constructor
      · rintro ⟨l,member,⟨source,target,below⟩ | ⟨target,source,below⟩⟩
        · exact ⟨l,member,.inr ⟨target,source,(below_inv_iff h closed l.role r).mp below⟩⟩
        · refine ⟨l,member,.inl ⟨source,target,?_⟩⟩
          have := (below_inv_iff h closed (inv l.role) r).mp below
          rwa [Rowl.Concepts.inv_inv] at this
      · rintro ⟨l,member,⟨source,target,below⟩ | ⟨target,source,below⟩⟩
        · refine ⟨l,member,.inr ⟨target,source,?_⟩⟩
          rw [below_inv_iff h closed,Rowl.Concepts.inv_inv]
          exact below
        · exact ⟨l,member,.inl ⟨source,target,(below_inv_iff h closed l.role r).mpr below⟩⟩
    | inr L =>
      simp only [Step,Compatible,Rowl.Concepts.inv_inv]
      exact And.comm
  | inr L =>
    cases y with
    | inl b =>
      simp only [Step,Compatible,Rowl.Concepts.inv_inv]
      exact And.comm
    | inr L' =>
      simp only [Step,Compatible,Rowl.Concepts.inv_inv]
      exact And.comm

theorem rel_inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (count : Nat)
    (nodes : List completion.Node) (r : ObjectPropertyExpression) (x y : Element count nodes) :
    Rel P h count nodes (inv r) x y ↔ Rel P h count nodes r y x := by
  have path : ∀ t, Relation.TransGen (Step P h count nodes (inv t)) x y ↔
      Relation.TransGen (Step P h count nodes t) y x := by
    intro t
    have same : Function.swap (Step P h count nodes t) = Step P h count nodes (inv t) := by
      funext a b
      exact propext (step_inv P h closed count nodes t a b).symm
    rw [← same,Relation.transGen_swap]
  unfold Rel
  rw [step_inv P h closed count nodes r x y]
  apply or_congr_right
  constructor
  · rintro ⟨t,transitive,below,steps⟩
    refine ⟨inv t,closed.2.2 t transitive,(below_inv_iff h closed t r).mp below,?_⟩
    have := (path (inv t)).mp (by rwa [Rowl.Concepts.inv_inv])
    exact this
  · rintro ⟨t,transitive,below,steps⟩
    refine ⟨inv t,closed.2.2 t transitive,?_,?_⟩
    · rw [below_inv_iff h closed,Rowl.Concepts.inv_inv]; exact below
    · exact (path t).mpr steps

/-- The model relates along every role expression exactly as `Rel`. -/
theorem relation_model (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (count : Nat)
    (nodes : List completion.Node) (root : Element count nodes) (r : ObjectPropertyExpression)
    (x y : Element count nodes) :
    objectRelation (model P h count nodes root) r x y ↔ Rel P h count nodes r x y := by
  cases r with
  | Property p => rfl
  | Inverse p =>
    show Rel P h count nodes (.Property p) y x ↔ Rel P h count nodes (.Inverse p) x y
    exact (rel_inv P h closed count nodes (.Property p) x y).symm

theorem step_mono (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (count : Nat)
    (nodes : List completion.Node) {s r : ObjectPropertyExpression} (included : Below h s r)
    (x y : Element count nodes) : Step P h count nodes s x y → Step P h count nodes r x y := by
  have inverse : Below h (inv s) (inv r) := closed.2.1 s r included
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      rintro ⟨l,member,⟨source,target,below⟩ | ⟨target,source,below⟩⟩
      · exact ⟨l,member,.inl ⟨source,target,closed.1 _ _ _ below included⟩⟩
      · exact ⟨l,member,.inr ⟨target,source,closed.1 _ _ _ below included⟩⟩
    | inr L =>
      rintro ⟨first,second⟩
      exact ⟨edgeOk_mono _ h closed _ _ included first,edgeOk_mono _ h closed _ _ inverse second⟩
  | inr L =>
    cases y with
    | inl b =>
      rintro ⟨first,second⟩
      exact ⟨edgeOk_mono _ h closed _ _ included first,edgeOk_mono _ h closed _ _ inverse second⟩
    | inr L' =>
      rintro ⟨first,second⟩
      exact ⟨edgeOk_mono _ h closed _ _ included first,edgeOk_mono _ h closed _ _ inverse second⟩

theorem rel_mono (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (count : Nat)
    (nodes : List completion.Node) {s r : ObjectPropertyExpression} (included : Below h s r)
    (x y : Element count nodes) : Rel P h count nodes s x y → Rel P h count nodes r x y := by
  rintro (step | ⟨t,transitive,below,steps⟩)
  · exact .inl (step_mono P h closed count nodes included x y step)
  · exact .inr ⟨t,transitive,closed.1 _ _ _ below included,steps⟩

theorem rel_trans (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (count : Nat)
    (nodes : List completion.Node) {t : ObjectPropertyExpression} (transitive : t ∈ transitives h)
    {x y z : Element count nodes} (first : Rel P h count nodes t x y) (second : Rel P h count nodes t y z) :
    Rel P h count nodes t x z := by
  have along : ∀ a b, Rel P h count nodes t a b → Relation.TransGen (Step P h count nodes t) a b := by
    intro a b
    rintro (step | ⟨t',_,below,steps⟩)
    · exact .single step
    · exact Relation.TransGen.mono (fun c d => step_mono P h closed count nodes below c d) steps
  exact .inr ⟨t,transitive,below_refl h t,(along x y first).trans (along y z second)⟩

/-- The model respects a closed hierarchy. -/
theorem model_respects (P : completion.Problem) (h : hierarchy.RoleHierarchy) (closed : Closed h) (count : Nat)
    (nodes : List completion.Node) (root : Element count nodes) : Respects (model P h count nodes root) h := by
  refine ⟨?_,?_⟩
  · intro s r listed x y related
    rw [relation_model P h closed] at related ⊢
    exact rel_mono P h closed count nodes (.inr listed) x y related
  · intro t transitive x y z first second
    rw [relation_model P h closed] at first second ⊢
    exact rel_trans P h closed count nodes transitive first second

/-- Every element's label is the label of a node. -/
theorem lab_node {count : Nat} {nodes : List completion.Node} (x : Element count nodes) :
    ∃ y, lab x = labelOf nodes y ∧ (∀ n, nodes[y]? = some n → n.tree = false → y < count) := by
  cases x with
  | inl a => exact ⟨a.val,rfl,fun _ _ _ => a.property⟩
  | inr L =>
    obtain ⟨y,n,at_y,tree,_,same⟩ := (family_mem nodes L.val).mp L.property
    refine ⟨y,same,?_⟩
    intro n' at_y' named
    rw [at_y] at at_y'
    cases at_y'
    rw [tree] at named
    cases named

theorem treePath_named (nodes : List completion.Node) (a : Nat) (n : completion.Node) (at_a : nodes[a]? = some n)
    (named : n.tree = false) : treePath nodes a = [] := by
  rw [treePath.eq_def,at_a]
  simp [named]

theorem treePath_self (nodes : List completion.Node) (p : Nat) (n : completion.Node) (at_p : nodes[p]? = some n)
    (tree : n.tree = true) : p ∈ treePath nodes p := by
  rw [treePath.eq_def,at_p]
  simp only [tree,↓reduceIte]
  split <;> simp

theorem treePath_parent (nodes : List completion.Node) (w : Nat) (n : completion.Node) (at_w : nodes[w]? = some n)
    (tree : n.tree = true) (below : n.parent.val < w) : treePath nodes w = w :: treePath nodes n.parent.val := by
  rw [treePath.eq_def,at_w]
  simp [tree,dif_pos below]

/-- A step of the model satisfies what its source requires along the role. -/
theorem step_ok (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (shape : Shape P h count nodes) (complete : Complete P h nodes) (r : ObjectPropertyExpression)
    (x y : Element count nodes) : Step P h count nodes r x y → EdgeOk P.entries.val h (lab x) r (lab y) := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      rintro ⟨l,member,⟨source,target,below⟩ | ⟨target,source,below⟩⟩
      · have inside := shape.links l member
        have edge := (complete.2.1 l member (by have := shape.countIn; omega) (by have := shape.countIn; omega)).1
        rw [source,target] at edge
        exact edgeOk_mono _ h shape.closed _ _ below edge
      · have inside := shape.links l member
        have edge := (complete.2.1 l member (by have := shape.countIn; omega) (by have := shape.countIn; omega)).2
        rw [source,target] at edge
        exact edgeOk_mono _ h shape.closed _ _ below edge
    | inr L => exact fun step => step.1
  | inr L =>
    cases y with
    | inl b => exact fun step => step.1
    | inr L' => exact fun step => step.1

/-- The two ends of a tree edge are compatible along every role that includes
    the role that created the child, read from parent to child. -/
theorem tree_compatible (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat)
    (nodes : List completion.Node) (shape : Shape P h count nodes) (complete : Complete P h nodes) (y : Nat)
    (n : completion.Node) (at_y : nodes[y]? = some n) (tree : n.tree = true) (s r : ObjectPropertyExpression)
    (role : createdRole P.entries.val n = some s) (parentIn : n.parent.val < nodes.length) :
    (Below h s r → Compatible P.entries.val h (labelOf nodes n.parent.val) r (labelOf nodes y)) ∧
    (Below h (inv s) r → Compatible P.entries.val h (labelOf nodes y) r (labelOf nodes n.parent.val)) := by
  obtain ⟨down,up⟩ := complete.2.2.1 y n s at_y tree role parentIn
  refine ⟨fun below => ⟨edgeOk_mono _ h shape.closed _ _ below down,
    edgeOk_mono _ h shape.closed _ _ (shape.closed.2.1 s r below) up⟩,fun below => ⟨?_,?_⟩⟩
  · exact edgeOk_mono _ h shape.closed _ _ below up
  · exact edgeOk_mono _ h shape.closed _ _ ((below_inv_iff h shape.closed s r).mpr below) down

/-- Every existential restriction of an element has a successor in the model
    that satisfies its filler. -/
theorem witness (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (shape : Shape P h count nodes) (complete : Complete P h nodes) (x : Element count nodes) (c : Usize)
    (member : c ∈ lab x) (r : ObjectPropertyExpression) (f : Usize)
    (at_c : P.entries.val[c.val]? = some (.Exists r f)) :
    ∃ y, Step P h count nodes r x y ∧ Holds P.entries.val (lab y) f.val := by
  -- A tree node that is not blocked, or the node blocking it, gives an element.
  have element : ∀ (w y0 : Nat) (nw ny : completion.Node), nodes[w]? = some nw → ¬ Blocked nodes w →
      nodes[y0]? = some ny → ny.tree = true → ny.parent.val = w →
      ∃ L : {L : List Usize // L ∈ family nodes}, SameLabel (labelOf nodes y0) L.val := by
    intro w y0 nw ny at_w free at_y0 tree parent
    by_cases blocked : Blocked nodes y0
    · obtain ⟨v,onPath,same⟩ := child_blocked nodes w y0 ny at_y0 parent blocked free
      obtain ⟨nv,at_v,vTree⟩ := treePath_tree nodes w v onPath
      have vFree : ¬ Blocked nodes v := fun vBlocked => free (blocked_down nodes w v onPath vBlocked)
      exact ⟨⟨labelOf nodes v,(family_mem nodes _).mpr ⟨v,nv,at_v,vTree,vFree,rfl⟩⟩,same⟩
    · exact ⟨⟨labelOf nodes y0,(family_mem nodes _).mpr ⟨y0,ny,at_y0,tree,blocked,rfl⟩⟩,fun _ => Iff.rfl⟩
  have sameEdge : ∀ (A B B' : List Usize), SameLabel B B' → Compatible P.entries.val h A r B →
      Compatible P.entries.val h A r B' := by
    intro A B B' same compatible
    exact ⟨edgeOk_same _ h _ _ _ _ r (fun _ => Iff.rfl) same compatible.1,
      edgeOk_same _ h _ _ _ _ (inv r) same (fun _ => Iff.rfl) compatible.2⟩
  cases x with
  | inl a =>
    have aIn : a.val < nodes.length := by have := shape.countIn; have := a.property; omega
    obtain ⟨na,at_a⟩ : ∃ na, nodes[a.val]? = some na := ⟨_,List.getElem?_eq_getElem aIn⟩
    have named : na.tree = false := (shape.named a.val na at_a).mpr a.property
    have free := named_free nodes a.val na at_a named
    obtain ⟨y0,neighbour,holds⟩ := complete.2.2.2 a.val aIn free c member r f at_c
    rcases neighbour with ⟨ny,at_y0,tree,parent,s,role,below⟩ | ⟨nx,at_a',tree,_⟩ |
        ⟨l,linked,source,target,_,below⟩ | ⟨l,linked,target,source,_,below⟩
    · obtain ⟨L,same⟩ := element a.val y0 na ny at_a free at_y0 tree parent
      refine ⟨.inr L,?_,(holds_same _ _ _ same f.val).mp holds⟩
      have compatible := (tree_compatible P h count nodes shape complete y0 ny at_y0 tree s r role
        (by rw [parent]; exact aIn)).1 below
      rw [parent] at compatible
      exact sameEdge _ _ _ same compatible
    · rw [at_a] at at_a'
      cases at_a'
      rw [named] at tree
      cases tree
    · have bIn := (shape.links l linked).2
      refine ⟨.inl ⟨y0,by rw [← target]; exact bIn⟩,⟨l,linked,.inl ⟨source,target,below⟩⟩,holds⟩
    · have bIn := (shape.links l linked).1
      refine ⟨.inl ⟨y0,by rw [← source]; exact bIn⟩,⟨l,linked,.inr ⟨target,source,below⟩⟩,holds⟩
  | inr L =>
    obtain ⟨w,nw,at_w,wTree,free,labelIs⟩ := (family_mem nodes L.val).mp L.property
    have wIn : w < nodes.length := (List.getElem?_eq_some_iff.mp at_w).1
    have memberW : c ∈ labelOf nodes w := by rw [← labelIs]; exact member
    obtain ⟨y0,neighbour,holds⟩ := complete.2.2.2 w wIn free c memberW r f at_c
    rcases neighbour with ⟨ny,at_y0,tree,parent,s,role,below⟩ | ⟨nx,at_w',tree,parent,yIn,s,role,below⟩ |
        ⟨l,linked,source,_,_,_⟩ | ⟨l,linked,target,_,_,_⟩
    · obtain ⟨L',same⟩ := element w y0 nw ny at_w free at_y0 tree parent
      refine ⟨.inr L',?_,(holds_same _ _ _ same f.val).mp holds⟩
      have compatible := (tree_compatible P h count nodes shape complete y0 ny at_y0 tree s r role
        (by rw [parent]; exact wIn)).1 below
      rw [parent,← labelIs] at compatible
      exact sameEdge _ _ _ same compatible
    · rw [at_w] at at_w'
      cases at_w'
      have compatible := (tree_compatible P h count nodes shape complete w nw at_w wTree s r role
        (by rw [parent]; exact yIn)).2 below
      rw [parent,← labelIs] at compatible
      obtain ⟨np,at_p⟩ : ∃ np, nodes[y0]? = some np := ⟨_,List.getElem?_eq_getElem yIn⟩
      cases pTree : np.tree with
      | false =>
        have pNamed := (shape.named y0 np at_p).mp pTree
        exact ⟨.inl ⟨y0,pNamed⟩,compatible,holds⟩
      | true =>
        have below' := shape.parents w nw at_w wTree
        rw [parent] at below'
        have onPath : y0 ∈ treePath nodes w := by
          rw [treePath_parent nodes w nw at_w wTree (by rw [parent]; exact below'),parent]
          exact List.mem_cons_of_mem _ (treePath_self nodes y0 np at_p pTree)
        have pFree : ¬ Blocked nodes y0 := fun blocked => free (blocked_down nodes w y0 onPath blocked)
        exact ⟨.inr ⟨labelOf nodes y0,(family_mem nodes _).mpr ⟨y0,np,at_p,pTree,pFree,rfl⟩⟩,compatible,holds⟩
    · have := (shape.links l linked).1
      have notNamed := (shape.named w nw at_w).not.mp (by rw [wTree]; simp)
      omega
    · have := (shape.links l linked).2
      have notNamed := (shape.named w nw at_w).not.mp (by rw [wTree]; simp)
      omega

/-- The truth lemma: every element satisfies every entry its label satisfies. -/
theorem truth (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (shape : Shape P h count nodes) (complete : Complete P h nodes) (root : Element count nodes) :
    ∀ (c : Nat) (x : Element count nodes), Holds P.entries.val (lab x) c →
      denote (model P h count nodes root) (meaning P.entries.val c) x := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro x holds
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
        obtain ⟨y,labelIs,_⟩ := lab_node x
        rw [labelIs] at member listed
        exact shape.clashFree y i member j listed (.NotAtom k) (.Atom k) (by rw [value]; exact at_c) at_j
          (show Complementary (.NotAtom k) (.Atom k) from rfl)
      | And a b =>
        simp only at holds
        rw [dif_pos (below a.val (by simp [parts])),dif_pos (below b.val (by simp [parts]))] at holds
        exact ⟨ih a.val (below a.val (by simp [parts])) x holds.1,ih b.val (below b.val (by simp [parts])) x holds.2⟩
      | Or a b =>
        simp only at holds
        rw [dif_pos (below a.val (by simp [parts])),dif_pos (below b.val (by simp [parts]))] at holds
        rcases holds with one | two
        · exact .inl (ih a.val (below a.val (by simp [parts])) x one)
        · exact .inr (ih b.val (below b.val (by simp [parts])) x two)
      | Exists r f =>
        obtain ⟨i,member,value⟩ := holds
        obtain ⟨y,step,fillerHolds⟩ := witness P h count nodes shape complete x i member r f (by rw [value]; exact at_c)
        refine ⟨y,(relation_model P h shape.closed count nodes root r x y).mpr (.inl step),?_⟩
        exact ih f.val (below f.val (by simp [parts])) y fillerHolds
      | Forall r f =>
        obtain ⟨i,member,value⟩ := holds
        have at_i : P.entries.val[i.val]? = some (.Forall r f) := by rw [value]; exact at_c
        intro y related
        rw [relation_model P h shape.closed count nodes root r x y] at related
        apply ih f.val (below f.val (by simp [parts])) y
        rcases related with step | ⟨t,transitive,tr,steps⟩
        · exact (step_ok P h count nodes shape complete r x y step i member r f at_i (below_refl h r)).1
        · obtain ⟨j0,at_j0⟩ := shape.closedTable i.val r f at_i t transitive tr
          have along : ∀ z, Relation.TransGen (Step P h count nodes t) x z →
              Holds P.entries.val (lab z) f.val ∧ HasUniversal P.entries.val (lab z) t f := by
            intro z steps
            induction steps with
            | single step =>
              obtain ⟨holds,through⟩ := step_ok P h count nodes shape complete t x _ step i member r f at_i tr
              exact ⟨holds,through t transitive (below_refl h t) tr ⟨j0,at_j0⟩⟩
            | tail _ step ih' =>
              obtain ⟨_,⟨j,listed,at_j⟩⟩ := ih'
              obtain ⟨holds,through⟩ := step_ok P h count nodes shape complete t _ _ step j listed t f at_j
                (below_refl h t)
              exact ⟨holds,through t transitive (below_refl h t) (below_refl h t) ⟨j.val,at_j⟩⟩
          exact (along y steps).1
      | AtLeast m r f | AtMost m r f _ =>
        -- Labels list only literals, and a cardinality restriction is none.
        exfalso
        obtain ⟨i,member,value⟩ := holds
        obtain ⟨y,labelIs,_⟩ := lab_node x
        rw [labelIs] at member
        obtain ⟨e',at_i,literal⟩ := shape.literals y i member
        rw [value,at_c] at at_i
        cases at_i
        exact literal

theorem lab_in {count : Nat} {nodes : List completion.Node} (countIn : count ≤ nodes.length) (x : Element count nodes) :
    ∃ y, y < nodes.length ∧ lab x = labelOf nodes y := by
  cases x with
  | inl a => exact ⟨a.val,by have := a.property; omega,rfl⟩
  | inr L =>
    obtain ⟨y,n,at_y,_,_,same⟩ := (family_mem nodes L.val).mp L.property
    exact ⟨y,(List.getElem?_eq_some_iff.mp at_y).1,same⟩

/-- A literal is satisfied exactly when it is listed. -/
theorem holds_literal (entries : List concept_table.Entry) (L : List Usize) (i : Usize) (e : concept_table.Entry)
    (at_i : entries[i.val]? = some e) (literal : Literal e) (member : i ∈ L) : Holds entries L i.val := by
  rw [holds_listed entries L i.val e at_i]
  · exact ⟨i,member,rfl⟩
  · intro a b
    cases e <;> simp_all [Literal]
  · cases e <;> simp_all [Literal]
  · cases e <;> simp_all [Literal]

/-- A complete, clash-free graph of the right shape with a named node has a
    model: it respects the hierarchy and satisfies the TBox concept at every
    element, every unfolding, every requirement at its node, every link and the
    label of every named node; without role axioms it relates named nodes only
    along links, and different named nodes are different elements. -/
theorem model_of_complete (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat)
    (nodes : List completion.Node) (shape : Shape P h count nodes) (complete : Complete P h nodes)
    (positive : 0 < count) :
    ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
      Respects I h ∧
      (∀ y, denote I (meaning P.entries.val P.axioms.val) y) ∧
      (∀ u ∈ P.unfoldings.val, ∀ y, I.classes u.class y → denote I (meaning P.entries.val u.concept.val) y) ∧
      (∀ q ∈ P.requirements.val, denote I (meaning P.entries.val q.concept.val) (π q.node.val)) ∧
      (∀ l ∈ P.links.val, objectRelation I l.role (π l.from.val) (π l.to.val)) ∧
      (∀ a < count, ∀ i ∈ labelOf nodes a, denote I (meaning P.entries.val i.val) (π a)) ∧
      (h.inclusions.val = [] → h.transitive.val = [] → ∀ r a b, a < count → b < count →
        objectRelation I r (π a) (π b) → ∃ l ∈ P.links.val,
          (l.from.val = a ∧ l.to.val = b ∧ l.role = r) ∨ (l.to.val = a ∧ l.from.val = b ∧ inv l.role = r)) ∧
      (∀ a b, a < count → b < count → π a = π b → a = b) := by
  let root : Element count nodes := .inl ⟨0,positive⟩
  let π : Nat → Element count nodes := fun a => if inside : a < count then .inl ⟨a,inside⟩ else root
  have named : ∀ a (inside : a < count), π a = .inl ⟨a,inside⟩ := by
    intro a inside
    simp only [π,dif_pos inside]
  refine ⟨Element count nodes,model P h count nodes root,π,model_respects P h shape.closed count nodes root,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · intro y
    obtain ⟨node,nodeIn,labelIs⟩ := lab_in shape.countIn y
    apply truth P h count nodes shape complete root P.axioms.val y
    rw [labelIs]
    exact complete.1 node nodeIn P.axioms (.inr (.inl rfl))
  · intro u member y classes
    obtain ⟨node,nodeIn,labelIs⟩ := lab_in shape.countIn y
    apply truth P h count nodes shape complete root u.concept.val y
    have atom : HasAtom P.entries.val (labelOf nodes node) u.class := by
      have : HasAtom P.entries.val (lab y) u.class := classes
      rwa [labelIs] at this
    rw [labelIs]
    exact complete.1 node nodeIn u.concept (.inr (.inr ⟨u,member,atom,rfl⟩))
  · intro q member
    have inside := shape.requirements q member
    rw [named _ inside]
    apply truth P h count nodes shape complete root q.concept.val
    exact complete.1 q.node.val (by have := shape.countIn; omega) q.concept (.inl ⟨q,member,rfl,rfl⟩)
  · intro l member
    obtain ⟨fromIn,toIn⟩ := shape.links l member
    rw [named _ fromIn,named _ toIn,relation_model P h shape.closed count nodes root]
    exact .inl ⟨l,member,.inl ⟨rfl,rfl,below_refl h l.role⟩⟩
  · intro a inside i member
    rw [named _ inside]
    apply truth P h count nodes shape complete root i.val
    obtain ⟨e,at_i,literal⟩ := shape.literals a i member
    exact holds_literal P.entries.val _ i e at_i literal member
  · intro noInclusions noTransitive r a b aIn bIn related
    rw [named _ aIn,named _ bIn,relation_model P h shape.closed count nodes root] at related
    have equal : ∀ s q, Below h s q → s = q := by
      intro s q below
      rcases below with same | listed
      · exact same
      · simp [Rowl.Hierarchy.inclusionList,noInclusions] at listed
    rcases related with ⟨l,member,⟨source,target,below⟩ | ⟨target,source,below⟩⟩ | ⟨t,transitive,_,_⟩
    · exact ⟨l,member,.inl ⟨source,target,equal _ _ below⟩⟩
    · exact ⟨l,member,.inr ⟨target,source,equal _ _ below⟩⟩
    · simp [transitives,noTransitive] at transitive
  · intro a b aIn bIn same
    rw [named _ aIn,named _ bIn] at same
    injection same with same
    injection same
end Rowl.CompletionModel
