import Rowl.CompletionModel

/-!
The completion graph tableau: totality, soundness and completeness of `run`.
`run` terminates on every graph of the right shape: every rule application
either adds a literal to a label or creates a tree node for an existential
restriction without a witness, and both decrease a measure that weights each
node by the remaining room below it, which equality blocking bounds. An answer
`true` comes with a model of what the named nodes need (`NamedModel`); an answer
`false` rules out every model, in any universes, that places every node of the
graph (`FullModel`). `satisfiable` interns the facts, the TBox concept and the
definitions, closes the table under the transitive roles, starts from one blank
named node per individual and runs the tableau; its answer is proved exact
against the facts, links, TBox concept, definitions and role hierarchy it was
given.
-/
namespace Rowl.Completion
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation objectRelation)
open Rowl.Concepts (inv relation_inv denote)
open Rowl.Hierarchy (Below Closed Respects transitives below_refl respects_below)
open Rowl.ConceptTable (WellFormed meaning meaning_at rebuild TransitiveClosed parts)
open Rowl.CompletionSearch
open Rowl.CompletionModel (Shape Literal model_of_complete holds_literal treePath_tree blocked_down treePath_parent
  treePath_self treePath_named)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
universe u v

private theorem usize_max_val : (core.num.Usize.MAX).val = Usize.max := by
  simp [core.num.Usize.MAX]

/-- The table indices still to be added. -/
def pendingList : completion.Pending → List Usize
  | .Empty => []
  | .Item c next => c :: pendingList next

/-- An interpretation, in any universes, with a placement of every node: it
    respects the role hierarchy, the TBox concept and the unfoldings hold
    everywhere, every requirement and link holds, every label holds at its node,
    every tree node is reached from its parent along the role that created it,
    and the extra entries hold at node `x`. -/
def FullModel (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (x : Nat)
    (extra : List Usize) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
    Respects I h ∧
    (∀ y, denote I (meaning P.entries.val P.axioms.val) y) ∧
    (∀ w ∈ P.unfoldings.val, ∀ y, I.classes w.class y → denote I (meaning P.entries.val w.concept.val) y) ∧
    (∀ q ∈ P.requirements.val, denote I (meaning P.entries.val q.concept.val) (π q.node.val)) ∧
    (∀ l ∈ P.links.val, objectRelation I l.role (π l.from.val) (π l.to.val)) ∧
    (∀ y, ∀ i ∈ labelOf nodes y, denote I (meaning P.entries.val i.val) (π y)) ∧
    (∀ y n s, nodes[y]? = some n → n.tree = true → createdRole P.entries.val n = some s →
      objectRelation I s (π n.parent.val) (π y)) ∧
    (∀ c ∈ extra, denote I (meaning P.entries.val c.val) (π x))

/-- A model in `Type` of what the named nodes need: it respects the role
    hierarchy, the TBox concept and the unfoldings hold everywhere, every
    requirement and link holds, the label of every named node holds at it, and
    without role axioms named nodes are related only along links. -/
def NamedModel (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node) :
    Prop :=
  ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
    Respects I h ∧
    (∀ y, denote I (meaning P.entries.val P.axioms.val) y) ∧
    (∀ w ∈ P.unfoldings.val, ∀ y, I.classes w.class y → denote I (meaning P.entries.val w.concept.val) y) ∧
    (∀ q ∈ P.requirements.val, denote I (meaning P.entries.val q.concept.val) (π q.node.val)) ∧
    (∀ l ∈ P.links.val, objectRelation I l.role (π l.from.val) (π l.to.val)) ∧
    (∀ a < count, ∀ i ∈ labelOf nodes a, denote I (meaning P.entries.val i.val) (π a)) ∧
    (h.inclusions.val = [] → h.transitive.val = [] → ∀ r a b, a < count → b < count →
      objectRelation I r (π a) (π b) → ∃ l ∈ P.links.val,
        (l.from.val = a ∧ l.to.val = b ∧ l.role = r) ∨ (l.to.val = a ∧ l.from.val = b ∧ inv l.role = r))

theorem copy_label_correct (label : alloc.vec.Vec Usize) (index : Usize) (out : alloc.vec.Vec Usize)
    (copied : out.val = label.val.take index.val) (inside : index.val ≤ label.val.length) :
    completion.copy_label label index out = .ok label := by
  rw [completion.copy_label]
  by_cases more : index.val < label.val.length
  · have lookup : label.index_usize index = .ok label.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have shorter : out.val.length < Usize.max := by
      rw [copied]; simp; have := label.property; scalar_tac
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out label.val[index.val] shorter)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := copy_label_correct label next appended
      (by rw [contents,copied,nextIndex,List.take_succ_eq_append_getElem more]) (by omega)
    have room : out.val.length < Usize.max := shorter
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,push,advance,rest]
  · have full : index.val = label.val.length := by omega
    have same : out = label := by
      apply (alloc.vec.Vec.eq_iff out label).mpr
      rw [copied,full,List.take_length]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,same]
termination_by label.val.length - index.val
decreasing_by omega

theorem copy_nodes_correct (nodes : alloc.vec.Vec completion.Node) (index : Usize) (out : alloc.vec.Vec completion.Node)
    (copied : out.val = nodes.val.take index.val) (inside : index.val ≤ nodes.val.length) :
    completion.copy_nodes nodes index out = .ok nodes := by
  rw [completion.copy_nodes]
  by_cases more : index.val < nodes.val.length
  · have lookup : nodes.index_usize index = .ok nodes.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    have room : out.val.length < Usize.max := by
      rw [copied]; simp; have := nodes.property; scalar_tac
    have labelCopy := copy_label_correct nodes.val[index.val].label 0#usize (alloc.vec.Vec.new Usize) (by simp)
      (by simp)
    have same : (⟨nodes.val[index.val].label,nodes.val[index.val].parent,nodes.val[index.val].via,
        nodes.val[index.val].tree⟩ : completion.Node) = nodes.val[index.val] := rfl
    obtain ⟨appended,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec out nodes.val[index.val] room)
    obtain ⟨next,advance,nextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nextIndex : next.val = index.val+1 := by simpa using nextValue
    have rest := copy_nodes_correct nodes next appended
      (by rw [contents,copied,nextIndex,List.take_succ_eq_append_getElem more]) (by omega)
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room,
      alloc.vec.Vec.index_slice_index,lookup,bind_ok,labelCopy,same,push,advance,rest]
  · have full : index.val = nodes.val.length := by omega
    have same : out = nodes := by
      apply (alloc.vec.Vec.eq_iff out nodes).mpr
      rw [copied,full,List.take_length]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,same]
termination_by nodes.val.length - index.val
decreasing_by omega

theorem copy_pending_correct (pending : completion.Pending) : completion.copy_pending pending = .ok pending := by
  induction pending with
  | Empty => rw [completion.copy_pending]
  | Item c next ih => rw [completion.copy_pending]; simp [ih]

theorem filler_of_correct (entries : alloc.vec.Vec concept_table.Entry) (i : Usize) :
    completion.filler_of entries i =
      .ok (match entries.val[i.val]? with
        | some (.Exists _ f) => some f
        | _ => none) := by
  rw [completion.filler_of]
  by_cases inside : i.val < entries.val.length
  · have lookup : entries.index_usize i = .ok entries.val[i.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    rw [List.getElem?_eq_getElem inside]
    cases entry : entries.val[i.val] <;> simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,entry]
  · rw [List.getElem?_eq_none_iff.mpr (by omega)]
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]

/-- Inserting into a label appends the item to that label and changes nothing
    else; `None` only without room. -/
theorem insert_correct (nodes : alloc.vec.Vec completion.Node) (x item : Usize) :
    ∃ r, completion.insert nodes x item = .ok r ∧ ∀ nodes', r = some nodes' →
      ∃ inside : x.val < nodes.val.length, ∃ label : alloc.vec.Vec Usize,
        label.val = nodes.val[x.val].label.val ++ [item] ∧
        nodes'.val = nodes.val.set x.val { nodes.val[x.val] with label := label } := by
  rw [completion.insert]
  by_cases inside : x.val < nodes.val.length
  · have lookup : nodes.index_usize x = .ok nodes.val[x.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    by_cases room : nodes.val[x.val].label.val.length < Usize.max
    · obtain ⟨label,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec nodes.val[x.val].label item room)
      refine ⟨some (nodes.set x { nodes.val[x.val] with label := label }),?_,?_⟩
      · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
          lookup,bind_ok,usize_max_val,room,alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize,push]
        simp [push]
      · intro nodes' same
        cases same
        exact ⟨inside,label,contents,by simp⟩
    · refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,lookup,usize_max_val,room]
  · refine ⟨none,?_,by simp⟩
    simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside]

/-- In an interpretation where every listed literal holds at an element, every
    entry the label satisfies holds there too. -/
theorem holds_denote (entries : List concept_table.Entry) (wf : WellFormed entries) {Object : Type u}
    {Value : Type v} (I : Interpretation Object Value) (L : List Usize) (z : Object)
    (labelTrue : ∀ i ∈ L, denote I (meaning entries i.val) z) :
    ∀ c, Holds entries L c → denote I (meaning entries c) z := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro holds
    rw [Holds.eq_def] at holds
    cases at_c : entries[c]? with
    | none => rw [at_c] at holds; exact holds.elim
    | some e =>
      rw [at_c] at holds
      have below := wf c e at_c
      have listed : (∃ i ∈ L, i.val = c) → denote I (meaning entries c) z := by
        rintro ⟨i,member,value⟩
        rw [← value]
        exact labelTrue i member
      rw [meaning_at entries wf c e at_c]
      cases e with
      | Top => trivial
      | Bottom => exact holds.elim
      | And a b =>
        simp only at holds
        rw [dif_pos (below a.val (by simp [parts])),dif_pos (below b.val (by simp [parts]))] at holds
        exact ⟨ih a.val (below a.val (by simp [parts])) holds.1,ih b.val (below b.val (by simp [parts])) holds.2⟩
      | Or a b =>
        simp only at holds
        rw [dif_pos (below a.val (by simp [parts])),dif_pos (below b.val (by simp [parts]))] at holds
        rcases holds with one | two
        · exact .inl (ih a.val (below a.val (by simp [parts])) one)
        · exact .inr (ih b.val (below b.val (by simp [parts])) two)
      | Atom k =>
        have := listed holds
        rwa [meaning_at entries wf c _ at_c] at this
      | NotAtom k =>
        have := listed holds
        rwa [meaning_at entries wf c _ at_c] at this
      | Exists r f =>
        have := listed holds
        rwa [meaning_at entries wf c _ at_c] at this
      | Forall r f =>
        have := listed holds
        rwa [meaning_at entries wf c _ at_c] at this

/-- An entry that a label requires along an edge holds at the target of that
    edge, in every interpretation respecting the hierarchy where the label holds
    at the source. -/
theorem edge_need_holds {Object : Type u} {Value : Type v} (I : Interpretation Object Value)
    (h : hierarchy.RoleHierarchy) (respects : Respects I h) (entries : List concept_table.Entry)
    (wf : WellFormed entries) (L : List Usize) (r : ObjectPropertyExpression) (c : Usize) (a b : Object)
    (labelTrue : ∀ i ∈ L, denote I (meaning entries i.val) a) (edge : objectRelation I r a b)
    (needs : EdgeNeeds entries h L r c) : denote I (meaning entries c.val) b := by
  obtain ⟨i,member,q,f,at_i,included,kind⟩ := needs
  have universal := labelTrue i member
  rw [meaning_at entries wf i.val _ at_i] at universal
  rcases kind with rfl | ⟨t,transitive,first,second,at_c⟩
  · exact universal b (respects_below respects included edge)
  · rw [meaning_at entries wf c.val _ at_c]
    intro z next
    have along : objectRelation I t a b := respects_below respects first edge
    exact universal z (respects_below respects second (respects.2 t transitive a b z along next))

/-- Everything a node needs holds at its element in every interpretation that
    places every node. -/
theorem needs_hold {Object : Type u} {Value : Type v} (P : completion.Problem) (h : hierarchy.RoleHierarchy)
    (nodes : List completion.Node) (wf : WellFormed P.entries.val) (I : Interpretation Object Value)
    (π : Nat → Object) (respects : Respects I h)
    (axiomsHold : ∀ y, denote I (meaning P.entries.val P.axioms.val) y)
    (unfoldingsHold : ∀ w ∈ P.unfoldings.val, ∀ y, I.classes w.class y →
      denote I (meaning P.entries.val w.concept.val) y)
    (requirementsHold : ∀ q ∈ P.requirements.val, denote I (meaning P.entries.val q.concept.val) (π q.node.val))
    (linksHold : ∀ l ∈ P.links.val, objectRelation I l.role (π l.from.val) (π l.to.val))
    (labelsHold : ∀ y, ∀ i ∈ labelOf nodes y, denote I (meaning P.entries.val i.val) (π y))
    (treeHold : ∀ y n s, nodes[y]? = some n → n.tree = true → createdRole P.entries.val n = some s →
      objectRelation I s (π n.parent.val) (π y))
    (x : Nat) (c : Usize) (needs : Needs P h nodes x c) : denote I (meaning P.entries.val c.val) (π x) := by
  rcases needs with (⟨q,member,node,rfl⟩ | rfl | ⟨w,member,⟨i,listed,at_i⟩,rfl⟩) |
      ⟨l,member,_,_,⟨rfl,edgeNeeds⟩ | ⟨rfl,edgeNeeds⟩⟩ | ⟨y,n,s,at_y,tree,role,_,⟨rfl,edgeNeeds⟩ | ⟨rfl,edgeNeeds⟩⟩
  · rw [← node]; exact requirementsHold q member
  · exact axiomsHold (π x)
  · apply unfoldingsHold w member
    have := labelsHold x i listed
    rwa [meaning_at P.entries.val wf i.val _ at_i] at this
  · exact edge_need_holds I h respects P.entries.val wf _ l.role c (π l.from.val) (π l.to.val)
      (labelsHold l.from.val) (linksHold l member) edgeNeeds
  · exact edge_need_holds I h respects P.entries.val wf _ (inv l.role) c (π l.to.val) (π l.from.val)
      (labelsHold l.to.val) ((relation_inv I l.role _ _).mpr (linksHold l member)) edgeNeeds
  · exact edge_need_holds I h respects P.entries.val wf _ s c (π n.parent.val) (π x)
      (labelsHold n.parent.val) (treeHold x n s at_y tree role) edgeNeeds
  · exact edge_need_holds I h respects P.entries.val wf _ (inv s) c (π y) (π n.parent.val)
      (labelsHold y) ((relation_inv I s _ _).mpr (treeHold y n s at_y tree role)) edgeNeeds

/-- The number of tree nodes on the path from `y` to its named root. -/
def depth (nodes : List completion.Node) (y : Nat) : Nat := (treePath nodes y).length

/-- `nodes'` grows `nodes`: at least as many nodes, the same structure for the
    old ones, and every old label contained in the new one. -/
def Grows (nodes nodes' : List completion.Node) : Prop :=
  nodes.length ≤ nodes'.length ∧ ∀ (y : Nat) (n : completion.Node), nodes[y]? = some n → ∃ n' : completion.Node,
    nodes'[y]? = some n' ∧
    n'.parent = n.parent ∧ n'.via = n.via ∧ n'.tree = n.tree ∧ ∀ i ∈ n.label.val, i ∈ n'.label.val

theorem grows_refl (nodes : List completion.Node) : Grows nodes nodes :=
  ⟨le_refl _,fun _ n at_y => ⟨n,at_y,rfl,rfl,rfl,fun _ member => member⟩⟩

theorem grows_trans {a b c : List completion.Node} (first : Grows a b) (second : Grows b c) : Grows a c := by
  refine ⟨le_trans first.1 second.1,?_⟩
  intro y n at_y
  obtain ⟨n',at_y',parent',via',tree',labels'⟩ := first.2 y n at_y
  obtain ⟨n'',at_y'',parent'',via'',tree'',labels''⟩ := second.2 y n' at_y'
  exact ⟨n'',at_y'',parent''.trans parent',via''.trans via',tree''.trans tree',fun i member => labels'' i (labels' i member)⟩

theorem grows_label {nodes nodes' : List completion.Node} (grows : Grows nodes nodes') (y : Nat) :
    ∀ i ∈ labelOf nodes y, i ∈ labelOf nodes' y := by
  intro i member
  unfold labelOf at member ⊢
  cases at_y : nodes[y]? with
  | none => rw [at_y] at member; cases member
  | some n =>
    rw [at_y] at member
    obtain ⟨n',at_y',_,_,_,labels⟩ := grows.2 y n at_y
    rw [at_y']
    exact labels i member

theorem grows_treePath {nodes nodes' : List completion.Node} (grows : Grows nodes nodes') :
    ∀ y, y < nodes.length → treePath nodes' y = treePath nodes y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro inside
    obtain ⟨n,at_y⟩ : ∃ n, nodes[y]? = some n := ⟨_,List.getElem?_eq_getElem inside⟩
    obtain ⟨n',at_y',parent,_,tree,_⟩ := grows.2 y n at_y
    rw [treePath.eq_def,at_y',treePath.eq_def nodes,at_y]
    simp only [tree,parent]
    split
    · split
      · rename_i below
        rw [ih n.parent.val below (by omega)]
      · rfl
    · rfl

theorem holds_mono (entries : List concept_table.Entry) (L L' : List Usize) (sub : ∀ i ∈ L, i ∈ L') :
    ∀ c, Holds entries L c → Holds entries L' c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro holds
    rw [Holds.eq_def] at holds ⊢
    cases at_c : entries[c]? with
    | none => rw [at_c] at holds; exact holds
    | some e =>
      rw [at_c] at holds
      cases e with
      | And a b =>
        simp only at holds ⊢
        split at holds
        · split at holds
          · rename_i one two
            rw [dif_pos one,dif_pos two]
            exact ⟨ih a.val one holds.1,ih b.val two holds.2⟩
          · exact holds.elim
        · exact holds.elim
      | Or a b =>
        simp only at holds ⊢
        split at holds
        · split at holds
          · rename_i one two
            rw [dif_pos one,dif_pos two]
            exact holds.elim (fun x => .inl (ih a.val one x)) (fun x => .inr (ih b.val two x))
          · exact holds.elim
        · exact holds.elim
      | Top | Bottom => exact holds
      | Atom _ | NotAtom _ | Exists _ _ | Forall _ _ =>
        obtain ⟨i,member,value⟩ := holds
        exact ⟨i,sub i member,value⟩

/-- Witnesses survive growth. -/
theorem witnessed_mono (P : completion.Problem) (h : hierarchy.RoleHierarchy) {nodes nodes' : List completion.Node}
    (grows : Grows nodes nodes') (x : Nat) (r : ObjectPropertyExpression) (f : Usize) :
    Witnessed P h nodes x r f → Witnessed P h nodes' x r f := by
  rintro ⟨y,neighbour,holds⟩
  refine ⟨y,?_,holds_mono _ _ _ (grows_label grows y) f.val holds⟩
  rcases neighbour with ⟨ny,at_y,tree,parent,s,role,below⟩ | ⟨nx,at_x,tree,parent,yIn,s,role,below⟩ |
      ⟨l,member,source,target,yIn,below⟩ | ⟨l,member,target,source,yIn,below⟩
  · obtain ⟨ny',at_y',parent',via',tree',_⟩ := grows.2 y ny at_y
    refine .inl ⟨ny',at_y',by rw [tree']; exact tree,by rw [parent']; exact parent,s,?_,below⟩
    unfold createdRole at role ⊢
    rw [via']; exact role
  · obtain ⟨nx',at_x',parent',via',tree',_⟩ := grows.2 x nx at_x
    refine .inr (.inl ⟨nx',at_x',by rw [tree']; exact tree,by rw [parent']; exact parent,
      by have := grows.1; omega,s,?_,below⟩)
    unfold createdRole at role ⊢
    rw [via']; exact role
  · exact .inr (.inr (.inl ⟨l,member,source,target,by have := grows.1; omega,below⟩))
  · exact .inr (.inr (.inr ⟨l,member,target,source,by have := grows.1; omega,below⟩))

/-- The labels along the tree path of an unblocked node are pairwise different
    sets. -/
theorem path_distinct (nodes : List completion.Node) :
    ∀ x, ¬ Blocked nodes x →
      ((treePath nodes x).map (fun v => ((labelOf nodes v).map (·.val)).toFinset)).Nodup := by
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
              SameLabel (labelOf nodes x) (labelOf nodes v)) ∨ Blocked nodes n.parent.val) := by
            rw [Blocked.eq_def,at_x]
            simp only [dif_pos below]
          have parentFree : ¬ Blocked nodes n.parent.val := fun blocked => free (unfold.mpr ⟨tree,.inr blocked⟩)
          rw [List.map_cons,List.nodup_cons]
          refine ⟨?_,ih n.parent.val below parentFree⟩
          intro member
          rw [List.mem_map] at member
          obtain ⟨v,onPath,same⟩ := member
          apply free
          refine unfold.mpr ⟨tree,.inl ⟨v,onPath,?_⟩⟩
          intro i
          have := congrArg (fun S => i.val ∈ S) same
          simp only [List.mem_toFinset,List.mem_map] at this
          constructor
          · intro member
            obtain ⟨j,listed,value⟩ := this.mpr ⟨i,member,rfl⟩
            rwa [show j = i from UScalar.eq_of_val_eq value] at listed
          · intro member
            obtain ⟨j,listed,value⟩ := this.mp ⟨i,member,rfl⟩
            rwa [show j = i from UScalar.eq_of_val_eq value] at listed
        · rw [dif_neg below]
          simp
      · rw [if_neg tree]
        simp

/-- An unblocked node with labels of table indices has at most `2^n` tree nodes
    on its path. -/
theorem depth_le (nodes : List completion.Node) (n : Nat) (labelsIn : ∀ y, ∀ i ∈ labelOf nodes y, i.val < n)
    (x : Nat) (free : ¬ Blocked nodes x) : depth nodes x ≤ 2 ^ n := by
  have nodup := path_distinct nodes x free
  have sub : ∀ S ∈ (treePath nodes x).map (fun v => ((labelOf nodes v).map (·.val)).toFinset),
      S ∈ (Finset.range n).powerset := by
    intro S member
    rw [List.mem_map] at member
    obtain ⟨v,_,rfl⟩ := member
    rw [Finset.mem_powerset]
    intro k kIn
    simp only [List.mem_toFinset,List.mem_map] at kIn
    obtain ⟨i,listed,rfl⟩ := kIn
    exact Finset.mem_range.mpr (labelsIn v i listed)
  have card := Finset.card_le_card (show ((treePath nodes x).map
      (fun v => ((labelOf nodes v).map (·.val)).toFinset)).toFinset ⊆ (Finset.range n).powerset from
    fun S member => sub S (List.mem_toFinset.mp member))
  rw [List.toFinset_card_of_nodup nodup,List.length_map,Finset.card_powerset,Finset.card_range] at card
  exact card

/-- The existential restrictions of `y`'s label that have a witness. -/
noncomputable def witnessedCount (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node)
    (y : Nat) : Nat :=
  ((labelOf nodes y).filter (fun i => decide (∃ r f, P.entries.val[i.val]? = some (.Exists r f) ∧
    Witnessed P h nodes y r f))).length

/-- The weight of a node: the room below it, `(2n+2)^(2^n + 1 - depth)` for a
    table of `n` entries, times the room in it, `2n` minus its label and its
    witnessed existential restrictions. -/
noncomputable def weight (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node)
    (y : Nat) : Nat :=
  (2 * P.entries.val.length + 2) ^ (2 ^ P.entries.val.length + 1 - depth nodes y) *
    (2 * P.entries.val.length - (labelOf nodes y).length - witnessedCount P h nodes y)

/-- The termination measure: the sum of the weights. -/
noncomputable def measure (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) : Nat :=
  ∑ y ∈ Finset.range nodes.length, weight P h nodes y

theorem count_le (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (y : Nat) :
    witnessedCount P h nodes y ≤ (labelOf nodes y).length := List.length_filter_le _ _

/-- A label without repetitions of table indices has at most `n` items. -/
theorem label_le (L : List Usize) (n : Nat) (nodup : L.Nodup) (inside : ∀ i ∈ L, i.val < n) : L.length ≤ n := by
  have injective : (L.map (·.val)).Nodup := by
    apply List.Nodup.map _ nodup
    intro a b same
    exact UScalar.eq_of_val_eq same
  have card := Finset.card_le_card (show (L.map (·.val)).toFinset ⊆ Finset.range n from by
    intro k member
    simp only [List.mem_toFinset,List.mem_map] at member
    obtain ⟨i,listed,rfl⟩ := member
    exact Finset.mem_range.mpr (inside i listed))
  rw [List.toFinset_card_of_nodup injective,List.length_map,Finset.card_range] at card
  exact card

theorem count_mono (P : completion.Problem) (h : hierarchy.RoleHierarchy) {nodes nodes' : List completion.Node}
    (grows : Grows nodes nodes') (y : Nat) (nodup : (labelOf nodes y).Nodup) :
    witnessedCount P h nodes y ≤ witnessedCount P h nodes' y := by
  unfold witnessedCount
  apply List.Subperm.length_le
  apply List.Nodup.subperm (List.Nodup.filter _ nodup)
  intro i member
  rw [List.mem_filter] at member ⊢
  obtain ⟨listed,found⟩ := member
  refine ⟨grows_label grows y i listed,?_⟩
  rw [decide_eq_true_iff] at found ⊢
  obtain ⟨r,f,at_i,witnessed⟩ := found
  exact ⟨r,f,at_i,witnessed_mono P h grows y r f witnessed⟩

/-- Growth never increases the weight of an old node with a label of distinct
    table indices. -/
theorem weight_le (P : completion.Problem) (h : hierarchy.RoleHierarchy) {nodes nodes' : List completion.Node}
    (grows : Grows nodes nodes') (y : Nat) (inside : y < nodes.length) (nodup : (labelOf nodes y).Nodup) :
    weight P h nodes' y ≤ weight P h nodes y := by
  unfold weight depth
  rw [grows_treePath grows y inside]
  apply Nat.mul_le_mul_left
  have longer : (labelOf nodes y).length ≤ (labelOf nodes' y).length :=
    (List.Nodup.subperm nodup (grows_label grows y)).length_le
  have counts := count_mono P h grows y nodup
  omega

/-- A label that grows strictly makes the weight of its node drop. -/
theorem weight_lt (P : completion.Problem) (h : hierarchy.RoleHierarchy) {nodes nodes' : List completion.Node}
    (grows : Grows nodes nodes') (y : Nat) (inside : y < nodes.length) (nodup : (labelOf nodes y).Nodup)
    (nodup' : (labelOf nodes' y).Nodup) (labelsIn : ∀ i ∈ labelOf nodes' y, i.val < P.entries.val.length)
    (longer : (labelOf nodes y).length < (labelOf nodes' y).length) :
    weight P h nodes' y < weight P h nodes y := by
  unfold weight depth
  rw [grows_treePath grows y inside]
  apply Nat.mul_lt_mul_of_pos_left _ (pow_pos (by omega) _)
  have counts := count_mono P h grows y nodup
  have bounded := label_le _ _ nodup' labelsIn
  have counted := count_le P h nodes' y
  omega

/-- A node gains a witness for one of its existential restrictions: its weight
    drops by at least the room below it. -/
theorem weight_witness (P : completion.Problem) (h : hierarchy.RoleHierarchy) {nodes nodes' : List completion.Node}
    (grows : Grows nodes nodes') (x : Nat) (inside : x < nodes.length) (nodup : (labelOf nodes x).Nodup)
    (labelsIn : ∀ i ∈ labelOf nodes x, i.val < P.entries.val.length)
    (same : labelOf nodes' x = labelOf nodes x) (i : Usize) (member : i ∈ labelOf nodes x)
    (r : ObjectPropertyExpression) (f : Usize) (at_i : P.entries.val[i.val]? = some (.Exists r f))
    (missing : ¬ Witnessed P h nodes x r f) (found : Witnessed P h nodes' x r f) :
    weight P h nodes' x + (2 * P.entries.val.length + 2) ^ (2 ^ P.entries.val.length + 1 - depth nodes x) ≤
      weight P h nodes x := by
  have more : witnessedCount P h nodes x + 1 ≤ witnessedCount P h nodes' x := by
    unfold witnessedCount
    rw [same]
    have nodupFilter := List.Nodup.filter (fun i => decide (∃ r f, P.entries.val[i.val]? = some (.Exists r f) ∧
      Witnessed P h nodes x r f)) nodup
    have notIn : i ∉ (labelOf nodes x).filter (fun i => decide (∃ r f, P.entries.val[i.val]? = some (.Exists r f) ∧
        Witnessed P h nodes x r f)) := by
      rw [List.mem_filter,decide_eq_true_iff]
      rintro ⟨_,r',f',at_i',witnessed⟩
      rw [at_i] at at_i'
      simp only [Option.some.injEq,concept_table.Entry.Exists.injEq] at at_i'
      obtain ⟨rfl,rfl⟩ := at_i'
      exact missing witnessed
    have sub := List.Nodup.subperm (List.nodup_cons.mpr ⟨notIn,nodupFilter⟩) (show i ::
        (labelOf nodes x).filter (fun i => decide (∃ r f, P.entries.val[i.val]? = some (.Exists r f) ∧
          Witnessed P h nodes x r f)) ⊆ (labelOf nodes x).filter (fun i => decide (∃ r f,
            P.entries.val[i.val]? = some (.Exists r f) ∧ Witnessed P h nodes' x r f)) from by
      intro j listed
      rcases List.mem_cons.mp listed with rfl | later
      · rw [List.mem_filter,decide_eq_true_iff]
        exact ⟨member,r,f,at_i,found⟩
      · rw [List.mem_filter,decide_eq_true_iff] at later ⊢
        obtain ⟨listed',r',f',at_j,witnessed⟩ := later
        exact ⟨listed',r',f',at_j,witnessed_mono P h grows x r' f' witnessed⟩)
    have := sub.length_le
    simp only [List.length_cons] at this
    exact this
  have uncounted : witnessedCount P h nodes x + 1 ≤ (labelOf nodes x).length := by
    have := count_le P h nodes' x
    rw [same] at this
    omega
  have bounded := label_le _ _ nodup labelsIn
  unfold weight depth
  rw [grows_treePath grows x inside,same]
  have room : 1 ≤ 2 * P.entries.val.length - (labelOf nodes x).length - witnessedCount P h nodes x := by omega
  calc (2 * P.entries.val.length + 2) ^ (2 ^ P.entries.val.length + 1 - (treePath nodes x).length) *
          (2 * P.entries.val.length - (labelOf nodes x).length - witnessedCount P h nodes' x) +
        (2 * P.entries.val.length + 2) ^ (2 ^ P.entries.val.length + 1 - (treePath nodes x).length)
      = (2 * P.entries.val.length + 2) ^ (2 ^ P.entries.val.length + 1 - (treePath nodes x).length) *
          ((2 * P.entries.val.length - (labelOf nodes x).length - witnessedCount P h nodes' x) + 1) := by ring
    _ ≤ (2 * P.entries.val.length + 2) ^ (2 ^ P.entries.val.length + 1 - (treePath nodes x).length) *
          (2 * P.entries.val.length - (labelOf nodes x).length - witnessedCount P h nodes x) := by
        apply Nat.mul_le_mul_left
        omega

/-- Growing one label strictly, with the same nodes, decreases the measure. -/
theorem measure_lt_label (P : completion.Problem) (h : hierarchy.RoleHierarchy) {nodes nodes' : List completion.Node}
    (grows : Grows nodes nodes') (sameLength : nodes'.length = nodes.length)
    (nodup : ∀ y, (labelOf nodes y).Nodup) (nodup' : ∀ y, (labelOf nodes' y).Nodup)
    (labelsIn : ∀ y, ∀ i ∈ labelOf nodes' y, i.val < P.entries.val.length) (x : Nat) (inside : x < nodes.length)
    (longer : (labelOf nodes x).length < (labelOf nodes' x).length) : measure P h nodes' < measure P h nodes := by
  unfold measure
  rw [sameLength]
  apply Finset.sum_lt_sum
  · intro y member
    exact weight_le P h grows y (Finset.mem_range.mp member) (nodup y)
  · exact ⟨x,Finset.mem_range.mpr inside,weight_lt P h grows x inside (nodup x) (nodup' x) (labelsIn x) longer⟩

/-- A sum that drops by at least `d` at one index and nowhere grows. -/
theorem sum_drop (n x d : Nat) (inside : x < n) (f g : Nat → Nat) (le : ∀ y < n, g y ≤ f y)
    (drop : g x + d ≤ f x) : (∑ y ∈ Finset.range n, g y) + d ≤ ∑ y ∈ Finset.range n, f y := by
  have member : x ∈ Finset.range n := Finset.mem_range.mpr inside
  rw [← Finset.add_sum_erase _ g member,← Finset.add_sum_erase _ f member]
  have rest : (∑ y ∈ (Finset.range n).erase x, g y) ≤ ∑ y ∈ (Finset.range n).erase x, f y := by
    apply Finset.sum_le_sum
    intro y yIn
    exact le y (Finset.mem_range.mp (Finset.mem_of_mem_erase yIn))
  omega

/-- Creating a tree node that witnesses an existential restriction of its parent
    decreases the measure, whatever the new label, as long as the parent's path
    leaves room. -/
theorem measure_lt_child (P : completion.Problem) (h : hierarchy.RoleHierarchy) {nodes nodes' : List completion.Node}
    (grows : Grows nodes nodes') (longer : nodes'.length = nodes.length + 1)
    (sameLabels : ∀ y < nodes.length, labelOf nodes' y = labelOf nodes y)
    (nodup : ∀ y, (labelOf nodes y).Nodup) (labelsIn : ∀ y, ∀ i ∈ labelOf nodes y, i.val < P.entries.val.length)
    (x : Nat) (inside : x < nodes.length) (room : depth nodes x ≤ 2 ^ P.entries.val.length)
    (childDepth : depth nodes' nodes.length = depth nodes x + 1)
    (i : Usize) (member : i ∈ labelOf nodes x) (r : ObjectPropertyExpression) (f : Usize)
    (at_i : P.entries.val[i.val]? = some (.Exists r f)) (missing : ¬ Witnessed P h nodes x r f)
    (found : Witnessed P h nodes' x r f) : measure P h nodes' < measure P h nodes := by
  set n := P.entries.val.length
  set B := 2 * n + 2
  set k := 2 ^ n + 1 - depth nodes x
  have drop := weight_witness P h grows x inside (nodup x) (labelsIn x) (sameLabels x inside) i member r f at_i
    missing found
  have bounded : (∑ y ∈ Finset.range nodes.length, weight P h nodes' y) + B ^ k ≤
      ∑ y ∈ Finset.range nodes.length, weight P h nodes y :=
    sum_drop nodes.length x (B ^ k) inside (weight P h nodes) (weight P h nodes')
      (fun y yIn => weight_le P h grows y yIn (nodup y)) drop
  have newWeight : weight P h nodes' nodes.length < B ^ k := by
    unfold weight
    rw [childDepth]
    have positive : 1 ≤ k := by simp only [k]; omega
    have power : B ^ k = B ^ (2 ^ n + 1 - (depth nodes x + 1)) * B := by
      rw [← pow_succ]
      congr 1
      simp only [k]
      omega
    rw [power]
    apply Nat.mul_lt_mul_of_pos_left _ (pow_pos (by omega) _)
    simp only [B]
    omega
  unfold measure
  rw [longer,Finset.sum_range_succ]
  omega

/-- What `run` maintains: the shape the model needs, labels without repetitions,
    paths within the depth bound, and tree nodes created by existential entries. -/
structure Inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node) :
    Prop where
  shape : Shape P h count nodes
  nodup : ∀ y, (labelOf nodes y).Nodup
  deep : ∀ y < nodes.length, depth nodes y ≤ 2 ^ P.entries.val.length + 1
  roles : ∀ (y : Nat) (m : completion.Node), nodes[y]? = some m → m.tree = true →
    ∃ s f, P.entries.val[m.via.val]? = some (.Exists s f)

theorem labels_in {P : completion.Problem} {h : hierarchy.RoleHierarchy} {count : Nat} {nodes : List completion.Node}
    (shape : Shape P h count nodes) : ∀ y, ∀ i ∈ labelOf nodes y, i.val < P.entries.val.length := by
  intro y i member
  obtain ⟨e,at_i,_⟩ := shape.literals y i member
  exact (List.getElem?_eq_some_iff.mp at_i).1

theorem complementary_symm (a b : concept_table.Entry) : Complementary a b → Complementary b a := by
  cases a <;> cases b <;> simp [Complementary] <;> intro same <;> exact same.symm

theorem complementary_irrefl (e : concept_table.Entry) : ¬ Complementary e e := by
  cases e <;> simp [Complementary]

/-- The graph after inserting an item into one label. -/
theorem set_label (nodes : List completion.Node) (x : Nat) (inside : x < nodes.length) (label : alloc.vec.Vec Usize) :
    let nodes' := nodes.set x { nodes[x] with label := label }
    nodes'.length = nodes.length ∧ (∀ y, y ≠ x → nodes'[y]? = nodes[y]?) ∧
      nodes'[x]? = some { nodes[x] with label := label } ∧
      (∀ y, labelOf nodes' y = if y = x then label.val else labelOf nodes y) := by
  intro nodes'
  have length : nodes'.length = nodes.length := List.length_set ..
  have other : ∀ y, y ≠ x → nodes'[y]? = nodes[y]? := by
    intro y different
    exact List.getElem?_set_ne (Ne.symm different)
  have here : nodes'[x]? = some { nodes[x] with label := label } := by
    simp [nodes',List.getElem?_set_self inside]
  refine ⟨length,other,here,?_⟩
  intro y
  by_cases same : y = x
  · subst same
    simp [labelOf,here]
  · simp only [same,↓reduceIte]
    unfold labelOf
    rw [other y same]

/-- Inserting a new literal without a clash keeps the invariant, grows the graph
    and grows exactly that label. -/
theorem insert_inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (inv : Inv P h count nodes) (x : Nat) (inside : x < nodes.length) (item : Usize) (e : concept_table.Entry)
    (at_item : P.entries.val[item.val]? = some e) (literal : Literal e) (fresh : item ∉ labelOf nodes x)
    (noClash : ¬ Clashes P.entries.val (labelOf nodes x) item) (label : alloc.vec.Vec Usize)
    (labelIs : label.val = nodes[x].label.val ++ [item]) (nodes' : List completion.Node)
    (isSet : nodes' = nodes.set x { nodes[x] with label := label }) :
    Inv P h count nodes' ∧ Grows nodes nodes' ∧ nodes'.length = nodes.length ∧
      (∀ y, y ≠ x → labelOf nodes' y = labelOf nodes y) ∧ labelOf nodes' x = labelOf nodes x ++ [item] := by
  obtain ⟨length,other,here,labels⟩ := set_label nodes x inside label
  rw [← isSet] at length other here labels
  have hereLabel : labelOf nodes x = nodes[x].label.val := by simp [labelOf,List.getElem?_eq_getElem inside]
  have newLabel : labelOf nodes' x = labelOf nodes x ++ [item] := by
    rw [labels x]; simp [labelIs,hereLabel]
  have oldLabels : ∀ y, y ≠ x → labelOf nodes' y = labelOf nodes y := by
    intro y different; rw [labels y]; simp [different]
  have structure' : ∀ (y : Nat) (n : completion.Node), nodes[y]? = some n → ∃ n' : completion.Node, nodes'[y]? = some n' ∧
      n'.parent = n.parent ∧ n'.via = n.via ∧ n'.tree = n.tree ∧ n'.label.val = labelOf nodes' y := by
    intro y n at_y
    by_cases same : y = x
    · subst same
      rw [List.getElem?_eq_getElem inside] at at_y
      cases at_y
      refine ⟨_,here,rfl,rfl,rfl,?_⟩
      simp [labelOf,here]
    · refine ⟨n,by rw [other y same]; exact at_y,rfl,rfl,rfl,?_⟩
      simp [labelOf,other y same,at_y]
  have grows : Grows nodes nodes' := by
    refine ⟨by rw [length],?_⟩
    intro y n at_y
    obtain ⟨n',at_y',parent,via,tree,label'⟩ := structure' y n at_y
    refine ⟨n',at_y',parent,via,tree,?_⟩
    intro i member
    rw [label']
    by_cases same : y = x
    · subst same
      rw [newLabel]
      have : i ∈ labelOf nodes y := by simp [labelOf,at_y,member]
      exact List.mem_append_left _ this
    · rw [oldLabels y same]
      simp [labelOf,at_y,member]
  have back : ∀ (y : Nat) (n' : completion.Node), nodes'[y]? = some n' → ∃ n : completion.Node, nodes[y]? = some n ∧
      n'.parent = n.parent ∧ n'.via = n.via ∧ n'.tree = n.tree := by
    intro y n' at_y'
    have yIn : y < nodes.length := by rw [← length]; exact (List.getElem?_eq_some_iff.mp at_y').1
    obtain ⟨n'',at_y'',parent,via,tree,_⟩ := structure' y nodes[y] (List.getElem?_eq_getElem yIn)
    rw [at_y'] at at_y''
    cases at_y''
    exact ⟨nodes[y],List.getElem?_eq_getElem yIn,parent,via,tree⟩
  have shape := inv.shape
  refine ⟨⟨⟨shape.wellFormed,shape.closedTable,shape.closed,?_,by rw [length]; exact shape.countIn,?_,shape.links,
      shape.requirements,?_,?_⟩,?_,?_,?_⟩,grows,length,oldLabels,newLabel⟩
  · intro y n' at_y'
    obtain ⟨n,at_y,_,_,tree⟩ := back y n' at_y'
    rw [tree]; exact shape.named y n at_y
  · intro y n' at_y' isTree
    obtain ⟨n,at_y,parent,_,tree⟩ := back y n' at_y'
    rw [parent]; exact shape.parents y n at_y (by rw [← tree]; exact isTree)
  · intro y i member
    by_cases same : y = x
    · subst same
      rw [newLabel] at member
      rcases List.mem_append.mp member with old | new
      · exact shape.literals y i old
      · simp only [List.mem_singleton] at new
        subst new
        exact ⟨e,at_item,literal⟩
    · rw [oldLabels y same] at member
      exact shape.literals y i member
  · intro y i member j listed e1 e2 at_i at_j
    by_cases same : y = x
    · subst same
      rw [newLabel] at member listed
      rcases List.mem_append.mp member with old | new
      · rcases List.mem_append.mp listed with old' | new'
        · exact shape.clashFree y i old j old' e1 e2 at_i at_j
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
      exact shape.clashFree y i member j listed e1 e2 at_i at_j
  · intro y
    by_cases same : y = x
    · subst same
      rw [newLabel]
      exact List.nodup_append.mpr ⟨inv.nodup y,List.nodup_singleton _,by
        intro a member b single
        simp only [List.mem_singleton] at single
        subst single
        intro equal; subst equal; exact fresh member⟩
    · rw [oldLabels y same]; exact inv.nodup y
  · intro y yIn
    have : depth nodes' y = depth nodes y := by
      unfold depth
      rw [grows_treePath grows y (by rw [← length]; exact yIn)]
    rw [this]
    exact inv.deep y (by rw [← length]; exact yIn)
  · intro y n' at_y' isTree
    obtain ⟨n,at_y,_,via,tree⟩ := back y n' at_y'
    rw [via]
    exact inv.roles y n at_y (by rw [← tree]; exact isTree)

/-- Appending a tree node below an unblocked node for an existential entry keeps
    the invariant and grows the graph; the child is one level deeper. -/
theorem create_inv (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (inv : Inv P h count nodes) (x : Nat) (inside : x < nodes.length) (free : ¬ Blocked nodes x) (i : Usize)
    (r : ObjectPropertyExpression) (f : Usize) (at_i : P.entries.val[i.val]? = some (.Exists r f)) (parent : Usize)
    (parentIs : parent.val = x) (nodes1 : List completion.Node)
    (isPush : nodes1 = nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) :
    Inv P h count nodes1 ∧ Grows nodes nodes1 ∧ nodes1.length = nodes.length + 1 ∧
      (∀ y < nodes.length, labelOf nodes1 y = labelOf nodes y) ∧ labelOf nodes1 nodes.length = [] ∧
      depth nodes1 nodes.length = depth nodes x + 1 ∧
      nodes1[nodes.length]? = some (⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node) := by
  subst isPush
  have shape := inv.shape
  have old : ∀ y, y < nodes.length → (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)])[y]? =
      nodes[y]? := fun y yIn => List.getElem?_append_left yIn
  have new : (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)])[nodes.length]? =
      some ⟨alloc.vec.Vec.new Usize,parent,i,true⟩ := by simp
  have beyond : ∀ y, nodes.length < y →
      (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)])[y]? = none := by
    intro y yOut
    apply List.getElem?_eq_none_iff.mpr
    simp; omega
  have labelsOld : ∀ y < nodes.length,
      labelOf (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) y = labelOf nodes y := by
    intro y yIn
    unfold labelOf
    rw [old y yIn]
  have labelNew : labelOf (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) nodes.length = [] := by
    simp [labelOf,new]
  have labelBeyond : ∀ y, nodes.length < y →
      labelOf (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) y = [] := by
    intro y yOut
    simp [labelOf,beyond y yOut]
  have grows : Grows nodes (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) := by
    refine ⟨by simp,?_⟩
    intro y n at_y
    have yIn : y < nodes.length := (List.getElem?_eq_some_iff.mp at_y).1
    exact ⟨n,by rw [old y yIn]; exact at_y,rfl,rfl,rfl,fun _ member => member⟩
  have childDepth : depth (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) nodes.length =
      depth nodes x + 1 := by
    unfold depth
    rw [treePath_parent _ nodes.length _ new rfl (by simp only []; omega)]
    simp only [List.length_cons]
    rw [parentIs,grows_treePath grows x inside]
  have labelsIn := labels_in shape
  have shallow := depth_le nodes P.entries.val.length labelsIn x free
  -- Every index is old, the new one, or beyond.
  have cases' : ∀ y, y < nodes.length ∨ y = nodes.length ∨ nodes.length < y := by intro y; omega
  refine ⟨⟨⟨shape.wellFormed,shape.closedTable,shape.closed,?_,by simp; have := shape.countIn; omega,?_,shape.links,
      shape.requirements,?_,?_⟩,?_,?_,?_⟩,grows,by simp,labelsOld,labelNew,childDepth,new⟩
  · intro y n at_y
    rcases cases' y with yIn | rfl | yOut
    · rw [old y yIn] at at_y; exact shape.named y n at_y
    · rw [new] at at_y
      cases at_y
      have := shape.countIn
      simp only [Bool.true_eq_false,false_iff]
      omega
    · rw [beyond y yOut] at at_y; cases at_y
  · intro y n at_y isTree
    rcases cases' y with yIn | rfl | yOut
    · rw [old y yIn] at at_y; exact shape.parents y n at_y isTree
    · rw [new] at at_y
      cases at_y
      simp only []
      omega
    · rw [beyond y yOut] at at_y; cases at_y
  · intro y j member
    rcases cases' y with yIn | rfl | yOut
    · rw [labelsOld y yIn] at member; exact shape.literals y j member
    · rw [labelNew] at member; cases member
    · rw [labelBeyond y yOut] at member; cases member
  · intro y j member k listed e1 e2 at_j at_k
    rcases cases' y with yIn | rfl | yOut
    · rw [labelsOld y yIn] at member listed; exact shape.clashFree y j member k listed e1 e2 at_j at_k
    · rw [labelNew] at member; cases member
    · rw [labelBeyond y yOut] at member; cases member
  · intro y
    rcases cases' y with yIn | rfl | yOut
    · rw [labelsOld y yIn]; exact inv.nodup y
    · rw [labelNew]; exact List.nodup_nil
    · rw [labelBeyond y yOut]; exact List.nodup_nil
  · intro y yIn
    rcases cases' y with yOld | rfl | yOut
    · have : depth (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) y = depth nodes y := by
        unfold depth; rw [grows_treePath grows y yOld]
      rw [this]; exact inv.deep y yOld
    · rw [childDepth]; omega
    · simp at yIn; omega
  · intro y m at_y isTree
    rcases cases' y with yIn | rfl | yOut
    · rw [old y yIn] at at_y; exact inv.roles y m at_y isTree
    · rw [new] at at_y
      cases at_y
      exact ⟨r,f,at_i⟩
    · rw [beyond y yOut] at at_y; cases at_y

/-- A model of a grown graph is a model of the graph. -/
theorem namedModel_mono (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat)
    {nodes nodes' : List completion.Node} (grows : Grows nodes nodes') :
    NamedModel P h count nodes' → NamedModel P h count nodes := by
  rintro ⟨Object,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,exact⟩
  exact ⟨Object,I,π,respects,axiomsHold,unfoldings,requirements,links,
    fun a aIn i member => labels a aIn i (grows_label grows a i member),exact⟩

theorem fullModel_drop (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (x : Nat)
    (c : Usize) (rest : List Usize) : FullModel.{u,v} P h nodes x (c :: rest) → FullModel.{u,v} P h nodes x rest := by
  rintro ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,extra⟩
  exact ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,
    fun c' member => extra c' (List.mem_cons_of_mem _ member)⟩

theorem fullModel_any (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node)
    (x y : Nat) : FullModel.{u,v} P h nodes x [] → FullModel.{u,v} P h nodes y [] := by
  rintro ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,_⟩
  exact ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,by simp⟩

/-- A model with the inserted item at its node models the graph with the
    inserted item. -/
theorem fullModel_insert (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (x : Nat)
    (inside : x < nodes.length) (item : Usize) (rest : List Usize) (label : alloc.vec.Vec Usize)
    (labelIs : label.val = nodes[x].label.val ++ [item]) :
    FullModel.{u,v} P h nodes x (item :: rest) →
      FullModel.{u,v} P h (nodes.set x { nodes[x] with label := label }) x rest := by
  rintro ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,extra⟩
  obtain ⟨_,other,here,labelsNew⟩ := set_label nodes x inside label
  refine ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,?_,?_,
    fun c member => extra c (List.mem_cons_of_mem _ member)⟩
  · intro y i member
    rw [labelsNew y] at member
    by_cases same : y = x
    · subst same
      simp only [↓reduceIte,labelIs,List.mem_append,List.mem_singleton] at member
      rcases member with old | rfl
      · exact labels y i (by simp [labelOf,List.getElem?_eq_getElem inside,old])
      · exact extra _ (List.mem_cons_self ..)
    · simp only [same,↓reduceIte] at member
      exact labels y i member
  · intro y n s at_y isTree role
    by_cases same : y = x
    · subst same
      rw [here] at at_y
      cases at_y
      exact tree y nodes[y] s (List.getElem?_eq_getElem inside) isTree role
    · rw [other y same] at at_y
      exact tree y n s at_y isTree role

/-- A model of the graph has, at the element of a node, a witness for each of
    its existential restrictions, which models the graph with a child for it. -/
theorem fullModel_create (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node)
    (wf : WellFormed P.entries.val) (parents : ∀ (y : Nat) (n : completion.Node), nodes[y]? = some n → n.tree = true →
      n.parent.val < y)
    (requirementsIn : ∀ q ∈ P.requirements.val, q.node.val < nodes.length)
    (linksIn : ∀ l ∈ P.links.val, l.from.val < nodes.length ∧ l.to.val < nodes.length)
    (x : Nat) (inside : x < nodes.length) (i : Usize) (r : ObjectPropertyExpression) (f : Usize)
    (at_i : P.entries.val[i.val]? = some (.Exists r f)) (member : i ∈ labelOf nodes x) (parent : Usize)
    (parentIs : parent.val = x) :
    FullModel.{u,v} P h nodes 0 [] →
      FullModel.{u,v} P h (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)]) nodes.length
        [f,P.axioms] := by
  rintro ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,_⟩
  have existential := labels x i member
  rw [meaning_at P.entries.val wf i.val _ at_i] at existential
  obtain ⟨e,edge,fillerHolds⟩ := existential
  let π' : Nat → Object := fun y => if y < nodes.length then π y else e
  have old : ∀ y, y < nodes.length → π' y = π y := by intro y yIn; simp [π',yIn]
  have new : π' nodes.length = e := by simp [π']
  have oldNode : ∀ y, y < nodes.length → (nodes ++ [(⟨alloc.vec.Vec.new Usize,parent,i,true⟩ : completion.Node)])[y]? =
      nodes[y]? := fun y yIn => List.getElem?_append_left yIn
  refine ⟨Object,Value,I,π',respects,axiomsHold,unfoldings,?_,?_,?_,?_,?_⟩
  · intro q listed
    rw [old _ (requirementsIn q listed)]
    exact requirements q listed
  · intro l listed
    rw [old _ (linksIn l listed).1,old _ (linksIn l listed).2]
    exact links l listed
  · intro y j listed
    by_cases yIn : y < nodes.length
    · rw [old y yIn]
      apply labels y j
      unfold labelOf at listed ⊢
      rw [oldNode y yIn] at listed
      exact listed
    · unfold labelOf at listed
      by_cases same : y = nodes.length
      · subst same; simp at listed
      · rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at listed
        cases listed
  · intro y n s at_y isTree role
    by_cases yIn : y < nodes.length
    · rw [oldNode y yIn] at at_y
      have below := parents y n at_y isTree
      rw [old y yIn,old _ (by omega)]
      exact tree y n s at_y isTree role
    · by_cases same : y = nodes.length
      · subst same
        simp at at_y
        subst at_y
        simp only [createdRole,at_i,Option.some.injEq] at role
        subst role
        rw [new,parentIs,old x inside]
        exact edge
      · rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at at_y
        cases at_y
  · intro c listed
    rw [new]
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at listed
    rcases listed with rfl | rfl
    · exact fillerHolds
    · exact axiomsHold e

/-- An entry that a grown label satisfies and the old one does not makes the
    label strictly longer, when the old one has no repetitions. -/
theorem grow_strict (entries : List concept_table.Entry) (L L' : List Usize) (nodup : L.Nodup)
    (sub : ∀ i ∈ L, i ∈ L') (c : Nat) (now : Holds entries L' c) (before : ¬ Holds entries L c) :
    L.length < L'.length := by
  by_contra notLonger
  have perm := (List.Nodup.subperm nodup sub).perm_of_length_le (by omega)
  exact before (holds_mono entries L' L (fun i member => perm.mem_iff.mpr member) c now)

/-- The weight of pending entries: `3^c` for each entry `c`. -/
def pendingWeight (l : List Usize) : Nat := (l.map (fun c => 3 ^ c.val)).sum

/-- What a run of the tableau means: an acceptance comes with a model of what the
    named nodes need, and a rejection rules out every model, in any universes,
    that places every node with the extra entries at node `x`. -/
def Answers (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (nodes : List completion.Node)
    (x : Nat) (extra : List Usize) (r : Option Bool) : Prop :=
  (r = some true → NamedModel P h count nodes) ∧ (r = some false → ¬ FullModel.{u,v} P h nodes x extra)

theorem three_pow_lt (a b c : Nat) (ha : a < c) (hb : b < c) : 3 ^ a + 3 ^ b < 3 ^ c := by
  have one : 3 ^ a ≤ 3 ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have two : 3 ^ b ≤ 3 ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have three : 3 ^ c = 3 * 3 ^ (c - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have positive : 0 < 3 ^ (c - 1) := pow_pos (by omega) _
  omega

/-- A model of the graph with the extra entries also has entries implied by them. -/
theorem fullModel_imply (P : completion.Problem) (h : hierarchy.RoleHierarchy) (nodes : List completion.Node) (x : Nat)
    (extra extra' : List Usize)
    (implies : ∀ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (z : Object),
      (∀ c ∈ extra, denote I (meaning P.entries.val c.val) z) → ∀ c ∈ extra', denote I (meaning P.entries.val c.val) z) :
    FullModel.{u,v} P h nodes x extra → FullModel.{u,v} P h nodes x extra' := by
  rintro ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,extras⟩
  exact ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,
    implies Object Value I (π x) extras⟩

theorem add_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (M : Nat)
    (IH : ∀ nodes : alloc.vec.Vec completion.Node, measure P h nodes.val < M → Inv P h count nodes.val →
      ∃ r, completion.run P h nodes = .ok r ∧ Answers.{u,v} P h count nodes.val 0 [] r) :
    ∀ (w : Nat) (pending : completion.Pending) (nodes : alloc.vec.Vec completion.Node) (x : Usize),
      pendingWeight (pendingList pending) = w → Inv P h count nodes.val → x.val < nodes.val.length →
      (∀ nodes' : List completion.Node, Inv P h count nodes' → Grows nodes.val nodes' →
        nodes'.length = nodes.val.length → (∀ y, y ≠ x.val → labelOf nodes' y = labelOf nodes.val y) →
        (∀ c ∈ pendingList pending, Holds P.entries.val (labelOf nodes' x.val) c.val) → measure P h nodes' < M) →
      ∃ r, completion.add P h nodes x pending = .ok r ∧
        Answers.{u,v} P h count nodes.val x.val (pendingList pending) r := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro pending nodes x weight inv inside progress
  cases pending with
  | Empty =>
    obtain ⟨r,run,sound,complete⟩ := IH nodes
      (progress nodes.val inv (grows_refl _) rfl (fun _ _ => rfl) (by simp [pendingList])) inv
    exact ⟨r,by rw [completion.add]; exact run,sound,
      fun rejected model => complete rejected (fullModel_any P h nodes.val x.val 0 model)⟩
  | Item c next =>
    have wf := inv.shape.wellFormed
    by_cases cIn : c.val < P.entries.val.length
    · have lookup : P.entries.index_usize c = .ok P.entries.val[c.val] := by
        simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem cIn]
      have at_c : P.entries.val[c.val]? = some P.entries.val[c.val] := List.getElem?_eq_getElem cIn
      have below := wf c.val _ at_c
      have weightIs : pendingWeight (pendingList (.Item c next)) = 3 ^ c.val + pendingWeight (pendingList next) := by
        simp [pendingWeight,pendingList]
      -- A literal is added unless it is there or clashes.
      have literalCase : Literal P.entries.val[c.val] →
          ∃ r, completion.add_literal P h nodes x c next = .ok r ∧
            Answers.{u,v} P h count nodes.val x.val (c :: pendingList next) r := by
        intro literal
        have nodeLookup : nodes.index_usize x = .ok nodes.val[x.val] := by
          simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
        have labelIs : labelOf nodes.val x.val = nodes.val[x.val].label.val := by
          simp [labelOf,List.getElem?_eq_getElem inside]
        have smaller : pendingWeight (pendingList next) < w := by
          rw [← weight,weightIs]; have := pow_pos (show 0 < 3 by omega) c.val; omega
        rw [completion.add_literal]
        by_cases present : c ∈ labelOf nodes.val x.val
        · obtain ⟨r,run,sound,complete⟩ := ih _ smaller next nodes x rfl inv inside (by
            intro nodes' inv' grows' length' others' holds'
            apply progress nodes' inv' grows' length' others'
            intro c' member
            rcases List.mem_cons.mp member with rfl | later
            · exact holds_literal _ _ c' _ at_c literal (grows_label grows' x.val c' present)
            · exact holds' c' later)
          refine ⟨r,?_,sound,fun rejected model => complete rejected (fullModel_drop P h _ _ _ _ model)⟩
          rw [labelIs] at present
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
            nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,present,decide_true,run]
        · have absent : c ∉ nodes.val[x.val].label.val := by rwa [← labelIs]
          by_cases clash : Clashes P.entries.val (labelOf nodes.val x.val) c
          · refine ⟨some false,?_,by simp,?_⟩
            · rw [labelIs] at clash
              simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
                nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,absent,
                decide_false,Bool.false_eq_true,clashes_correct,clash,decide_true]
            · intro _
              rintro ⟨Object,Value,I,π,_,_,_,_,_,labels,_,extras⟩
              obtain ⟨j,listed,e,e',at_c',at_j,complementary⟩ := clash
              have here := extras c (List.mem_cons_self ..)
              have there := labels x.val j listed
              rw [meaning_at P.entries.val wf c.val e at_c'] at here
              rw [meaning_at P.entries.val wf j.val e' at_j] at there
              cases e <;> cases e' <;> simp only [Complementary] at complementary
              · subst complementary; exact there here
              · subst complementary; exact here there
          · obtain ⟨inserted,insertRun,insertSpec⟩ := insert_correct nodes x c
            cases inserted with
            | none =>
              refine ⟨none,?_,by simp,by simp⟩
              rw [labelIs] at clash
              simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
                nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,absent,
                decide_false,Bool.false_eq_true,clashes_correct,clash,insertRun]
            | some nodes1 =>
              obtain ⟨_,label,labelValue,shape1⟩ := insertSpec nodes1 rfl
              obtain ⟨inv1,grows1,length1,others1,new1⟩ := insert_inv P h count nodes.val inv x.val inside c
                P.entries.val[c.val] at_c literal present clash label labelValue nodes1.val shape1
              obtain ⟨r,run,sound,complete⟩ := ih _ smaller next nodes1 x rfl inv1 (by rw [length1]; exact inside)
                (by
                  intro nodes' inv' grows' length' others' holds'
                  apply progress nodes' inv' (grows_trans grows1 grows') (by rw [length',length1])
                    (fun y different => by rw [others' y different,others1 y different])
                  intro c' member
                  rcases List.mem_cons.mp member with rfl | later
                  · exact holds_literal _ _ c' _ at_c literal
                      (grows_label grows' x.val c' (by rw [new1]; exact List.mem_append_right _ (by simp)))
                  · exact holds' c' later)
              refine ⟨r,?_,fun accepted => namedModel_mono P h count grows1 (sound accepted),?_⟩
              · rw [labelIs] at clash
                simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,alloc.vec.Vec.index_slice_index,
                  nodeLookup,bind_ok,contains_correct,show (0#usize).val = 0 from rfl,List.drop_zero,absent,
                  decide_false,Bool.false_eq_true,clashes_correct,clash,insertRun,run]
              · intro rejected model
                apply complete rejected
                rw [shape1]
                exact fullModel_insert P h nodes.val x.val inside c (pendingList next) label labelValue model
      cases entry : P.entries.val[c.val] with
      | Top =>
        have smaller : pendingWeight (pendingList next) < w := by
          rw [← weight,weightIs]; have := pow_pos (show 0 < 3 by omega) c.val; omega
        obtain ⟨r,run,sound,complete⟩ := ih _ smaller next nodes x rfl inv inside (by
          intro nodes' inv' grows' length' others' holds'
          apply progress nodes' inv' grows' length' others'
          intro c' member
          rcases List.mem_cons.mp member with rfl | later
          · rw [Holds.eq_def,at_c,entry]; trivial
          · exact holds' c' later)
        refine ⟨r,?_,sound,fun rejected model => complete rejected (fullModel_drop P h _ _ _ _ model)⟩
        rw [completion.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | Bottom =>
        refine ⟨some false,?_,by simp,?_⟩
        · rw [completion.add]
          simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,lookup,entry]
        · intro _
          rintro ⟨Object,Value,I,π,_,_,_,_,_,_,_,extras⟩
          have here := extras c (List.mem_cons_self ..)
          rw [meaning_at P.entries.val wf c.val _ at_c,entry] at here
          exact here
      | And a b =>
        rw [entry] at below
        have aBelow : a.val < c.val := below a.val (by simp [parts])
        have bBelow : b.val < c.val := below b.val (by simp [parts])
        have smaller : pendingWeight (pendingList (.Item a (.Item b next))) < w := by
          rw [← weight,weightIs]
          have := three_pow_lt a.val b.val c.val aBelow bBelow
          simp [pendingWeight,pendingList] at this ⊢
          omega
        obtain ⟨r,run,sound,complete⟩ := ih _ smaller (.Item a (.Item b next)) nodes x rfl inv inside (by
          intro nodes' inv' grows' length' others' holds'
          apply progress nodes' inv' grows' length' others'
          intro c' member
          rcases List.mem_cons.mp member with rfl | later
          · rw [Holds.eq_def,at_c,entry]
            simp only [dif_pos aBelow,dif_pos bBelow]
            exact ⟨holds' a (by simp [pendingList]),holds' b (by simp [pendingList])⟩
          · exact holds' c' (by simp [pendingList,later]))
        refine ⟨r,?_,sound,?_⟩
        · rw [completion.add]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,entry,run]
        · intro rejected model
          apply complete rejected
          apply fullModel_imply P h nodes.val x.val _ _ _ model
          intro Object Value I z extras c' member
          have both := extras c (List.mem_cons_self ..)
          rw [meaning_at P.entries.val wf c.val _ at_c,entry] at both
          simp only [pendingList,List.mem_cons] at member
          rcases member with rfl | rfl | later
          · exact both.1
          · exact both.2
          · exact extras c' (List.mem_cons_of_mem _ later)
      | Or a b =>
        rw [entry] at below
        have aBelow : a.val < c.val := below a.val (by simp [parts])
        have bBelow : b.val < c.val := below b.val (by simp [parts])
        have smallerLeft : pendingWeight (pendingList (.Item a next)) < w := by
          rw [← weight,weightIs]
          have := Nat.pow_lt_pow_right (show 1 < 3 by omega) aBelow
          simp [pendingWeight,pendingList] at this ⊢
          omega
        have smallerRight : pendingWeight (pendingList (.Item b next)) < w := by
          rw [← weight,weightIs]
          have := Nat.pow_lt_pow_right (show 1 < 3 by omega) bBelow
          simp [pendingWeight,pendingList] at this ⊢
          omega
        have orHolds : ∀ (L : List Usize), (Holds P.entries.val L a.val ∨ Holds P.entries.val L b.val) →
            Holds P.entries.val L c.val := by
          intro L either
          rw [Holds.eq_def,at_c,entry]
          simp only [dif_pos aBelow,dif_pos bBelow]
          exact either
        have branchProgress : ∀ (d : Usize), (∀ (L : List Usize), Holds P.entries.val L d.val →
            Holds P.entries.val L c.val) →
            ∀ nodes' : List completion.Node, Inv P h count nodes' → Grows nodes.val nodes' →
              nodes'.length = nodes.val.length → (∀ y, y ≠ x.val → labelOf nodes' y = labelOf nodes.val y) →
              (∀ c' ∈ pendingList (.Item d next), Holds P.entries.val (labelOf nodes' x.val) c'.val) →
              measure P h nodes' < M := by
          intro d implies nodes' inv' grows' length' others' holds'
          apply progress nodes' inv' grows' length' others'
          intro c' member
          rcases List.mem_cons.mp member with rfl | later
          · exact implies _ (holds' d (List.mem_cons_self ..))
          · exact holds' c' (List.mem_cons_of_mem _ later)
        obtain ⟨left,leftRun,leftSound,leftComplete⟩ := ih _ smallerLeft (.Item a next) nodes x rfl inv inside
          (branchProgress a (fun L holds => orHolds L (.inl holds)))
        have code : completion.add P h nodes x (.Item c next) = completion.branch P h nodes x a b next := by
          rw [completion.add]
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,entry]
        rw [code,completion.branch]
        simp only [copy_nodes_correct nodes 0#usize (alloc.vec.Vec.new completion.Node) (by simp) (by simp),
          copy_pending_correct,bind_ok,leftRun]
        cases left with
        | none => exact ⟨none,rfl,by simp,by simp⟩
        | some accepted =>
          cases accepted with
          | true => exact ⟨some true,rfl,fun _ => leftSound rfl,by simp⟩
          | false =>
            obtain ⟨right,rightRun,rightSound,rightComplete⟩ := ih _ smallerRight (.Item b next) nodes x rfl inv inside
              (branchProgress b (fun L holds => orHolds L (.inr holds)))
            refine ⟨right,by simp [rightRun],rightSound,?_⟩
            intro rejected model
            obtain ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,extras⟩ := model
            have either := extras c (List.mem_cons_self ..)
            rw [meaning_at P.entries.val wf c.val _ at_c,entry] at either
            rcases either with one | two
            · apply leftComplete rfl
              refine ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,?_⟩
              intro c' member
              rcases List.mem_cons.mp member with rfl | later
              · exact one
              · exact extras c' (List.mem_cons_of_mem _ later)
            · apply rightComplete rejected
              refine ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,?_⟩
              intro c' member
              rcases List.mem_cons.mp member with rfl | later
              · exact two
              · exact extras c' (List.mem_cons_of_mem _ later)
      | Atom k =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [completion.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | NotAtom k =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [completion.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | Exists r' f =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [completion.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
      | Forall r' f =>
        obtain ⟨r,run,answers⟩ := literalCase (by rw [entry]; trivial)
        refine ⟨r,?_,answers⟩
        rw [completion.add]
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
          bind_ok,entry,run]
    · refine ⟨none,?_,by simp,by simp⟩
      rw [completion.add]
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,cIn]

/-- The main loop terminates on every graph satisfying the invariant, and its
    answer means what `Answers` says. -/
theorem run_correct (P : completion.Problem) (h : hierarchy.RoleHierarchy) (count : Nat) (positive : 0 < count) :
    ∀ (m : Nat) (nodes : alloc.vec.Vec completion.Node), measure P h nodes.val = m → Inv P h count nodes.val →
      ∃ r, completion.run P h nodes = .ok r ∧ Answers.{u,v} P h count nodes.val 0 [] r := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro nodes same inv
  have IH : ∀ nodes' : alloc.vec.Vec completion.Node, measure P h nodes'.val < m → Inv P h count nodes'.val →
      ∃ r, completion.run P h nodes' = .ok r ∧ Answers.{u,v} P h count nodes'.val 0 [] r :=
    fun nodes' smaller inv' => ih _ smaller nodes' rfl inv'
  have wf := inv.shape.wellFormed
  obtain ⟨step,stepRun,addCase,createCase,doneCase⟩ := next_step_correct P h nodes
  cases step with
  | Add x c =>
    obtain ⟨inside,needs,missing⟩ := addCase x c rfl
    obtain ⟨r,run,sound,complete⟩ := add_correct.{u,v} P h count m IH _ (.Item c .Empty) nodes x rfl inv inside
      (by
        intro nodes' inv' grows' length' _ holds'
        rw [← same]
        apply measure_lt_label P h grows' length' inv.nodup inv'.nodup (labels_in inv'.shape) x.val inside
        exact grow_strict P.entries.val _ _ (inv.nodup x.val) (grows_label grows' x.val) c.val
          (holds' c (by simp [pendingList])) missing)
    refine ⟨r,?_,sound,?_⟩
    · rw [completion.run,stepRun]
      simp only [bind_ok,run]
    · intro rejected model
      apply complete rejected
      obtain ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,_⟩ := model
      refine ⟨Object,Value,I,π,respects,axiomsHold,unfoldings,requirements,links,labels,tree,?_⟩
      intro c' member
      simp only [pendingList,List.mem_singleton] at member
      subst member
      exact needs_hold P h nodes.val wf I π respects axiomsHold unfoldings requirements links labels tree x.val c' needs
  | Create x i =>
    obtain ⟨inside,free,member,r',f,at_i,missing⟩ := createCase x i rfl
    have filler : completion.filler_of P.entries i = .ok (some f) := by
      rw [filler_of_correct,at_i]
    by_cases room : nodes.val.length < Usize.max
    · obtain ⟨nodes1,push,contents⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec nodes (⟨alloc.vec.Vec.new Usize,x,i,true⟩ : completion.Node) room)
      obtain ⟨inv1,grows1,length1,labels1,_,depth1,at_new⟩ := create_inv P h count nodes.val inv x.val inside free i r'
        f at_i x rfl nodes1.val contents
      have newIndex : (alloc.vec.Vec.len nodes).val = nodes.val.length := by simp
      have countIn := inv.shape.countIn
      obtain ⟨r,run,sound,complete⟩ := add_correct.{u,v} P h count m IH _ (.Item f (.Item P.axioms .Empty)) nodes1
        (alloc.vec.Vec.len nodes) rfl inv1 (by rw [newIndex,length1]; omega)
        (by
          intro nodes' inv' grows' length' others' holds'
          rw [← same,newIndex] at *
          obtain ⟨n',at_new',parent',via',tree',_⟩ := grows'.2 nodes.val.length _ at_new
          apply measure_lt_child P h (grows_trans grows1 grows') (by rw [length',length1])
            (fun y yIn => by rw [others' y (by omega),labels1 y yIn]) inv.nodup (labels_in inv.shape) x.val inside
            (depth_le nodes.val P.entries.val.length (labels_in inv.shape) x.val free)
            (by
              unfold depth
              rw [grows_treePath grows' nodes.val.length (by rw [length1]; omega)]
              exact depth1)
            i member r' f at_i missing
          refine ⟨nodes.val.length,.inl ⟨n',at_new',by rw [tree'],by rw [parent'],r',?_,below_refl h r'⟩,?_⟩
          · simp only [createdRole,via',at_i]
          · exact holds' f (by simp [pendingList]))
      refine ⟨r,?_,fun accepted => namedModel_mono P h count grows1 (sound accepted),?_⟩
      · rw [completion.run,stepRun]
        simp only [bind_ok,completion.create,filler,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room,
          ↓reduceIte,push,run]
      · intro rejected model
        apply complete rejected
        rw [newIndex,contents]
        exact fullModel_create P h nodes.val wf inv.shape.parents
          (fun q listed => by have := inv.shape.requirements q listed; omega)
          (fun l listed => by have := inv.shape.links l listed; omega)
          x.val inside i r' f at_i member x rfl model
    · refine ⟨none,?_,by simp,by simp⟩
      rw [completion.run,stepRun]
      simp [completion.create,filler,alloc.vec.Vec.len_val,UScalar.lt_equiv,usize_max_val,room]
  | Done =>
    obtain ⟨Object,I,π,body⟩ := model_of_complete P h count nodes.val inv.shape (doneCase rfl) positive
    refine ⟨some true,?_,fun _ => ⟨Object,I,π,body⟩,by simp⟩
    rw [completion.run,stepRun]
    simp

/-- The requirements are the facts, with each concept interned. -/
def Corresponds (facts : List completion.Fact) (entries : List concept_table.Entry)
    (requirements : List completion.Requirement) : Prop :=
  (∀ q ∈ requirements, q.concept.val < entries.length ∧
    ∃ f ∈ facts, q.node = f.node ∧ meaning entries q.concept.val = f.concept) ∧
  (∀ f ∈ facts, ∃ q ∈ requirements, q.node = f.node ∧ meaning entries q.concept.val = f.concept)

/-- The unfoldings are the definitions, with each concept interned. -/
def Unfolds (definitions : List completion.Definition) (entries : List concept_table.Entry)
    (unfoldings : List completion.Unfolding) : Prop :=
  (∀ w ∈ unfoldings, w.concept.val < entries.length ∧
    ∃ d ∈ definitions, w.class = d.class ∧ meaning entries w.concept.val = d.concept) ∧
  (∀ d ∈ definitions, ∃ w ∈ unfoldings, w.class = d.class ∧ meaning entries w.concept.val = d.concept)

theorem corresponds_append (facts : List completion.Fact) (entries more : List concept_table.Entry)
    (wf : WellFormed entries) (requirements : List completion.Requirement)
    (corresponds : Corresponds facts entries requirements) : Corresponds facts (entries ++ more) requirements := by
  obtain ⟨forward,backward⟩ := corresponds
  refine ⟨?_,?_⟩
  · intro q member
    obtain ⟨inside,f,listed,node,means⟩ := forward q member
    refine ⟨by simp; omega,f,listed,node,?_⟩
    rw [Rowl.ConceptTable.meaning_append entries more wf _ inside]; exact means
  · intro f listed
    obtain ⟨q,member,node,means⟩ := backward f listed
    refine ⟨q,member,node,?_⟩
    rw [Rowl.ConceptTable.meaning_append entries more wf _ (forward q member).1]; exact means

theorem unfolds_append (definitions : List completion.Definition) (entries more : List concept_table.Entry)
    (wf : WellFormed entries) (unfoldings : List completion.Unfolding)
    (unfolds : Unfolds definitions entries unfoldings) : Unfolds definitions (entries ++ more) unfoldings := by
  obtain ⟨forward,backward⟩ := unfolds
  refine ⟨?_,?_⟩
  · intro w member
    obtain ⟨inside,d,listed,same,means⟩ := forward w member
    refine ⟨by simp; omega,d,listed,same,?_⟩
    rw [Rowl.ConceptTable.meaning_append entries more wf _ inside]; exact means
  · intro d listed
    obtain ⟨w,member,same,means⟩ := backward d listed
    refine ⟨w,member,same,?_⟩
    rw [Rowl.ConceptTable.meaning_append entries more wf _ (forward w member).1]; exact means

theorem intern_facts_correct (facts : alloc.vec.Vec completion.Fact) (index : Usize)
    (entries : alloc.vec.Vec concept_table.Entry) (out : alloc.vec.Vec completion.Requirement)
    (wf : WellFormed entries.val) (inside : index.val ≤ facts.val.length)
    (corresponds : Corresponds (facts.val.take index.val) entries.val out.val) :
    ∃ r, completion.intern_facts entries facts index out = .ok r ∧ ∀ t requirements, r = some (t,requirements) →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more) ∧ Corresponds facts.val t.val requirements.val := by
  rw [completion.intern_facts]
  by_cases more : index.val < facts.val.length
  · have lookup : facts.index_usize index = .ok facts.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨interned,internRun,internSpec⟩ := Rowl.ConceptTable.intern_correct facts.val[index.val].concept entries wf
    cases interned with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,internRun]
    | some pair =>
      obtain ⟨t1,k⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,kIn,means⟩ := internSpec t1 k rfl
      by_cases room : out.val.length < Usize.max
      · obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out ⟨facts.val[index.val].node,k⟩ room)
        obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : index'.val = index.val+1 := by simpa using indexValue
        have corresponds1 : Corresponds (facts.val.take index'.val) t1.val out1.val := by
          rw [nextIndex,List.take_succ_eq_append_getElem more,contents,grows1]
          have old := corresponds_append _ entries.val more1 wf out.val corresponds
          obtain ⟨forward,backward⟩ := old
          refine ⟨?_,?_⟩
          · intro q member
            rcases List.mem_append.mp member with old | new
            · obtain ⟨inside',f,listed,node,meaning'⟩ := forward q old
              exact ⟨inside',f,List.mem_append_left _ listed,node,meaning'⟩
            · simp only [List.mem_singleton] at new
              subst new
              rw [← grows1]
              exact ⟨kIn,_,List.mem_append_right _ (List.mem_singleton_self _),rfl,means⟩
          · intro f listed
            rcases List.mem_append.mp listed with old | new
            · obtain ⟨q,member,node,meaning'⟩ := backward f old
              exact ⟨q,List.mem_append_left _ member,node,meaning'⟩
            · simp only [List.mem_singleton] at new
              subst new
              rw [← grows1]
              exact ⟨_,List.mem_append_right _ (List.mem_singleton_self _),rfl,means⟩
        obtain ⟨r,run,spec⟩ := intern_facts_correct facts index' t1 out1 wf1 (by omega) corresponds1
        refine ⟨r,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,internRun,uncurry_apply_pair,usize_max_val,room,push,advance,run]
        · intro t requirements same
          obtain ⟨wf2,⟨more2,grows2⟩,result⟩ := spec t requirements same
          exact ⟨wf2,⟨more1 ++ more2,by rw [grows2,grows1,List.append_assoc]⟩,result⟩
      · refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,internRun,usize_max_val,room]
  · refine ⟨some (entries,out),?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · intro t requirements same
      simp only [Option.some.injEq,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      refine ⟨wf,⟨[],by simp⟩,?_⟩
      rwa [List.take_of_length_le (by omega)] at corresponds
termination_by facts.val.length - index.val
decreasing_by omega

theorem intern_definitions_correct (definitions : alloc.vec.Vec completion.Definition) (index : Usize)
    (entries : alloc.vec.Vec concept_table.Entry) (out : alloc.vec.Vec completion.Unfolding)
    (wf : WellFormed entries.val) (inside : index.val ≤ definitions.val.length)
    (unfolds : Unfolds (definitions.val.take index.val) entries.val out.val) :
    ∃ r, completion.intern_definitions entries definitions index out = .ok r ∧ ∀ t unfoldings,
      r = some (t,unfoldings) →
      WellFormed t.val ∧ (∃ more, t.val = entries.val ++ more) ∧ Unfolds definitions.val t.val unfoldings.val := by
  rw [completion.intern_definitions]
  by_cases more : index.val < definitions.val.length
  · have lookup : definitions.index_usize index = .ok definitions.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem more]
    obtain ⟨interned,internRun,internSpec⟩ :=
      Rowl.ConceptTable.intern_correct definitions.val[index.val].concept entries wf
    cases interned with
    | none =>
      refine ⟨none,?_,by simp⟩
      simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,internRun]
    | some pair =>
      obtain ⟨t1,k⟩ := pair
      obtain ⟨wf1,⟨more1,grows1⟩,kIn,means⟩ := internSpec t1 k rfl
      by_cases room : out.val.length < Usize.max
      · obtain ⟨out1,push,contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec out ⟨definitions.val[index.val].class,k⟩ room)
        obtain ⟨index',advance,indexValue⟩ := WP.spec_imp_exists
          (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        have nextIndex : index'.val = index.val+1 := by simpa using indexValue
        have unfolds1 : Unfolds (definitions.val.take index'.val) t1.val out1.val := by
          rw [nextIndex,List.take_succ_eq_append_getElem more,contents,grows1]
          have old := unfolds_append _ entries.val more1 wf out.val unfolds
          obtain ⟨forward,backward⟩ := old
          refine ⟨?_,?_⟩
          · intro w member
            rcases List.mem_append.mp member with old | new
            · obtain ⟨inside',d,listed,same,meaning'⟩ := forward w old
              exact ⟨inside',d,List.mem_append_left _ listed,same,meaning'⟩
            · simp only [List.mem_singleton] at new
              subst new
              rw [← grows1]
              exact ⟨kIn,_,List.mem_append_right _ (List.mem_singleton_self _),rfl,means⟩
          · intro d listed
            rcases List.mem_append.mp listed with old | new
            · obtain ⟨w,member,same,meaning'⟩ := backward d old
              exact ⟨w,List.mem_append_left _ member,same,meaning'⟩
            · simp only [List.mem_singleton] at new
              subst new
              rw [← grows1]
              exact ⟨_,List.mem_append_right _ (List.mem_singleton_self _),rfl,means⟩
        obtain ⟨r,run,spec⟩ := intern_definitions_correct definitions index' t1 out1 wf1 (by omega) unfolds1
        have copied : ({ «class» := { iri := definitions.val[index.val].class.iri }, concept := k } :
            completion.Unfolding) = ⟨definitions.val[index.val].class,k⟩ := rfl
        refine ⟨r,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,alloc.vec.Vec.index_slice_index,lookup,
            bind_ok,internRun,uncurry_apply_pair,usize_max_val,room,Rowl.Nnf.copy_iri_identity,copied,push,advance,run]
        · intro t unfoldings same
          obtain ⟨wf2,⟨more2,grows2⟩,result⟩ := spec t unfoldings same
          exact ⟨wf2,⟨more1 ++ more2,by rw [grows2,grows1,List.append_assoc]⟩,result⟩
      · refine ⟨none,?_,by simp⟩
        simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,lookup,internRun,usize_max_val,room]
  · refine ⟨some (entries,out),?_,?_⟩
    · simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more]
    · intro t unfoldings same
      simp only [Option.some.injEq,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      refine ⟨wf,⟨[],by simp⟩,?_⟩
      rwa [List.take_of_length_le (by omega)] at unfolds
termination_by definitions.val.length - index.val
decreasing_by omega

/-- A named node with an empty label. -/
def blank : completion.Node := ⟨alloc.vec.Vec.new Usize,0#usize,0#usize,false⟩

theorem named_nodes_correct (count : Usize) (nodes : alloc.vec.Vec completion.Node)
    (inside : nodes.val.length ≤ count.val) (blanks : ∀ n ∈ nodes.val, n = blank) :
    ∃ nodes', completion.named_nodes count nodes = .ok (some nodes') ∧ nodes'.val.length = count.val ∧
      ∀ n ∈ nodes'.val, n = blank := by
  rw [completion.named_nodes]
  by_cases more : nodes.val.length < count.val
  · have room : nodes.val.length < Usize.max := by have := count.hBounds; scalar_tac
    obtain ⟨nodes1,push,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec nodes blank room)
    obtain ⟨result,run,length,all⟩ := named_nodes_correct count nodes1 (by rw [contents]; simp; omega)
      (by
        intro n member
        rw [contents] at member
        rcases List.mem_append.mp member with old | new
        · exact blanks n old
        · simpa using new)
    refine ⟨result,?_,length,all⟩
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,more,↓reduceIte,usize_max_val,room]
    exact (show alloc.vec.Vec.push nodes ⟨alloc.vec.Vec.new Usize,0#usize,0#usize,false⟩ = .ok nodes1 from push) ▸
      (by simp [run])
  · refine ⟨nodes,by simp [alloc.vec.Vec.len_val,UScalar.lt_equiv,more],by omega,blanks⟩
termination_by count.val - nodes.val.length
decreasing_by
  rw [contents]; simp; omega

/-- The completion graph tableau terminates; an acceptance comes with a model of
    the role hierarchy in which the TBox concept and every definition hold
    everywhere and every fact and link holds at the elements of its named nodes
    (and, without role axioms, named nodes are related only along links); a
    rejection rules out every such model, in any universes. -/
theorem satisfiable_correct (count : Usize) (facts : alloc.vec.Vec completion.Fact)
    (links : alloc.vec.Vec completion.Link) (axioms : concepts.Concept)
    (definitions : alloc.vec.Vec completion.Definition) (h : hierarchy.RoleHierarchy) (closed : Closed h)
    (positive : 0 < count.val) (factsIn : ∀ f ∈ facts.val, f.node.val < count.val)
    (linksIn : ∀ l ∈ links.val, l.from.val < count.val ∧ l.to.val < count.val) :
    ∃ r, completion.satisfiable count facts links axioms definitions h = .ok r ∧
      (r = some true → ∃ (Object : Type) (I : Interpretation Object Unit) (π : Nat → Object),
        Respects I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val)) ∧
        (h.inclusions.val = [] → h.transitive.val = [] → ∀ r a b, a < count.val → b < count.val →
          objectRelation I r (π a) (π b) → ∃ l ∈ links.val,
            (l.from.val = a ∧ l.to.val = b ∧ l.role = r) ∨ (l.to.val = a ∧ l.from.val = b ∧ inv l.role = r))) ∧
      (r = some false → ¬ ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (π : Nat → Object),
        Respects I h ∧ (∀ y, denote I axioms y) ∧
        (∀ d ∈ definitions.val, ∀ y, I.classes d.class y → denote I d.concept y) ∧
        (∀ f ∈ facts.val, denote I f.concept (π f.node.val)) ∧
        (∀ l ∈ links.val, objectRelation I l.role (π l.from.val) (π l.to.val))) := by
  have emptyTable : WellFormed (alloc.vec.Vec.new concept_table.Entry).val := by
    intro i e at_i
    simp at at_i
  obtain ⟨r0,run0,spec0⟩ := Rowl.ConceptTable.intern_correct axioms (alloc.vec.Vec.new concept_table.Entry) emptyTable
  cases r0 with
  | none => exact ⟨none,by rw [completion.satisfiable]; simp [run0],by simp,by simp⟩
  | some pair0 =>
  obtain ⟨t0,ax⟩ := pair0
  obtain ⟨wf0,_,axIn,axMeaning⟩ := spec0 t0 ax rfl
  obtain ⟨r1,run1,spec1⟩ := intern_facts_correct facts 0#usize t0 (alloc.vec.Vec.new completion.Requirement) wf0
    (by simp) (by simp [Corresponds])
  cases r1 with
  | none => exact ⟨none,by rw [completion.satisfiable]; simp [run0,run1],by simp,by simp⟩
  | some pair1 =>
  obtain ⟨t1,requirements⟩ := pair1
  obtain ⟨wf1,⟨more1,grows1⟩,corresponds1⟩ := spec1 t1 requirements rfl
  obtain ⟨r2,run2,spec2⟩ := intern_definitions_correct definitions 0#usize t1
    (alloc.vec.Vec.new completion.Unfolding) wf1 (by simp) (by simp [Unfolds])
  cases r2 with
  | none => exact ⟨none,by rw [completion.satisfiable]; simp [run0,run1,run2],by simp,by simp⟩
  | some pair2 =>
  obtain ⟨t2,unfoldings⟩ := pair2
  obtain ⟨wf2,⟨more2,grows2⟩,unfolds2⟩ := spec2 t2 unfoldings rfl
  obtain ⟨r3,run3,spec3⟩ := Rowl.ConceptTable.close_correct h t2 wf2
  cases r3 with
  | none => exact ⟨none,by rw [completion.satisfiable]; simp [run0,run1,run2,run3],by simp,by simp⟩
  | some t3 =>
  obtain ⟨wf3,⟨more3,grows3,_⟩,closedTable⟩ := spec3 t3 rfl
  obtain ⟨nodes0,run4,length0,blanks⟩ := named_nodes_correct count (alloc.vec.Vec.new completion.Node) (by simp)
    (by simp)
  let P : completion.Problem := { entries := t3, links, requirements, unfoldings, axioms := ax }
  have axMeaning3 : meaning t3.val ax.val = axioms := by
    have inside1 : ax.val < t1.val.length := by rw [grows1]; simp; omega
    have inside2 : ax.val < t2.val.length := by rw [grows2]; simp; omega
    rw [grows3,Rowl.ConceptTable.meaning_append _ _ wf2 _ inside2,grows2,
      Rowl.ConceptTable.meaning_append _ _ wf1 _ inside1,grows1,Rowl.ConceptTable.meaning_append _ _ wf0 _ axIn,
      axMeaning]
  have corresponds3 : Corresponds facts.val t3.val requirements.val := by
    rw [grows3,grows2]
    exact corresponds_append _ _ _ (by rw [← grows2]; exact wf2) _ (corresponds_append _ _ _ wf1 _ corresponds1)
  have unfolds3 : Unfolds definitions.val t3.val unfoldings.val := by
    rw [grows3]
    exact unfolds_append _ _ _ wf2 _ unfolds2
  have blankLabel : ∀ y, labelOf nodes0.val y = [] := by
    intro y
    unfold labelOf
    cases at_y : nodes0.val[y]? with
    | none => rfl
    | some n =>
      have := blanks n (List.mem_of_getElem? at_y)
      subst this
      rfl
  have blankNode : ∀ (y : Nat) (n : completion.Node), nodes0.val[y]? = some n → n = blank :=
    fun y n at_y => blanks n (List.mem_of_getElem? at_y)
  have inv0 : Inv P h count.val nodes0.val := by
    refine ⟨⟨wf3,closedTable closed.1,closed,?_,by rw [length0],?_,linksIn,?_,?_,?_⟩,?_,?_,?_⟩
    · intro y n at_y
      rw [blankNode y n at_y]
      simp only [blank,true_iff]
      rw [← length0]
      exact (List.getElem?_eq_some_iff.mp at_y).1
    · intro y n at_y isTree
      rw [blankNode y n at_y] at isTree
      cases isTree
    · intro q member
      obtain ⟨_,f,listed,node,_⟩ := corresponds3.1 q member
      rw [node]
      exact factsIn f listed
    · intro y i member
      rw [blankLabel y] at member
      cases member
    · intro y i member
      rw [blankLabel y] at member
      cases member
    · intro y
      rw [blankLabel y]
      exact List.nodup_nil
    · intro y yIn
      have path : treePath nodes0.val y = [] := by
        obtain ⟨n,at_y⟩ : ∃ n, nodes0.val[y]? = some n := ⟨_,List.getElem?_eq_getElem yIn⟩
        exact treePath_named _ y n at_y (by rw [blankNode y n at_y]; rfl)
      simp [depth,path]
    · intro y n at_y isTree
      rw [blankNode y n at_y] at isTree
      cases isTree
  obtain ⟨r,run,sound,complete⟩ := run_correct.{u,v} P h count.val positive _ nodes0 rfl inv0
  refine ⟨r,?_,?_,?_⟩
  · rw [completion.satisfiable]
    simp only [run0,run1,run2,run3,run4,bind_ok,uncurry_apply_pair]
    exact run
  · intro accepted
    obtain ⟨Object,I,π,respects,axiomsHold,unfoldingsHold,requirementsHold,linksHold,_,exact⟩ := sound accepted
    refine ⟨Object,I,π,respects,?_,?_,?_,linksHold,exact⟩
    · intro y
      have := axiomsHold y
      rwa [axMeaning3] at this
    · intro d member y classes
      obtain ⟨w,wMember,same,means⟩ := unfolds3.2 d member
      have := unfoldingsHold w wMember y (by rw [same]; exact classes)
      rwa [means] at this
    · intro f member
      obtain ⟨q,qMember,node,means⟩ := corresponds3.2 f member
      have := requirementsHold q qMember
      rwa [means,node] at this
  · intro rejected
    rintro ⟨Object,Value,I,π,respects,axiomsHold,definitionsHold,factsHold,linksHold⟩
    apply complete rejected
    refine ⟨Object,Value,I,π,respects,?_,?_,?_,linksHold,?_,?_,by simp⟩
    · intro y
      show denote I (meaning t3.val ax.val) y
      rw [axMeaning3]
      exact axiomsHold y
    · intro w member y classes
      obtain ⟨_,d,listed,same,means⟩ := unfolds3.1 w member
      show denote I (meaning t3.val w.concept.val) y
      rw [means]
      exact definitionsHold d listed y (by rw [← same]; exact classes)
    · intro q member
      obtain ⟨_,f,listed,node,means⟩ := corresponds3.1 q member
      show denote I (meaning t3.val q.concept.val) (π q.node.val)
      rw [means,node]
      exact factsHold f listed
    · intro y i member
      rw [blankLabel y] at member
      cases member
    · intro y n _ at_y isTree
      rw [blankNode y n at_y] at isTree
      cases isTree

end Rowl.Completion
