import Rowl.Symbols
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Rowl.AnonymousGraph
open Aeneas Aeneas.Std RowlRust.model RowlRust.anonymous_graph
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000

/-- Structural identity after standardization apart; never logical inequality. -/
abbrev Key := List U8 × List U8
abbrev Edge := Key × Key

def key (value : AnonymousIndividual) : Key := (value.scope.val, value.label.val)

def edgeKeys : AnonymousEdges → List Edge
  | .Empty => []
  | .Edge a b next => (key a, key b) :: edgeKeys next

/-- Only positive object assertions between two anonymous individuals add edges. -/
def axiomEdges : Axiom → List Edge
  | .ObjectPropertyAssertion _ (.Anonymous a) (.Anonymous b) => [(key a, key b)]
  | _ => []

def closureEdges (axioms : List AnnotatedAxiom) : List Edge :=
  axioms.flatMap (fun item => axiomEdges item.axiom)

/-- A structural undirected edge; repetitions and orientation do not add edges. -/
def HasPair (edges : List Edge) (x y : Key) : Prop :=
  (x,y) ∈ edges ∨ (y,x) ∈ edges

/-- Simple graph over the full key carrier. Non-occurring keys and other anonymous
    occurrences are isolated; self assertions are separately rejected below. -/
def graph : List Edge → SimpleGraph Key
  | [] => ⊥
  | (a,b) :: edges => graph edges ⊔ SimpleGraph.edge a b

/-- Forest means no self edge and no undirected cyclic walk. -/
def Forest (edges : List Edge) : Prop :=
  (∀ pair ∈ edges, pair.1 ≠ pair.2) ∧ (graph edges).IsAcyclic

/-- Success is exact; failures contain actual endpoints and certify non-forest. -/
def Correct (edges : List Edge) : ForestCheck → Prop
  | .Forest => Forest edges
  | .SelfLoop value => (key value,key value) ∈ edges ∧ ¬ Forest edges
  | .Cycle a b => key a ≠ key b ∧ HasPair edges (key a) (key b) ∧ ¬ Forest edges

/-- Byte comparison checks both the document scope and the local label. -/
theorem same_individual_total_correct (left right : AnonymousIndividual) :
    same_individual left right = .ok (decide (key left = key right)) := by
  rw [same_individual, Rowl.Symbols.same_spelling_total_correct]
  by_cases scope : left.scope.val = right.scope.val <;>
    simp [scope, Rowl.Symbols.same_spelling_total_correct, key]

/-- Equal scoped byte keys are exactly equal structural anonymous individuals.
    This statement concerns syntax; no distinct-denotation assumption is made. -/
theorem key_injective : Function.Injective key := by
  intro left right equal
  cases left with
  | mk ls ll =>
    cases right with
    | mk rs rl =>
      have scope : ls.val = rs.val := congrArg Prod.fst equal
      have label : ll.val = rl.val := congrArg Prod.snd equal
      have scopes := alloc.vec.Vec.ext ls rs scope
      have labels := alloc.vec.Vec.ext ll rl label
      cases scopes
      cases labels
      rfl

private theorem graph_adj (edges : List Edge) (x y : Key) :
    (graph edges).Adj x y ↔ x ≠ y ∧ HasPair edges x y := by
  induction edges with
  | nil => simp [graph, HasPair]
  | cons pair next ih =>
    rcases pair with ⟨a,b⟩
    simp only [graph, SimpleGraph.sup_adj, SimpleGraph.edge_adj, ih, HasPair, List.mem_cons, Prod.mk.injEq]
    tauto

private theorem graph_cons (a b : Key) (edges : List Edge) :
    graph ((a,b)::edges) = graph edges ⊔ SimpleGraph.edge a b := rfl

private theorem graph_le_cons (a b : Key) (edges : List Edge) :
    graph edges ≤ graph ((a,b)::edges) := le_sup_left

private theorem graph_pair_le (edges : List Edge) (a b : Key) (h : HasPair edges a b) :
    SimpleGraph.edge a b ≤ graph edges := by
  intro x y adj
  rw [SimpleGraph.edge_adj] at adj
  rcases adj with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩), ne⟩
  · exact (graph_adj edges _ _).mpr ⟨ne,h⟩
  · exact (graph_adj edges _ _).mpr ⟨ne,by simpa [HasPair,or_comm] using h⟩

private theorem graph_duplicate (edges : List Edge) (a b : Key) (h : HasPair edges a b) :
    graph ((a,b)::edges) = graph edges := by
  exact sup_eq_left.mpr (graph_pair_le edges a b h)

private def Cross (G : SimpleGraph Key) (a b x y : Key) : Prop :=
  G.Reachable x y ∨ (G.Reachable x a ∧ G.Reachable b y) ∨
    (G.Reachable x b ∧ G.Reachable a y)

private theorem cross_trans (G : SimpleGraph Key) (a b x y z : Key)
    (left : Cross G a b x y) (right : Cross G a b y z) : Cross G a b x z := by
  rcases left with direct | forward | reverse
  · rcases right with direct' | forward' | reverse'
    · exact Or.inl (direct.trans direct')
    · exact Or.inr (Or.inl ⟨direct.trans forward'.1,forward'.2⟩)
    · exact Or.inr (Or.inr ⟨direct.trans reverse'.1,reverse'.2⟩)
  · rcases right with direct' | forward' | reverse'
    · exact Or.inr (Or.inl ⟨forward.1,forward.2.trans direct'⟩)
    · exact Or.inr (Or.inl ⟨forward.1,forward'.2⟩)
    · exact Or.inl (forward.1.trans reverse'.2)
  · rcases right with direct' | forward' | reverse'
    · exact Or.inr (Or.inr ⟨reverse.1,reverse.2.trans direct'⟩)
    · exact Or.inl (reverse.1.trans forward'.2)
    · exact Or.inr (Or.inr ⟨reverse.1,reverse'.2⟩)

/-- A walk using one added undirected edge can be shortened to cross it once. -/
private theorem reachable_sup_edge (G : SimpleGraph Key) (a b x y : Key) :
    (G ⊔ SimpleGraph.edge a b).Reachable x y ↔ Cross G a b x y := by
  constructor
  · intro reachable
    rw [SimpleGraph.reachable_iff_reflTransGen] at reachable
    induction reachable with
    | refl => exact Or.inl .rfl
    | @tail z w prior adj ih =>
      apply cross_trans G a b x z w ih
      rcases adj with old | added
      · exact Or.inl old.reachable
      · rw [SimpleGraph.edge_adj] at added
        rcases added with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩), _⟩
        · exact Or.inr (Or.inl ⟨.rfl,.rfl⟩)
        · exact Or.inr (Or.inr ⟨.rfl,.rfl⟩)
  · intro cross
    rcases cross with direct | forward | reverse
    · exact direct.mono le_sup_left
    · by_cases same : a = b
      · subst b
        exact (forward.1.trans forward.2).mono le_sup_left
      · have added : (G ⊔ SimpleGraph.edge a b).Adj a b :=
          Or.inr (by simp [SimpleGraph.edge_adj, same])
        exact ((forward.1.mono le_sup_left).trans added.reachable).trans (forward.2.mono le_sup_left)
    · by_cases same : a = b
      · subst b
        exact (reverse.1.trans reverse.2).mono le_sup_left
      · have added : (G ⊔ SimpleGraph.edge a b).Adj b a :=
          Or.inr (by simp [SimpleGraph.edge_adj, same, Ne.symm same])
        exact ((reverse.1.mono le_sup_left).trans added.reachable).trans (reverse.2.mono le_sup_left)

private theorem contains_edge_total (edges : AnonymousEdges) (left right : AnonymousIndividual) :
    contains_edge edges left right = .ok (decide (HasPair (edgeKeys edges) (key left) (key right)),edges) := by
  induction edges with
  | Empty => simp [contains_edge,edgeKeys,HasPair]
  | Edge a b next ih =>
    rw [contains_edge]
    by_cases al : key a = key left <;> by_cases br : key b = key right <;>
      by_cases ar : key a = key right <;> by_cases bl : key b = key left <;>
      simp_all [same_individual_total_correct,HasPair,edgeKeys,eq_comm,Bool.or_assoc]

/-- Exact connectivity, total on arbitrary finite graphs including cycles,
    self loops, repeated edges and equal endpoints; the edge input is restored. -/
theorem connected_total_correct (edges : AnonymousEdges) (left right : AnonymousIndividual) :
    connected edges left right =
      .ok (decide ((graph (edgeKeys edges)).Reachable (key left) (key right)),edges) := by
  induction edges generalizing left right with
  | Empty =>
    by_cases same : key left = key right <;>
      simp [connected,same_individual_total_correct,edgeKeys,graph,same]
  | Edge a b next ih =>
    by_cases same : key left = key right
    · simp [connected,same_individual_total_correct,same]
    · rw [connected,same_individual_total_correct]
      by_cases direct : (graph (edgeKeys next)).Reachable (key left) (key right) <;>
        by_cases toA : (graph (edgeKeys next)).Reachable (key left) (key a) <;>
        by_cases fromB : (graph (edgeKeys next)).Reachable (key b) (key right) <;>
        by_cases toB : (graph (edgeKeys next)).Reachable (key left) (key b) <;>
        by_cases fromA : (graph (edgeKeys next)).Reachable (key a) (key right) <;>
        simp [same,ih,edgeKeys,graph,reachable_sup_edge,Cross,direct,toA,fromB,toB,fromA]

private theorem forest_cons (edges : List Edge) (a b : Key) :
    Forest ((a,b)::edges) ↔
      a ≠ b ∧ Forest edges ∧
        (HasPair edges a b ∨ ¬ (graph edges).Reachable a b) := by
  simp only [Forest, graph_cons, List.forall_mem_cons, Prod.fst, Prod.snd,
    SimpleGraph.isAcyclic_sup_fromEdgeSet_iff, graph_adj]
  tauto

private theorem lift_correct (edges : List Edge) (a b : Key) (result : ForestCheck)
    (correct : Correct edges result)
    (extend : Forest edges → Forest ((a,b)::edges)) : Correct ((a,b)::edges) result := by
  cases result with
  | Forest => exact extend correct
  | SelfLoop value =>
    refine ⟨List.mem_cons_of_mem _ correct.1, ?_⟩
    intro accepted
    exact correct.2 (forest_cons edges a b |>.mp accepted).2.1
  | Cycle x y =>
    refine ⟨correct.1, ?_, ?_⟩
    · rcases correct.2.1 with left | right
      · exact Or.inl (List.mem_cons_of_mem _ left)
      · exact Or.inr (List.mem_cons_of_mem _ right)
    · intro accepted
      exact correct.2.2 (forest_cons edges a b |>.mp accepted).2.1

/-- The actual Rust decision terminates and returns correct success or actual
    non-forest evidence. Duplicate edges are not mistaken for a cycle. -/
theorem check_edges_total_correct (edges : AnonymousEdges) :
    ∃ result, check_edges edges = .ok result ∧ Correct (edgeKeys edges) result := by
  induction edges with
  | Empty =>
    exact ⟨.Forest,by simp [check_edges],by simp [Correct,Forest,edgeKeys,graph]⟩
  | Edge a b next ih =>
    obtain ⟨result,executed,correct⟩ := ih
    by_cases same : key a = key b
    · refine ⟨.SelfLoop a,by simp [check_edges,same_individual_total_correct,same], ?_⟩
      refine ⟨by simp [edgeKeys,same], ?_⟩
      intro accepted
      exact (forest_cons (edgeKeys next) (key a) (key b) |>.mp accepted).1 same
    · by_cases duplicate : HasPair (edgeKeys next) (key a) (key b)
      · refine ⟨result,by simp [check_edges,same_individual_total_correct,same,
          contains_edge_total,duplicate,executed], ?_⟩
        exact lift_correct (edgeKeys next) (key a) (key b) result correct
          (fun old => (forest_cons ..).mpr ⟨same,old,Or.inl duplicate⟩)
      · by_cases reachable : (graph (edgeKeys next)).Reachable (key a) (key b)
        · refine ⟨.Cycle a b,by simp [check_edges,same_individual_total_correct,same,
            contains_edge_total,duplicate,connected_total_correct,reachable], ?_⟩
          refine ⟨same,by simp [HasPair,edgeKeys], ?_⟩
          intro accepted
          rcases (forest_cons (edgeKeys next) (key a) (key b) |>.mp accepted).2.2 with dup | absent
          · exact duplicate dup
          · exact absent reachable
        · refine ⟨result,by simp [check_edges,same_individual_total_correct,same,
            contains_edge_total,duplicate,connected_total_correct,reachable,executed], ?_⟩
          exact lift_correct (edgeKeys next) (key a) (key b) result correct
            (fun old => (forest_cons ..).mpr ⟨same,old,Or.inr reachable⟩)

/-- Acceptance is equivalent to loop freedom and absence of all undirected cycles. -/
theorem check_edges_accepted_iff (edges : AnonymousEdges) :
    check_edges edges = .ok .Forest ↔ Forest (edgeKeys edges) := by
  obtain ⟨result,executed,correct⟩ := check_edges_total_correct edges
  rw [executed]
  cases result with
  | Forest => simp [Correct] at correct; simp [correct]
  | SelfLoop value => simp [Correct] at correct; simp [correct.2]
  | Cycle a b => simp [Correct] at correct; simp [correct.2.2]

private def fromAxiom (body : Axiom) (next : AnonymousEdges) : AnonymousEdges :=
  match body with
  | .ObjectPropertyAssertion _ (.Anonymous a) (.Anonymous b) => .Edge a b next
  | _ => next

private def fromClosure : List AnnotatedAxiom → AnonymousEdges
  | [] => .Empty
  | item::next => fromAxiom item.axiom (fromClosure next)

private theorem fromAxiom_keys (body : Axiom) (next : AnonymousEdges) :
    edgeKeys (fromAxiom body next) = axiomEdges body ++ edgeKeys next := by
  cases body <;> simp [fromAxiom,axiomEdges]
  case ObjectPropertyAssertion p a b =>
    cases a <;> cases b <;> simp [fromAxiom,axiomEdges,edgeKeys]

private theorem fromClosure_keys (axioms : List AnnotatedAxiom) :
    edgeKeys (fromClosure axioms) = closureEdges axioms := by
  induction axioms with
  | nil => simp [fromClosure,edgeKeys,closureEdges]
  | cons item next ih => simp [fromClosure,fromAxiom_keys,closureEdges,ih]

private theorem collect_from_total (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    collect_from axioms index = .ok (fromClosure (axioms.val.drop index.val)) := by
  rw [collect_from]
  by_cases inside : index.val < axioms.val.length
  · obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    have recursive := collect_from_total axioms next
    simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,advance,bind_ok,
      recursive,alloc.vec.Vec.index_slice_index,lookup]
    rw [List.drop_eq_getElem_cons inside]
    simp only [fromClosure,nv]
    cases h : axioms.val[index.val].axiom <;> simp [fromAxiom]
    case ObjectPropertyAssertion p a b => cases a <;> cases b <;> simp [fromAxiom]
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty,fromClosure]
termination_by axioms.val.length - index.val
decreasing_by omega

/-- Exact ordered projection of all raw positive anonymous assertions; no imported
    closure or parser claims are assumed by this theorem. -/
theorem collect_edges_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ edges, collect_edges axioms = .ok edges ∧ edgeKeys edges = closureEdges axioms.val := by
  refine ⟨fromClosure axioms.val, ?_, fromClosure_keys axioms.val⟩
  simpa [collect_edges] using collect_from_total axioms 0#usize

/-- The supplied full raw closure is accepted exactly when its anonymous assertion
    graph is a forest. Edge multiplicity and named-boundary conditions are separate. -/
theorem check_forest_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_forest axioms = .ok result ∧ Correct (closureEdges axioms.val) result := by
  obtain ⟨edges,collected,content⟩ := collect_edges_total_correct axioms
  obtain ⟨result,checked,correct⟩ := check_edges_total_correct edges
  exact ⟨result,by simp [check_forest,collected,checked],content ▸ correct⟩

/-- No false acceptance or rejection of the forest condition on actual raw axioms. -/
theorem check_forest_accepted_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_forest axioms = .ok .Forest ↔ Forest (closureEdges axioms.val) := by
  obtain ⟨edges,collected,content⟩ := collect_edges_total_correct axioms
  simpa [check_forest,collected,content] using check_edges_accepted_iff edges

/-- A checked acyclic graph partitions into connected components that are trees.
    This includes isolated anonymous vertices and the empty used-vertex set. -/
theorem forest_components_are_trees (edges : List Edge) (accepted : Forest edges)
    (component : (graph edges).ConnectedComponent) :
    (graph edges).induce component.supp |>.IsTree :=
  accepted.2.isTree_connectedComponent component

end Rowl.AnonymousGraph
