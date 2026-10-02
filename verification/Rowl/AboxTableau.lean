import Rowl.TboxTableau

/-!
ALC reasoning with named individuals, proved total, sound and complete. Facts
say that concepts hold at numbered nodes, and edges say that named object
properties relate nodes. The completion adds every fact once, expands
conjunctions, branches on disjunctions and pushes universal restrictions along
the edges of their role; it then checks every node for a clash and decides every
existential restriction with the TBox tableau. Every acceptance yields an
interpretation with an element for each node that satisfies the facts, the edges
and the TBox concept everywhere; every such interpretation, in any universe,
forces acceptance. Termination: each added fact is new and drawn from the finite
set of node and closure pairs.
-/
namespace Rowl.AboxTableau
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation)
open Rowl.Nnf (conceptDenote)
open Rowl.Tableau (toList fromList toList_fromList Holds property_eq_iff class_eq_iff)
open Rowl.TboxTableau (subconcepts Closed subconcepts_self subconcepts_closed closed_append listSubconcepts
  listSubconcepts_closed listSubconcepts_self same_concept_correct satisfiable_all_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- The facts of a list, in order: the node and the concept that holds there. -/
def factsList : abox.Facts → List (Nat × nnf.NnfConcept)
  | .Empty => []
  | .Entry node c next => (node.val,c) :: factsList next
/-- The edges of a list, in order: the role, its source node and its target node. -/
def edgesList : abox.Edges → List (ObjectProperty × Nat × Nat)
  | .Empty => []
  | .Entry r source target next => (r,source.val,target.val) :: edgesList next
/-- The targets of the edges of a role from a node, in list order. -/
noncomputable def targetsOf (role : ObjectProperty) (node : Nat) : List (ObjectProperty × Nat × Nat) → List Nat
  | [] => []
  | e :: rest => if e.1 = role ∧ e.2.1 = node then e.2.2 :: targetsOf role node rest else targetsOf role node rest
/-- The fillers of the universal restrictions on a role at a node, in list order. -/
noncomputable def nodeFillers (role : ObjectProperty) (node : Nat) : List (Nat × nnf.NnfConcept) → List nnf.NnfConcept
  | [] => []
  | (n,.Forall r d) :: rest => if n = node ∧ r = role then d :: nodeFillers role node rest else nodeFillers role node rest
  | _ :: rest => nodeFillers role node rest

theorem targetsOf_mem (role : ObjectProperty) (node m : Nat) (edges : List (ObjectProperty × Nat × Nat)) :
    m ∈ targetsOf role node edges ↔ (role,node,m) ∈ edges := by
  induction edges with
  | nil => simp [targetsOf]
  | cons e rest ih =>
    obtain ⟨r,s,t⟩ := e
    by_cases hit : r = role ∧ s = node
    · obtain ⟨rfl,rfl⟩ := hit
      simp [targetsOf,ih,eq_comm]
    · simp only [targetsOf,hit,if_false,ih,List.mem_cons,Prod.mk.injEq]
      constructor
      · exact .inr
      · rintro (⟨rfl,rfl,rfl⟩ | later)
        · exact absurd ⟨rfl,rfl⟩ hit
        · exact later
theorem nodeFillers_mem (role : ObjectProperty) (node : Nat) (facts : List (Nat × nnf.NnfConcept))
    (d : nnf.NnfConcept) : d ∈ nodeFillers role node facts ↔ (node,.Forall role d) ∈ facts := by
  induction facts with
  | nil => simp [nodeFillers]
  | cons p rest ih =>
    obtain ⟨n,c⟩ := p
    cases c with
    | Forall r e =>
      by_cases hit : n = node ∧ r = role
      · obtain ⟨rfl,rfl⟩ := hit
        simp [nodeFillers,ih,eq_comm]
      · simp only [nodeFillers,hit,if_false,ih,List.mem_cons,Prod.mk.injEq]
        constructor
        · exact .inr
        · rintro (⟨rfl,same⟩ | later)
          · cases same; exact absurd ⟨rfl,rfl⟩ hit
          · exact later
    | _ => simp [nodeFillers,ih]

theorem duplicate_facts_correct (list : abox.Facts) : abox.duplicate_facts list = .ok (list,list) := by
  induction list with
  | Empty => rw [abox.duplicate_facts]
  | Entry node c next ih => rw [abox.duplicate_facts]; simp [ih]
theorem duplicate_edges_correct (list : abox.Edges) : abox.duplicate_edges list = .ok (list,list) := by
  induction list with
  | Empty => rw [abox.duplicate_edges]
  | Entry r source target next ih => rw [abox.duplicate_edges]; simp [ih]

private theorem usize_eq_iff (a b : Usize) : a = b ↔ a.val = b.val := by
  constructor
  · rintro rfl; rfl
  · intro same; exact UScalar.eq_of_val_eq same

/-- Membership of a fact is decided exactly; the list is handed back. -/
theorem contains_fact_correct (list : abox.Facts) (node : Usize) (sought : nnf.NnfConcept) :
    abox.contains_fact list node sought = .ok (decide ((node.val,sought) ∈ factsList list),list) := by
  induction list with
  | Empty => rw [abox.contains_fact.eq_def]; simp [factsList]
  | Entry other c next ih =>
    rw [abox.contains_fact.eq_def]
    by_cases same : other = node
    · subst same
      by_cases equal : c = sought
      · subst equal; simp [ih,factsList,same_concept_correct]
      · have equal' : ¬ sought = c := fun h => equal h.symm
        simp [ih,factsList,same_concept_correct,equal,equal']
    · have different : ¬ node.val = other.val := fun h => same ((usize_eq_iff other node).mpr h.symm)
      simp [ih,factsList,same,different]

/-- Universal restrictions reach exactly the targets of their role's edges from
    the node; the edges are handed back. -/
theorem propagate_correct (edges : abox.Edges) (node : Usize) (role : ObjectProperty) (filler : nnf.NnfConcept)
    (pending : abox.Facts) :
    ∃ pushed, abox.propagate edges node role filler pending = .ok (pushed,edges) ∧
      factsList pushed =
        (targetsOf role node.val (edgesList edges)).map (fun m => (m,filler)) ++ factsList pending := by
  induction edges with
  | Empty => exact ⟨pending,by rw [abox.propagate.eq_def],by simp [targetsOf,edgesList]⟩
  | Entry other source target next ih =>
    obtain ⟨pushed,run,contents⟩ := ih
    rw [abox.propagate.eq_def]
    by_cases from_node : source = node
    · subst from_node
      by_cases same_role : other = role
      · subst same_role
        exact ⟨.Entry target filler pushed,by simp [run,Rowl.Symbols.same_spelling_total_correct],
          by simp [factsList,targetsOf,edgesList,contents]⟩
      · have different : ¬ other.iri.spelling.val = role.iri.spelling.val :=
          fun h => same_role ((property_eq_iff other role).mpr h)
        exact ⟨pushed,by simp [run,Rowl.Symbols.same_spelling_total_correct,different],
          by simp [targetsOf,edgesList,contents,same_role]⟩
    · have different : ¬ source.val = node.val := fun h => from_node ((usize_eq_iff source node).mpr h)
      exact ⟨pushed,by simp [run,from_node],by simp [targetsOf,edgesList,contents,different]⟩

/-- Positive membership of a named class at a node is decided exactly. -/
theorem has_atom_correct (list : abox.Facts) (node : Usize) (k : Class) :
    abox.has_atom list node k = .ok (decide ((node.val,.Atom k) ∈ factsList list),list) := by
  induction list with
  | Empty => rw [abox.has_atom.eq_def]; simp [factsList]
  | Entry other c next ih =>
    rw [abox.has_atom.eq_def]
    cases c with
    | Atom j =>
      by_cases same : other = node
      · subst same
        by_cases equal : j = k
        · subst equal; simp [ih,factsList,Rowl.Symbols.same_spelling_total_correct]
        · have different : ¬ j.iri.spelling.val = k.iri.spelling.val := fun h => equal ((class_eq_iff j k).mpr h)
          have equal' : ¬ k = j := fun h => equal h.symm
          simp [ih,factsList,Rowl.Symbols.same_spelling_total_correct,different,equal,equal']
      · have different : ¬ node.val = other.val := fun h => same ((usize_eq_iff other node).mpr h.symm)
        simp [ih,factsList,same,different]
    | _ => simp [ih,factsList]
/-- A clash is decided exactly: some node holds a named class negated in the
    cursor and positively in the list, which is handed back. -/
theorem has_clash_correct (all cursor : abox.Facts) :
    abox.has_clash all cursor =
      .ok (decide (∃ n k, (n,.NotAtom k) ∈ factsList cursor ∧ (n,.Atom k) ∈ factsList all),all) := by
  induction cursor with
  | Empty => rw [abox.has_clash.eq_def]; simp [factsList]
  | Entry node c next ih =>
    rw [abox.has_clash.eq_def]
    cases c with
    | NotAtom k =>
      have claim : (∃ n j, (n,.NotAtom j) ∈ factsList (.Entry node (.NotAtom k) next) ∧ (n,.Atom j) ∈ factsList all) ↔
          (node.val,.Atom k) ∈ factsList all ∨ ∃ n j, (n,.NotAtom j) ∈ factsList next ∧ (n,.Atom j) ∈ factsList all := by
        simp only [factsList,List.mem_cons,Prod.mk.injEq]
        constructor
        · rintro ⟨n,j,(⟨rfl,same⟩ | inNext),positive⟩
          · cases same; exact .inl positive
          · exact .inr ⟨n,j,inNext,positive⟩
        · rintro (positive | ⟨n,j,inNext,positive⟩)
          · exact ⟨node.val,k,.inl ⟨rfl,rfl⟩,positive⟩
          · exact ⟨n,j,.inr inNext,positive⟩
      rw [claim]
      by_cases present : (node.val,.Atom k) ∈ factsList all <;> simp [has_atom_correct,ih,present]
    | _ => simp [ih,factsList]

/-- The fillers at a node are found exactly; the list is handed back. -/
theorem node_fillers_correct (list : abox.Facts) (node : Usize) (role : ObjectProperty) :
    abox.node_fillers list node role = .ok (fromList (nodeFillers role node.val (factsList list)),list) := by
  induction list with
  | Empty => rw [abox.node_fillers.eq_def]; simp [factsList,nodeFillers,fromList]
  | Entry other c next ih =>
    rw [abox.node_fillers.eq_def]
    cases c with
    | Forall r d =>
      by_cases same : other = node
      · subst same
        by_cases equal : r = role
        · subst equal; simp [ih,factsList,nodeFillers,fromList,Rowl.Symbols.same_spelling_total_correct]
        · have different : ¬ r.iri.spelling.val = role.iri.spelling.val :=
            fun h => equal ((property_eq_iff r role).mpr h)
          simp [ih,factsList,nodeFillers,Rowl.Symbols.same_spelling_total_correct,different,equal]
      · have different : ¬ other.val = node.val := fun h => same ((usize_eq_iff other node).mpr h)
        simp [ih,factsList,nodeFillers,same,different]
    | _ => simp [ih,factsList,nodeFillers]

/-- The TBox tableau's verdict on an existential obligation: its filler with the
    fillers of the universal restrictions on its role at the same node. -/
def Obligation (axioms : nnf.NnfConcept) (facts : List (Nat × nnf.NnfConcept)) (n : Nat) (r : ObjectProperty)
    (d : nnf.NnfConcept) : Prop :=
  tbox.satisfiable_all (.Entry d (fromList (nodeFillers r n facts))) axioms = .ok true

/-- The obligations check is exact: it accepts when the TBox tableau accepts
    every existential restriction in the cursor; the list is handed back. -/
theorem obligations_hold_correct (all cursor : abox.Facts) (axioms : nnf.NnfConcept) :
    ∃ result, abox.obligations_hold all cursor axioms = .ok (result,all) ∧
      (result = true ↔ ∀ n r d, (n,.Exists r d) ∈ factsList cursor → Obligation axioms (factsList all) n r d) := by
  induction cursor with
  | Empty => exact ⟨true,by rw [abox.obligations_hold.eq_def],by simp [factsList]⟩
  | Entry node c next ih =>
    obtain ⟨later,laterRun,laterIff⟩ := ih
    rw [abox.obligations_hold.eq_def]
    cases c with
    | Exists r d =>
      obtain ⟨here,hereRun,_,_⟩ := satisfiable_all_correct.{0,0}
        (.Entry d (fromList (nodeFillers r node.val (factsList all)))) axioms
      refine ⟨here && later,by simp [node_fillers_correct,hereRun,laterRun]; cases here <;> rfl,?_⟩
      simp only [Bool.and_eq_true,laterIff,factsList,List.mem_cons,Prod.mk.injEq]
      constructor
      · rintro ⟨hereTrue,rest⟩ n s e (⟨rfl,same⟩ | inNext)
        · cases same; subst hereTrue; exact hereRun
        · exact rest n s e inNext
      · intro every
        refine ⟨?_,fun n s e inNext => every n s e (.inr inNext)⟩
        have := every node.val r d (.inl ⟨rfl,rfl⟩)
        rw [Obligation,hereRun] at this
        exact Result.ok_injective this
    | _ =>
      refine ⟨later,by simp [laterRun],?_⟩
      rw [laterIff]
      simp [factsList]

/-- The TBox concept is added at every node below the count, before the facts. -/
theorem with_axioms_correct (count : Usize) (pending : abox.Facts) (axioms : nnf.NnfConcept) :
    ∃ result, abox.with_axioms count pending axioms = .ok result ∧
      factsList result = (List.range count.val).map (fun n => (n,axioms)) ++ factsList pending := by
  rw [abox.with_axioms]
  by_cases zero : count = 0#usize
  · subst zero
    exact ⟨pending,by simp,by simp⟩
  · have positive : 0 < count.val := by
      have : count.val ≠ 0 := fun h => zero (by apply UScalar.eq_of_val_eq; simpa using h)
      omega
    obtain ⟨previous,run,value⟩ := WP.spec_imp_exists (Usize.sub_spec (x := count) (y := 1#usize) (by simp; omega))
    have previousValue : previous.val = count.val-1 := by simp at value; exact value.1
    obtain ⟨result,executed,contents⟩ := with_axioms_correct previous (.Entry previous axioms pending) axioms
    refine ⟨result,by simp [zero,run,executed],?_⟩
    rw [contents,previousValue]
    have split : count.val = (count.val-1)+1 := by omega
    conv => rhs; rw [split,List.range_succ]
    simp [factsList,previousValue]
termination_by count.val
decreasing_by
  have : previous.val = count.val-1 := previousValue
  omega

/-- An interpretation with an element for every node, in which the TBox concept
    holds at every element, every fact holds at its node and every edge relates
    its nodes. -/
def AboxModel {Object : Type u} {Value : Type v} (axioms : nnf.NnfConcept) (facts : List (Nat × nnf.NnfConcept))
    (edges : List (ObjectProperty × Nat × Nat)) (I : Interpretation Object Value) (f : Nat → Object) : Prop :=
  (∀ y, conceptDenote I axioms y) ∧ (∀ p ∈ facts, conceptDenote I p.2 (f p.1)) ∧
    ∀ e ∈ edges, I.objectProperties e.1 (f e.2.1) (f e.2.2)

/-- What an added fact requires of the known facts: a conjunction both conjuncts,
    a disjunction one disjunct and a universal restriction its filler at every
    target of its role's edges from the node; the bottom concept is never added. -/
def Requires (edges : List (ObjectProperty × Nat × Nat)) (known : List (Nat × nnf.NnfConcept)) :
    Nat × nnf.NnfConcept → Prop
  | (n,.And a b) => (n,a) ∈ known ∧ (n,b) ∈ known
  | (n,.Or a b) => (n,a) ∈ known ∨ (n,b) ∈ known
  | (n,.Forall r d) => ∀ m, (r,n,m) ∈ edges → (m,d) ∈ known
  | (_,.Bottom) => False
  | _ => True

theorem requires_mono {edges : List (ObjectProperty × Nat × Nat)} {small large : List (Nat × nnf.NnfConcept)}
    (sub : ∀ p ∈ small, p ∈ large) (p : Nat × nnf.NnfConcept) (required : Requires edges small p) :
    Requires edges large p := by
  obtain ⟨n,c⟩ := p
  cases c with
  | And a b =>
    obtain ⟨left,right⟩ := required
    exact ⟨sub _ left,sub _ right⟩
  | Or a b =>
    rcases required with left | right
    · exact .inl (sub _ left)
    · exact .inr (sub _ right)
  | Forall r d => exact fun m edge => sub _ (required m edge)
  | Bottom => exact required
  | Top | Atom _ | NotAtom _ | Exists _ _ => trivial

/-- The existential obligations of a fact set: a node, a role and a filler. -/
abbrev Obligations (facts : List (Nat × nnf.NnfConcept)) : Type :=
  {o : Nat × ObjectProperty × nnf.NnfConcept // (o.1,.Exists o.2.1 o.2.2) ∈ facts}

/-- The interpretation of a saturated fact set: one element per node and a
    disjoint copy of a successor model for every existential obligation. A node is
    in a named class when the class holds there; its role successors are the
    targets of its edges and the roots of its obligations' models; successor
    elements keep their own model's classes and roles. -/
def aboxModel (count : Nat) (positive : 0 < count) (facts : List (Nat × nnf.NnfConcept))
    (edges : List (ObjectProperty × Nat × Nat)) (Obj : Obligations facts → Type)
    (J : ∀ o, Interpretation (Obj o) Unit) (root : ∀ o, Obj o) :
    Interpretation (Fin count ⊕ Σ o, Obj o) Unit where
  objectsNonempty := ⟨.inl ⟨0,positive⟩⟩
  dataNonempty := ⟨()⟩
  classes k x := match x with
    | .inl n => (n.val,.Atom k) ∈ facts
    | .inr y => (J y.1).classes k y.2
  objectProperties r x z := match x with
    | .inl n => (∃ m : Fin count, z = .inl m ∧ (r,n.val,m.val) ∈ edges) ∨
        ∃ o : Obligations facts, o.val.1 = n.val ∧ o.val.2.1 = r ∧ z = .inr ⟨o,root o⟩
    | .inr y => ∃ y', z = .inr ⟨y.1,y'⟩ ∧ (J y.1).objectProperties r y.2 y'
  dataProperties _ _ _ := False
  namedIndividuals _ := .inl ⟨0,positive⟩
  anonymousIndividuals _ := .inl ⟨0,positive⟩
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := True

section Model
variable {count : Nat} {positive : 0 < count} {facts : List (Nat × nnf.NnfConcept)}
  {edges : List (ObjectProperty × Nat × Nat)} {Obj : Obligations facts → Type}
  {J : ∀ o, Interpretation (Obj o) Unit} {root : ∀ o, Obj o}

/-- A successor element satisfies exactly what it satisfies in its own model. -/
theorem component_truth (c : nnf.NnfConcept) : ∀ (o : Obligations facts) (y : Obj o),
    conceptDenote (aboxModel count positive facts edges Obj J root) c (.inr ⟨o,y⟩) ↔ conceptDenote (J o) c y := by
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ => intro o y; exact Iff.rfl
  | And a b iha ihb => intro o y; simp only [conceptDenote,iha o y,ihb o y]
  | Or a b iha ihb => intro o y; simp only [conceptDenote,iha o y,ihb o y]
  | Exists r c ih =>
    intro o y
    simp only [conceptDenote]
    constructor
    · rintro ⟨z,⟨y',rfl,edge⟩,holds⟩
      exact ⟨y',edge,(ih o y').mp holds⟩
    · rintro ⟨y',edge,holds⟩
      exact ⟨.inr ⟨o,y'⟩,⟨y',rfl,edge⟩,(ih o y').mpr holds⟩
  | Forall r c ih =>
    intro o y
    simp only [conceptDenote]
    constructor
    · intro every y' edge
      exact (ih o y').mp (every (.inr ⟨o,y'⟩) ⟨y',rfl,edge⟩)
    · rintro every z ⟨y',rfl,edge⟩
      exact (ih o y').mpr (every y' edge)

/-- In a saturated, clash-free fact set whose obligations have successor models,
    every fact holds at its node. -/
theorem node_truth (requires : ∀ p ∈ facts, Requires edges facts p)
    (clashFree : ∀ n k, (n,.NotAtom k) ∈ facts → (n,.Atom k) ∉ facts)
    (spec : ∀ o : Obligations facts, Holds (J o) (root o) (o.val.2.2 :: nodeFillers o.val.2.1 o.val.1 facts)) :
    ∀ c (n : Fin count), (n.val,c) ∈ facts →
      conceptDenote (aboxModel count positive facts edges Obj J root) c (.inl n) := by
  intro c
  induction c with
  | Top => intro n _; trivial
  | Bottom => intro n member; exact False.elim (requires _ member)
  | Atom k => intro n member; exact member
  | NotAtom k => intro n member; exact clashFree n.val k member
  | And a b iha ihb =>
    intro n member
    obtain ⟨left,right⟩ := requires _ member
    exact ⟨iha n left,ihb n right⟩
  | Or a b iha ihb =>
    intro n member
    rcases requires _ member with left | right
    · exact .inl (iha n left)
    · exact .inr (ihb n right)
  | Exists r d ih =>
    intro n member
    refine ⟨.inr ⟨⟨(n.val,r,d),member⟩,root ⟨(n.val,r,d),member⟩⟩,.inr ⟨⟨(n.val,r,d),member⟩,rfl,rfl,rfl⟩,?_⟩
    exact (component_truth d _ _).mpr (spec ⟨(n.val,r,d),member⟩ d (List.mem_cons_self ..))
  | Forall r d ih =>
    intro n member z edge
    rcases edge with ⟨m,rfl,inEdges⟩ | ⟨o,source,role,rfl⟩
    · exact ih m (requires _ member m.val inEdges)
    · apply (component_truth d o (root o)).mpr
      apply spec o d
      apply List.mem_cons_of_mem
      rw [nodeFillers_mem,source,role]
      exact member
end Model

private theorem choose_successors (axioms : nnf.NnfConcept) (facts : List (Nat × nnf.NnfConcept))
    (obligations : ∀ n r d, (n,.Exists r d) ∈ facts → ∃ (Object : Type) (I : Interpretation Object Unit),
      (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (d :: nodeFillers r n facts)) :
    ∃ (Obj : Obligations facts → Type) (J : ∀ o, Interpretation (Obj o) Unit) (root : ∀ o, Obj o),
      ∀ o, (∀ y, conceptDenote (J o) axioms y) ∧
        Holds (J o) (root o) (o.val.2.2 :: nodeFillers o.val.2.1 o.val.1 facts) := by
  have pick : ∀ o : Obligations facts, Nonempty (Σ' (Obj : Type) (J : Interpretation Obj Unit) (root : Obj),
      (∀ y, conceptDenote J axioms y) ∧ Holds J root (o.val.2.2 :: nodeFillers o.val.2.1 o.val.1 facts)) := by
    intro o
    obtain ⟨Obj,J,everywhereJ,root,holds⟩ := obligations o.val.1 o.val.2.1 o.val.2.2 o.property
    exact ⟨⟨Obj,J,root,everywhereJ,holds⟩⟩
  exact ⟨fun o => (Classical.choice (pick o)).1,fun o => (Classical.choice (pick o)).2.1,
    fun o => (Classical.choice (pick o)).2.2.1,fun o => (Classical.choice (pick o)).2.2.2⟩

/-- A saturated, clash-free fact set at nodes below a positive count, with the
    TBox concept at every node and a successor model for every existential
    obligation, has a model. -/
theorem model_of_saturated (count : Nat) (positive : 0 < count) (axioms : nnf.NnfConcept)
    (edges : List (ObjectProperty × Nat × Nat)) (facts : List (Nat × nnf.NnfConcept))
    (factsIn : ∀ p ∈ facts, p.1 < count) (edgesIn : ∀ e ∈ edges, e.2.1 < count ∧ e.2.2 < count)
    (requires : ∀ p ∈ facts, Requires edges facts p) (everywhere : ∀ n < count, (n,axioms) ∈ facts)
    (clashFree : ∀ n k, (n,.NotAtom k) ∈ facts → (n,.Atom k) ∉ facts)
    (obligations : ∀ n r d, (n,.Exists r d) ∈ facts → ∃ (Object : Type) (I : Interpretation Object Unit),
      (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (d :: nodeFillers r n facts)) :
    ∃ (Object : Type) (I : Interpretation Object Unit) (f : Nat → Object), AboxModel axioms facts edges I f := by
  obtain ⟨Obj,J,root,spec⟩ := choose_successors axioms facts obligations
  refine ⟨_,aboxModel count positive facts edges Obj J root,
    fun n => if h : n < count then .inl ⟨n,h⟩ else .inl ⟨0,positive⟩,?_,?_,?_⟩
  · intro y
    rcases y with n | ⟨o,y⟩
    · exact node_truth requires clashFree (fun o => (spec o).2) axioms n (everywhere n.val n.isLt)
    · exact (component_truth axioms o y).mpr ((spec o).1 y)
  · intro p member
    have bound := factsIn p member
    simp only [bound,↓reduceDIte]
    exact node_truth requires clashFree (fun o => (spec o).2) p.2 ⟨p.1,bound⟩ member
  · intro e member
    obtain ⟨sourceIn,targetIn⟩ := edgesIn e member
    simp only [sourceIn,targetIn,↓reduceDIte]
    exact .inl ⟨⟨e.2.2,targetIn⟩,rfl,member⟩

/-- Invariants of every call: facts and pending facts stay at nodes below the
    count with concepts in a closed closure; the added facts are distinct; the
    edges stay below the count; every added fact's requirements are among the
    added and pending facts; and the TBox concept is at every node. -/
structure Invariant (count : Nat) (cl : List nnf.NnfConcept) (axioms : nnf.NnfConcept)
    (edges : List (ObjectProperty × Nat × Nat)) (pending facts : List (Nat × nnf.NnfConcept)) : Prop where
  closed : Closed cl
  pendingIn : ∀ p ∈ pending, p.1 < count ∧ p.2 ∈ cl
  factsIn : ∀ p ∈ facts, p.1 < count ∧ p.2 ∈ cl
  nodup : facts.Nodup
  edgesIn : ∀ e ∈ edges, e.2.1 < count ∧ e.2.2 < count
  requires : ∀ p ∈ facts, Requires edges (facts ++ pending) p
  everywhere : ∀ n < count, (n,axioms) ∈ facts ++ pending

/-- At most one added fact per node and closure concept. -/
theorem facts_bound {count : Nat} {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {pending facts : List (Nat × nnf.NnfConcept)}
    (inv : Invariant count cl axioms edges pending facts) : facts.length ≤ count * cl.toFinset.card := by
  have sub : facts.toFinset ⊆ Finset.range count ×ˢ cl.toFinset := by
    intro p member
    rw [List.mem_toFinset] at member
    obtain ⟨node,inCl⟩ := inv.factsIn p member
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr node,List.mem_toFinset.mpr inCl⟩
  have := Finset.card_le_card sub
  rwa [List.toFinset_card_of_nodup inv.nodup,Finset.card_product,Finset.card_range] at this

/-- A fact already added is dropped from the pending facts. -/
theorem invariant_skip {count : Nat} {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {next facts : List (Nat × nnf.NnfConcept)}
    {p : Nat × nnf.NnfConcept} (inv : Invariant count cl axioms edges (p :: next) facts) (present : p ∈ facts) :
    Invariant count cl axioms edges next facts := by
  have sub : ∀ q ∈ facts ++ p :: next, q ∈ facts ++ next := by
    intro q member
    simp only [List.mem_append,List.mem_cons] at member ⊢
    rcases member with old | rfl | later
    · exact .inl old
    · exact .inl present
    · exact .inr later
  exact { closed := inv.closed
          pendingIn := fun q member => inv.pendingIn q (List.mem_cons_of_mem _ member)
          factsIn := inv.factsIn
          nodup := inv.nodup
          edgesIn := inv.edgesIn
          requires := fun q member => requires_mono sub q (inv.requires q member)
          everywhere := fun n bound => sub _ (inv.everywhere n bound) }
/-- A new fact is added, and its pending entry is replaced by `extra`. -/
theorem invariant_add {count : Nat} {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {next facts extra : List (Nat × nnf.NnfConcept)}
    {p : Nat × nnf.NnfConcept} (inv : Invariant count cl axioms edges (p :: next) facts) (fresh : p ∉ facts)
    (extraIn : ∀ q ∈ extra, q.1 < count ∧ q.2 ∈ cl)
    (required : Requires edges (p :: facts ++ (extra ++ next)) p) :
    Invariant count cl axioms edges (extra ++ next) (p :: facts) := by
  have sub : ∀ q ∈ facts ++ p :: next, q ∈ p :: facts ++ (extra ++ next) := by
    intro q member
    simp only [List.mem_append,List.mem_cons] at member ⊢
    rcases member with old | rfl | later
    · exact .inl (.inr old)
    · exact .inl (.inl rfl)
    · exact .inr (.inr later)
  refine { closed := inv.closed
           pendingIn := ?_
           factsIn := ?_
           nodup := List.nodup_cons.mpr ⟨fresh,inv.nodup⟩
           edgesIn := inv.edgesIn
           requires := ?_
           everywhere := fun n bound => sub _ (inv.everywhere n bound) }
  · intro q member
    rcases List.mem_append.mp member with new | later
    · exact extraIn q new
    · exact inv.pendingIn q (List.mem_cons_of_mem _ later)
  · intro q member
    rcases List.mem_cons.mp member with rfl | old
    · exact inv.pendingIn _ (List.mem_cons_self ..)
    · exact inv.factsIn q old
  · intro q member
    rcases List.mem_cons.mp member with rfl | old
    · exact required
    · exact requires_mono sub q (inv.requires q old)

/-- The procedure's contract on the current facts: acceptance yields a model
    over a type, and every model, in the given universes, forces acceptance. -/
def Decides (axioms : nnf.NnfConcept) (edges : List (ObjectProperty × Nat × Nat))
    (current : List (Nat × nnf.NnfConcept)) (result : Bool) : Prop :=
  (result = true → ∃ (Object : Type) (I : Interpretation Object Unit) (f : Nat → Object),
    AboxModel axioms current edges I f) ∧
  ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (f : Nat → Object),
    AboxModel axioms current edges I f) → result = true)

theorem model_mono {Object : Type u} {Value : Type v} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {small large : List (Nat × nnf.NnfConcept)}
    {I : Interpretation Object Value} {f : Nat → Object} (sub : ∀ p ∈ small, p ∈ large)
    (model : AboxModel axioms large edges I f) : AboxModel axioms small edges I f :=
  ⟨model.1,fun p member => model.2.1 p (sub p member),model.2.2⟩
/-- A contract on more facts is a contract on fewer, when every model of the
    fewer facts is a model of the more. -/
theorem decides_of_implies {axioms : nnf.NnfConcept} {edges : List (ObjectProperty × Nat × Nat)}
    {small large : List (Nat × nnf.NnfConcept)} {result : Bool} (sub : ∀ p ∈ small, p ∈ large)
    (back : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (f : Nat → Object),
      AboxModel axioms small edges I f → AboxModel axioms large edges I f)
    (decides : Decides.{u,v} axioms edges large result) : Decides.{u,v} axioms edges small result := by
  refine ⟨fun accepted => ?_,fun ⟨Object,Value,I,f,model⟩ => decides.2 ⟨Object,Value,I,f,back I f model⟩⟩
  obtain ⟨Object,I,f,model⟩ := decides.1 accepted
  exact ⟨Object,I,f,model_mono sub model⟩

/-- Models of fewer facts extend to more facts that every such model satisfies. -/
theorem model_extend {Object : Type u} {Value : Type v} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {small large extra : List (Nat × nnf.NnfConcept)}
    {I : Interpretation Object Value} {f : Nat → Object} (cover : ∀ p ∈ large, p ∈ small ∨ p ∈ extra)
    (model : AboxModel axioms small edges I f) (implied : ∀ p ∈ extra, conceptDenote I p.2 (f p.1)) :
    AboxModel axioms large edges I f :=
  ⟨model.1,fun p member => (cover p member).elim (model.2.1 p) (implied p),model.2.2⟩
theorem decides_of_extra {axioms : nnf.NnfConcept} {edges : List (ObjectProperty × Nat × Nat)}
    {small large extra : List (Nat × nnf.NnfConcept)} {result : Bool}
    (sub : ∀ p ∈ small, p ∈ large) (cover : ∀ p ∈ large, p ∈ small ∨ p ∈ extra)
    (implied : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (f : Nat → Object),
      AboxModel axioms small edges I f → ∀ p ∈ extra, conceptDenote I p.2 (f p.1))
    (decides : Decides.{u,v} axioms edges large result) : Decides.{u,v} axioms edges small result :=
  decides_of_implies sub (fun I f model => model_extend cover model (implied I f model)) decides

/-- The actual completion terminates on every call satisfying the invariants and
    decides exactly whether the added and pending facts have a model. -/
theorem complete_correct (count : Nat) (positive : 0 < count) (cl : List nnf.NnfConcept) (axioms : nnf.NnfConcept)
    (edges : abox.Edges) (pending facts : abox.Facts)
    (inv : Invariant count cl axioms (edgesList edges) (factsList pending) (factsList facts)) :
    ∃ result, abox.complete pending facts edges axioms = .ok result ∧
      Decides.{u,v} axioms (edgesList edges) (factsList facts ++ factsList pending) result := by
  cases pending with
  | Empty =>
    rw [abox.complete.eq_def]
    by_cases clash : ∃ n k, (n,.NotAtom k) ∈ factsList facts ∧ (n,.Atom k) ∈ factsList facts
    · refine ⟨false,by simp [duplicate_facts_correct,has_clash_correct,clash],?_⟩
      constructor
      · intro impossible; cases impossible
      rintro ⟨Object,Value,I,f,_,holds,_⟩
      obtain ⟨n,k,negative,positive'⟩ := clash
      exact False.elim
        ((holds (n,.NotAtom k) (by simp [factsList,negative])) (holds (n,.Atom k) (by simp [factsList,positive'])))
    · obtain ⟨ok,okRun,okIff⟩ := obligations_hold_correct facts facts axioms
      refine ⟨ok,by simp [duplicate_facts_correct,has_clash_correct,clash,okRun],?_⟩
      constructor
      · intro accepted
        have every := okIff.mp accepted
        have alone : factsList facts ++ factsList abox.Facts.Empty = factsList facts := by simp [factsList]
        rw [alone]
        apply model_of_saturated count positive axioms _ _ (fun p member => (inv.factsIn p member).1) inv.edgesIn
        · intro p member
          simpa [factsList] using inv.requires p member
        · intro n bound
          simpa [factsList] using inv.everywhere n bound
        · intro n k negative positive'
          exact clash ⟨n,k,negative,positive'⟩
        · intro n r d member
          obtain ⟨result,run,sound,_⟩ :=
            satisfiable_all_correct.{0,0} (.Entry d (fromList (nodeFillers r n (factsList facts)))) axioms
          have obligation := every n r d member
          rw [Obligation,run] at obligation
          obtain ⟨Object,I,everywhere,x,holds⟩ := sound (Result.ok_injective obligation)
          exact ⟨Object,I,everywhere,x,by simpa [toList,toList_fromList] using holds⟩
      · rintro ⟨Object,Value,I,f,everywhere,holds,_⟩
        apply okIff.mpr
        intro n r d member
        obtain ⟨y,edge,inner⟩ := holds (n,.Exists r d) (by simp [factsList,member])
        obtain ⟨result,run,_,complete⟩ :=
          satisfiable_all_correct.{u,v} (.Entry d (fromList (nodeFillers r n (factsList facts)))) axioms
        have accepted : result = true := by
          apply complete
          refine ⟨Object,Value,I,everywhere,y,fun e eMem => ?_⟩
          simp only [toList,toList_fromList,List.mem_cons] at eMem
          rcases eMem with rfl | filler
          · exact inner
          · exact holds (n,.Forall r e) (by simp [factsList]; exact (nodeFillers_mem r n _ e).mp filler) y edge
        rw [Obligation,run,accepted]
  | Entry node c next =>
    rw [abox.complete.eq_def]
    have head := inv.pendingIn _ (List.mem_cons_self ..)
    by_cases present : (node.val,c) ∈ factsList facts
    · have inv' := invariant_skip inv present
      obtain ⟨result,run,decides⟩ := complete_correct count positive cl axioms edges next facts inv'
      refine ⟨result,by simp [contains_fact_correct,present,run],?_⟩
      refine decides_of_extra (extra := []) ?_ ?_ (fun _ _ _ p member => by cases member) decides
      · intro p member
        simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
        rcases member with old | rfl | later
        · exact .inl old
        · exact .inl present
        · exact .inr later
      · intro p member
        simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
        rcases member with old | later
        · exact .inl (.inl old)
        · exact .inl (.inr (.inr later))
    · have unchanged : ∀ p ∈ factsList facts ++ factsList (.Entry node c next),
          p ∈ (node.val,c) :: factsList facts ++ factsList next := by
        intro p member
        simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
        rcases member with old | rfl | later
        · exact .inl (.inr old)
        · exact .inl (.inl rfl)
        · exact .inr later
      have back : ∀ p ∈ (node.val,c) :: factsList facts ++ factsList next,
          p ∈ factsList facts ++ factsList (.Entry node c next) ∨ p ∈ ([] : List (Nat × nnf.NnfConcept)) := by
        intro p member
        simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
        rcases member with (rfl | old) | later
        · exact .inl (.inr (.inl rfl))
        · exact .inl (.inl old)
        · exact .inl (.inr (.inr later))
      cases c with
      | Bottom =>
        refine ⟨false,by simp [contains_fact_correct,present],?_⟩
        constructor
        · intro impossible; cases impossible
        rintro ⟨Object,Value,I,f,_,holds,_⟩
        exact False.elim (holds (node.val,.Bottom) (by simp [factsList]))
      | Top =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ := complete_correct count positive cl axioms edges next (.Entry node .Top facts) inv'
        exact ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra unchanged back (fun _ _ _ p member => by cases member) decides⟩
      | Atom k =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ := complete_correct count positive cl axioms edges next (.Entry node (.Atom k) facts)
          inv'
        exact ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra unchanged back (fun _ _ _ p member => by cases member) decides⟩
      | NotAtom k =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ :=
          complete_correct count positive cl axioms edges next (.Entry node (.NotAtom k) facts) inv'
        exact ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra unchanged back (fun _ _ _ p member => by cases member) decides⟩
      | Exists r d =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ :=
          complete_correct count positive cl axioms edges next (.Entry node (.Exists r d) facts) inv'
        exact ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra unchanged back (fun _ _ _ p member => by cases member) decides⟩
      | And a b =>
        have parts := inv.closed.1 a b head.2
        have inv' := invariant_add (extra := [(node.val,a),(node.val,b)]) inv present
          (by
            intro q member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl
            · exact ⟨head.1,parts.1⟩
            · exact ⟨head.1,parts.2⟩)
          ⟨by simp,by simp⟩
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ := complete_correct count positive cl axioms edges
          (.Entry node a (.Entry node b next)) (.Entry node (.And a b) facts) inv'
        refine ⟨result,by simp [contains_fact_correct,present,run],decides_of_extra (extra := [(node.val,a),(node.val,b)])
          ?_ ?_ ?_ decides⟩
        · intro p member
          simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
          rcases member with old | rfl | later
          · exact .inl (.inr old)
          · exact .inl (.inl rfl)
          · exact .inr (.inr (.inr later))
        · intro p member
          simp only [factsList,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
          rcases member with (rfl | old) | rfl | rfl | later
          · exact .inl (.inr (.inl rfl))
          · exact .inl (.inl old)
          · exact .inr (.inl rfl)
          · exact .inr (.inr rfl)
          · exact .inl (.inr (.inr later))
        · intro Object Value I f model p member
          have both := model.2.1 (node.val,.And a b) (by simp [factsList])
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact both.1
          · exact both.2
      | Or a b =>
        have parts := inv.closed.2.1 a b head.2
        have invLeft := invariant_add (extra := [(node.val,a)]) inv present
          (by intro q member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst member
              exact ⟨head.1,parts.1⟩)
          (.inl (by simp))
        have invRight := invariant_add (extra := [(node.val,b)]) inv present
          (by intro q member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst member
              exact ⟨head.1,parts.2⟩)
          (.inr (by simp))
        have boundLeft := facts_bound invLeft
        have boundRight := facts_bound invRight
        obtain ⟨left,leftRun,leftDecides⟩ := complete_correct count positive cl axioms edges
          (.Entry node a next) (.Entry node (.Or a b) facts) invLeft
        obtain ⟨right,rightRun,rightDecides⟩ := complete_correct count positive cl axioms edges
          (.Entry node b next) (.Entry node (.Or a b) facts) invRight
        have subLeft : ∀ p ∈ factsList facts ++ factsList (.Entry node (.Or a b) next),
            p ∈ factsList (.Entry node (.Or a b) facts) ++ factsList (.Entry node a next) := by
          intro p member
          simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
          rcases member with old | rfl | later
          · exact .inl (.inr old)
          · exact .inl (.inl rfl)
          · exact .inr (.inr later)
        have subRight : ∀ p ∈ factsList facts ++ factsList (.Entry node (.Or a b) next),
            p ∈ factsList (.Entry node (.Or a b) facts) ++ factsList (.Entry node b next) := by
          intro p member
          simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
          rcases member with old | rfl | later
          · exact .inl (.inr old)
          · exact .inl (.inl rfl)
          · exact .inr (.inr later)
        have cover : ∀ (e : nnf.NnfConcept), ∀ p ∈ factsList (.Entry node (.Or a b) facts) ++ factsList (.Entry node e next),
            p ∈ factsList facts ++ factsList (.Entry node (.Or a b) next) ∨ p ∈ [(node.val,e)] := by
          intro e p member
          simp only [factsList,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
          rcases member with (rfl | old) | rfl | later
          · exact .inl (.inr (.inl rfl))
          · exact .inl (.inl old)
          · exact .inr rfl
          · exact .inl (.inr (.inr later))
        refine ⟨left || right,?_,?_⟩
        · simp [contains_fact_correct,present,duplicate_facts_correct,duplicate_edges_correct,leftRun,rightRun]
          cases left <;> rfl
        constructor
        · intro accepted
          rcases Bool.or_eq_true_iff.mp accepted with chosen | chosen
          · obtain ⟨Object,I,f,model⟩ := leftDecides.1 chosen
            exact ⟨Object,I,f,model_mono subLeft model⟩
          · obtain ⟨Object,I,f,model⟩ := rightDecides.1 chosen
            exact ⟨Object,I,f,model_mono subRight model⟩
        · rintro ⟨Object,Value,I,f,model⟩
          rcases model.2.1 (node.val,.Or a b) (by simp [factsList]) with inA | inB
          · have := leftDecides.2 ⟨Object,Value,I,f,model_extend (cover a) model (by
              intro p member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst member; exact inA)⟩
            simp [this]
          · have := rightDecides.2 ⟨Object,Value,I,f,model_extend (cover b) model (by
              intro p member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst member; exact inB)⟩
            simp [this]
      | Forall r d =>
        have filler := inv.closed.2.2.2 r d head.2
        obtain ⟨pushed,pushRun,pushContents⟩ := propagate_correct edges node r d next
        have inv' := invariant_add
          (extra := (targetsOf r node.val (edgesList edges)).map (fun m => (m,d))) inv present
          (by
            intro q member
            simp only [List.mem_map] at member
            obtain ⟨m,target,rfl⟩ := member
            exact ⟨(inv.edgesIn _ ((targetsOf_mem r node.val m _).mp target)).2,filler⟩)
          (by
            intro m edge
            simp only [List.mem_append,List.mem_cons,List.mem_map]
            exact .inr (.inl ⟨m,(targetsOf_mem r node.val m _).mpr edge,rfl⟩))
        have bound := facts_bound inv'
        rw [← pushContents] at inv'
        obtain ⟨result,run,decides⟩ := complete_correct count positive cl axioms edges pushed
          (.Entry node (.Forall r d) facts) inv'
        refine ⟨result,by simp [contains_fact_correct,present,pushRun,run],?_⟩
        rw [pushContents] at decides
        refine decides_of_extra (extra := (targetsOf r node.val (edgesList edges)).map (fun m => (m,d))) ?_ ?_ ?_ decides
        · intro p member
          simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
          rcases member with old | rfl | later
          · exact .inl (.inr old)
          · exact .inl (.inl rfl)
          · exact .inr (.inr later)
        · intro p member
          simp only [factsList,List.mem_append,List.mem_cons] at member ⊢
          rcases member with (rfl | old) | pushedHere | later
          · exact .inl (.inr (.inl rfl))
          · exact .inl (.inl old)
          · exact .inr pushedHere
          · exact .inl (.inr (.inr later))
        · intro Object Value I f model p member
          simp only [List.mem_map] at member
          obtain ⟨m,target,rfl⟩ := member
          exact model.2.1 (node.val,.Forall r d) (by simp [factsList]) (f m)
            (model.2.2 _ ((targetsOf_mem r node.val m _).mp target))
termination_by (count * cl.toFinset.card - (factsList facts).length, (factsList pending).length)
decreasing_by
  all_goals
    simp_wf
    try subst_vars
    try simp only [factsList,List.length_cons,List.length_append,List.length_map,List.length_nil] at *
    try generalize count * cl.toFinset.card = capacity at *
    try rw [Prod.lex_def]
    try omega

/-- The public procedure terminates. For facts and edges at nodes below a positive
    count, every acceptance yields an interpretation with an element for every
    node that satisfies the facts, the edges and the TBox concept everywhere, and
    every such interpretation, in any universe, forces acceptance. -/
theorem abox_satisfiable_correct (count : Usize) (positive : 0 < count.val) (facts : abox.Facts)
    (edges : abox.Edges) (axioms : nnf.NnfConcept) (factsIn : ∀ p ∈ factsList facts, p.1 < count.val)
    (edgesIn : ∀ e ∈ edgesList edges, e.2.1 < count.val ∧ e.2.2 < count.val) :
    ∃ result, abox.abox_satisfiable count facts edges axioms = .ok result ∧
      (result = true → ∃ (Object : Type) (I : Interpretation Object Unit) (f : Nat → Object),
        AboxModel axioms (factsList facts) (edgesList edges) I f) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (f : Nat → Object),
        AboxModel axioms (factsList facts) (edgesList edges) I f) → result = true) := by
  obtain ⟨initial,initialRun,initialContents⟩ := with_axioms_correct count facts axioms
  have inv : Invariant count.val (listSubconcepts ((factsList facts).map Prod.snd) ++ subconcepts axioms) axioms
      (edgesList edges) (factsList initial) (factsList .Empty) :=
    { closed := closed_append (listSubconcepts_closed _) (subconcepts_closed axioms)
      pendingIn := by
        intro p member
        rw [initialContents] at member
        rcases List.mem_append.mp member with everywhere | given
        · simp only [List.mem_map,List.mem_range] at everywhere
          obtain ⟨n,bound,rfl⟩ := everywhere
          exact ⟨bound,List.mem_append_right _ (subconcepts_self axioms)⟩
        · exact ⟨factsIn p given,List.mem_append_left _ (listSubconcepts_self (List.mem_map_of_mem given))⟩
      factsIn := by simp [factsList]
      nodup := List.nodup_nil
      edgesIn := edgesIn
      requires := by simp [factsList]
      everywhere := by
        intro n bound
        simp only [factsList,List.nil_append,initialContents,List.mem_append,List.mem_map,List.mem_range]
        exact .inl ⟨n,bound,rfl⟩ }
  obtain ⟨result,run,decides⟩ := complete_correct.{u,v} count.val positive _ axioms edges initial .Empty inv
  have contents : factsList abox.Facts.Empty ++ factsList initial =
      (List.range count.val).map (fun n => (n,axioms)) ++ factsList facts := by
    simp [factsList,initialContents]
  rw [contents] at decides
  refine ⟨result,by rw [abox.abox_satisfiable]; simp [initialRun,run],?_,?_⟩
  · intro accepted
    obtain ⟨Object,I,f,model⟩ := decides.1 accepted
    exact ⟨Object,I,f,model_mono (fun p member => List.mem_append_right _ member) model⟩
  · rintro ⟨Object,Value,I,f,model⟩
    apply decides.2
    refine ⟨Object,Value,I,f,model_extend (extra := (List.range count.val).map (fun n => (n,axioms)))
      (fun p member => (List.mem_append.mp member).symm) model ?_⟩
    intro p member
    simp only [List.mem_map] at member
    obtain ⟨n,_,rfl⟩ := member
    exact model.1 (f n)
end Rowl.AboxTableau
