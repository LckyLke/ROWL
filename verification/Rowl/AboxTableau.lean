import Rowl.TboxTableau

/-!
Reasoning with named individuals under role axioms (SH), proved total, sound and
complete. Facts say that concepts hold at numbered nodes, edges say that named
object properties relate nodes, and a role box lists inclusions between named
object properties, closed under composition, and transitive properties. The
completion adds every fact once, expands conjunctions, branches on disjunctions
and pushes every universal restriction along each edge whose property it
includes, together with its restrictions on the transitive properties in
between; it then checks every node for a clash and decides every existential
restriction with the TBox tableau. Every acceptance yields an interpretation of
the role axioms with an element for each node that satisfies the facts, the
edges and the TBox concept everywhere, and that relates node elements only as
the edges and role axioms entail; every such interpretation, in any universe,
forces acceptance. Termination: each added fact is new and drawn from the finite
set of node and closure pairs. The ALC entry point is the procedure without role
axioms.
-/
namespace Rowl.AboxTableau
open Aeneas Aeneas.Std Aeneas.Std.Result RowlRust RowlRust.model
open Rowl.Owl (Interpretation)
open Rowl.Nnf (conceptDenote)
open Rowl.Tableau (Holds property_eq_iff class_eq_iff)
open Rowl.RoleBox (Below Respects transitives below_refl respects_below closed_of_empty respects_of_empty)
open Rowl.Hintikka (universalItems roleFillers roleFillers_mem universalItems_mem)
open Rowl.TboxTableau (subconcepts Closed subconcepts_self subconcepts_closed closed_append listSubconcepts
  listSubconcepts_closed listSubconcepts_self same_concept_correct universal_is_correct universal_correct itemsList
  withThroughs Throughs withThroughs_base withThroughs_closed withThroughs_throughs satisfiable_items_correct
  no_roles_correct)
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
universe u v

/-- The facts of a list, in order: the node and the concept that holds there; a
    `Through` fact is its universal restriction. -/
def factsList : abox.Facts → List (Nat × nnf.NnfConcept)
  | .Empty => []
  | .Entry node c next => (node.val,c) :: factsList next
  | .Through node t d next => (node.val,.Forall t d) :: factsList next
/-- The edges of a list, in order: the role, its source node and its target node. -/
def edgesList : abox.Edges → List (ObjectProperty × Nat × Nat)
  | .Empty => []
  | .Entry r source target next => (r,source.val,target.val) :: edgesList next
/-- The concepts at a node, in list order. -/
def nodeConcepts (node : Nat) : List (Nat × nnf.NnfConcept) → List nnf.NnfConcept
  | [] => []
  | p :: rest => if p.1 = node then p.2 :: nodeConcepts node rest else nodeConcepts node rest
/-- What the universal restrictions at a node require of an element reached
    along the role, in list order. -/
noncomputable def nodeFillers (rb : role_box.RoleBox) (role : ObjectProperty) (node : Nat)
    (facts : List (Nat × nnf.NnfConcept)) : List nnf.NnfConcept :=
  roleFillers rb role (nodeConcepts node facts)
/-- What a universal restriction at a node requires of the targets of the edges
    from the node, in edge order. -/
noncomputable def pushes (rb : role_box.RoleBox) (role : ObjectProperty) (filler : nnf.NnfConcept) (node : Nat) :
    List (ObjectProperty × Nat × Nat) → List (Nat × nnf.NnfConcept)
  | [] => []
  | e :: rest => (if e.2.1 = node then (universalItems rb e.1 role filler).map (fun x => (e.2.2,x)) else []) ++
      pushes rb role filler node rest

theorem nodeConcepts_mem (node : Nat) (facts : List (Nat × nnf.NnfConcept)) (c : nnf.NnfConcept) :
    c ∈ nodeConcepts node facts ↔ (node,c) ∈ facts := by
  induction facts with
  | nil => simp [nodeConcepts]
  | cons p rest ih =>
    obtain ⟨n,e⟩ := p
    by_cases here : n = node
    · subst here
      simp only [nodeConcepts,↓reduceIte,List.mem_cons,ih,Prod.mk.injEq,true_and]
    · simp only [nodeConcepts,here,↓reduceIte,ih,List.mem_cons,Prod.mk.injEq]
      constructor
      · exact .inr
      · rintro (⟨rfl,_⟩ | later)
        · exact absurd rfl here
        · exact later
theorem nodeFillers_mem (rb : role_box.RoleBox) (role : ObjectProperty) (node : Nat)
    (facts : List (Nat × nnf.NnfConcept)) (x : nnf.NnfConcept) :
    x ∈ nodeFillers rb role node facts ↔ ∃ q d, (node,.Forall q d) ∈ facts ∧ Below rb role q ∧
      (x = d ∨ ∃ t ∈ transitives rb, Below rb role t ∧ Below rb t q ∧ x = .Forall t d) := by
  simp only [nodeFillers,roleFillers_mem,nodeConcepts_mem]
theorem pushes_mem (rb : role_box.RoleBox) (role : ObjectProperty) (filler : nnf.NnfConcept) (node : Nat)
    (edges : List (ObjectProperty × Nat × Nat)) (p : Nat × nnf.NnfConcept) :
    p ∈ pushes rb role filler node edges ↔
      ∃ s m, (s,node,m) ∈ edges ∧ p.1 = m ∧ p.2 ∈ universalItems rb s role filler := by
  induction edges with
  | nil => simp [pushes]
  | cons e rest ih =>
    obtain ⟨s,n,m⟩ := e
    obtain ⟨k,x⟩ := p
    simp only [pushes,List.mem_append,ih,List.mem_cons,Prod.mk.injEq]
    by_cases here : n = node
    · subst here
      simp only [↓reduceIte,List.mem_map,Prod.mk.injEq]
      constructor
      · rintro (⟨y,member,hm,hx⟩ | ⟨s',m',edge,first,second⟩)
        · exact ⟨s,m,.inl (by simp),hm.symm,hx ▸ member⟩
        · exact ⟨s',m',.inr edge,first,second⟩
      · rintro ⟨s',m',(⟨rfl,-,rfl⟩ | edge),first,second⟩
        · exact .inl ⟨x,second,first.symm,rfl⟩
        · exact .inr ⟨s',m',edge,first,second⟩
    · simp only [here,↓reduceIte,List.not_mem_nil,false_or]
      constructor
      · rintro ⟨s',m',edge,first,second⟩
        exact ⟨s',m',.inr edge,first,second⟩
      · rintro ⟨s',m',(⟨rfl,same,rfl⟩ | edge),first,second⟩
        · exact absurd same.symm here
        · exact ⟨s',m',edge,first,second⟩

theorem duplicate_facts_correct (list : abox.Facts) : abox.duplicate_facts list = .ok (list,list) := by
  induction list with
  | Empty => rw [abox.duplicate_facts]
  | Entry node c next ih => rw [abox.duplicate_facts]; simp [ih]
  | Through node t d next ih => rw [abox.duplicate_facts]; simp [ih]
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
  | Through other t d next ih =>
    rw [abox.contains_fact.eq_def]
    by_cases same : other = node
    · subst same
      by_cases equal : sought = .Forall t d
      · subst equal; simp [ih,factsList,universal_is_correct]
      · simp [ih,factsList,universal_is_correct,equal]
    · have different : ¬ node.val = other.val := fun h => same ((usize_eq_iff other node).mpr h.symm)
      simp [ih,factsList,same,different]
/-- Membership of a universal restriction is decided exactly, whether it was
    added as a concept or as a `Through` fact; the list is handed back. -/
theorem contains_through_correct (list : abox.Facts) (node : Usize) (role : ObjectProperty)
    (filler : nnf.NnfConcept) :
    abox.contains_through list node role filler =
      .ok (decide ((node.val,.Forall role filler) ∈ factsList list),list) := by
  induction list with
  | Empty => rw [abox.contains_through.eq_def]; simp [factsList]
  | Entry other c next ih =>
    rw [abox.contains_through.eq_def]
    by_cases same : other = node
    · subst same
      by_cases equal : c = .Forall role filler
      · subst equal; simp [ih,factsList,universal_is_correct]
      · have equal' : ¬ .Forall role filler = c := fun h => equal h.symm
        simp [ih,factsList,universal_is_correct,equal,equal']
    · have different : ¬ node.val = other.val := fun h => same ((usize_eq_iff other node).mpr h.symm)
      simp [ih,factsList,same,different]
  | Through other t d next ih =>
    rw [abox.contains_through.eq_def]
    by_cases same : other = node
    · subst same
      by_cases sameRole : role = t
      · subst sameRole
        by_cases sameFiller : filler = d
        · subst sameFiller; simp [ih,factsList,Rowl.Symbols.same_spelling_total_correct,same_concept_correct]
        · simp [ih,factsList,Rowl.Symbols.same_spelling_total_correct,same_concept_correct,sameFiller]
      · have different : ¬ role.iri.spelling.val = t.iri.spelling.val :=
          fun h => sameRole ((property_eq_iff _ _).mpr h)
        simp [ih,factsList,Rowl.Symbols.same_spelling_total_correct,different,sameRole]
    · have different : ¬ node.val = other.val := fun h => same ((usize_eq_iff other node).mpr h.symm)
      simp [ih,factsList,same,different]

/-- Items become facts at one node, in order, in front of the tail. -/
theorem place_correct (node : Usize) (items : tbox.Items) (tail : abox.Facts) :
    ∃ placed, abox.place node items tail = .ok placed ∧
      factsList placed = (itemsList items).map (fun x => (node.val,x)) ++ factsList tail := by
  induction items with
  | Empty => exact ⟨tail,by rw [abox.place],by simp [itemsList]⟩
  | Concept c next ih =>
    obtain ⟨placed,run,list⟩ := ih
    exact ⟨.Entry node c placed,by rw [abox.place]; simp [run],by simp [factsList,itemsList,list]⟩
  | Through t d next ih =>
    obtain ⟨placed,run,list⟩ := ih
    exact ⟨.Through node t d placed,by rw [abox.place]; simp [run],by simp [factsList,itemsList,list]⟩

/-- A universal restriction at a node reaches exactly what it requires at the
    targets of the edges from the node; the edges are handed back. -/
theorem propagate_correct (edges : abox.Edges) (node : Usize) (role : ObjectProperty) (filler : nnf.NnfConcept)
    (pending : abox.Facts) (rb : role_box.RoleBox) :
    ∃ pushed, abox.propagate edges node role filler pending rb = .ok (pushed,edges) ∧
      factsList pushed = pushes rb role filler node.val (edgesList edges) ++ factsList pending := by
  induction edges with
  | Empty => exact ⟨pending,by rw [abox.propagate.eq_def],by simp [pushes,edgesList]⟩
  | Entry other source target next ih =>
    obtain ⟨pushed,run,contents⟩ := ih
    rw [abox.propagate.eq_def]
    by_cases from_node : source = node
    · subst from_node
      obtain ⟨required,requiredRun,requiredList⟩ := universal_correct rb other role filler .Empty
      obtain ⟨placed,placeRun,placeList⟩ := place_correct target required pushed
      refine ⟨placed,by simp [run,requiredRun,placeRun],?_⟩
      rw [placeList,requiredList,contents]
      simp [pushes,edgesList,itemsList]
    · have different : ¬ source.val = node.val := fun h => from_node ((usize_eq_iff source node).mpr h)
      exact ⟨pushed,by simp [run,from_node],by simp [pushes,edgesList,contents,different]⟩

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
  | Through other t d next ih => rw [abox.has_atom.eq_def]; simp [ih,factsList]
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
  | Through node t d next ih => rw [abox.has_clash.eq_def]; simp [ih,factsList]

/-- What the universal restrictions at a node require along a role is found
    exactly; the list is handed back. -/
theorem node_fillers_correct (list : abox.Facts) (node : Usize) (role : ObjectProperty) (rb : role_box.RoleBox) :
    ∃ fillers, abox.node_fillers list node role rb = .ok (fillers,list) ∧
      itemsList fillers = nodeFillers rb role node.val (factsList list) := by
  induction list with
  | Empty => exact ⟨.Empty,by rw [abox.node_fillers.eq_def],by simp [itemsList,nodeFillers,nodeConcepts,roleFillers,factsList]⟩
  | Entry other c next ih =>
    obtain ⟨fillers,run,list⟩ := ih
    rw [abox.node_fillers.eq_def]
    by_cases same : other = node
    · subst same
      cases c with
      | Forall q d =>
        obtain ⟨result,universalRun,universalList⟩ := universal_correct rb role q d fillers
        refine ⟨result,by simp [run,universalRun],?_⟩
        rw [universalList,list]
        simp [nodeFillers,nodeConcepts,roleFillers,factsList]
      | _ =>
        refine ⟨fillers,by simp [run],?_⟩
        rw [list]
        simp [nodeFillers,nodeConcepts,roleFillers,factsList]
    · have different : ¬ other.val = node.val := fun h => same ((usize_eq_iff other node).mpr h)
      have unchanged : nodeFillers rb role node.val (factsList (.Entry other c next)) =
          nodeFillers rb role node.val (factsList next) := by
        simp [nodeFillers,nodeConcepts,factsList,different]
      rw [unchanged]
      cases c with
      | Forall q d => exact ⟨fillers,by simp [run,same],list⟩
      | _ => exact ⟨fillers,by simp [run],list⟩
  | Through other t d next ih =>
    obtain ⟨fillers,run,list⟩ := ih
    rw [abox.node_fillers.eq_def]
    by_cases same : other = node
    · subst same
      obtain ⟨result,universalRun,universalList⟩ := universal_correct rb role t d fillers
      refine ⟨result,by simp [run,universalRun],?_⟩
      rw [universalList,list]
      simp [nodeFillers,nodeConcepts,roleFillers,factsList]
    · have different : ¬ other.val = node.val := fun h => same ((usize_eq_iff other node).mpr h)
      have unchanged : nodeFillers rb role node.val (factsList (.Through other t d next)) =
          nodeFillers rb role node.val (factsList next) := by
        simp [nodeFillers,nodeConcepts,factsList,different]
      rw [unchanged]
      exact ⟨fillers,by simp [run,same],list⟩

/-- Some model of the role axioms, in the given universes, in which the TBox
    concept holds everywhere, has an element satisfying the filler and what the
    universal restrictions at the node require along the role. -/
def Successor (rb : role_box.RoleBox) (axioms : nnf.NnfConcept) (facts : List (Nat × nnf.NnfConcept)) (n : Nat)
    (r : ObjectProperty) (d : nnf.NnfConcept) : Prop :=
  ∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value), Respects I rb ∧
    (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (d :: nodeFillers rb r n facts)

/-- One existential obligation is decided by the TBox tableau; the list is
    handed back. -/
theorem obligation_holds_correct (all : abox.Facts) (node : Usize) (role : ObjectProperty)
    (filler axioms : nnf.NnfConcept) (rb : role_box.RoleBox) :
    ∃ result, abox.obligation_holds all node role filler axioms rb = .ok (result,all) ∧
      (result = true → Rowl.RoleBox.Closed rb → ∃ (Object : Type) (I : Interpretation Object Unit),
        Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧
          ∃ x, Holds I x (filler :: nodeFillers rb role node.val (factsList all))) ∧
      (Successor.{u,v} rb axioms (factsList all) node.val role filler → result = true) := by
  obtain ⟨fillers,fillersRun,fillersList⟩ := node_fillers_correct all node role rb
  obtain ⟨result,run,sound,complete⟩ := satisfiable_items_correct.{u,v} (.Concept filler fillers) axioms rb
  refine ⟨result,by rw [abox.obligation_holds]; simp [fillersRun,run],?_,?_⟩
  · intro accepted closed
    obtain ⟨Object,I,respects,everywhere,x,holds⟩ := sound accepted closed
    exact ⟨Object,I,respects,everywhere,x,by simpa [itemsList,fillersList] using holds⟩
  · rintro ⟨Object,Value,I,respects,everywhere,x,holds⟩
    exact complete ⟨Object,Value,I,respects,everywhere,x,by simpa [itemsList,fillersList] using holds⟩

/-- The obligations check is exact: it accepts when the TBox tableau accepts
    every existential restriction in the cursor; the list is handed back. -/
theorem obligations_hold_correct (all cursor : abox.Facts) (axioms : nnf.NnfConcept) (rb : role_box.RoleBox) :
    ∃ result, abox.obligations_hold all cursor axioms rb = .ok (result,all) ∧
      (result = true → Rowl.RoleBox.Closed rb → ∀ n r d, (n,.Exists r d) ∈ factsList cursor →
        ∃ (Object : Type) (I : Interpretation Object Unit), Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧
          ∃ x, Holds I x (d :: nodeFillers rb r n (factsList all))) ∧
      ((∀ n r d, (n,.Exists r d) ∈ factsList cursor → Successor.{u,v} rb axioms (factsList all) n r d) →
        result = true) := by
  induction cursor with
  | Empty => exact ⟨true,by rw [abox.obligations_hold.eq_def],by simp [factsList],by simp⟩
  | Entry node c next ih =>
    obtain ⟨later,laterRun,laterSound,laterComplete⟩ := ih
    rw [abox.obligations_hold.eq_def]
    cases c with
    | Exists r d =>
      obtain ⟨here,hereRun,hereSound,hereComplete⟩ := obligation_holds_correct.{u,v} all node r d axioms rb
      refine ⟨here && later,by simp [hereRun,laterRun]; cases here <;> rfl,?_,?_⟩
      · intro accepted closed n s e member
        rw [Bool.and_eq_true] at accepted
        simp only [factsList,List.mem_cons,Prod.mk.injEq] at member
        rcases member with ⟨rfl,same⟩ | inNext
        · cases same; exact hereSound accepted.1 closed
        · exact laterSound accepted.2 closed n s e inNext
      · intro every
        rw [hereComplete (every node.val r d (by simp [factsList])),
          laterComplete (fun n s e member => every n s e (by simp [factsList,member]))]
        rfl
    | _ =>
      refine ⟨later,by simp [laterRun],?_,?_⟩
      · intro accepted closed n s e member
        simp only [factsList,List.mem_cons,Prod.mk.injEq] at member
        rcases member with ⟨_,impossible⟩ | inNext
        · cases impossible
        · exact laterSound accepted closed n s e inNext
      · intro every
        exact laterComplete (fun n s e member => every n s e (by simp [factsList,member]))
  | Through node t d next ih =>
    obtain ⟨later,laterRun,laterSound,laterComplete⟩ := ih
    rw [abox.obligations_hold.eq_def]
    refine ⟨later,by simp [laterRun],?_,?_⟩
    · intro accepted closed n s e member
      simp only [factsList,List.mem_cons,Prod.mk.injEq] at member
      rcases member with ⟨_,impossible⟩ | inNext
      · cases impossible
      · exact laterSound accepted closed n s e inNext
    · intro every
      exact laterComplete (fun n s e member => every n s e (by simp [factsList,member]))

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

/-- Between node elements below the count, the interpretation relates nodes
    only along the given edges. -/
def ExactEdges {Object : Type u} {Value : Type v} (count : Nat) (edges : List (ObjectProperty × Nat × Nat))
    (I : Interpretation Object Value) (f : Nat → Object) : Prop :=
  ∀ r n m, n < count → m < count → I.objectProperties r (f n) (f m) → (r,n,m) ∈ edges

/-- An `AboxModel` that also satisfies the role axioms. -/
def RoleModel {Object : Type u} {Value : Type v} (rb : role_box.RoleBox) (axioms : nnf.NnfConcept)
    (facts : List (Nat × nnf.NnfConcept)) (edges : List (ObjectProperty × Nat × Nat))
    (I : Interpretation Object Value) (f : Nat → Object) : Prop :=
  Respects I rb ∧ AboxModel axioms facts edges I f

/-- An edge along a property included in `t`. -/
def EdgeStep (rb : role_box.RoleBox) (edges : List (ObjectProperty × Nat × Nat)) (t : ObjectProperty)
    (n m : Nat) : Prop :=
  ∃ s, Below rb s t ∧ (s,n,m) ∈ edges
/-- The edges and role axioms entail that `r` relates the nodes: an edge along a
    property included in `r`, or a path of edges along the properties included
    in a transitive property that is included in `r`. -/
def Entailed (rb : role_box.RoleBox) (edges : List (ObjectProperty × Nat × Nat)) (r : ObjectProperty)
    (n m : Nat) : Prop :=
  EdgeStep rb edges r n m ∨ ∃ t ∈ transitives rb, Below rb t r ∧ Relation.TransGen (EdgeStep rb edges t) n m
/-- Between node elements below the count, the interpretation relates nodes only
    as the edges and role axioms entail. -/
def EntailedEdges {Object : Type u} {Value : Type v} (rb : role_box.RoleBox) (count : Nat)
    (edges : List (ObjectProperty × Nat × Nat)) (I : Interpretation Object Value) (f : Nat → Object) : Prop :=
  ∀ r n m, n < count → m < count → I.objectProperties r (f n) (f m) → Entailed rb edges r n m

/-- What an added fact requires of the known facts: a conjunction both conjuncts,
    a disjunction one disjunct and a universal restriction what it requires at
    the target of every edge from the node; the bottom concept is never added. -/
def Requires (rb : role_box.RoleBox) (edges : List (ObjectProperty × Nat × Nat))
    (known : List (Nat × nnf.NnfConcept)) : Nat × nnf.NnfConcept → Prop
  | (n,.And a b) => (n,a) ∈ known ∧ (n,b) ∈ known
  | (n,.Or a b) => (n,a) ∈ known ∨ (n,b) ∈ known
  | (n,.Forall q d) => ∀ s m, (s,n,m) ∈ edges → ∀ x ∈ universalItems rb s q d, (m,x) ∈ known
  | (_,.Bottom) => False
  | _ => True

theorem requires_mono {rb : role_box.RoleBox} {edges : List (ObjectProperty × Nat × Nat)}
    {small large : List (Nat × nnf.NnfConcept)} (sub : ∀ p ∈ small, p ∈ large) (p : Nat × nnf.NnfConcept)
    (required : Requires rb edges small p) : Requires rb edges large p := by
  obtain ⟨n,c⟩ := p
  cases c with
  | And a b =>
    obtain ⟨left,right⟩ := required
    exact ⟨sub _ left,sub _ right⟩
  | Or a b =>
    rcases required with left | right
    · exact .inl (sub _ left)
    · exact .inr (sub _ right)
  | Forall q d => exact fun s m edge x member => sub _ (required s m edge x member)
  | Bottom => exact required
  | Top | Atom _ | NotAtom _ | Exists _ _ => trivial

/-- The existential obligations of a fact set: a node, a role and a filler. -/
abbrev Obligations (facts : List (Nat × nnf.NnfConcept)) : Type :=
  {o : Nat × ObjectProperty × nnf.NnfConcept // (o.1,.Exists o.2.1 o.2.2) ∈ facts}

/-- One step along exactly `s`, before the role axioms: an edge between nodes, a
    link from a node to the root of one of its obligations' models along `s`, or a
    step along `s` inside such a model. -/
def baseStep (count : Nat) (facts : List (Nat × nnf.NnfConcept)) (edges : List (ObjectProperty × Nat × Nat))
    (Obj : Obligations facts → Type) (J : ∀ o, Interpretation (Obj o) Unit) (root : ∀ o, Obj o)
    (s : ObjectProperty) : (Fin count ⊕ Σ o, Obj o) → (Fin count ⊕ Σ o, Obj o) → Prop
  | .inl n, z => (∃ m : Fin count, z = .inl m ∧ (s,n.val,m.val) ∈ edges) ∨
      ∃ o : Obligations facts, o.val.1 = n.val ∧ o.val.2.1 = s ∧ z = .inr ⟨o,root o⟩
  | .inr y, z => ∃ y', z = .inr ⟨y.1,y'⟩ ∧ (J y.1).objectProperties s y.2 y'
/-- One step along a property included in `t`. -/
def underStep (rb : role_box.RoleBox) (count : Nat) (facts : List (Nat × nnf.NnfConcept))
    (edges : List (ObjectProperty × Nat × Nat)) (Obj : Obligations facts → Type)
    (J : ∀ o, Interpretation (Obj o) Unit) (root : ∀ o, Obj o) (t : ObjectProperty)
    (x z : Fin count ⊕ Σ o, Obj o) : Prop :=
  ∃ s, Below rb s t ∧ baseStep count facts edges Obj J root s x z

/-- The interpretation of a saturated fact set under role axioms: one element per
    node and a disjoint copy of a successor model for every existential
    obligation. A node is in a named class when the class holds there, and a
    successor element as in its own model. A role relates two elements when one
    step along a property it includes does, or a path of steps along the
    properties included in a transitive property it includes. -/
def roleModel (rb : role_box.RoleBox) (count : Nat) (positive : 0 < count) (facts : List (Nat × nnf.NnfConcept))
    (edges : List (ObjectProperty × Nat × Nat)) (Obj : Obligations facts → Type)
    (J : ∀ o, Interpretation (Obj o) Unit) (root : ∀ o, Obj o) :
    Interpretation (Fin count ⊕ Σ o, Obj o) Unit where
  objectsNonempty := ⟨.inl ⟨0,positive⟩⟩
  dataNonempty := ⟨()⟩
  classes k x := match x with
    | .inl n => (n.val,.Atom k) ∈ facts
    | .inr y => (J y.1).classes k y.2
  objectProperties r x z := underStep rb count facts edges Obj J root r x z ∨
    ∃ t ∈ transitives rb, Below rb t r ∧ Relation.TransGen (underStep rb count facts edges Obj J root t) x z
  dataProperties _ _ _ := False
  namedIndividuals _ := .inl ⟨0,positive⟩
  anonymousIndividuals _ := .inl ⟨0,positive⟩
  datatypes _ _ := False
  literals _ := ()
  facets _ _ := False
  named _ := True

section Model
variable {rb : role_box.RoleBox} {count : Nat} {positive : 0 < count} {facts : List (Nat × nnf.NnfConcept)}
  {edges : List (ObjectProperty × Nat × Nat)} {Obj : Obligations facts → Type}
  {J : ∀ o, Interpretation (Obj o) Unit} {root : ∀ o, Obj o}

/-- A step from a successor element stays in its model, along the including
    property. -/
theorem component_step (respects : ∀ o, Respects (J o) rb) {t : ObjectProperty} {o : Obligations facts}
    {y : Obj o} {z : Fin count ⊕ Σ o, Obj o} (step : underStep rb count facts edges Obj J root t (.inr ⟨o,y⟩) z) :
    ∃ y', z = .inr ⟨o,y'⟩ ∧ (J o).objectProperties t y y' := by
  obtain ⟨s,below,y',same,edge⟩ := step
  exact ⟨y',same,respects_below (respects o) below edge⟩
/-- A path from a successor element along a transitive property stays in its
    model and is one step of that property there. -/
theorem component_path (respects : ∀ o, Respects (J o) rb) {t : ObjectProperty} (transitive : t ∈ transitives rb)
    {o : Obligations facts} {y : Obj o} {z : Fin count ⊕ Σ o, Obj o}
    (path : Relation.TransGen (underStep rb count facts edges Obj J root t) (.inr ⟨o,y⟩) z) :
    ∃ y', z = .inr ⟨o,y'⟩ ∧ (J o).objectProperties t y y' := by
  induction path with
  | single step => exact component_step respects step
  | tail _ step ih =>
    obtain ⟨y1,rfl,first⟩ := ih
    obtain ⟨y2,rfl,second⟩ := component_step respects step
    exact ⟨y2,rfl,(respects o).2 t transitive y y1 y2 first second⟩
/-- A successor element is related exactly as in its own model. -/
theorem component_related (respects : ∀ o, Respects (J o) rb) (r : ObjectProperty) (o : Obligations facts)
    (y : Obj o) (z : Fin count ⊕ Σ o, Obj o) :
    (roleModel rb count positive facts edges Obj J root).objectProperties r (.inr ⟨o,y⟩) z ↔
      ∃ y', z = .inr ⟨o,y'⟩ ∧ (J o).objectProperties r y y' := by
  constructor
  · rintro (step | ⟨t,transitive,below,path⟩)
    · exact component_step respects step
    · obtain ⟨y',rfl,edge⟩ := component_path respects transitive path
      exact ⟨y',rfl,respects_below (respects o) below edge⟩
  · rintro ⟨y',rfl,edge⟩
    exact .inl ⟨r,below_refl rb r,y',rfl,edge⟩

/-- A successor element satisfies exactly what it satisfies in its own model. -/
theorem component_truth (respects : ∀ o, Respects (J o) rb) (c : nnf.NnfConcept) :
    ∀ (o : Obligations facts) (y : Obj o),
      conceptDenote (roleModel rb count positive facts edges Obj J root) c (.inr ⟨o,y⟩) ↔ conceptDenote (J o) c y := by
  induction c with
  | Top | Bottom | Atom _ | NotAtom _ => intro o y; exact Iff.rfl
  | And a b iha ihb => intro o y; simp only [conceptDenote,iha o y,ihb o y]
  | Or a b iha ihb => intro o y; simp only [conceptDenote,iha o y,ihb o y]
  | Exists r c ih =>
    intro o y
    simp only [conceptDenote]
    constructor
    · rintro ⟨z,related,holds⟩
      obtain ⟨y',rfl,edge⟩ := (component_related respects r o y z).mp related
      exact ⟨y',edge,(ih o y').mp holds⟩
    · rintro ⟨y',edge,holds⟩
      exact ⟨.inr ⟨o,y'⟩,(component_related respects r o y _).mpr ⟨y',rfl,edge⟩,(ih o y').mpr holds⟩
  | Forall r c ih =>
    intro o y
    simp only [conceptDenote]
    constructor
    · intro every y' edge
      exact (ih o y').mp (every (.inr ⟨o,y'⟩) ((component_related respects r o y _).mpr ⟨y',rfl,edge⟩))
    · intro every z related
      obtain ⟨y',rfl,edge⟩ := (component_related respects r o y z).mp related
      exact (ih o y').mpr (every y' edge)

/-- What a concept requires at an element: a fact at a node, truth in its own
    model at a successor element. -/
def Required (facts : List (Nat × nnf.NnfConcept)) (J : ∀ o, Interpretation (Obj o) Unit) (c : nnf.NnfConcept) :
    (Fin count ⊕ Σ o, Obj o) → Prop
  | .inl m => (m.val,c) ∈ facts
  | .inr y => conceptDenote (J y.1) c y.2

/-- One step from a node along `s` reaches an element with everything a
    universal restriction at the node requires along `s`. -/
theorem step_required (requires : ∀ p ∈ facts, Requires rb edges facts p)
    (spec : ∀ o : Obligations facts, Holds (J o) (root o) (o.val.2.2 :: nodeFillers rb o.val.2.1 o.val.1 facts))
    {m : Fin count} {q s : ObjectProperty} {d : nnf.NnfConcept} {w : Fin count ⊕ Σ o, Obj o}
    (universal : (m.val,.Forall q d) ∈ facts) (step : baseStep count facts edges Obj J root s (.inl m) w) :
    ∀ x ∈ universalItems rb s q d, Required facts J x w := by
  intro x member
  rcases step with ⟨m',rfl,edge⟩ | ⟨o,source,role,rfl⟩
  · exact requires _ universal s m'.val edge x member
  · apply spec o x
    apply List.mem_cons_of_mem
    obtain ⟨below,kind⟩ := (universalItems_mem rb s q d x).mp member
    rw [nodeFillers_mem,source,role]
    exact ⟨q,d,universal,below,kind⟩

/-- In a saturated, clash-free fact set whose obligations have successor models
    of the role axioms, every fact holds at its node. -/
theorem node_truth (closed : Rowl.RoleBox.Closed rb) (respects : ∀ o, Respects (J o) rb)
    (requires : ∀ p ∈ facts, Requires rb edges facts p)
    (clashFree : ∀ n k, (n,.NotAtom k) ∈ facts → (n,.Atom k) ∉ facts)
    (spec : ∀ o : Obligations facts, Holds (J o) (root o) (o.val.2.2 :: nodeFillers rb o.val.2.1 o.val.1 facts)) :
    ∀ c (n : Fin count), (n.val,c) ∈ facts →
      conceptDenote (roleModel rb count positive facts edges Obj J root) c (.inl n) := by
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
    refine ⟨.inr ⟨⟨(n.val,r,d),member⟩,root ⟨(n.val,r,d),member⟩⟩,
      .inl ⟨r,below_refl rb r,.inr ⟨⟨(n.val,r,d),member⟩,rfl,rfl,rfl⟩⟩,?_⟩
    exact (component_truth respects d _ _).mpr (spec ⟨(n.val,r,d),member⟩ d (List.mem_cons_self ..))
  | Forall q d ih =>
    intro n member z related
    have conclude : ∀ w, Required facts J d w →
        conceptDenote (roleModel rb count positive facts edges Obj J root) d w := by
      intro w required
      rcases w with m | ⟨o,y⟩
      · exact ih m required
      · exact (component_truth respects d o y).mpr required
    rcases related with ⟨s,below,step⟩ | ⟨t,transitive,tq,path⟩
    · exact conclude z (step_required requires spec member step d
        ((universalItems_mem rb s q d d).mpr ⟨below,.inl rfl⟩))
    · -- Along a path of the transitive t, every element has the filler and `∀t.d`.
      have along : ∀ w, Required facts J d w ∧ Required facts J (.Forall t d) w →
          ∀ w', underStep rb count facts edges Obj J root t w w' →
            Required facts J d w' ∧ Required facts J (.Forall t d) w' := by
        intro w ⟨_,universal⟩ w' ⟨s,st,step⟩
        rcases w with m | ⟨o,y⟩
        · exact ⟨step_required requires spec universal step d
              ((universalItems_mem rb s t d d).mpr ⟨st,.inl rfl⟩),
            step_required requires spec universal step _
              ((universalItems_mem rb s t d _).mpr ⟨st,.inr ⟨t,transitive,st,below_refl rb t,rfl⟩⟩)⟩
        · obtain ⟨y',rfl,edge⟩ := component_step respects ⟨s,st,step⟩
          refine ⟨universal y' edge,fun z next => universal z ((respects o).2 t transitive y y' z edge next)⟩
      have reached : Required facts J d z ∧ Required facts J (.Forall t d) z := by
        induction path with
        | single step =>
          obtain ⟨s,st,stepped⟩ := step
          exact ⟨step_required requires spec member stepped d
              ((universalItems_mem rb s q d d).mpr ⟨closed s t q st tq,.inl rfl⟩),
            step_required requires spec member stepped _
              ((universalItems_mem rb s q d _).mpr ⟨closed s t q st tq,.inr ⟨t,transitive,st,tq,rfl⟩⟩)⟩
        | tail _ step ih' => exact along _ ih' _ step
      exact conclude z reached.1

/-- With closed role axioms, the model of a saturated fact set satisfies them:
    its relations include the steps along included properties and are closed
    along the paths of transitive properties. -/
theorem roleModel_respects (closed : Rowl.RoleBox.Closed rb) :
    Respects (roleModel rb count positive facts edges Obj J root) rb := by
  have widen : ∀ {t t' : ObjectProperty}, Below rb t' t → ∀ x z,
      underStep rb count facts edges Obj J root t' x z → underStep rb count facts edges Obj J root t x z := by
    intro t t' below x z ⟨s,sb,step⟩
    exact ⟨s,closed s t' t sb below,step⟩
  have toPath : ∀ t ∈ transitives rb, ∀ x z, (roleModel rb count positive facts edges Obj J root).objectProperties t x z →
      Relation.TransGen (underStep rb count facts edges Obj J root t) x z := by
    intro t _ x z related
    rcases related with step | ⟨t',_,below,path⟩
    · exact .single step
    · exact Relation.TransGen.mono (fun a b => widen below a b) path
  refine ⟨?_,?_⟩
  · intro s r listed x z related
    have sr : Below rb s r := .inr listed
    rcases related with step | ⟨t,transitive,below,path⟩
    · exact .inl (widen sr x z step)
    · exact .inr ⟨t,transitive,closed t s r below sr,path⟩
  · intro t transitive x y z first second
    exact .inr ⟨t,transitive,below_refl rb t,(toPath t transitive x y first).trans (toPath t transitive y z second)⟩

/-- A path between node elements runs along edges only. -/
theorem node_path (t : ObjectProperty) (n : Fin count) (z : Fin count ⊕ Σ o, Obj o)
    (path : Relation.TransGen (underStep rb count facts edges Obj J root t) (.inl n) z) :
    ∀ m : Fin count, z = .inl m → Relation.TransGen (EdgeStep rb edges t) n.val m.val := by
  induction path with
  | single step =>
    intro m same
    subst same
    obtain ⟨s,below,stepped⟩ := step
    rcases stepped with ⟨m',same,edge⟩ | ⟨o,_,_,impossible⟩
    · cases same; exact .single ⟨s,below,edge⟩
    · cases impossible
  | @tail b c _ step ih =>
    intro m same
    subst same
    cases b with
    | inl k =>
      obtain ⟨s,below,stepped⟩ := step
      rcases stepped with ⟨m',same,edge⟩ | ⟨o,_,_,impossible⟩
      · cases same; exact (ih k rfl).tail ⟨s,below,edge⟩
      · cases impossible
    | inr y =>
      obtain ⟨s,_,y',impossible,_⟩ := step
      cases impossible
/-- The model relates node elements only as the edges and role axioms entail. -/
theorem roleModel_entailed (r : ObjectProperty) (n m : Fin count)
    (related : (roleModel rb count positive facts edges Obj J root).objectProperties r (.inl n) (.inl m)) :
    Entailed rb edges r n.val m.val := by
  rcases related with ⟨s,below,stepped⟩ | ⟨t,transitive,below,path⟩
  · rcases stepped with ⟨m',same,edge⟩ | ⟨o,_,_,impossible⟩
    · cases same; exact .inl ⟨s,below,edge⟩
    · cases impossible
  · exact .inr ⟨t,transitive,below,node_path t n _ path m rfl⟩
end Model

private theorem choose_successors (rb : role_box.RoleBox) (axioms : nnf.NnfConcept)
    (facts : List (Nat × nnf.NnfConcept))
    (obligations : ∀ n r d, (n,.Exists r d) ∈ facts → ∃ (Object : Type) (I : Interpretation Object Unit),
      Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (d :: nodeFillers rb r n facts)) :
    ∃ (Obj : Obligations facts → Type) (J : ∀ o, Interpretation (Obj o) Unit) (root : ∀ o, Obj o),
      ∀ o, Respects (J o) rb ∧ (∀ y, conceptDenote (J o) axioms y) ∧
        Holds (J o) (root o) (o.val.2.2 :: nodeFillers rb o.val.2.1 o.val.1 facts) := by
  have pick : ∀ o : Obligations facts, Nonempty (Σ' (Obj : Type) (J : Interpretation Obj Unit) (root : Obj),
      Respects J rb ∧ (∀ y, conceptDenote J axioms y) ∧
        Holds J root (o.val.2.2 :: nodeFillers rb o.val.2.1 o.val.1 facts)) := by
    intro o
    obtain ⟨Obj,J,respects,everywhereJ,root,holds⟩ := obligations o.val.1 o.val.2.1 o.val.2.2 o.property
    exact ⟨⟨Obj,J,root,respects,everywhereJ,holds⟩⟩
  exact ⟨fun o => (Classical.choice (pick o)).1,fun o => (Classical.choice (pick o)).2.1,
    fun o => (Classical.choice (pick o)).2.2.1,fun o => (Classical.choice (pick o)).2.2.2⟩

/-- A saturated, clash-free fact set at nodes below a positive count, with the
    TBox concept at every node and a successor model of the closed role axioms
    for every existential obligation, has a model of the role axioms that relates
    node elements only as the edges and role axioms entail. -/
theorem model_of_saturated (rb : role_box.RoleBox) (closed : Rowl.RoleBox.Closed rb) (count : Nat)
    (positive : 0 < count) (axioms : nnf.NnfConcept) (edges : List (ObjectProperty × Nat × Nat))
    (facts : List (Nat × nnf.NnfConcept)) (factsIn : ∀ p ∈ facts, p.1 < count)
    (edgesIn : ∀ e ∈ edges, e.2.1 < count ∧ e.2.2 < count) (requires : ∀ p ∈ facts, Requires rb edges facts p)
    (everywhere : ∀ n < count, (n,axioms) ∈ facts) (clashFree : ∀ n k, (n,.NotAtom k) ∈ facts → (n,.Atom k) ∉ facts)
    (obligations : ∀ n r d, (n,.Exists r d) ∈ facts → ∃ (Object : Type) (I : Interpretation Object Unit),
      Respects I rb ∧ (∀ y, conceptDenote I axioms y) ∧ ∃ x, Holds I x (d :: nodeFillers rb r n facts)) :
    ∃ (Object : Type) (I : Interpretation Object Unit) (f : Nat → Object),
      RoleModel rb axioms facts edges I f ∧ EntailedEdges rb count edges I f := by
  obtain ⟨Obj,J,root,spec⟩ := choose_successors rb axioms facts obligations
  have respects : ∀ o, Respects (J o) rb := fun o => (spec o).1
  have truth := node_truth (positive := positive) (edges := edges) closed respects requires clashFree
    (fun o => (spec o).2.2)
  refine ⟨_,roleModel rb count positive facts edges Obj J root,
    fun n => if h : n < count then .inl ⟨n,h⟩ else .inl ⟨0,positive⟩,
    And.intro (roleModel_respects closed) (And.intro ?_ (And.intro ?_ ?_)),?_⟩
  · intro y
    rcases y with n | ⟨o,y⟩
    · exact truth axioms n (everywhere n.val n.isLt)
    · exact (component_truth respects axioms o y).mpr ((spec o).2.1 y)
  · intro p member
    have bound := factsIn p member
    simp only [bound,↓reduceDIte]
    exact truth p.2 ⟨p.1,bound⟩ member
  · intro e member
    obtain ⟨sourceIn,targetIn⟩ := edgesIn e member
    simp only [sourceIn,targetIn,↓reduceDIte]
    exact .inl ⟨e.1,below_refl rb e.1,.inl ⟨⟨e.2.2,targetIn⟩,rfl,member⟩⟩
  · intro r n m sourceIn targetIn related
    simp only [sourceIn,targetIn,↓reduceDIte] at related
    exact roleModel_entailed r ⟨n,sourceIn⟩ ⟨m,targetIn⟩ related

/-- Invariants of every call: facts and pending facts stay at nodes below the
    count with concepts in a closed closure that carries universal restrictions
    over to the transitive properties; the added facts are distinct; the edges
    stay below the count; every added fact's requirements are among the added and
    pending facts; and the TBox concept is at every node. -/
structure Invariant (rb : role_box.RoleBox) (count : Nat) (cl : List nnf.NnfConcept) (axioms : nnf.NnfConcept)
    (edges : List (ObjectProperty × Nat × Nat)) (pending facts : List (Nat × nnf.NnfConcept)) : Prop where
  closed : Closed cl
  throughs : Throughs rb cl
  pendingIn : ∀ p ∈ pending, p.1 < count ∧ p.2 ∈ cl
  factsIn : ∀ p ∈ facts, p.1 < count ∧ p.2 ∈ cl
  nodup : facts.Nodup
  edgesIn : ∀ e ∈ edges, e.2.1 < count ∧ e.2.2 < count
  requires : ∀ p ∈ facts, Requires rb edges (facts ++ pending) p
  everywhere : ∀ n < count, (n,axioms) ∈ facts ++ pending

/-- At most one added fact per node and closure concept. -/
theorem facts_bound {rb : role_box.RoleBox} {count : Nat} {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {pending facts : List (Nat × nnf.NnfConcept)}
    (inv : Invariant rb count cl axioms edges pending facts) : facts.length ≤ count * cl.toFinset.card := by
  have sub : facts.toFinset ⊆ Finset.range count ×ˢ cl.toFinset := by
    intro p member
    rw [List.mem_toFinset] at member
    obtain ⟨node,inCl⟩ := inv.factsIn p member
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr node,List.mem_toFinset.mpr inCl⟩
  have := Finset.card_le_card sub
  rwa [List.toFinset_card_of_nodup inv.nodup,Finset.card_product,Finset.card_range] at this

/-- A fact already added is dropped from the pending facts. -/
theorem invariant_skip {rb : role_box.RoleBox} {count : Nat} {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {next facts : List (Nat × nnf.NnfConcept)}
    {p : Nat × nnf.NnfConcept} (inv : Invariant rb count cl axioms edges (p :: next) facts) (present : p ∈ facts) :
    Invariant rb count cl axioms edges next facts := by
  have sub : ∀ q ∈ facts ++ p :: next, q ∈ facts ++ next := by
    intro q member
    simp only [List.mem_append,List.mem_cons] at member ⊢
    rcases member with old | rfl | later
    · exact .inl old
    · exact .inl present
    · exact .inr later
  exact { closed := inv.closed
          throughs := inv.throughs
          pendingIn := fun q member => inv.pendingIn q (List.mem_cons_of_mem _ member)
          factsIn := inv.factsIn
          nodup := inv.nodup
          edgesIn := inv.edgesIn
          requires := fun q member => requires_mono sub q (inv.requires q member)
          everywhere := fun n bound => sub _ (inv.everywhere n bound) }
/-- A new fact is added, and its pending entry is replaced by `extra`. -/
theorem invariant_add {rb : role_box.RoleBox} {count : Nat} {cl : List nnf.NnfConcept} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {next facts extra : List (Nat × nnf.NnfConcept)}
    {p : Nat × nnf.NnfConcept} (inv : Invariant rb count cl axioms edges (p :: next) facts) (fresh : p ∉ facts)
    (extraIn : ∀ q ∈ extra, q.1 < count ∧ q.2 ∈ cl)
    (required : Requires rb edges (p :: facts ++ (extra ++ next)) p) :
    Invariant rb count cl axioms edges (extra ++ next) (p :: facts) := by
  have sub : ∀ q ∈ facts ++ p :: next, q ∈ p :: facts ++ (extra ++ next) := by
    intro q member
    simp only [List.mem_append,List.mem_cons] at member ⊢
    rcases member with old | rfl | later
    · exact .inl (.inr old)
    · exact .inl (.inl rfl)
    · exact .inr (.inr later)
  refine { closed := inv.closed
           throughs := inv.throughs
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

/-- The procedure's contract on the current facts: for closed role axioms,
    acceptance yields a model over a type, and every model, in the given
    universes, forces acceptance. -/
def Decides (rb : role_box.RoleBox) (count : Nat) (axioms : nnf.NnfConcept) (edges : List (ObjectProperty × Nat × Nat))
    (current : List (Nat × nnf.NnfConcept)) (result : Bool) : Prop :=
  (result = true → Rowl.RoleBox.Closed rb → ∃ (Object : Type) (I : Interpretation Object Unit) (f : Nat → Object),
    RoleModel rb axioms current edges I f ∧ EntailedEdges rb count edges I f) ∧
  ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (f : Nat → Object),
    RoleModel rb axioms current edges I f) → result = true)

theorem model_mono {Object : Type u} {Value : Type v} {rb : role_box.RoleBox} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {small large : List (Nat × nnf.NnfConcept)}
    {I : Interpretation Object Value} {f : Nat → Object} (sub : ∀ p ∈ small, p ∈ large)
    (model : RoleModel rb axioms large edges I f) : RoleModel rb axioms small edges I f :=
  And.intro model.1 (And.intro model.2.1 (And.intro (fun p member => model.2.2.1 p (sub p member)) model.2.2.2))
/-- A contract on more facts is a contract on fewer, when every model of the
    fewer facts is a model of the more. -/
theorem decides_of_implies {rb : role_box.RoleBox} {count : Nat} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {small large : List (Nat × nnf.NnfConcept)} {result : Bool}
    (sub : ∀ p ∈ small, p ∈ large)
    (back : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (f : Nat → Object),
      RoleModel rb axioms small edges I f → RoleModel rb axioms large edges I f)
    (decides : Decides.{u,v} rb count axioms edges large result) : Decides.{u,v} rb count axioms edges small result := by
  refine ⟨fun accepted closed => ?_,fun ⟨Object,Value,I,f,model⟩ => decides.2 ⟨Object,Value,I,f,back I f model⟩⟩
  obtain ⟨Object,I,f,model,exact⟩ := decides.1 accepted closed
  exact ⟨Object,I,f,model_mono sub model,exact⟩

/-- Models of fewer facts extend to more facts that every such model satisfies. -/
theorem model_extend {Object : Type u} {Value : Type v} {rb : role_box.RoleBox} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {small large extra : List (Nat × nnf.NnfConcept)}
    {I : Interpretation Object Value} {f : Nat → Object} (cover : ∀ p ∈ large, p ∈ small ∨ p ∈ extra)
    (model : RoleModel rb axioms small edges I f) (implied : ∀ p ∈ extra, conceptDenote I p.2 (f p.1)) :
    RoleModel rb axioms large edges I f :=
  And.intro model.1 (And.intro model.2.1
    (And.intro (fun p member => (cover p member).elim (model.2.2.1 p) (implied p)) model.2.2.2))
theorem decides_of_extra {rb : role_box.RoleBox} {count : Nat} {axioms : nnf.NnfConcept}
    {edges : List (ObjectProperty × Nat × Nat)} {small large extra : List (Nat × nnf.NnfConcept)} {result : Bool}
    (sub : ∀ p ∈ small, p ∈ large) (cover : ∀ p ∈ large, p ∈ small ∨ p ∈ extra)
    (implied : ∀ {Object : Type u} {Value : Type v} (I : Interpretation Object Value) (f : Nat → Object),
      RoleModel rb axioms small edges I f → ∀ p ∈ extra, conceptDenote I p.2 (f p.1))
    (decides : Decides.{u,v} rb count axioms edges large result) : Decides.{u,v} rb count axioms edges small result :=
  decides_of_implies sub (fun I f model => model_extend cover model (implied I f model)) decides

/-- What a universal restriction at a node requires at the targets of its edges
    holds in every model of the role axioms where the restriction and the edges
    hold. -/
theorem pushes_hold {Object : Type u} {Value : Type v} {rb : role_box.RoleBox} {I : Interpretation Object Value}
    {f : Nat → Object} {q : ObjectProperty} {d : nnf.NnfConcept} {node : Nat}
    {edges : List (ObjectProperty × Nat × Nat)} (respects : Respects I rb)
    (universal : conceptDenote I (.Forall q d) (f node))
    (edgesHold : ∀ e ∈ edges, I.objectProperties e.1 (f e.2.1) (f e.2.2)) :
    ∀ p ∈ pushes rb q d node edges, conceptDenote I p.2 (f p.1) := by
  intro p member
  obtain ⟨s,m,edge,first,second⟩ := (pushes_mem rb q d node edges p).mp member
  rw [first]
  have related := edgesHold _ edge
  obtain ⟨below,kind⟩ := (universalItems_mem rb s q d p.2).mp second
  rcases kind with same | ⟨t,transitive,st,tq,same⟩
  · rw [same]; exact universal (f m) (respects_below respects below related)
  · rw [same]
    intro z next
    exact universal z (respects_below respects tq
      (respects.2 t transitive (f node) (f m) z (respects_below respects st related) next))

/-- The actual completion terminates on every call satisfying the invariants and
    decides exactly whether the added and pending facts have a model of the role
    axioms. -/
theorem complete_correct (rb : role_box.RoleBox) (count : Nat) (positive : 0 < count) (cl : List nnf.NnfConcept)
    (axioms : nnf.NnfConcept) (edges : abox.Edges) (pending facts : abox.Facts)
    (inv : Invariant rb count cl axioms (edgesList edges) (factsList pending) (factsList facts)) :
    ∃ result, abox.complete pending facts edges axioms rb = .ok result ∧
      Decides.{u,v} rb count axioms (edgesList edges) (factsList facts ++ factsList pending) result := by
  cases pending with
  | Empty =>
    rw [abox.complete.eq_def]
    by_cases clash : ∃ n k, (n,.NotAtom k) ∈ factsList facts ∧ (n,.Atom k) ∈ factsList facts
    · refine ⟨false,by simp [duplicate_facts_correct,has_clash_correct,clash],?_⟩
      constructor
      · intro impossible; cases impossible
      rintro ⟨Object,Value,I,f,_,_,holds,_⟩
      obtain ⟨n,k,negative,positive'⟩ := clash
      exact False.elim
        ((holds (n,.NotAtom k) (by simp [factsList,negative])) (holds (n,.Atom k) (by simp [factsList,positive'])))
    · obtain ⟨ok,okRun,okSound,okComplete⟩ := obligations_hold_correct.{u,v} facts facts axioms rb
      refine ⟨ok,by simp [duplicate_facts_correct,has_clash_correct,clash,okRun],?_⟩
      constructor
      · intro accepted closed
        have every := okSound accepted closed
        have alone : factsList facts ++ factsList abox.Facts.Empty = factsList facts := by simp [factsList]
        rw [alone]
        apply model_of_saturated rb closed count positive axioms _ _ (fun p member => (inv.factsIn p member).1)
          inv.edgesIn
        · intro p member
          simpa [factsList] using inv.requires p member
        · intro n bound
          simpa [factsList] using inv.everywhere n bound
        · intro n k negative positive'
          exact clash ⟨n,k,negative,positive'⟩
        · exact every
      · rintro ⟨Object,Value,I,f,respects,everywhere,holds,_⟩
        simp only [factsList,List.append_nil] at holds
        apply okComplete
        intro n r d member
        obtain ⟨y,edge,inner⟩ := holds (n,.Exists r d) member
        refine ⟨Object,Value,I,respects,everywhere,y,fun e eMem => ?_⟩
        simp only [List.mem_cons] at eMem
        rcases eMem with rfl | filler
        · exact inner
        · obtain ⟨q,e',universal,below,kind⟩ := (nodeFillers_mem rb r n _ e).mp filler
          have universal' := holds (n,.Forall q e') universal
          rcases kind with rfl | ⟨t,transitive,first,second,rfl⟩
          · exact universal' y (respects_below respects below edge)
          · intro z next
            exact universal' z (respects_below respects second
              (respects.2 t transitive (f n) y z (respects_below respects first edge) next))
  | Entry node c next =>
    rw [abox.complete.eq_def]
    have head := inv.pendingIn _ (List.mem_cons_self ..)
    by_cases present : (node.val,c) ∈ factsList facts
    · have inv' := invariant_skip inv present
      obtain ⟨result,run,decides⟩ := complete_correct rb count positive cl axioms edges next facts inv'
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
        rintro ⟨Object,Value,I,f,_,_,holds,_⟩
        exact False.elim (holds (node.val,.Bottom) (by simp [factsList]))
      | Top =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ :=
          complete_correct rb count positive cl axioms edges next (.Entry node .Top facts) inv'
        exact ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra unchanged back (fun _ _ _ p member => by cases member) decides⟩
      | Atom k =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ :=
          complete_correct rb count positive cl axioms edges next (.Entry node (.Atom k) facts) inv'
        exact ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra unchanged back (fun _ _ _ p member => by cases member) decides⟩
      | NotAtom k =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ :=
          complete_correct rb count positive cl axioms edges next (.Entry node (.NotAtom k) facts) inv'
        exact ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra unchanged back (fun _ _ _ p member => by cases member) decides⟩
      | Exists r d =>
        have inv' := invariant_add (extra := []) inv present (by simp) trivial
        have bound := facts_bound inv'
        obtain ⟨result,run,decides⟩ :=
          complete_correct rb count positive cl axioms edges next (.Entry node (.Exists r d) facts) inv'
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
        obtain ⟨result,run,decides⟩ := complete_correct rb count positive cl axioms edges
          (.Entry node a (.Entry node b next)) (.Entry node (.And a b) facts) inv'
        refine ⟨result,by simp [contains_fact_correct,present,run],
          decides_of_extra (extra := [(node.val,a),(node.val,b)]) ?_ ?_ ?_ decides⟩
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
          have both := model.2.2.1 (node.val,.And a b) (by simp [factsList])
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
        obtain ⟨left,leftRun,leftDecides⟩ := complete_correct rb count positive cl axioms edges
          (.Entry node a next) (.Entry node (.Or a b) facts) invLeft
        obtain ⟨right,rightRun,rightDecides⟩ := complete_correct rb count positive cl axioms edges
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
        have cover : ∀ (e : nnf.NnfConcept),
            ∀ p ∈ factsList (.Entry node (.Or a b) facts) ++ factsList (.Entry node e next),
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
        · intro accepted closed
          rcases Bool.or_eq_true_iff.mp accepted with chosen | chosen
          · obtain ⟨Object,I,f,model,exact⟩ := leftDecides.1 chosen closed
            exact ⟨Object,I,f,model_mono subLeft model,exact⟩
          · obtain ⟨Object,I,f,model,exact⟩ := rightDecides.1 chosen closed
            exact ⟨Object,I,f,model_mono subRight model,exact⟩
        · rintro ⟨Object,Value,I,f,model⟩
          rcases model.2.2.1 (node.val,.Or a b) (by simp [factsList]) with inA | inB
          · have := leftDecides.2 ⟨Object,Value,I,f,model_extend (cover a) model (by
              intro p member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst member; exact inA)⟩
            simp [this]
          · have := rightDecides.2 ⟨Object,Value,I,f,model_extend (cover b) model (by
              intro p member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst member; exact inB)⟩
            simp [this]
      | Forall q d =>
        have filler := inv.closed.2.2.2 q d head.2
        obtain ⟨pushed,pushRun,pushContents⟩ := propagate_correct edges node q d next rb
        have extraIn : ∀ p ∈ pushes rb q d node.val (edgesList edges), p.1 < count ∧ p.2 ∈ cl := by
          intro p member
          obtain ⟨s,m,edge,first,second⟩ := (pushes_mem rb q d node.val _ p).mp member
          refine ⟨first ▸ (inv.edgesIn _ edge).2,?_⟩
          obtain ⟨_,kind⟩ := (universalItems_mem rb s q d p.2).mp second
          rcases kind with same | ⟨t,transitive,_,_,same⟩
          · rw [same]; exact filler
          · rw [same]; exact inv.throughs q d head.2 t transitive
        have inv' := invariant_add (extra := pushes rb q d node.val (edgesList edges)) inv present extraIn
          (by
            intro s m edge x member
            simp only [List.mem_append,List.mem_cons]
            exact .inr (.inl ((pushes_mem rb q d node.val _ (m,x)).mpr ⟨s,m,edge,rfl,member⟩)))
        have bound := facts_bound inv'
        rw [← pushContents] at inv'
        obtain ⟨result,run,decides⟩ := complete_correct rb count positive cl axioms edges pushed
          (.Entry node (.Forall q d) facts) inv'
        refine ⟨result,by simp [contains_fact_correct,present,pushRun,run],?_⟩
        rw [pushContents] at decides
        refine decides_of_extra (extra := pushes rb q d node.val (edgesList edges)) ?_ ?_ ?_ decides
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
        · intro Object Value I f model
          exact pushes_hold model.1 (model.2.2.1 (node.val,.Forall q d) (by simp [factsList])) model.2.2.2
  | Through node t d next =>
    rw [abox.complete.eq_def]
    have head := inv.pendingIn _ (List.mem_cons_self ..)
    by_cases present : (node.val,.Forall t d) ∈ factsList facts
    · have inv' := invariant_skip inv present
      obtain ⟨result,run,decides⟩ := complete_correct rb count positive cl axioms edges next facts inv'
      refine ⟨result,by simp [contains_through_correct,present,run],?_⟩
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
    · have filler := inv.closed.2.2.2 t d head.2
      obtain ⟨pushed,pushRun,pushContents⟩ := propagate_correct edges node t d next rb
      have extraIn : ∀ p ∈ pushes rb t d node.val (edgesList edges), p.1 < count ∧ p.2 ∈ cl := by
        intro p member
        obtain ⟨s,m,edge,first,second⟩ := (pushes_mem rb t d node.val _ p).mp member
        refine ⟨first ▸ (inv.edgesIn _ edge).2,?_⟩
        obtain ⟨_,kind⟩ := (universalItems_mem rb s t d p.2).mp second
        rcases kind with same | ⟨t',transitive,_,_,same⟩
        · rw [same]; exact filler
        · rw [same]; exact inv.throughs t d head.2 t' transitive
      have inv' := invariant_add (extra := pushes rb t d node.val (edgesList edges)) inv present extraIn
        (by
          intro s m edge x member
          simp only [List.mem_append,List.mem_cons]
          exact .inr (.inl ((pushes_mem rb t d node.val _ (m,x)).mpr ⟨s,m,edge,rfl,member⟩)))
      have bound := facts_bound inv'
      rw [← pushContents] at inv'
      obtain ⟨result,run,decides⟩ := complete_correct rb count positive cl axioms edges pushed
        (.Through node t d facts) inv'
      refine ⟨result,by simp [contains_through_correct,present,pushRun,run],?_⟩
      rw [pushContents] at decides
      refine decides_of_extra (extra := pushes rb t d node.val (edgesList edges)) ?_ ?_ ?_ decides
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
      · intro Object Value I f model
        exact pushes_hold model.1 (model.2.2.1 (node.val,.Forall t d) (by simp [factsList])) model.2.2.2
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
    count, every acceptance under role axioms closed under composition yields an
    interpretation of the role axioms with an element for every node that
    satisfies the facts, the edges and the TBox concept everywhere, and that
    relates node elements only as the edges and role axioms entail; every such
    interpretation, in any universe, forces acceptance. -/
theorem abox_satisfiable_with_correct (count : Usize) (positive : 0 < count.val) (facts : abox.Facts)
    (edges : abox.Edges) (axioms : nnf.NnfConcept) (rb : role_box.RoleBox)
    (factsIn : ∀ p ∈ factsList facts, p.1 < count.val)
    (edgesIn : ∀ e ∈ edgesList edges, e.2.1 < count.val ∧ e.2.2 < count.val) :
    ∃ result, abox.abox_satisfiable_with count facts edges axioms rb = .ok result ∧
      (result = true → Rowl.RoleBox.Closed rb → ∃ (Object : Type) (I : Interpretation Object Unit) (f : Nat → Object),
        RoleModel rb axioms (factsList facts) (edgesList edges) I f ∧ EntailedEdges rb count.val (edgesList edges) I f) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (f : Nat → Object),
        RoleModel rb axioms (factsList facts) (edgesList edges) I f) → result = true) := by
  obtain ⟨initial,initialRun,initialContents⟩ := with_axioms_correct count facts axioms
  have base := closed_append (listSubconcepts_closed ((factsList facts).map Prod.snd)) (subconcepts_closed axioms)
  have inv : Invariant rb count.val (withThroughs rb (listSubconcepts ((factsList facts).map Prod.snd) ++
      subconcepts axioms)) axioms (edgesList edges) (factsList initial) (factsList .Empty) :=
    { closed := withThroughs_closed rb base
      throughs := withThroughs_throughs rb _
      pendingIn := by
        intro p member
        rw [initialContents] at member
        rcases List.mem_append.mp member with everywhere | given
        · simp only [List.mem_map,List.mem_range] at everywhere
          obtain ⟨n,bound,rfl⟩ := everywhere
          exact ⟨bound,withThroughs_base (List.mem_append_right _ (subconcepts_self axioms))⟩
        · exact ⟨factsIn p given,
            withThroughs_base (List.mem_append_left _ (listSubconcepts_self (List.mem_map_of_mem given)))⟩
      factsIn := by simp [factsList]
      nodup := List.nodup_nil
      edgesIn := edgesIn
      requires := by simp [factsList]
      everywhere := by
        intro n bound
        simp only [factsList,List.nil_append,initialContents,List.mem_append,List.mem_map,List.mem_range]
        exact .inl ⟨n,bound,rfl⟩ }
  obtain ⟨result,run,decides⟩ := complete_correct.{u,v} rb count.val positive _ axioms edges initial .Empty inv
  have contents : factsList abox.Facts.Empty ++ factsList initial =
      (List.range count.val).map (fun n => (n,axioms)) ++ factsList facts := by
    simp [factsList,initialContents]
  rw [contents] at decides
  refine ⟨result,by rw [abox.abox_satisfiable_with]; simp [initialRun,run],?_,?_⟩
  · intro accepted closed
    obtain ⟨Object,I,f,model,exact⟩ := decides.1 accepted closed
    exact ⟨Object,I,f,model_mono (fun p member => List.mem_append_right _ member) model,exact⟩
  · rintro ⟨Object,Value,I,f,model⟩
    apply decides.2
    refine ⟨Object,Value,I,f,model_extend (extra := (List.range count.val).map (fun n => (n,axioms)))
      (fun p member => (List.mem_append.mp member).symm) model ?_⟩
    intro p member
    simp only [List.mem_map] at member
    obtain ⟨n,_,rfl⟩ := member
    exact model.2.1 (f n)

/-- The ALC entry point, the procedure without role axioms. For facts and edges
    at nodes below a positive count, every acceptance yields an interpretation
    with an element for every node that satisfies the facts, the edges and the
    TBox concept everywhere, and every such interpretation, in any universe,
    forces acceptance. The accepting interpretation relates node elements only
    along the given edges. -/
theorem abox_satisfiable_correct (count : Usize) (positive : 0 < count.val) (facts : abox.Facts)
    (edges : abox.Edges) (axioms : nnf.NnfConcept) (factsIn : ∀ p ∈ factsList facts, p.1 < count.val)
    (edgesIn : ∀ e ∈ edgesList edges, e.2.1 < count.val ∧ e.2.2 < count.val) :
    ∃ result, abox.abox_satisfiable count facts edges axioms = .ok result ∧
      (result = true → ∃ (Object : Type) (I : Interpretation Object Unit) (f : Nat → Object),
        AboxModel axioms (factsList facts) (edgesList edges) I f ∧ ExactEdges count.val (edgesList edges) I f) ∧
      ((∃ (Object : Type u) (Value : Type v) (I : Interpretation Object Value) (f : Nat → Object),
        AboxModel axioms (factsList facts) (edgesList edges) I f) → result = true) := by
  obtain ⟨rb,noRun,noInclusions,noTransitive⟩ := no_roles_correct
  obtain ⟨result,run,sound,complete⟩ :=
    abox_satisfiable_with_correct.{u,v} count positive facts edges axioms rb factsIn edgesIn
  refine ⟨result,by rw [abox.abox_satisfiable]; simp [noRun,run],?_,?_⟩
  · intro accepted
    obtain ⟨Object,I,f,model,entailed⟩ := sound accepted (closed_of_empty rb noInclusions)
    refine ⟨Object,I,f,model.2,?_⟩
    intro r n m sourceIn targetIn related
    rcases entailed r n m sourceIn targetIn related with ⟨s,below,edge⟩ | ⟨t,transitive,_,_⟩
    · rcases below with rfl | listed
      · exact edge
      · simp [Rowl.RoleBox.inclusionList,noInclusions] at listed
    · simp [transitives,noTransitive] at transitive
  · rintro ⟨Object,Value,I,f,model⟩
    exact complete ⟨Object,Value,I,f,And.intro (respects_of_empty I rb noInclusions noTransitive) model⟩
end Rowl.AboxTableau
