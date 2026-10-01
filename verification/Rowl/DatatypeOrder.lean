import Rowl.Collection
import Rowl.Symbols
import Mathlib.Logic.Relation

namespace Rowl.DatatypeOrder
open Aeneas Aeneas.Std RowlRust.model RowlRust.typing RowlRust.datatype_order
attribute [local instance] Classical.propDecidable
attribute [local simp] alloc.vec.Vec.eq_iff
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

abbrev Edge := Iri × Iri

def edgeKeys : Dependencies → List Edge
  | .Empty => []
  | .Edge smaller larger next => (smaller,larger)::edgeKeys next

/-- Only explicit typed datatype occurrences in a defining range add an edge. -/
def useEdges (uses : List Rowl.Collection.Row) (defined : Iri) : List Edge :=
  uses.filterMap (fun row => match row.2 with | .Datatype => some (row.1,defined) | _ => none)

def axiomEdges : Axiom → List Edge
  | .DatatypeDefinition defined range => useEdges (Rowl.Collection.rangeUses range) defined.iri
  | _ => []

def closureEdges (axioms : List AnnotatedAxiom) : List Edge :=
  axioms.flatMap (fun item => axiomEdges item.axiom)

/-- Directed reflexive reachability on exact datatype identities. -/
def Reach (edges : List Edge) (left right : Iri) : Prop :=
  Relation.ReflTransGen (fun a b => (a,b) ∈ edges) left right

/-- A nonempty directed path; reflexivity alone does not count as a cycle. -/
def Path (edges : List Edge) (left right : Iri) : Prop :=
  Relation.TransGen (fun a b => (a,b) ∈ edges) left right

def Acyclic (edges : List Edge) : Prop := ∀ value, ¬ Path edges value value

/-- A strict partial order containing every required dependency pair. -/
def Order (edges : List Edge) : Prop :=
  ∃ relation : Iri → Iri → Prop, (∀ value, ¬ relation value value) ∧ (∀ a b c, relation a b → relation b c → relation a c) ∧
    ∀ pair ∈ edges, relation pair.1 pair.2

/-- The actual datatype carrier in the full axiom closure. -/
def DatatypeNodes (axioms : List AnnotatedAxiom) : List Iri :=
  (axioms.flatMap Rowl.Collection.annotatedUses).filterMap
    (fun row => match row.2 with | .Datatype => some row.1 | _ => none)

/-- The normative strict partial order on the datatypes actually occurring in Ax.
    Values outside the carrier are unrestricted and do not affect this predicate. -/
def OrderOn (nodes : List Iri) (edges : List Edge) : Prop :=
  ∃ relation : Iri → Iri → Prop,
    (∀ value ∈ nodes, ¬ relation value value) ∧
    (∀ a ∈ nodes, ∀ b ∈ nodes, ∀ c ∈ nodes, relation a b → relation b c → relation a c) ∧
    ∀ pair ∈ edges, relation pair.1 pair.2

def Restriction (axioms : List AnnotatedAxiom) : Prop :=
  OrderOn (DatatypeNodes axioms) (closureEdges axioms)

/-- A rejection retains an original directed dependency with a reverse path,
    and proves that no permitted strict partial order exists. -/
def Correct (edges : List Edge) : DependencyCheck → Prop
  | .Acyclic => Order edges
  | .Cycle smaller larger => (smaller,larger) ∈ edges ∧ Reach edges larger smaller ∧ ¬ Order edges

private theorem reach_empty (a b : Iri) : Reach [] a b ↔ a = b := by
  constructor
  · intro path
    cases path with
    | refl => rfl
    | tail _ edge => simp at edge
  · rintro rfl; exact .refl

private theorem acyclic_empty : Acyclic [] := by
  intro value path
  cases path with
  | single edge => simp at edge
  | tail _ edge => simp at edge

private theorem iri_eq (left right : Iri) : left.spelling.val = right.spelling.val ↔ left = right := by
  cases left; cases right; simp

private def Cross (edges : List Edge) (a b x y : Iri) : Prop :=
  Reach edges x y ∨ (Reach edges x a ∧ Reach edges b y)

private theorem cross_trans (edges : List Edge) (a b x y z : Iri)
    (left : Cross edges a b x y) (right : Cross edges a b y z) : Cross edges a b x z := by
  rcases left with direct | added
  · rcases right with direct' | added'
    · exact Or.inl (direct.trans direct')
    · exact Or.inr ⟨direct.trans added'.1,added'.2⟩
  · rcases right with direct' | added'
    · exact Or.inr ⟨added.1,added.2.trans direct'⟩
    · exact Or.inr ⟨added.1,added'.2⟩

private theorem reach_mono (edges : List Edge) (a b x y : Iri) (path : Reach edges x y) :
    Reach ((a,b)::edges) x y := path.mono (fun _ _ member => List.mem_cons_of_mem _ member)

private theorem reachable_cons (edges : List Edge) (a b x y : Iri) :
    Reach ((a,b)::edges) x y ↔ Cross edges a b x y := by
  constructor
  · intro path
    induction path with
    | refl => exact Or.inl .refl
    | @tail z w prior edge ih =>
      apply cross_trans edges a b x z w ih
      rcases List.mem_cons.mp edge with equal | old
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        exact Or.inr ⟨.refl,.refl⟩
      · exact Or.inl (.single old)
  · rintro (direct | ⟨headPath,suffix⟩)
    · exact reach_mono edges a b x y direct
    · exact ((reach_mono edges a b x a headPath).tail (List.mem_cons_self)).trans
        (reach_mono edges a b b y suffix)

private def PositiveCross (edges : List Edge) (a b x y : Iri) : Prop :=
  Path edges x y ∨ (Reach edges x a ∧ Reach edges b y)

private theorem positive_cross_trans (edges : List Edge) (a b x y z : Iri)
    (left : PositiveCross edges a b x y) (right : PositiveCross edges a b y z) :
    PositiveCross edges a b x z := by
  rcases left with direct | added
  · rcases right with direct' | added'
    · exact Or.inl (direct.trans direct')
    · exact Or.inr ⟨direct.to_reflTransGen.trans added'.1,added'.2⟩
  · rcases right with direct' | added'
    · exact Or.inr ⟨added.1,added.2.trans direct'.to_reflTransGen⟩
    · exact Or.inr ⟨added.1,added'.2⟩

private theorem positive_cons (edges : List Edge) (a b x y : Iri) :
    Path ((a,b)::edges) x y ↔ PositiveCross edges a b x y := by
  constructor
  · intro path
    induction path using Relation.TransGen.trans_induction_on with
    | single edge =>
      rcases List.mem_cons.mp edge with equal | old
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        exact Or.inr ⟨.refl,.refl⟩
      · exact Or.inl (.single old)
    | @trans x y z left right ihLeft ihRight => exact positive_cross_trans edges a b x y z ihLeft ihRight
  · rintro (direct | ⟨headPath,suffix⟩)
    · exact direct.mono (fun _ _ member => List.mem_cons_of_mem _ member)
    · exact Relation.TransGen.trans_left
        (Relation.TransGen.tail' (reach_mono edges a b x a headPath) (List.mem_cons_self))
        (reach_mono edges a b b y suffix)

private theorem acyclic_cons (edges : List Edge) (a b : Iri) :
    Acyclic ((a,b)::edges) ↔ Acyclic edges ∧ ¬ Reach edges b a := by
  constructor
  · intro valid
    refine ⟨?_,?_⟩
    · intro value cycle
      exact valid value (cycle.mono (fun _ _ member => List.mem_cons_of_mem _ member))
    · intro reverse
      exact valid a (Relation.TransGen.trans_left (.single (List.mem_cons_self))
        (reach_mono edges a b b a reverse))
  · rintro ⟨old,noReverse⟩ value cycle
    rcases (positive_cons edges a b value value).mp cycle with direct | added
    · exact old value direct
    · exact noReverse (added.2.trans added.1)

private theorem path_in_order (edges : List Edge) (relation : Iri → Iri → Prop)
    (transitive : ∀ a b c, relation a b → relation b c → relation a c) (containsEdges : ∀ pair ∈ edges, relation pair.1 pair.2)
    (a b : Iri) (path : Path edges a b) : relation a b := by
  induction path with
  | single edge => exact containsEdges _ edge
  | tail prior edge ih => exact transitive _ _ _ ih (containsEdges _ edge)

/-- Cycle freedom is equivalent to the existence of a containing strict partial
    order. Nonempty transitive reachability is the constructive success witness. -/
theorem acyclic_iff_order (edges : List Edge) : Acyclic edges ↔ Order edges := by
  constructor
  · intro valid
    exact ⟨Path edges,valid,fun _ _ _ left right => left.trans right,fun _ member => .single member⟩
  · rintro ⟨relation,irreflexive,transitive,containsEdges⟩ value cycle
    exact irreflexive value (path_in_order edges relation transitive containsEdges value value cycle)

/-- Restricting a containing order to an actual carrier, or extending it by
    isolated values, preserves precisely the normative order condition. -/
theorem order_on_iff_order (nodes : List Iri) (edges : List Edge)
    (support : ∀ pair ∈ edges, pair.1 ∈ nodes ∧ pair.2 ∈ nodes) :
    OrderOn nodes edges ↔ Order edges := by
  constructor
  · rintro ⟨relation,irreflexive,transitive,containsEdges⟩
    refine ⟨fun a b => a ∈ nodes ∧ b ∈ nodes ∧ relation a b,?_,?_,?_⟩
    · rintro value ⟨member,_,same⟩; exact irreflexive value member same
    · rintro a b c ⟨aMem,bMem,ab⟩ ⟨_,cMem,bc⟩
      exact ⟨aMem,cMem,transitive a aMem b bMem c cMem ab bc⟩
    · intro pair member
      exact ⟨(support pair member).1,(support pair member).2,containsEdges pair member⟩
  · rintro ⟨relation,irreflexive,transitive,containsEdges⟩
    exact ⟨relation,fun value _ => irreflexive value,
      fun _ _ _ _ _ _ ab bc => transitive _ _ _ ab bc,containsEdges⟩

/-- The actual directed reachability operation is total and exact on arbitrary
    finite graphs, including loops and repetitions, and restores its owned input. -/
theorem reachable_total_correct (edges : Dependencies) (left right : Iri) :
    reachable edges left right = .ok (decide (Reach (edgeKeys edges) left right),edges) := by
  induction edges generalizing left right with
  | Empty =>
    by_cases same : left = right <;>
      simp [reachable,Rowl.Symbols.same_spelling_total_correct,iri_eq,edgeKeys,reach_empty,same]
  | Edge a b next ih =>
    by_cases same : left = right
    · subst right
      have reflexive : Reach (edgeKeys (.Edge a b next)) left left := .refl
      simp [reachable,Rowl.Symbols.same_spelling_total_correct,iri_eq,reflexive]
    · rw [reachable,Rowl.Symbols.same_spelling_total_correct]
      by_cases direct : Reach (edgeKeys next) left right <;>
        by_cases toA : Reach (edgeKeys next) left a <;>
        by_cases fromB : Reach (edgeKeys next) b right <;>
        simp [iri_eq,same,ih,edgeKeys,reachable_cons,Cross,direct,toA,fromB]

private theorem cyclic_edge (edges : List Edge) (a b : Iri)
    (member : (a,b) ∈ edges) (reverse : Reach edges b a) : ¬ Order edges := by
  intro permitted
  exact (acyclic_iff_order edges).mpr permitted a
    (Relation.TransGen.trans_left (.single member) reverse)

/-- The actual graph decision terminates with exact success or a witnessed
    original edge on a directed cycle; undirected diamonds are accepted. -/
theorem check_dependencies_total_correct (edges : Dependencies) :
    ∃ result, check_dependencies edges = .ok result ∧ Correct (edgeKeys edges) result := by
  induction edges with
  | Empty =>
    refine ⟨.Acyclic,by simp [check_dependencies],?_⟩
    apply (acyclic_iff_order []).mp
    exact acyclic_empty
  | Edge a b next ih =>
    by_cases reverse : Reach (edgeKeys next) b a
    · have member : (a,b) ∈ edgeKeys (.Edge a b next) := List.mem_cons_self
      have extended := reach_mono (edgeKeys next) a b b a reverse
      exact ⟨.Cycle a b,by simp [check_dependencies,reachable_total_correct,reverse],
        member,extended,cyclic_edge _ a b member extended⟩
    · obtain ⟨result,executed,correct⟩ := ih
      refine ⟨result,by simp [check_dependencies,reachable_total_correct,reverse,executed],?_⟩
      cases result with
      | Acyclic =>
        exact (acyclic_iff_order _).mp ((acyclic_cons (edgeKeys next) a b).mpr
          ⟨(acyclic_iff_order _).mpr correct,reverse⟩)
      | Cycle x y =>
        have member : (x,y) ∈ edgeKeys (.Edge a b next) := List.mem_cons_of_mem _ correct.1
        have extended := reach_mono (edgeKeys next) a b y x correct.2.1
        exact ⟨member,extended,cyclic_edge _ x y member extended⟩

private theorem dependency_uses_total (uses : RowlRust.collection.EntityUses) (defined : Iri)
    (tail : Dependencies) : ∃ result, dependency_uses uses defined tail = .ok result ∧
      edgeKeys result = useEdges (Rowl.Collection.rows uses) defined ++ edgeKeys tail := by
  induction uses with
  | Empty => exact ⟨tail,by simp [dependency_uses],by simp [useEdges,Rowl.Collection.rows]⟩
  | Entry iri kind next ih =>
    obtain ⟨result,executed,correct⟩ := ih
    cases kind with
    | Datatype =>
      exact ⟨.Edge iri defined result,by simp [dependency_uses,executed],
        by simp [edgeKeys,useEdges,Rowl.Collection.rows,correct]⟩
    | Class | ObjectProperty | DataProperty | AnnotationProperty | NamedIndividual =>
      all_goals exact ⟨result,by simp [dependency_uses,executed],
        by simp [useEdges,Rowl.Collection.rows,correct]⟩

private theorem axiom_dependencies_total (item : AnnotatedAxiom) (tail : Dependencies) :
    ∃ result, axiom_dependencies item tail = .ok result ∧
      edgeKeys result = axiomEdges item.axiom ++ edgeKeys tail := by
  cases body : item.axiom
  case DatatypeDefinition defined range =>
    obtain ⟨uses,executed,correct⟩ := Rowl.Collection.range_entities_total_correct range
    obtain ⟨result,used,edges⟩ := dependency_uses_total uses defined.iri tail
    exact ⟨result,by simp [axiom_dependencies,body,executed,used],by simpa [axiomEdges,body,correct] using edges⟩
  all_goals exact ⟨tail,by simp [axiom_dependencies,body],by simp [axiomEdges,body]⟩

private theorem visit_total (axioms : alloc.vec.Vec AnnotatedAxiom) (index : Usize) :
    ∃ result, visit_axioms axioms index = .ok result ∧
      edgeKeys result = closureEdges (axioms.val.drop index.val) := by
  rw [visit_axioms]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    obtain ⟨tail,executed,correct⟩ := visit_total axioms next
    obtain ⟨result,added,edges⟩ := axiom_dependencies_total axioms.val[index.val] tail
    refine ⟨result,by simp [inside,advance,executed,alloc.vec.Vec.index_slice_index,lookup,added],?_⟩
    change edgeKeys result = (axioms.val.drop index.val).flatMap (fun item => axiomEdges item.axiom)
    rw [List.drop_eq_getElem_cons inside,List.flatMap_cons]
    simpa only [correct,closureEdges,nv] using edges
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    exact ⟨.Empty,by simp [inside],by simp [edgeKeys,closureEdges,empty]⟩
termination_by axioms.val.length - index.val
decreasing_by omega

/-- Exact ordered dependency collection from every definition in the supplied
    raw closure, with all range datatype occurrences and no enclosing metadata. -/
theorem collect_dependencies_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, collect_dependencies axioms = .ok result ∧ edgeKeys result = closureEdges axioms.val := by
  obtain ⟨result,executed,correct⟩ := visit_total axioms 0#usize
  exact ⟨result,by simp [collect_dependencies,executed],by simpa using correct⟩

private theorem datatype_mem (uses : List Rowl.Collection.Row) (value : Iri) :
    value ∈ uses.filterMap (fun row => match row.2 with | .Datatype => some row.1 | _ => none) ↔
      (value,EntityKind.Datatype) ∈ uses := by
  induction uses with
  | nil => simp
  | cons row next ih =>
    rcases row with ⟨iri,kind⟩
    cases kind <;> simp [ih,Prod.mk.injEq]

private theorem use_edge_mem (uses : List Rowl.Collection.Row) (defined a b : Iri) :
    (a,b) ∈ useEdges uses defined ↔ b = defined ∧ (a,EntityKind.Datatype) ∈ uses := by
  induction uses with
  | nil => simp [useEdges]
  | cons row next ih =>
    rcases row with ⟨iri,kind⟩
    cases kind <;> simp [useEdges] at ih ⊢
    all_goals first | exact ih | (simp [ih,Prod.mk.injEq]; tauto)

/-- Every dependency endpoint is an actual typed datatype occurrence in Ax.
    This connects the graph carrier to the normative finite datatype set. -/
theorem dependency_support (axioms : List AnnotatedAxiom) :
    ∀ pair ∈ closureEdges axioms, pair.1 ∈ DatatypeNodes axioms ∧ pair.2 ∈ DatatypeNodes axioms := by
  intro pair member
  rcases pair with ⟨a,b⟩
  obtain ⟨item,itemMem,edgeMem⟩ := List.mem_flatMap.mp member
  have nodes (value : Iri) (used : (value,EntityKind.Datatype) ∈ Rowl.Collection.annotatedUses item) :
      value ∈ DatatypeNodes axioms := by
    apply (datatype_mem _ value).mpr
    exact List.mem_flatMap.mpr ⟨item,itemMem,used⟩
  cases body : item.axiom <;> simp only [axiomEdges,body,List.not_mem_nil] at edgeMem
  case DatatypeDefinition defined range =>
    obtain ⟨parent,child⟩ := (use_edge_mem (Rowl.Collection.rangeUses range) defined.iri a b).mp edgeMem
    subst b
    refine ⟨nodes a ?_,nodes defined.iri ?_⟩
    · simp only [Rowl.Collection.annotatedUses,body,Rowl.Collection.axiomUses]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ child)
    · simp [Rowl.Collection.annotatedUses,body,Rowl.Collection.axiomUses]

/-- The actual raw-closure operation terminates and returns exact order success
    or an original dependency pair whose reverse path proves rejection. -/
theorem check_acyclic_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_acyclic axioms = .ok result ∧ Correct (closureEdges axioms.val) result := by
  obtain ⟨dependencies,collected,collectCorrect⟩ := collect_dependencies_total_correct axioms
  obtain ⟨result,executed,correct⟩ := check_dependencies_total_correct dependencies
  exact ⟨result,by simp [check_acyclic,collected,executed],by simpa only [collectCorrect] using correct⟩

/-- No false acceptance or rejection for the full datatype dependency-order
    condition on the actual datatypes in the supplied raw axiom closure. -/
theorem check_acyclic_accepted_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_acyclic axioms = .ok .Acyclic ↔ Restriction axioms.val := by
  have carrier := order_on_iff_order (DatatypeNodes axioms.val) (closureEdges axioms.val)
    (dependency_support axioms.val)
  obtain ⟨result,executed,correct⟩ := check_acyclic_total_correct axioms
  rw [executed]
  cases result with
  | Acyclic =>
    have accepted : Restriction axioms.val := carrier.mpr correct
    simp [accepted]
  | Cycle a b =>
    have rejected : ¬ Restriction axioms.val := fun valid => correct.2.2 (carrier.mp valid)
    simp [rejected]

end Rowl.DatatypeOrder
