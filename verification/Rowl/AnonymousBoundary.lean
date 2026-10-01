import Rowl.AssertionEquality

namespace Rowl.AnonymousBoundary
open Aeneas Aeneas.Std RowlRust.model RowlRust.anonymous_boundary Rowl.AnonymousGraph
open Rowl.AssertionEquality
attribute [local instance] Classical.propDecidable
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1500000

/-- Only anonymous endpoints of positive object assertions can have graph edges
    or named incidences. Other occurrences are harmless isolated vertices. -/
def First (item : AnnotatedAxiom) : Option AnonymousIndividual :=
  match item.axiom with
  | .ObjectPropertyAssertion _ (.Anonymous a) _ => some a
  | .ObjectPropertyAssertion _ (.Named _) (.Anonymous b) => some b
  | _ => none

def Second (item : AnnotatedAxiom) : Option AnonymousIndividual :=
  match item.axiom with
  | .ObjectPropertyAssertion _ (.Anonymous _) (.Anonymous b) => some b
  | _ => none

def Candidates (axioms : List AnnotatedAxiom) : List AnonymousIndividual :=
  axioms.flatMap (fun item => (First item).toList ++ (Second item).toList)

/-- The property, orientation and metadata belong to the assertion's structural
    identity; incidence itself requires precisely one named endpoint. -/
def TouchesNamed (item : AnnotatedAxiom) (vertex : AnonymousIndividual) : Prop :=
  match item.axiom with
  | .ObjectPropertyAssertion _ (.Anonymous a) (.Named _) => a = vertex
  | .ObjectPropertyAssertion _ (.Named _) (.Anonymous a) => a = vertex
  | _ => False

/-- The incident assertion subset has at most one structural equivalence class. -/
def AtMostOne (axioms : List AnnotatedAxiom) (vertex : AnonymousIndividual) : Prop :=
  ∀ first ∈ axioms, TouchesNamed first vertex → ∀ second ∈ axioms,
    TouchesNamed second vertex → AssertionEq first second

/-- Each connected component has a qualifying vertex. The full carrier also
    includes unused and otherwise occurring isolated vertices; these have zero
    named incidences and qualify automatically. Forest validity is separate. -/
def Restriction (axioms : List AnnotatedAxiom) : Prop :=
  ∀ root : AnonymousIndividual, ∃ vertex : AnonymousIndividual,
    (graph (closureEdges axioms)).Reachable (key root) (key vertex) ∧ AtMostOne axioms vertex

/-- A failing original endpoint belongs to a component with no qualifying vertex. -/
def Correct (axioms : List AnnotatedAxiom) : BoundaryCheck → Prop
  | .Allowed => Restriction axioms
  | .NoRoot root => root ∈ Candidates axioms ∧
      (∀ vertex : AnonymousIndividual,
        (graph (closureEdges axioms)).Reachable (key root) (key vertex) → ¬ AtMostOne axioms vertex) ∧
      ¬ Restriction axioms

/-- The first raw endpoint projection is total, retaining the original identity. -/
theorem first_candidate_total_correct (item : AnnotatedAxiom) :
    first_candidate item = .ok (First item) := by
  cases h : item.axiom <;> simp [first_candidate,First,h]
  case ObjectPropertyAssertion p a b => cases a <;> cases b <;> simp

/-- The second projection preserves only the other anonymous endpoint. -/
theorem second_candidate_total_correct (item : AnnotatedAxiom) :
    second_candidate item = .ok (Second item) := by
  cases h : item.axiom <;> simp [second_candidate,Second,h]
  case ObjectPropertyAssertion p a b => cases a <;> cases b <;> simp

/-- Exact positive named/anonymous incidence, with scoped structural identities. -/
theorem touches_named_total_correct (item : AnnotatedAxiom) (vertex : AnonymousIndividual) :
    touches_named item vertex = .ok (decide (TouchesNamed item vertex)) := by
  cases h : item.axiom <;> simp [touches_named,TouchesNamed,h]
  case ObjectPropertyAssertion p a b =>
    cases a <;> cases b <;> simp [TouchesNamed,same_individual_total_correct,key_injective.eq_iff]

private def Row (rows : List AnnotatedAxiom) (vertex : AnonymousIndividual) (first : AnnotatedAxiom) : Prop :=
  ∀ second ∈ rows, TouchesNamed second vertex → AssertionEq first second

private theorem row_from_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (vertex : AnonymousIndividual) (first : AnnotatedAxiom) (index : Usize) :
    row_from axioms vertex first index = .ok (decide (Row (axioms.val.drop index.val) vertex first)) := by
  rw [row_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    have recursive := row_from_total axioms vertex first next
    have splitting : Row (axioms.val.drop index.val) vertex first ↔
        ((TouchesNamed axioms.val[index.val] vertex → AssertionEq first axioms.val[index.val]) ∧
        Row (axioms.val.drop (index.val+1)) vertex first) := by
      simp only [Row,List.drop_eq_getElem_cons inside,List.forall_mem_cons]
    have splitBool : decide (Row (axioms.val.drop index.val) vertex first) =
        decide ((TouchesNamed axioms.val[index.val] vertex → AssertionEq first axioms.val[index.val]) ∧
          Row (axioms.val.drop (index.val+1)) vertex first) := decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases touched : TouchesNamed axioms.val[index.val] vertex <;>
      by_cases equal : AssertionEq first axioms.val[index.val] <;>
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,touches_named_total_correct,
        same_object_assertion_total_correct,advance,recursive,nv,touched,equal]
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty,Row]
termination_by axioms.val.length - index.val
decreasing_by omega

private def Limits (all rows : List AnnotatedAxiom) (vertex : AnonymousIndividual) : Prop :=
  ∀ first ∈ rows, TouchesNamed first vertex → Row all vertex first

private theorem limit_from_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (vertex : AnonymousIndividual) (index : Usize) :
    limit_from axioms vertex index = .ok (decide (Limits axioms.val (axioms.val.drop index.val) vertex)) := by
  rw [limit_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    have recursive := limit_from_total axioms vertex next
    have splitting : Limits axioms.val (axioms.val.drop index.val) vertex ↔
        ((TouchesNamed axioms.val[index.val] vertex → Row axioms.val vertex axioms.val[index.val]) ∧
          Limits axioms.val (axioms.val.drop (index.val+1)) vertex) := by
      simp only [Limits,List.drop_eq_getElem_cons inside,List.forall_mem_cons]
    have splitBool : decide (Limits axioms.val (axioms.val.drop index.val) vertex) =
        decide ((TouchesNamed axioms.val[index.val] vertex → Row axioms.val vertex axioms.val[index.val]) ∧
          Limits axioms.val (axioms.val.drop (index.val+1)) vertex) := decide_eq_decide.mpr splitting
    rw [splitBool]
    have row := row_from_total axioms vertex axioms.val[index.val] 0#usize
    by_cases touched : TouchesNamed axioms.val[index.val] vertex <;>
      by_cases limit : Row axioms.val vertex axioms.val[index.val] <;>
      simp [inside,alloc.vec.Vec.index_slice_index,lookup,touches_named_total_correct,
        row,advance,recursive,nv,touched,limit]
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty,Limits]
termination_by axioms.val.length - index.val
decreasing_by omega

/-- Total distinct-assertion bound; raw equivalent copies never increase it. -/
theorem at_most_one_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) (vertex : AnonymousIndividual) :
    at_most_one axioms vertex = .ok (decide (AtMostOne axioms.val vertex)) := by
  have execution := limit_from_total axioms vertex 0#usize
  change limit_from axioms vertex 0#usize = _
  rw [execution]
  exact congrArg Result.ok (decide_eq_decide.mpr (by simp only [Limits,Row,AtMostOne,show (0#usize).val = 0 from rfl,List.drop_zero]))

private def Qualifying (axioms : List AnnotatedAxiom) (edges : List Edge)
    (root vertex : AnonymousIndividual) : Prop :=
  (graph edges).Reachable (key root) (key vertex) ∧ AtMostOne axioms vertex

private theorem qualifies_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (edges : RowlRust.anonymous_graph.AnonymousEdges) (root : AnonymousIndividual)
    (candidate : Option AnonymousIndividual) :
    qualifies axioms edges root candidate = .ok
      (decide (∃ vertex ∈ candidate.toList, Qualifying axioms.val (edgeKeys edges) root vertex),edges) := by
  cases candidate with
  | none => simp [qualifies]
  | some vertex =>
    by_cases reach : (graph (edgeKeys edges)).Reachable (key root) (key vertex) <;>
      simp [qualifies,connected_total_correct,at_most_one_total_correct,Qualifying,reach]

private def Found (all : List AnnotatedAxiom) (edges : List Edge)
    (root : AnonymousIndividual) (rows : List AnnotatedAxiom) : Prop :=
  ∃ vertex ∈ Candidates rows, Qualifying all edges root vertex

private theorem find_from_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (edges : RowlRust.anonymous_graph.AnonymousEdges) (root : AnonymousIndividual) (index : Usize) :
    find_from axioms edges root index = .ok
      (decide (Found axioms.val (edgeKeys edges) root (axioms.val.drop index.val)),edges) := by
  rw [find_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    have recursive := find_from_total axioms edges root next
    let item := axioms.val[index.val]
    let P := ∃ vertex ∈ (First item).toList, Qualifying axioms.val (edgeKeys edges) root vertex
    let Q := ∃ vertex ∈ (Second item).toList, Qualifying axioms.val (edgeKeys edges) root vertex
    have splitting : Found axioms.val (edgeKeys edges) root (axioms.val.drop index.val) ↔
        P ∨ Q ∨ Found axioms.val (edgeKeys edges) root (axioms.val.drop (index.val+1)) := by
      simp only [Found,Candidates,List.drop_eq_getElem_cons inside,List.flatMap_cons,
        List.mem_append,or_and_right,exists_or,or_assoc,P,Q,item]
    have splitBool : decide (Found axioms.val (edgeKeys edges) root (axioms.val.drop index.val)) =
        decide (P ∨ Q ∨ Found axioms.val (edgeKeys edges) root (axioms.val.drop (index.val+1))) :=
      decide_eq_decide.mpr splitting
    rw [splitBool]
    by_cases p : (∃ vertex ∈ (First axioms.val[index.val]).toList, Qualifying axioms.val (edgeKeys edges) root vertex) <;>
      by_cases q : (∃ vertex ∈ (Second axioms.val[index.val]).toList, Qualifying axioms.val (edgeKeys edges) root vertex) <;>
      simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
        alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,
        second_candidate_total_correct,qualifies_total,advance,recursive,nv,P,Q,item,p,q,
        decide_true,decide_false,bind_ok,or_true,true_or,false_or,or_false] <;> simp_all
  · have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [inside,empty,Found,Candidates]
termination_by axioms.val.length - index.val
decreasing_by omega

private theorem touched_candidate (item : AnnotatedAxiom) (vertex : AnonymousIndividual)
    (touched : TouchesNamed item vertex) : vertex ∈ (First item).toList := by
  cases h : item.axiom <;> simp [TouchesNamed,h] at touched
  case ObjectPropertyAssertion p a b =>
    cases a <;> cases b <;> simp [TouchesNamed] at touched
    all_goals subst vertex; simp [First,h]

private theorem outside_limit (axioms : List AnnotatedAxiom) (vertex : AnonymousIndividual)
    (outside : vertex ∉ Candidates axioms) : AtMostOne axioms vertex := by
  intro first firstMem touched
  apply False.elim
  apply outside
  exact List.mem_flatMap.mpr ⟨first,firstMem,List.mem_append_left _ (touched_candidate first vertex touched)⟩

private theorem edge_candidates (axioms : List AnnotatedAxiom) (pair : Edge)
    (member : pair ∈ closureEdges axioms) :
    (∃ a ∈ Candidates axioms, key a = pair.1) ∧ (∃ b ∈ Candidates axioms, key b = pair.2) := by
  obtain ⟨item,itemMem,pairMem⟩ := List.mem_flatMap.mp member
  cases h : item.axiom <;> simp [axiomEdges,h] at pairMem
  case ObjectPropertyAssertion p a b =>
    cases a <;> cases b <;> simp [axiomEdges] at pairMem
    case Anonymous.Anonymous a b =>
      subst pair
      constructor
      · refine ⟨a,List.mem_flatMap.mpr ⟨item,itemMem,?_⟩,rfl⟩
        simp [First,Second,h]
      · refine ⟨b,List.mem_flatMap.mpr ⟨item,itemMem,?_⟩,rfl⟩
        simp [First,Second,h]

private theorem graph_supported (edges : List Edge) (S : Key → Prop)
    (supported : ∀ pair ∈ edges, S pair.1 ∧ S pair.2) :
    ∀ x y, (graph edges).Adj x y → S y := by
  induction edges with
  | nil => simp [graph]
  | cons pair rest ih =>
    intro x y adj
    rcases adj with old | added
    · exact ih (fun p mem => supported p (List.mem_cons_of_mem _ mem)) x y old
    · rw [SimpleGraph.edge_adj] at added
      rcases added with ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),_⟩
      · exact (supported pair List.mem_cons_self).2
      · exact (supported pair List.mem_cons_self).1

private theorem reachable_candidate (axioms : List AnnotatedAxiom) (root vertex : AnonymousIndividual)
    (member : root ∈ Candidates axioms)
    (reachable : (graph (closureEdges axioms)).Reachable (key root) (key vertex)) :
    vertex ∈ Candidates axioms := by
  let S := fun k => ∃ a ∈ Candidates axioms, key a = k
  have supported : ∀ pair ∈ closureEdges axioms, S pair.1 ∧ S pair.2 := edge_candidates axioms
  have initial : S (key root) := ⟨root,member,rfl⟩
  have finish : S (key vertex) := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at reachable
    generalize endpoint : key vertex = k at reachable ⊢
    induction reachable with
    | refl => exact initial
    | @tail x y prior adj ih => exact graph_supported (closureEdges axioms) S supported x y adj
  obtain ⟨a,aMem,equal⟩ := finish
  have same := key_injective equal
  simpa only [same] using aMem

private theorem found_iff_witness (axioms : List AnnotatedAxiom) (root : AnonymousIndividual)
    (member : root ∈ Candidates axioms) :
    Found axioms (closureEdges axioms) root axioms ↔
      ∃ vertex, (graph (closureEdges axioms)).Reachable (key root) (key vertex) ∧ AtMostOne axioms vertex := by
  constructor
  · rintro ⟨vertex,_,good⟩; exact ⟨vertex,good⟩
  · rintro ⟨vertex,reachable,limit⟩
    exact ⟨vertex,reachable_candidate axioms root vertex member reachable,reachable,limit⟩

private def Rows (all : List AnnotatedAxiom) (edges : List Edge) (rows : List AnnotatedAxiom) : Prop :=
  ∀ root ∈ Candidates rows, Found all edges root all

private theorem rows_iff_restriction (axioms : List AnnotatedAxiom) :
    Rows axioms (closureEdges axioms) axioms ↔ Restriction axioms := by
  constructor
  · intro valid root
    by_cases member : root ∈ Candidates axioms
    · exact (found_iff_witness axioms root member).mp (valid root member)
    · exact ⟨root,.rfl,outside_limit axioms root member⟩
  · intro valid root member
    exact (found_iff_witness axioms root member).mpr (valid root)

private def CorrectFrom (all : List AnnotatedAxiom) (edges : List Edge)
    (rows : List AnnotatedAxiom) : BoundaryCheck → Prop
  | .Allowed => Rows all edges rows
  | .NoRoot root => root ∈ Candidates rows ∧ ¬ Found all edges root all

private theorem check_from_total (axioms : alloc.vec.Vec AnnotatedAxiom)
    (edges : RowlRust.anonymous_graph.AnonymousEdges) (index : Usize) :
    ∃ result, check_from axioms edges index = .ok result ∧
      CorrectFrom axioms.val (edgeKeys edges) (axioms.val.drop index.val) result := by
  rw [check_from]
  by_cases inside : index.val < axioms.val.length
  · have lookup : axioms.index_usize index = .ok axioms.val[index.val] := by
      simp [alloc.vec.Vec.index_usize,List.getElem?_eq_getElem inside]
    obtain ⟨next,advance,nextval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have nv : next.val = index.val + 1 := by simpa using nextval
    obtain ⟨result,executed,correct⟩ := check_from_total axioms edges next
    have search : ∀ root, find_from axioms edges root 0#usize =
        .ok (decide (Found axioms.val (edgeKeys edges) root axioms.val),edges) := by
      intro root
      simpa only [show (0#usize).val = 0 from rfl,List.drop_zero] using find_from_total axioms edges root 0#usize
    have splitRows : Rows axioms.val (edgeKeys edges) (axioms.val.drop index.val) ↔
        (∀ root ∈ (First axioms.val[index.val]).toList, Found axioms.val (edgeKeys edges) root axioms.val) ∧
        (∀ root ∈ (Second axioms.val[index.val]).toList, Found axioms.val (edgeKeys edges) root axioms.val) ∧
        Rows axioms.val (edgeKeys edges) (axioms.val.drop (index.val+1)) := by
      simp only [Rows,Candidates,List.drop_eq_getElem_cons inside,List.flatMap_cons,
        List.forall_mem_append,and_assoc]
    have retain : CorrectFrom axioms.val (edgeKeys edges) (axioms.val.drop (index.val+1)) result := by
      simpa only [nv] using correct
    have tailMem : ∀ root ∈ Candidates (axioms.val.drop (index.val+1)),
        root ∈ Candidates (axioms.val.drop index.val) := by
      intro root member
      simpa only [Candidates,List.drop_eq_getElem_cons inside,List.flatMap_cons,List.mem_append] using
        (Or.inr member : root ∈ (First axioms.val[index.val]).toList ++ (Second axioms.val[index.val]).toList ∨
          root ∈ Candidates (axioms.val.drop (index.val+1)))
    have firstMem : ∀ root ∈ (First axioms.val[index.val]).toList,
        root ∈ Candidates (axioms.val.drop index.val) := by
      intro root member
      simp only [Candidates,List.drop_eq_getElem_cons inside,List.flatMap_cons,List.mem_append]
      exact Or.inl (Or.inl member)
    have secondMem : ∀ root ∈ (Second axioms.val[index.val]).toList,
        root ∈ Candidates (axioms.val.drop index.val) := by
      intro root member
      simp only [Candidates,List.drop_eq_getElem_cons inside,List.flatMap_cons,List.mem_append]
      exact Or.inl (Or.inr member)
    cases first : First axioms.val[index.val] with
    | none =>
      cases second : Second axioms.val[index.val] with
      | none =>
        refine ⟨result,?_,?_⟩
        · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
            alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,first,
            second_candidate_total_correct,second,advance,executed,bind_ok]
        · cases result with
          | Allowed => exact splitRows.mpr ⟨by simp [first],by simp [second],retain⟩
          | NoRoot root => exact ⟨tailMem root retain.1,retain.2⟩
      | some b =>
        by_cases goodB : Found axioms.val (edgeKeys edges) b axioms.val
        · refine ⟨result,?_,?_⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
              alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,first,
              second_candidate_total_correct,second,search,goodB,decide_true,advance,executed,bind_ok]; simp_all
          · cases result with
            | Allowed => exact splitRows.mpr ⟨by simp [first],by simpa [second] using goodB,retain⟩
            | NoRoot root => exact ⟨tailMem root retain.1,retain.2⟩
        · refine ⟨.NoRoot b,?_,secondMem b (by simp [second]),goodB⟩
          simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
            alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,first,
            second_candidate_total_correct,second,search,goodB,decide_false,bind_ok]; simp_all
    | some a =>
      by_cases goodA : Found axioms.val (edgeKeys edges) a axioms.val
      · cases second : Second axioms.val[index.val] with
        | none =>
          refine ⟨result,?_,?_⟩
          · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
              alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,first,
              second_candidate_total_correct,second,search,goodA,decide_true,advance,executed,bind_ok]; simp_all
          · cases result with
            | Allowed => exact splitRows.mpr ⟨by simpa [first] using goodA,by simp [second],retain⟩
            | NoRoot root => exact ⟨tailMem root retain.1,retain.2⟩
        | some b =>
          by_cases goodB : Found axioms.val (edgeKeys edges) b axioms.val
          · refine ⟨result,?_,?_⟩
            · simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
                alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,first,
                second_candidate_total_correct,second,search,goodA,goodB,decide_true,advance,executed,bind_ok]; simp_all
            · cases result with
              | Allowed => exact splitRows.mpr ⟨by simpa [first] using goodA,by simpa [second] using goodB,retain⟩
              | NoRoot root => exact ⟨tailMem root retain.1,retain.2⟩
          · refine ⟨.NoRoot b,?_,secondMem b (by simp [second]),goodB⟩
            simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
              alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,first,
              second_candidate_total_correct,second,search,goodA,goodB,decide_true,decide_false,bind_ok]; simp_all
      · refine ⟨.NoRoot a,?_,firstMem a (by simp [first]),goodA⟩
        simp only [alloc.vec.Vec.len_val,UScalar.lt_equiv,inside,↓reduceIte,
          alloc.vec.Vec.index_slice_index,lookup,first_candidate_total_correct,first,
          search,goodA,decide_false,bind_ok]; simp_all
  · refine ⟨.Allowed,by simp [inside],?_⟩
    have empty : axioms.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp [CorrectFrom,Rows,Candidates,empty]
termination_by axioms.val.length - index.val
decreasing_by omega

/-- The actual closure checker terminates and includes every graph component,
    including isolated occurrences omitted from its finite endpoint scan. -/
theorem check_boundary_total_correct (axioms : alloc.vec.Vec AnnotatedAxiom) :
    ∃ result, check_boundary axioms = .ok result ∧ Correct axioms.val result := by
  obtain ⟨edges,collected,projection⟩ := collect_edges_total_correct axioms
  obtain ⟨result,executed,correct⟩ := check_from_total axioms edges 0#usize
  refine ⟨result,by simp [check_boundary,collected,executed],?_⟩
  have actual : CorrectFrom axioms.val (closureEdges axioms.val) axioms.val result := by
    simpa only [show (0#usize).val = 0 from rfl,List.drop_zero,projection] using correct
  cases result with
  | Allowed => exact rows_iff_restriction axioms.val |>.mp actual
  | NoRoot root =>
    rcases actual with ⟨member,missing⟩
    have absent := (found_iff_witness axioms.val root member).not.mp missing
    refine ⟨member,?_,?_⟩
    · intro vertex reach limit; exact absent ⟨vertex,reach,limit⟩
    · intro valid; exact absent (valid root)

/-- Exact acceptance of the normative component condition, with duplicates
    interpreted using structural axiom equivalence rather than raw occurrences. -/
theorem check_boundary_accepted_iff (axioms : alloc.vec.Vec AnnotatedAxiom) :
    check_boundary axioms = .ok .Allowed ↔ Restriction axioms.val := by
  obtain ⟨result,executed,correct⟩ := check_boundary_total_correct axioms
  rw [executed]
  cases result with
  | Allowed => simp [Correct] at correct; simp [correct]
  | NoRoot root => simp [Correct] at correct; simp [correct.2.2]

end Rowl.AnonymousBoundary
