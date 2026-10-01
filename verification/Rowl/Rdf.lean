import Rowl.Generated.RowlFrontend

namespace Rowl.Rdf
open Aeneas Aeneas.Std RowlFrontendRust.rdf
attribute [local simp] alloc.vec.Vec.eq_iff
attribute [local instance] Classical.propDecidable

/-- Ordered raw records; an empty named graph is still a record. -/
def graphRows : NamedGraphs → List (GraphName × RawGraph)
  | .Empty => []
  | .Entry key graph next => (key, graph) :: graphRows next

def graphNames (graphs : NamedGraphs) : List GraphName := (graphRows graphs).map Prod.fst

def NamesUnique (graphs : NamedGraphs) : Prop := (graphNames graphs).Nodup

/-- Set membership disregards repeated stored triples, without changing storage. -/
def GraphContains (graph : RawGraph) (triple : Triple) : Prop := triple ∈ graph.triples.val

noncomputable def namedLookup (graphs : NamedGraphs) (key : GraphName) : Option RawGraph :=
  ((graphRows graphs).find? (fun row => decide (row.1 = key))).map Prod.snd

noncomputable def requestedGraph (dataset : RawDataset) : GraphChoice → Option RawGraph
  | .Default => some dataset.default
  | .Named key => namedLookup dataset.named key

noncomputable def RepeatedName (graphs : NamedGraphs) (key : GraphName) : Prop :=
  2 ≤ (graphNames graphs).countP (fun stored => decide (stored = key))

noncomputable def SelectionCorrect (dataset : RawDataset) (choice : GraphChoice) : SelectionResult → Prop
  | .Selected selection => NamesUnique dataset.named ∧ selection.dataset = dataset ∧
      requestedGraph dataset choice = some selection.graph
  | .MissingGraph => NamesUnique dataset.named ∧ requestedGraph dataset choice = none
  | .DuplicateGraphName key => RepeatedName dataset.named key

private theorem compare_correct (left right : alloc.vec.Vec U8)
    (equalLength : left.val.length = right.val.length) (index : Usize) :
    equal_from left right index =
      .ok (decide (left.val.drop index.val = right.val.drop index.val)) := by
  rw [equal_from]
  by_cases h : index.val < left.val.length
  · have notEnd : ¬ left.val.length ≤ index.val := by omega
    have hr : index.val < right.val.length := by omega
    have hlIndex : left.index_usize index = .ok left.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]
    have hrIndex : right.index_usize index = .ok right.val[index.val] := by
      simp [alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hr]
    by_cases heads : left.val[index.val] = right.val[index.val]
    · have size := left.property
      obtain ⟨next, hn, hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have nextval : next.val = index.val + 1 := by simpa using hv
      have ih := compare_correct left right equalLength next
      simp [notEnd, hlIndex, hrIndex, heads, hn, ih]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, true_and, nextval]
    · have different : left.val[index.val].val ≠ right.val[index.val].val := by
        intro same; exact heads (UScalar.eq_of_val_eq same)
      simp [notEnd, hlIndex, hrIndex, different]
      rw [List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hr]
      simp only [List.cons.injEq, heads, false_and, not_false_eq_true]
  · have ended : left.val.length ≤ index.val := by omega
    have hl : left.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hr : right.val.drop index.val = [] := List.drop_eq_nil_iff.mpr (by omega)
    simp only [UScalar.le_equiv, alloc.vec.Vec.len_val, ended, ↓reduceIte, hl, hr, decide_true]
termination_by left.val.length - index.val
decreasing_by omega

private theorem same_bytes_correct (left right : alloc.vec.Vec U8) :
    same_bytes left right = .ok (decide (left.val = right.val)) := by
  rw [same_bytes]
  by_cases h : left.val.length = right.val.length
  · have ih := compare_correct left right h 0#usize
    simpa [h] using ih
  · have unequal : left.val ≠ right.val := fun eq => h (congrArg List.length eq)
    simp [h, unequal]

/-- Exact identity; blank-node scope/label pairs cannot coincide with IRI names. -/
theorem same_graph_name_total_correct (left right : GraphName) :
    same_graph_name left right = .ok (decide (left = right)) := by
  classical
  cases left with
  | Iri left =>
    cases right with
    | Iri right =>
      cases left; cases right
      simp [same_graph_name, same_bytes_correct]
    | Blank right => simp [same_graph_name]
  | Blank left =>
    cases right with
    | Iri right => simp [same_graph_name]
    | Blank right =>
      cases left with
      | mk ls ll =>
        cases right with
        | mk rs rl =>
          by_cases scopes : ls.val = rs.val <;>
            simp [same_graph_name, same_bytes_correct, scopes]

private theorem find_correct (graphs : NamedGraphs) (key : GraphName) :
    find_graph graphs key = .ok (namedLookup graphs key) := by
  classical
  induction graphs with
  | Empty => simp [find_graph, namedLookup, graphRows]
  | Entry here graph next ih =>
    rw [find_graph, same_graph_name_total_correct]
    by_cases h : here = key <;> simp [h, namedLookup, graphRows] at ih ⊢
    exact ih

private theorem lookup_none_iff (graphs : NamedGraphs) (key : GraphName) :
    namedLookup graphs key = none ↔ key ∉ graphNames graphs := by
  classical
  induction graphs with
  | Empty => simp [namedLookup, graphNames, graphRows]
  | Entry here graph next ih =>
    by_cases h : here = key
    · simp [namedLookup, graphRows, graphNames, h]
    · simp [namedLookup, graphRows, graphNames, h, Ne.symm h] at ih ⊢
      exact ih

private theorem count_zero_of_unique (names : List GraphName) (unique : names.Nodup)
    (key : GraphName) : names.countP (fun stored => decide (stored = key)) ≤ 1 := by
  classical
  induction names with
  | nil => simp
  | cons here tail ih =>
    have clean := List.nodup_cons.mp unique
    have bound := ih clean.2
    by_cases equal : here = key
    · have zero : tail.countP (fun stored => decide (stored = key)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro x hx
        have ne : x ≠ key := by intro he; subst here; subst x; exact clean.1 hx
        simp [ne]
      simp [equal, zero]
    · simpa [equal] using bound

private theorem duplicate_correct (graphs : NamedGraphs) :
    ∃ found, first_duplicate graphs = .ok found ∧
      (match found with | none => NamesUnique graphs | some key => RepeatedName graphs key) := by
  classical
  induction graphs with
  | Empty => exact ⟨none, by simp [first_duplicate], by simp [NamesUnique, graphNames, graphRows]⟩
  | Entry key graph next ih =>
    rw [first_duplicate, find_correct]
    cases found : namedLookup next key with
    | some other =>
      have mem : key ∈ graphNames next := by
        by_contra absent
        have no := (lookup_none_iff next key).mpr absent
        rw [found] at no
        contradiction
      have positive : 0 < (graphNames next).countP (fun stored => decide (stored = key)) := by
        exact List.countP_pos_iff.mpr ⟨key, mem, by simp⟩
      refine ⟨some key, by simp [core.option.Option.is_some], ?_⟩
      change 2 ≤ (key :: graphNames next).countP (fun stored => decide (stored = key))
      simp only [List.countP_cons, decide_true, ↓reduceIte]
      omega
    | none =>
      have absent := (lookup_none_iff next key).mp found
      obtain ⟨tailFound, ht, correct⟩ := ih
      refine ⟨tailFound, by simp [core.option.Option.is_some, ht], ?_⟩
      cases tailFound with
      | none => exact List.nodup_cons.mpr ⟨absent, correct⟩
      | some repeated =>
        have bound : (graphNames next).countP (fun stored => decide (stored = repeated)) ≤
            (graphNames (.Entry key graph next)).countP (fun stored => decide (stored = repeated)) := by
          change (graphNames next).countP _ ≤ (key :: graphNames next).countP _
          rw [List.countP_cons]
          omega
        exact Nat.le_trans correct bound

/-- Total selection with exact success, absence and repeated-key diagnostics. -/
theorem select_graph_total_correct (dataset : RawDataset) (choice : GraphChoice) :
    ∃ result, select_graph dataset choice = .ok result ∧ SelectionCorrect dataset choice result := by
  obtain ⟨duplicate, hd, correct⟩ := duplicate_correct dataset.named
  cases duplicate with
  | some key => exact ⟨.DuplicateGraphName key, by simp [select_graph, hd], correct⟩
  | none =>
    cases choice with
    | Default => exact ⟨.Selected ⟨dataset, dataset.default⟩, by simp [select_graph, hd], correct, rfl, rfl⟩
    | Named key =>
      cases found : namedLookup dataset.named key with
      | none => exact ⟨.MissingGraph, by simp [select_graph, hd, find_correct, found], correct, found⟩
      | some graph => exact ⟨.Selected ⟨dataset, graph⟩, by simp [select_graph, hd, find_correct, found], correct, rfl, found⟩

/-- Successful runs retain the whole dataset verbatim and expose precisely the
    requested graph. All other graphs and cross-graph blank identities remain. -/
theorem successful_selection_preserves_dataset (dataset : RawDataset) (choice : GraphChoice)
    (selection : DatasetSelection) (success : select_graph dataset choice = .ok (.Selected selection)) :
    original_dataset selection = .ok dataset ∧
      selected_graph selection = .ok selection.graph ∧
      NamesUnique dataset.named ∧ requestedGraph dataset choice = some selection.graph := by
  obtain ⟨result, hr, correct⟩ := select_graph_total_correct dataset choice
  have same := Result.ok_injective (hr.symm.trans success)
  rw [same] at correct
  exact ⟨by simp [original_dataset, correct.2.1], rfl, correct.1, correct.2.2⟩

/-- Empty present graphs differ from missing graphs; duplicates are separate. -/
theorem missing_graph_iff (dataset : RawDataset) (choice : GraphChoice) :
    select_graph dataset choice = .ok .MissingGraph ↔
      NamesUnique dataset.named ∧ requestedGraph dataset choice = none := by
  obtain ⟨result, hr, correct⟩ := select_graph_total_correct dataset choice
  constructor
  · intro missing
    have same := Result.ok_injective (hr.symm.trans missing)
    rw [same] at correct
    exact correct
  · rintro ⟨unique, absent⟩
    cases result with
    | MissingGraph => exact hr
    | Selected selection =>
      have incompatible := correct.2.2
      rw [absent] at incompatible
      contradiction
    | DuplicateGraphName key =>
      have bound := count_zero_of_unique (graphNames dataset.named) unique key
      change RepeatedName dataset.named key at correct
      unfold RepeatedName at correct
      omega

/-- Default selection also rejects duplicate names in unselected graphs. -/
theorem default_selection_iff (dataset : RawDataset) :
    select_graph dataset .Default = .ok (.Selected ⟨dataset, dataset.default⟩) ↔
      NamesUnique dataset.named := by
  obtain ⟨result, hr, correct⟩ := select_graph_total_correct dataset .Default
  constructor
  · intro success
    have same := Result.ok_injective (hr.symm.trans success)
    rw [same] at correct
    exact correct.1
  · intro unique
    cases result with
    | MissingGraph => have impossible := correct.2; contradiction
    | DuplicateGraphName key =>
      have bound := count_zero_of_unique (graphNames dataset.named) unique key
      change RepeatedName dataset.named key at correct
      unfold RepeatedName at correct
      omega
    | Selected selection =>
      have graph : selection.graph = dataset.default := Option.some.inj correct.2.2 |>.symm
      have kept : selection.dataset = dataset := correct.2.1
      have same : selection = ⟨dataset, dataset.default⟩ := by cases selection; simp_all
      simpa [same] using hr

end Rowl.Rdf
